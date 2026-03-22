#!/usr/bin/env python3
"""
standalone.py — Descent-based computation of painted bipartitions (DRC diagrams)

Implements the combinatorics of special unipotent representations following:
  [BMSZ]  Barbasch–Ma–Sun–Zhu, "Special unipotent representations of real
          classical groups: construction and unitarity", arXiv:1712.05552v6
  [BMSZb] Barbasch–Ma–Sun–Zhu, "Special unipotent representations of real
          classical groups: counting and reduction", arXiv:2205.05266v4

This file is self-contained and uses only the descent algorithm (Definition 3.14
of [BMSZ]) — no theta lifting is used.

Key objects:
  - Painted bipartition τ = (ι, P) × (j, Q) × γ  (Definition 2.24 of [BMSZb])
  - Extended PBP: τ̂ = (τ, ℘) where ℘ ⊆ PP_★(Ǒ)
  - Descent map ∇: PBP_★(Ǒ) → PBP_{★'}(Ǒ')  (Definition 3.14 of [BMSZ])

Root system types (★):
  B (= B+ or B-) : O(p,q), p+q odd     ★' = C̃ (=M)
  C              : Sp(2n)               ★' = D
  D              : O(p,q), p+q even     ★' = C
  M (= C̃)       : Mp(2n)               ★' = B
"""
from itertools import chain
from copy import copy


# ============================================================================
# Phase 1: Core utilities — partitions and Young diagrams
# ============================================================================

def reg_part(part):
    """Regularize partition: sort descending, remove zeros."""
    return tuple(sorted((x for x in part if x > 0), reverse=True))


def part_trans(part):
    """Transpose (conjugate) partition: row lengths ↔ column lengths."""
    part = sorted((x for x in part if x > 0))
    if not part:
        return ()
    return tuple(sorted(
        (len([x for x in part if x > i]) for i in range(part[-1])),
        reverse=True))


def part_size(part):
    """Total number of boxes."""
    return sum(part)


def col_lengths(part):
    """Column lengths c_1 >= c_2 >= ... from row lengths r_1 >= r_2 >= ..."""
    return part_trans(part)


def row_lengths(part):
    """Just return the partition itself (rows are the natural representation)."""
    return reg_part(part)


def getz(seq, idx, default=None):
    """Safe index access."""
    try:
        return seq[idx]
    except (IndexError, KeyError):
        return default


# ============================================================================
# Phase 2: Orbit → bipartition  (Equation 2.16 of [BMSZb])
# ============================================================================

def orbit_to_bipartition(dpart, rtype):
    """
    Compute (ι_Ǒ, j_Ǒ) from dual partition Ǒ and type ★.

    Returns (tauL, tauR): column lengths of the two Young diagrams.
    tauL[i] = c_{i+1}(ι_Ǒ), tauR[i] = c_{i+1}(j_Ǒ).

    Reference: [BMSZb] Section 2.8, equation (2.16).
    """
    rows = reg_part(dpart)  # r_1 >= r_2 >= ...
    n = len(rows)

    if rtype == 'B':
        # ★ = B: Ǒ is type C, even rows only.
        # c_1(j) = r_1/2
        # For i >= 1: (c_i(ι), c_{i+1}(j)) = (r_{2i}/2, r_{2i+1}/2)
        # Pair up: add row of 0 if odd number of rows
        if n % 2 == 1:
            rows = rows + (0,)
            n += 1
        tauL = []
        tauR = [rows[0] // 2]  # c_1(j) = r_1/2
        for i in range(n // 2):
            tauL.append(rows[2 * i] // 2)
            if 2 * i + 1 < n:
                tauR.append(rows[2 * i + 1] // 2)
        tauL = reg_part(tauL)
        tauR = reg_part(tauR)
        return (tauL, tauR)

    elif rtype == 'M':
        # ★ = C̃: Ǒ is type C, even rows only.
        # For i >= 1: (c_i(ι), c_i(j)) = (r_{2i-1}/2, r_{2i}/2)
        if n % 2 == 1:
            rows = rows + (0,)
            n += 1
        tauL = []
        tauR = []
        for i in range(n // 2):
            tauL.append(rows[2 * i] // 2)
            tauR.append(rows[2 * i + 1] // 2)
        tauL = reg_part(tauL)
        tauR = reg_part(tauR)
        return (tauL, tauR)

    elif rtype in ('C',):
        # ★ = C: Ǒ is type B, odd rows only.
        # (c_i(j), c_i(ι)) for i >= 1:
        #   (2i-1, 2i) vacant → (0, 0)
        #   (2i-1, 2i) tailed → ((r_{2i-1}-1)/2, 0)
        #   otherwise → ((r_{2i-1}-1)/2, (r_{2i}+1)/2)
        if n % 2 == 0:
            rows = rows + (0,)
            n += 1
        tauL = []
        tauR = []
        for i in range(1, (n + 2) // 2 + 1):
            r_odd = getz(rows, 2 * i - 2, 0)   # r_{2i-1}
            r_even = getz(rows, 2 * i - 1, 0)  # r_{2i}
            if r_odd == 0 and r_even == 0:
                pass  # vacant
            elif r_even == 0 and r_odd > 0:
                # tailed
                tauR.append((r_odd - 1) // 2)
                tauL.append(0)
            else:
                tauR.append((r_odd - 1) // 2)
                tauL.append((r_even + 1) // 2)
        tauL = reg_part(tauL)
        tauR = reg_part(tauR)
        return (tauL, tauR)

    elif rtype in ('D',):
        # ★ = D: Ǒ is type D, odd rows only.
        # c_1(ι) = (r_1+1)/2 if r_1 > 0, else 0
        # For i >= 1: (c_i(j), c_{i+1}(ι)):
        #   (2i, 2i+1) vacant → (0, 0)
        #   (2i, 2i+1) tailed → ((r_{2i}-1)/2, 0)
        #   otherwise → ((r_{2i}-1)/2, (r_{2i+1}+1)/2)
        if n % 2 == 1:
            rows = rows + (0,)
            n += 1
        tauL = []
        tauR = []
        if rows[0] > 0:
            tauL.append((rows[0] + 1) // 2)
        for i in range(1, n // 2 + 1):
            r_even = getz(rows, 2 * i - 1, 0)  # r_{2i}
            r_odd = getz(rows, 2 * i, 0)       # r_{2i+1}
            if r_even == 0 and r_odd == 0:
                pass
            elif r_odd == 0 and r_even > 0:
                tauR.append((r_even - 1) // 2)
            else:
                tauR.append((r_even - 1) // 2)
                tauL.append((r_odd + 1) // 2)
        tauL = reg_part(tauL)
        tauR = reg_part(tauR)
        return (tauL, tauR)

    else:
        raise ValueError(f"Unknown rtype: {rtype}")


# ============================================================================
# Phase 3: Primitive pairs  (Definition 2.21 of [BMSZb])
# ============================================================================

def primitive_pairs(dpart, rtype):
    """
    Compute PP_★(Ǒ): the set of primitive ★-pairs in Ǒ.

    A ★-pair (i, i+1) is primitive if r_i(Ǒ) - r_{i+1}(Ǒ) is positive and even.
    The parity of i depends on ★:
      ★ ∈ {C, C̃, C*}: i is odd
      ★ ∈ {B, D, D*}: i is even

    Returns a set of pairs (i, i+1) (1-indexed).
    """
    rows = reg_part(dpart)
    PP = set()
    for idx in range(len(rows)):
        i = idx + 1  # 1-indexed
        r_i = getz(rows, idx, 0)
        r_next = getz(rows, idx + 1, 0)
        diff = r_i - r_next

        if rtype in ('C', 'M'):  # C, C̃
            need_odd_i = True
        elif rtype in ('B', 'D'):
            need_odd_i = False
        else:
            raise ValueError(f"Unknown rtype: {rtype}")

        if need_odd_i and i % 2 == 0:
            continue
        if not need_odd_i and i % 2 == 1:
            continue
        if diff > 0 and diff % 2 == 0:
            PP.add((i, i + 1))

    return PP


# ============================================================================
# Phase 4: DRC representation and display
# ============================================================================

def reg_drc(drc):
    """Remove empty trailing columns."""
    if drc is None:
        return None
    drcL, drcR = drc
    drcL = tuple(x for x in drcL if len(x) > 0)
    drcR = tuple(x for x in drcR if len(x) > 0)
    return (drcL, drcR)


def str_dgms(drc):
    """Display a DRC diagram as ASCII art."""
    drcL, drcR = drc
    cL, cR = len(drcL), len(drcR)
    r = max(len(getz(drcL, 0, '')), len(getz(drcR, 0, '')))
    S = []
    for i in range(r):
        ll = [getz(cl, i, ' ') for cl in drcL]
        rr = [getz(cr, i, ' ') for cr in drcR]
        S.append(''.join(ll) + '|' + ''.join(rr))
    s = '\n'.join(S)
    s = s.replace('*', '.')
    return s


def concat_strblocks(*args, sep=' '):
    """Combine string blocks side by side."""
    BLK = [b.splitlines() for b in args]
    v = max((0, *(len(b) for b in BLK)))
    hBLK = [max((0, *(len(r) for r in b))) for b in BLK]
    res = []
    for i in range(v):
        l = [b[i] + ' ' * (hBLK[j] - len(b[i])) if i < len(b) else ' ' * hBLK[j]
             for j, b in enumerate(BLK)]
        res.append(sep.join(l))
    return '\n'.join(res)


# ============================================================================
# Phase 5: DRC verification  (Definition 3.1 / 2.24)
# ============================================================================

# Symbol sets for P and Q by type (Definition 2.24 / 3.3)
P_SYMBOLS = {
    'B+': set('*c'), 'B-': set('*c'),
    'C': set('*rcd'), 'D': set('*srcd'), 'M': set('*sc'),
}
Q_SYMBOLS = {
    'B+': set('*srd'), 'B-': set('*srd'),
    'C': set('*s'), 'D': set('*'), 'M': set('*rd'),
}

HOWE_DUAL = {'B': 'M', 'M': 'B', 'C': 'D', 'D': 'C',
             'B+': 'M', 'B-': 'M'}


def verify_painting(dg, allowed_symbols):
    """Check that a painted Young diagram uses only allowed symbols."""
    for col in dg:
        for ch in col:
            if ch not in allowed_symbols:
                return False
    return True


def test_young_dg(dg):
    """Check that column lengths are non-increasing."""
    return all(len(getz(dg, i, '')) >= len(getz(dg, i + 1, ''))
               for i in range(len(dg)))


def count_symbol(drc, sym):
    """Count occurrences of a symbol in both diagrams."""
    drcL, drcR = drc
    return sum(c.count(sym) for c in chain(drcL, drcR))


def verify_drc(drc, rtype):
    """
    Verify that a DRC diagram satisfies all structural constraints.
    Reference: Definition 3.1 and Definition 2.24 of [BMSZb].
    """
    drcL, drcR = drc
    gamma = rtype

    # Both must be valid Young diagrams
    if not test_young_dg(drcL) or not test_young_dg(drcR):
        return False

    # Check symbol constraints
    p_sym = P_SYMBOLS.get(gamma, None)
    q_sym = Q_SYMBOLS.get(gamma, None)
    if p_sym is None or q_sym is None:
        return False
    if not verify_painting(drcL, p_sym):
        return False
    if not verify_painting(drcR, q_sym):
        return False

    # P and Q must have identical •-boxes
    for i in range(max(len(drcL), len(drcR))):
        cL = getz(drcL, i, '')
        cR = getz(drcR, i, '')
        nL = cL.count('*')
        nR = cR.count('*')
        if nL != nR:
            return False

    # Each row: at most one s, at most one r (across both diagrams)
    r_max = max(len(getz(drcL, 0, '')), len(getz(drcR, 0, '')))
    for row in range(r_max):
        s_count = sum(1 for col in chain(drcL, drcR)
                      if row < len(col) and col[row] == 's')
        r_count = sum(1 for col in chain(drcL, drcR)
                      if row < len(col) and col[row] == 'r')
        if s_count > 1 or r_count > 1:
            return False

    # Each column: at most one c, at most one d
    for col in chain(drcL, drcR):
        if col.count('c') > 1 or col.count('d') > 1:
            return False

    return True


# ============================================================================
# Phase 6: PBP enumeration — filling algorithm
# ============================================================================

def _simp_W_repn(tau):
    """Simplify bipartition: strip trailing zeros, check decreasing."""
    tauL, tauR = tau
    tauL = [x for x in tauL if x > 0]
    tauR = [x for x in tauR if x > 0]
    # Check decreasing
    for i in range(len(tauL) - 1):
        if tauL[i] < tauL[i + 1]:
            return None
    for i in range(len(tauR) - 1):
        if tauR[i] < tauR[i + 1]:
            return None
    return (tauL, tauR)


def _frow_col_list(part):
    """Group column indices by their length (for c-filling)."""
    lidx = {}
    for i, l in enumerate(part):
        lidx[l] = lidx.get(l, []) + [i]
    return list(lidx.values())


def _yield_cindex(lidxs):
    """Yield subsets of column indices respecting the group structure."""
    nlst = len(lidxs)
    llens = [len(lt) for lt in lidxs]
    cidx = [0 for _ in lidxs]
    yield [x for lt in lidxs for x in lt]
    while True:
        for i in reversed(range(nlst)):
            if cidx[i] != llens[i]:
                break
        else:
            return
        cidx[i] += 1
        cidx = cidx[:i + 1] + [0] * (nlst - i - 1)
        yield [x for j, lt in enumerate(lidxs) for x in lt[cidx[j]:llens[j]]]


def _frow_data(part):
    """Compute the row-difference data for r-filling."""
    if not part:
        return []
    return [part[i] - getz(part, i + 1, 0) for i in range(len(part))]


def _yield_r_del(Rind):
    """Yield all valid r-deletion vectors."""
    nlst = len(Rind)
    ridx = list(Rind)
    yield list(ridx)
    while True:
        for i in range(nlst):
            if ridx[i] > 0:
                break
        else:
            return
        ridx = list(Rind[:i]) + [ridx[i] - 1] + list(ridx[i + 1:])
        yield list(ridx)


# Identity and swap transforms for left/right diagrams
IDdgm = lambda x: x
SWdgm = lambda x: (x[1], x[0])


def fill_rdot(tau, reststeps=None, sym='s', LRdgm=IDdgm):
    """Fill remaining cells with dots and the given symbol."""
    tau = _simp_W_repn(tau)
    if tau is not None:
        tauL, tauR = LRdgm(tau)
        drcL, drcR = [], []
        cols = max(len(tauL), len(tauR))
        for i in range(cols):
            cL = getz(tauL, i, 0)
            cR = getz(tauR, i, 0)
            ncL = getz(tauL, i + 1, 0)
            if cL >= cR and cL - cR <= cL - ncL:
                bul = '*' * cR
                drcR.append(bul)
                drcL.append(bul + sym * (cL - cR))
            else:
                return
        yield LRdgm((tuple(drcL), tuple(drcR)))


def fill_r(tau, reststeps, sym='r', LRdgm=IDdgm):
    """Fill r-type symbols on the diagram."""
    rrsteps = reststeps[1:]
    rfun, rparam = reststeps[0]
    tau = _simp_W_repn(tau)
    if tau is not None:
        tauL, tauR = LRdgm(tau)
        rL = len(tauL)
        frow_lst = _frow_data(tauL)
        for rdel in _yield_r_del(frow_lst):
            tauLL = [tauL[i] - rdel[i] for i in range(rL)]
            for drcL, drcR in rfun((tauLL, tauR), rrsteps, *rparam):
                drcLL = tuple(getz(drcL, i, '') + (sym * rdel[i])
                              for i in range(rL))
                yield LRdgm((drcLL, drcR))


def fill_c(tau, reststeps, sym='c', LRdgm=IDdgm):
    """Fill c-type symbols at column bottoms."""
    rrsteps = reststeps[1:]
    rfun, rparam = reststeps[0]
    tau = _simp_W_repn(tau)
    if tau is not None:
        tauL, tauR = LRdgm(tau)
        rL = len(tauL)
        frow_lst = _frow_col_list(tauL)
        for cidx in _yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -= 1
            for drcL, drcR in rfun((tauLL, tauR), rrsteps, *rparam):
                drcL = list(drcL) + [''] * (rL - len(drcL))
                for i in cidx:
                    drcL[i] = getz(drcL, i, '') + sym
                yield LRdgm((tuple(drcL), drcR))


# Filling pipelines for each type (see drc.py steps_*)
STEPS = {
    'D': [
        (fill_c, ('d',)),
        (fill_c, ('c',)),
        (fill_r, ('r',)),
        (fill_rdot, ('s',))],
    'C': [
        (fill_c, ('d',)),
        (fill_c, ('c',)),
        (fill_r, ('s', SWdgm)),
        (fill_rdot, ('r', SWdgm))],
    'B': [
        (fill_c, ('d', SWdgm)),
        (fill_c, ('c', SWdgm)),
        (fill_r, ('r', SWdgm)),
        (fill_rdot, ('s',))],
    'M': [
        (fill_c, ('d', SWdgm)),
        (fill_c, ('c', SWdgm)),
        (fill_r, ('r', SWdgm)),
        (fill_rdot, ('s', SWdgm))],
}


def fill_drc(tau, rtype):
    """
    Enumerate all painted bipartitions for the bipartition tau and type rtype.
    Returns a list of DRC diagrams (drcL, drcR).
    """
    steps = STEPS[rtype]
    ffun, fparam = steps[0]
    return list(ffun(tau, steps[1:], *fparam))


def _allsubsets(S):
    """Yield all subsets of S."""
    S = list(S)
    for i in range(len(S) + 1):
        from itertools import combinations
        for ss in combinations(S, i):
            yield ss


def dpart2Wrepns(dpart, rtype):
    """
    Compute all W-representations (bipartitions) in the coherent family
    attached to the dual partition dpart and type rtype.

    This enumerates all bipartitions by selecting subsets of primitive pair
    indices to "swap". Reference: [BMSZb] Section 8.3.
    """
    dpart = reg_part(dpart)
    rows = list(dpart)
    a, res = divmod(len(rows), 2)

    if rtype == 'M' and res == 1:
        rows.append(0)
        a += 1
    elif rtype == 'C' and res == 1:
        rows.append(-1)
        a += 1
    elif rtype == 'B' and res == 0:
        rows.append(0)
    elif rtype == 'D' and res == 0:
        rows.append(-1)

    RES = []
    if rtype in ('B', 'D'):
        PPidx = [i for i in range(a)
                 if rows[2 * i + 1] > rows[2 * i + 2] and rows[2 * i + 2] >= 0]
    elif rtype in ('C', 'M'):
        PPidx = [i for i in range(a)
                 if rows[2 * i] > rows[2 * i + 1] and rows[2 * i + 1] >= 0]
    else:
        PPidx = []

    if rtype in ('B', 'M'):
        if rtype == 'B':
            otauL, otauR = [], [rows[0] // 2]
            rows = rows[1:]
        else:
            otauL, otauR = [], []
        for P in _allsubsets(PPidx):
            tauL, tauR = [], []
            for i in range(a):
                if i in P:
                    tauL.append(rows[2 * i + 1] // 2)
                    tauR.append(rows[2 * i] // 2)
                else:
                    tauL.append(rows[2 * i] // 2)
                    tauR.append(rows[2 * i + 1] // 2)
            tau = (sorted([x for x in otauL + tauL if x > 0], reverse=True),
                   sorted([x for x in otauR + tauR if x > 0], reverse=True))
            RES.append(tau)

    elif rtype in ('D', 'C'):
        if rtype == 'D':
            otauL, otauR = [(rows[0] + 1) // 2], []
            rows = rows[1:]
        else:
            otauL, otauR = [], []
        for P in _allsubsets(PPidx):
            tauL, tauR = [], []
            for i in range(a):
                if i in P:
                    tauR.append((rows[2 * i + 1] - 1) // 2)
                    tauL.append((rows[2 * i] + 1) // 2)
                else:
                    tauR.append((rows[2 * i] - 1) // 2)
                    tauL.append((rows[2 * i + 1] + 1) // 2)
            tau = (sorted([x for x in otauL + tauL if x > 0], reverse=True),
                   sorted([x for x in otauR + tauR if x > 0], reverse=True))
            RES.append(tau)

    return RES


def dpart2drc(dpart, rtype):
    """
    Compute all DRC diagrams for a dual partition and type.
    Returns a list of regularized DRC diagrams.
    """
    Atau = dpart2Wrepns(dpart, rtype)
    all_drcs = []
    for tau in Atau:
        drcs = fill_drc(tau, rtype)
        all_drcs.extend(reg_drc(drc) for drc in drcs)
    return all_drcs


# ============================================================================
# Phase 7: Signature and group form  (Equations 3.3-3.6 / 2.17 of [BMSZb])
# ============================================================================

def signature(drc, rtype):
    """
    Compute (p_τ, q_τ) for the painted bipartition.
    Reference: Equation (3.3) of [BMSZ] / (2.17) of [BMSZb].
    """
    n_dot = count_symbol(drc, '*')
    n_r = count_symbol(drc, 'r')
    n_s = count_symbol(drc, 's')
    n_c = count_symbol(drc, 'c')
    n_d = count_symbol(drc, 'd')

    if rtype in ('B+', 'B', 'D'):
        p = n_dot + 2 * n_r + n_c + n_d + (1 if rtype == 'B+' else 0)
        q = n_dot + 2 * n_s + n_c + n_d + (1 if rtype in ('B', 'B-') else 0)
        return (p, q)
    elif rtype in ('C', 'M'):
        n = n_dot + n_r + n_s + n_c + n_d
        return (n, n)
    elif rtype == 'B-':
        p = n_dot + 2 * n_r + n_c + n_d
        q = n_dot + 2 * n_s + n_c + n_d + 1
        return (p, q)
    else:
        raise ValueError(f"Unknown rtype: {rtype}")


def epsilon(drc, rtype):
    """
    Compute ε_τ ∈ {0, 1}.
    ε_τ = 0 iff 'd' occurs in the first column of P or Q.
    Reference: Equation (3.6) of [BMSZ].
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')
    fR = getz(drcR, 0, '')
    if 'd' in fL or 'd' in fR:
        return 0
    return 1


# ============================================================================
# Phase 8: Naive descent  (Lemma 3.7 / Lemma 10.4-10.5 of [BMSZb])
# ============================================================================

def _count_ds(s):
    """Count • and s in a column string."""
    return s.count('*') + s.count('s')


def _fill_ds_C(drc):
    """Redistribute dots/s for C-type (Lemma 3.7a with ★=C)."""
    from itertools import zip_longest
    drcL, drcR = drc
    ndrcL, ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = _count_ds(colL), len(colR)
        ndrcL.append('*' * cL + colL[cL:])
        ndrcR.append('*' * cL + 's' * (cR - cL))
    return reg_drc((tuple(ndrcL), tuple(ndrcR)))


def _fill_ds_D(drc):
    """Redistribute dots/s for D-type (Lemma 3.7a with ★=D)."""
    from itertools import zip_longest
    drcL, drcR = drc
    ndrcL, ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = len(colL), _count_ds(colR)
        ndrcL.append('*' * cR + 's' * (cL - cR) + colL[cL:])
        ndrcR.append('*' * cR + colR[cR:])
    return reg_drc((tuple(ndrcL), tuple(ndrcR)))


def _fill_ds_M(drc):
    """Redistribute dots/s for M-type (Lemma 3.7b with ★=M)."""
    from itertools import zip_longest
    drcL, drcR = drc
    ndrcL, ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = _count_ds(colL), _count_ds(colR)
        ndrcL.append('*' * cR + 's' * (cL - cR) + colL[cL:])
        ndrcR.append('*' * cR + colR[cR:])
    return reg_drc((tuple(ndrcL), tuple(ndrcR)))


def _fill_ds_B(drc):
    """Redistribute dots/s for B-type (Lemma 3.7b with ★=B)."""
    from itertools import zip_longest
    drcL, drcR = drc
    ndrcL, ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = _count_ds(colL), _count_ds(colR)
        ndrcL.append('*' * cL + colL[cL:])
        ndrcR.append('*' * cL + 's' * (cR - cL) + colR[cR:])
    return reg_drc((tuple(ndrcL), tuple(ndrcR)))


def naive_descent(drc, rtype):
    """
    Compute the naive descent τ'_naive = ∇_naive(τ).

    For ★ ∈ {B, C}: remove first column of Q, redistribute dots/s.
    For ★ ∈ {M, D}: remove first column of P, redistribute dots/s.

    Implements Lemma 3.7 / Lemma 10.4-10.5 of [BMSZb].

    Returns (drc', rtype').
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')

    if rtype in ('B+', 'B-', 'C'):
        # ★ ∈ {B, C}: keep ι (drcL), remove first column of j (drcR)
        # Then redistribute dots/s
        if rtype == 'C':
            res = _fill_ds_D((drcL, drcR[1:]))
            rtype_prime = 'D'
        else:
            # B → M: _fill_ds_M on (drcL, drcR[1:])
            res = _fill_ds_M((drcL, drcR[1:]))
            rtype_prime = 'M'
        return res, rtype_prime

    elif rtype in ('M', 'D'):
        # ★ ∈ {M, D}: remove first column of ι (drcL), keep j (drcR)
        if rtype == 'D':
            res = _fill_ds_C((drcL[1:], drcR))
            rtype_prime = 'C'
        else:
            # M → B: _fill_ds_B on (drcL[1:], drcR)
            res = _fill_ds_B((drcL[1:], drcR))
            # γ' from (3.11): B+ if c not in first column of P, B- if c in it
            if 'c' in fL:
                rtype_prime = 'B-'
            else:
                rtype_prime = 'B+'
        return res, rtype_prime

    else:
        raise ValueError(f"Unknown rtype for naive descent: {rtype}")


# ============================================================================
# Phase 9: Full descent  (Definition 3.14 of [BMSZ])
# ============================================================================

def descent(drc, rtype, dpart=None):
    """
    Compute the descent ∇(τ) of a painted bipartition.

    ∇(τ) = τ' (from Lemma 3.10 or 3.12) if conditions hold,
           τ'_naive otherwise.

    Reference: Definition 3.14 of [BMSZ].

    Returns (drc', rtype').
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')
    fR = getz(drcR, 0, '')

    # Compute naive descent first
    res, rtype_prime = naive_descent(drc, rtype)
    resL, resR = res

    # Lemma 3.10: ★ = B+
    # Conditions: γ = B+, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}
    if rtype in ('B+',):
        c1_iota = len(fL)  # c₁(ι) = length of first column of P
        q_c1 = fR[c1_iota - 1] if 0 < c1_iota <= len(fR) else ''
        # r₂(Ǒ) > 0: check if the orbit has at least 2 rows
        r2_positive = len(fR) > c1_iota or len(getz(drcR, 1, '')) > 0
        if r2_positive and q_c1 in ('r', 'd'):
            # P'(c₁(ι'), 1) = s
            if len(resL) > 0 and len(resL[0]) > 0:
                col0 = resL[0]
                resL = (col0[:-1] + 's', *resL[1:])

    # Lemma 3.12: ★ = D
    # Conditions: γ = D, r₂(Ǒ) = r₃(Ǒ) > 0,
    #   (P(c₂(ι),1), P(c₂(ι),2)) = (r, c),
    #   P(c₁(ι),1) ∈ {r, d}
    elif rtype == 'D':
        sL = getz(drcL, 1, '')  # second column of P
        c1 = len(fL)
        c2 = len(sL)
        # r₂ = r₃ > 0 iff c₂(ι) = c₁(j) + 1 (see existing code)
        if c2 > 0 and c2 == len(fR) + 1:
            p_c2_1 = fL[c2 - 1] if c2 <= len(fL) else ''
            p_c2_2 = sL[-1] if len(sL) > 0 else ''
            p_c1_1 = fL[c1 - 1] if c1 > 0 and c1 <= len(fL) else ''
            # Check: (P(c₂,1), P(c₂,2)) = (r, c) and P(c₁,1) ∈ {r, d}
            if (p_c2_1, p_c2_2) == ('r', 'c') and p_c1_1 in ('r', 'd'):
                # P'(c₁(ι'), 1) = r
                if len(resL) > 0 and len(resL[0]) > 0:
                    col0 = resL[0]
                    resL = (col0[:-1] + 'r', *resL[1:])
            # Also check the broader condition from the existing code
            elif c1 > 0 and fL.count('c') == 0 and fL[c2 - 1:].count('s') == 0 and sL[-1:] == 'c':
                if len(resL) > 0 and len(resL[0]) > 0:
                    col0 = resL[0]
                    resL = (col0[:-1] + 'r', *resL[1:])

    return reg_drc((resL, resR)), rtype_prime


# ============================================================================
# Phase 10: Dual descent of ℘  (Equation 3.15 of [BMSZ])
# ============================================================================

def dual_descent_pp(pp, rtype):
    """
    Compute ℘' = ∇̃(℘) from equation (3.15) of [BMSZ].
    ℘' = {(i, i+1) : i ∈ N⁺, (i+1, i+2) ∈ ℘} ⊆ PP_{★'}(Ǒ').
    """
    return frozenset((i, i + 1) for (j, k) in pp
                     if k == j + 1
                     for i in [j - 1] if i >= 1)


# ============================================================================
# Phase 11: Shape shifting  (Section 10.2 of [BMSZb])
# ============================================================================

# Translation table for M-type non-special twist
_TR_M = str.maketrans('cdrs', 'dcsr')


def twist_M_nonspecial(drc):
    """
    Type M (C̃): swap and translate the first column between P and Q.
    Implements the shape-shifting bijection T_{℘,℘↑} for type C̃.
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')
    fR = getz(drcR, 0, '')
    fLL = fR.translate(_TR_M)
    fRR = fL.translate(_TR_M)
    return ((fLL, *drcL[1:]), (fRR, *drcR[1:]))


# ============================================================================
# Phase 12: Main API
# ============================================================================

def compute_all_pbp(dpart, rtype, report=False):
    """
    Compute all painted bipartitions for the dual partition dpart and type rtype.

    Returns a list of (drc, rtype, (p, q), epsilon) tuples.
    """
    drcs = dpart2drc(dpart, rtype)
    results = []
    for drc in drcs:
        sig = signature(drc, rtype)
        eps = epsilon(drc, rtype)
        results.append((drc, rtype, sig, eps))
        if report:
            print(str_dgms(drc))
            print(f"  signature: {sig}, epsilon: {eps}")
            print()
    return results


def verify_descent(dpart, rtype, report=False):
    """
    Verify descent for all PBPs attached to (dpart, rtype).
    Checks that ∇(τ) is a valid PBP of the dual type.

    For type B, generates extended DRCs (B+/B-) from plain DRCs.
    """
    drcs = dpart2drc(dpart, rtype)
    passed = 0
    failed = 0

    if rtype == 'B':
        # For type B, we need to try both B+ and B- for each DRC
        test_items = []
        for drc in drcs:
            for btype in ('B+', 'B-'):
                if verify_drc(drc, btype):
                    test_items.append((drc, btype))
    else:
        test_items = [(drc, rtype) for drc in drcs]

    for drc, rt in test_items:
        try:
            ddrc, rtype_prime = descent(drc, rt, dpart)
            if ddrc is not None and verify_drc(ddrc, rtype_prime):
                passed += 1
            else:
                failed += 1
                if report:
                    print(f"INVALID descent:")
                    print(f"  {str_dgms(drc)} ({rt})")
                    print(f"  → {str_dgms(ddrc) if ddrc else 'None'} ({rtype_prime})")
        except Exception as e:
            failed += 1
            if report:
                print(f"ERROR: {e}")
                print(f"  {str_dgms(drc)} ({rt})")
    return passed, failed


# ============================================================================
# Phase 13: CLI interface
# ============================================================================

def main():
    import argparse
    parser = argparse.ArgumentParser(
        description='Compute painted bipartitions (DRC diagrams) using descent.')
    parser.add_argument('partition', type=str, nargs='?',
                        help='Comma-separated dual partition (e.g. "5,3,1,1")')
    parser.add_argument('-t', '--type', default='D', choices=['B', 'C', 'D', 'M'],
                        help='Root system type (default: D)')
    parser.add_argument('--print-drc', action='store_true',
                        help='Print all DRC diagrams')
    parser.add_argument('--verify', action='store_true',
                        help='Verify descent for all PBPs')
    parser.add_argument('--test', action='store_true',
                        help='Run cross-check tests against combunipotent')

    args = parser.parse_args()

    if args.test:
        run_tests()
        return

    if args.partition is None:
        parser.print_help()
        return

    parts = tuple(int(x) for x in args.partition.split(','))
    parts = reg_part(parts)
    rtype = args.type

    print(f"Dual partition: {parts}")
    print(f"Type: {rtype}")

    # Compute bipartition
    tauL, tauR = orbit_to_bipartition(parts, rtype)
    print(f"Bipartition: ({tauL}, {tauR})")

    # Compute primitive pairs
    PP = primitive_pairs(parts, rtype)
    print(f"Primitive pairs: {PP}")

    # Compute PBPs
    results = compute_all_pbp(parts, rtype, report=args.print_drc)
    print(f"Number of PBPs: {len(results)}")

    if args.verify:
        print(f"\nVerifying descent...")
        p, f = verify_descent(parts, rtype, report=True)
        print(f"Descent verification: {p} passed, {f} failed")


def run_tests():
    """Cross-check against the combunipotent package."""
    try:
        from combunipotent import dpart2drc as ref_dpart2drc
        from combunipotent import reg_drc as ref_reg_drc
    except ImportError:
        print("combunipotent package not available, skipping cross-check.")
        return

    test_cases = [
        ((1, 1), 'D'), ((3, 1), 'D'), ((3, 3), 'D'),
        ((5, 1), 'D'), ((5, 3), 'D'), ((5, 5), 'D'),
        ((5, 3, 1, 1), 'D'), ((7, 5, 3, 1), 'D'), ((7, 7, 3, 3), 'D'),
        ((1,), 'C'), ((3,), 'C'), ((5,), 'C'),
        ((5, 3, 1), 'C'), ((5, 3, 3), 'C'), ((7, 5, 3), 'C'),
        ((2, 2), 'M'), ((4, 2), 'M'), ((4, 4), 'M'),
        ((6, 4), 'M'), ((6, 4, 2, 2), 'M'), ((8, 6, 4, 2), 'M'),
        ((2, 2), 'B'), ((4, 2), 'B'), ((4, 4), 'B'),
        ((6, 4), 'B'), ((6, 4, 2, 2), 'B'), ((8, 6, 4, 2), 'B'),
    ]

    passed = 0
    failed = 0
    for dpart, rtype in test_cases:
        my_drcs = set(dpart2drc(dpart, rtype))
        ref_drcs = set(ref_reg_drc(d) for d in ref_dpart2drc(dpart, rtype, report=False))
        if my_drcs == ref_drcs:
            passed += 1
        else:
            failed += 1
            print(f"MISMATCH: {dpart} {rtype}")
            print(f"  standalone: {len(my_drcs)}, reference: {len(ref_drcs)}")
            extra = my_drcs - ref_drcs
            missing = ref_drcs - my_drcs
            if extra:
                print(f"  extra: {len(extra)}")
            if missing:
                print(f"  missing: {len(missing)}")

    print(f"\nCross-check: {passed} passed, {failed} failed, {passed + failed} total")


if __name__ == '__main__':
    main()
