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
# Phase 12: Marked Young diagrams and four operations
#           (Section 9.3-9.4 of [BMSZ])
# ============================================================================
#
# A marked Young diagram (MYD) E of type ★ is a map
#     E: N⁺ → Z × Z,   i ↦ (p_i, q_i)
# with finite support, satisfying parity conditions depending on ★.
#
# We represent E as a dict: {i: (p_i, q_i)} for i with (p_i, q_i) ≠ (0,0).
# Indices are 1-based.

def myd_sign_twist(E, ep, em, rtype):
    """
    Sign twist operation (9.15):
    (E ⊗ (ε⁺, ε⁻))(i) = ((-1)^{(i+1)/2·ε⁺ + (i-1)/2·ε⁻} p_i,
                           (-1)^{(i-1)/2·ε⁺ + (i+1)/2·ε⁻} q_i)  if i is odd;
                        = (p_i, q_i)                               if i is even.
    Here ep, em ∈ {0, 1} (elements of Z/2Z).
    Only for ★ ∈ {B, D}.
    """
    result = {}
    for i, (pi, qi) in E.items():
        if i % 2 == 1:  # i is odd
            exp_p = ((i + 1) // 2 * ep + (i - 1) // 2 * em) % 2
            exp_q = ((i - 1) // 2 * ep + (i + 1) // 2 * em) % 2
            result[i] = ((-1)**exp_p * pi, (-1)**exp_q * qi)
        else:
            result[i] = (pi, qi)
    return _myd_clean(result)


def myd_involution_T(E):
    """
    Involution T (9.16): for ★ ∈ {C, C̃},
    (TE)(i) = -E(i) if i ≡ 2 (mod 4); E(i) otherwise.
    T² = identity.
    """
    result = {}
    for i, (pi, qi) in E.items():
        if i % 4 == 2:
            result[i] = (-pi, -qi)
        else:
            result[i] = (pi, qi)
    return _myd_clean(result)


def myd_augmentation(Ep, p0, q0):
    """
    Augmentation operation ⊕(p₀, q₀) (9.18):
    (E' ⊕ (p₀, q₀))(i) = (p₀, q₀)    if i = 1;
                         = E'(i - 1)   if i > 1.
    Maps MYD_{★'} → MYD_★.
    """
    result = {1: (p0, q0)}
    for i, val in Ep.items():
        result[i + 1] = val
    return _myd_clean(result)


def myd_truncation(E, p0, q0):
    """
    Truncation Λ_{(p₀,q₀)} (9.20):
    (Λ_{(p₀,q₀)} E)(i) = E(1) - (p₀, q₀)   if i = 1;
                        = E(i)               if i > 1.
    Requires E ⊒ (p₀, q₀) (condition 9.19).
    Maps MYD_★ → MYD_★.
    """
    p1, q1 = E.get(1, (0, 0))
    result = dict(E)
    result[1] = (p1 - p0, q1 - q0)
    return _myd_clean(result)


def _myd_clean(E):
    """Remove entries with (0, 0)."""
    return {i: v for i, v in E.items() if v != (0, 0)}


def myd_size(E):
    """Total size |E| = sum of |p_i| + |q_i|."""
    return sum(abs(p) + abs(q) for p, q in E.values())


def myd_to_tuple(E):
    """Convert MYD to a canonical hashable form."""
    return tuple(sorted(E.items()))


# ============================================================================
# Phase 12b: Theta lift of marked Young diagrams
#            (Section 9.5, formulas 9.29 and 9.30 of [BMSZ])
# ============================================================================

def _lsign(Oprime):
    """
    Compute ˡSign(O') = Σ (p'_{2i}, q'_{2i}) + Σ (q'_{2i-1}, p'_{2i-1}).
    Reference: page 55 of [BMSZ].
    """
    sp, sq = 0, 0
    for i, (pi, qi) in Oprime.items():
        if i % 2 == 0:
            sp += pi
            sq += qi
        else:
            sp += qi
            sq += pi
    return (sp, sq)


def theta_lift_myd(Ep, rtype, p, q, pp, qp, delta=None, n0=None):
    """
    Compute the geometric theta lift ϑ̂^{s,O}_{s',O'}(E') of a marked Young
    diagram E' ∈ MYD_{★'}(O').

    Reference: formulas (9.29) and (9.30) of [BMSZ], page 55.

    Args:
        Ep: the marked Young diagram E' (dict)
        rtype: the TARGET type ★ ∈ {B, C, D, M}
        p, q: signature of the target s = (★, p, q)
        pp, qp: signature of the source s' = (★', p', q')
        delta: |s'| - |∇_naive(O)| from Lemma 4.4. If None, estimated.
        n0: (c₁(O) - c₂(O))/2 for C/C̃ types. If None, uses delta//2.

    Returns:
        A list of (coefficient, MYD) pairs in Z[MYD_★(O)].
    """
    s_size = p + q      # |s|
    sp_size = pp + qp   # |s'|

    if delta is None:
        if rtype in ('B', 'B+', 'B-', 'D'):
            delta = s_size - sp_size - 1
        else:
            delta = s_size - sp_size + 1

    # ˡSign(O') — page 55 of [BMSZ]
    lsign_p, lsign_q = _lsign(Ep)

    results = []

    if rtype in ('B', 'B+', 'B-', 'D'):
        # ★ ∈ {B, D}: formula (9.29), page 55
        # (p₀,q₀) = (p,q) - (p',q') - ˡSign(O') + (δ/2, δ/2)
        half_delta = delta / 2
        p0 = int(p - pp - lsign_p + half_delta)
        q0 = int(q - qp - lsign_q + half_delta)

        # Truncation Λ_{(δ/2, δ/2)}
        trunc = delta // 2
        truncated = myd_truncation(Ep, trunc, trunc)

        # Involution T^{exponent}
        if rtype in ('B', 'B+', 'B-'):
            t_exp = (p - q + 1) // 2   # (9.29) B case
        else:
            t_exp = (p - q) // 2        # (9.29) D case

        twisted = truncated
        if t_exp % 2 != 0:
            twisted = myd_involution_T(twisted)

        # Augmentation ⊕ (p₀, q₀)
        augmented = myd_augmentation(twisted, p0, q0)
        results.append((1, augmented))

    elif rtype in ('C', 'M'):
        # ★ ∈ {C, C̃}: formula (9.30), page 55
        # n₀ = (c₁(O) - c₂(O))/2
        if n0 is None:
            n0 = delta // 2

        # Involution T exponent
        # For C̃ (M): source is B type, use |p'-q'| convention
        # since O(p,q) ≅ O(q,p) and the formula uses the standard form
        if rtype == 'C':
            t_exp = (pp - qp) // 2         # (9.30) C case
        else:
            # (9.30) C̃ case: T^{(p'-q'-1)/2} where p'≥q' (B+ convention)
            t_exp = (max(pp, qp) - min(pp, qp) - 1) // 2

        # Sum over j = 0, ..., δ: Λ_{(j, δ-j)}(E') ⊕ (n₀, n₀)
        for j in range(delta + 1):
            truncated = myd_truncation(Ep, j, delta - j)
            augmented = myd_augmentation(truncated, n0, n0)
            twisted = augmented
            if t_exp % 2 != 0:
                twisted = myd_involution_T(twisted)
            results.append((1, twisted))

    return results


# ============================================================================
# Phase 12c: Associated cycle AC(τ) via iterated descent
#            (Equation 4.17 of [BMSZ])
# ============================================================================

def bv_dual(dpart, rtype):
    """
    Compute the Barbasch-Vogan dual d^★_BV(Ǒ) of a dual partition.
    Reference: Definition 4.5 of [BMSZ], [BMSZb] Section 2.5.

    Uses the combunipotent implementation if available, otherwise raises.
    """
    try:
        from combunipotent.tool import dualBVW
        # Normalize rtype for BV dual: B+/B- → B
        bv_rtype = rtype
        if bv_rtype in ('B+', 'B-'):
            bv_rtype = 'B'
        return reg_part(dualBVW(dpart, bv_rtype, partrc='c'))
    except ImportError:
        # Fallback: for purely even orbits, the BV dual has a simpler form
        # This is a placeholder — full BV duality requires Springer correspondence
        raise NotImplementedError("BV duality requires combunipotent package")


def compute_AC(drc, rtype, dpart=None):
    """
    Compute the associated cycle AC(τ) ∈ K_s(O) for a painted bipartition τ.

    Uses iterated descent: AC(τ) is defined recursively by (4.17) of [BMSZ]:
    - Base case (|Ǒ| = 0): AC(τ) = trivial/det/genuine
    - ★ = B or D: AC(τ) = ϑ̂^O_{O'}(AC(τ')) ⊗ (det_{-1})^{ε_τ}
    - ★ = C or C̃: AC(τ) = ϑ̂^O_{O'}(AC(τ') ⊗ det^{ε_℘})

    Args:
        drc: painted bipartition (drcL, drcR)
        rtype: root system type
        dpart: dual partition Ǒ (needed for BV dual computation)

    Returns a list of (coefficient, MYD) pairs.
    """
    # For B type: determine B+/B- from the DRC
    effective_rtype = rtype
    if rtype == 'B':
        if verify_drc(drc, 'B+'):
            effective_rtype = 'B+'
        elif verify_drc(drc, 'B-'):
            effective_rtype = 'B-'

    # Build the descent chain (with orbit tracking)
    ch = descent_chain(drc, effective_rtype, dpart)

    # Base case: the last element of the chain
    _, base_rtype, base_sig, base_eps, _ = ch[-1]

    # Base case |Ǒ| = 0: L_τ from page 62 of [BMSZ]
    #   α_τ = B⁺ : L_τ = (1, 0)_★
    #   α_τ = B⁻ : L_τ = (0, -1)_★
    #   otherwise: L_τ = (0, 0)_★
    if base_rtype == 'B+':
        current_AC = [(1, {1: (1, 0)})]
    elif base_rtype == 'B-':
        current_AC = [(1, {1: (0, -1)})]
    else:
        current_AC = [(1, {})]  # (0,0)_★ = trivial

    # Induction: walk backwards through the descent chain
    for idx in range(len(ch) - 2, -1, -1):
        tau_drc, tau_rtype, tau_sig, tau_eps, tau_dpart = ch[idx]
        tau_p, tau_q = tau_sig
        _, taup_rtype, taup_sig, taup_eps, taup_dpart = ch[idx + 1]
        taup_p, taup_q = taup_sig

        # Compute δ = |s'| - |∇_naive(O)| (Lemma 4.4 of [BMSZ])
        # where O = d^★_BV(Ǒ), s' = (★', p', q').
        # ∇_naive(O) removes the first row (for ★∈{B,D}) or first column
        # (for ★∈{C,C̃}) of O.
        delta = 0
        if tau_dpart is not None:
            try:
                O = bv_dual(tau_dpart, tau_rtype)
                O_rows = reg_part(O)
                O_cols = col_lengths(O)
                if tau_rtype in ('B', 'B+', 'B-', 'D'):
                    # ★∈{B,D}: ∇_naive removes first row
                    nabla_O_size = part_size(O) - (O_rows[0] if O_rows else 0)
                else:
                    # ★∈{C,M=C̃}: ∇_naive removes first column
                    nabla_O_size = part_size(O) - (O_cols[0] if O_cols else 0)
                delta = (taup_p + taup_q) - nabla_O_size
            except Exception:
                delta = abs(tau_p + tau_q - taup_p - taup_q)

        # Also compute n₀ = (c₁(O) - c₂(O))/2 for C/C̃ types
        n0 = 0
        if tau_rtype in ('C', 'M') and tau_dpart is not None:
            try:
                O = bv_dual(tau_dpart, tau_rtype)
                O_cols = col_lengths(O)
                c1_O = O_cols[0] if len(O_cols) > 0 else 0
                c2_O = O_cols[1] if len(O_cols) > 1 else 0
                n0 = (c1_O - c2_O) // 2
            except Exception:
                n0 = 0

        # Apply theta lift + sign twist (equation 11.2 of [BMSZ], page 62)
        new_AC = []
        for coeff, myd in current_AC:
            if tau_rtype in ('B', 'B+', 'B-', 'D'):
                # ★ ∈ {B,D}: L_τ = ϑ̂^{s_τ,O}_{s_{τ'},O'}(L_{τ'}) ⊗ (0, ε_τ)
                lifted = theta_lift_myd(myd, tau_rtype,
                                        tau_p, tau_q, taup_p, taup_q,
                                        delta=delta)
                for lc, lmyd in lifted:
                    # Apply sign twist ⊗ (0, ε_τ)
                    if tau_eps != 0:
                        lmyd = myd_sign_twist(lmyd, 0, tau_eps, tau_rtype)
                    new_AC.append((coeff * lc, lmyd))
            elif tau_rtype in ('C', 'M'):
                # ★ ∈ {C, C̃}: L_τ = ϑ̂(L_{τ'} ⊗ (ε_℘, ε_℘))
                # For ℘=∅: ε_℘ = 0, so no twist on L_{τ'}
                # For ℘≠∅: ε_℘ = 1 iff (1,2) ∈ ℘
                lifted = theta_lift_myd(myd, tau_rtype,
                                        tau_p, tau_q, taup_p, taup_q,
                                        delta=delta, n0=n0)
                new_AC.extend((coeff * lc, lmyd) for lc, lmyd in lifted)
            else:
                lifted = theta_lift_myd(myd, tau_rtype,
                                        tau_p, tau_q, taup_p, taup_q,
                                        delta=delta)
                new_AC.extend((coeff * lc, lmyd) for lc, lmyd in lifted)

        current_AC = new_AC

    return current_AC


def print_AC(drc, rtype):
    """Print the associated cycle for a painted bipartition."""
    ac = compute_AC(drc, rtype)
    print(f"AC ({rtype}):")
    for coeff, myd in ac:
        entries = sorted(myd.items())
        myd_str = ', '.join(f'{i}:({p},{q})' for i, (p, q) in entries)
        print(f"  {coeff} × [{myd_str}]")


# ============================================================================
# Phase 12d: Descent chain
# ============================================================================

def orbit_descent(dpart, rtype):
    """
    Compute the dual descent of the orbit: Ǒ' = ∇̂_★(Ǒ).
    Equation (3.10) of [BMSZ]:
      - ∇̂_naive(Ǒ) = Ǒ with first row removed.
      - Special case: if ★ ∈ {D, D*} and |Ǒ| = 0, then Ǒ' = □ (one box).

    Returns (dpart', rtype') where rtype' is the Howe dual of rtype.
    """
    rows = reg_part(dpart)
    if len(rows) == 0:
        if rtype in ('D',):
            return (1,), 'C'
        else:
            return (), HOWE_DUAL.get(rtype, rtype)
    # Remove first row
    dpart_prime = rows[1:]
    rtype_prime = HOWE_DUAL.get(rtype, rtype)
    if rtype in ('M',):
        # M → B: need B+ or B- depending on the DRC
        # For orbit descent, we just track as 'B'
        rtype_prime = 'B'
    elif rtype in ('B', 'B+', 'B-'):
        rtype_prime = 'M'
    return reg_part(dpart_prime), rtype_prime


def descent_chain(drc, rtype, dpart=None):
    """
    Compute the full descent chain from τ down to the trivial orbit.

    Returns a list of (drc, rtype, signature, epsilon, dpart) tuples.
    chain[0] is the input τ, chain[-1] is the base case.
    """
    result = []
    cur_drc = drc
    cur_rtype = rtype
    cur_dpart = dpart  # may be None if not provided

    for _ in range(1000):  # safety limit
        sig = signature(cur_drc, cur_rtype)
        eps = epsilon(cur_drc, cur_rtype)

        # Total size of the DRC
        drcL, drcR = cur_drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)

        result.append((cur_drc, cur_rtype, sig, eps, cur_dpart))

        if total == 0:
            break

        try:
            next_drc, next_rtype = descent(cur_drc, cur_rtype)
            if next_drc is None:
                break
            # Descend the orbit too
            if cur_dpart is not None:
                next_dpart, _ = orbit_descent(cur_dpart, cur_rtype)
            else:
                next_dpart = None
            cur_drc = next_drc
            cur_rtype = next_rtype
            cur_dpart = next_dpart
        except Exception:
            break

    return result


def descent_chain_signatures(drc, rtype, dpart=None):
    """
    Extract the sequence of classical signatures from the descent chain.

    Returns a list of (★, p, q, ε) tuples = the combinatorial data
    needed to reconstruct the associated cycle / local system.

    This is the key output: the iterated theta lift path that defines
    the representation π_τ (equation 3.16 of [BMSZ]).
    """
    ch = descent_chain(drc, rtype, dpart)
    return [(rt, sig[0], sig[1], eps) for (_, rt, sig, eps, _) in ch]


def print_descent_chain(drc, rtype, dpart=None):
    """Print the descent chain with DRC diagrams."""
    ch = descent_chain(drc, rtype, dpart)
    for i, (d, rt, sig, eps, dp) in enumerate(ch):
        dp_str = f" Ǒ={dp}" if dp is not None else ""
        prefix = f"Step {i}: {rt}, sig=({sig[0]},{sig[1]}), ε={eps}{dp_str}"
        print(prefix)
        print(str_dgms(d))
        print()


# ============================================================================
# Phase 13: Lift tree visualization (Graphviz)
# ============================================================================

RTYPE_GP = {'C': 'Sp(%d)', 'D': 'SO(%d,%d)', 'M': 'Mp(%d)',
            'B': 'O(%d,%d)', 'B+': 'O(%d,%d)', 'B-': 'O(%d,%d)'}


def _format_myd(myd):
    """Format a marked Young diagram as a compact string."""
    if not myd:
        return '(trivial)'
    entries = sorted(myd.items())
    parts = []
    for i, (p, q) in entries:
        parts.append(f'{i}:({p},{q})')
    return ' '.join(parts)


# Display symbols for LS/MYD visualization:
#   + : trivial system on + sign (p > 0)
#   * : non-trivial system on + sign (p < 0)
#   - : trivial system on - sign (q > 0)
#   = : non-trivial system on - sign (q < 0)
_PNPN = '+-+'   # trivial: row pattern for + rows
_QMQM = '*=*'   # non-trivial: row pattern for + rows


def _str_irr_myd(myd_entry):
    """
    Draw one irreducible MYD component as rows of +-*/=- symbols.

    An entry i ↦ (p_i, q_i) at level i means:
      - |p_i| rows of length i, with + sign if p_i > 0, * if p_i < 0
      - |q_i| rows of length i, with - sign if q_i > 0, = if q_i < 0

    Row patterns follow the alternating sign convention from [BMSZ]:
      odd-length rows:  +, -+, +-+, -+-+, ...
      even-length rows: -, +-, -+-, +-+-, ...
    """
    rows = []
    # Sort by level (descending, so longest rows on top)
    for i in sorted(myd_entry.keys(), reverse=True):
        pi, qi = myd_entry[i]
        hii, rii = divmod(i, 2)
        # q rows (- sign) come first (displayed on top within this level)
        if qi != 0:
            if qi > 0:
                onerow = _PNPN[1] * rii + _PNPN[0:2] * hii
            else:
                onerow = _QMQM[1] * rii + _QMQM[0:2] * hii
            rows.extend([onerow] * abs(qi))
        # p rows (+ sign)
        if pi != 0:
            if pi > 0:
                onerow = _PNPN[0] * rii + _PNPN[1:3] * hii
            else:
                onerow = _QMQM[0] * rii + _QMQM[1:3] * hii
            rows.extend([onerow] * abs(pi))
    return rows


def str_myd(myd):
    """
    Draw a marked Young diagram in the visual LS format.

    Uses the same display convention as combunipotent.LS.str_LS:
      + trivial on + sign, - trivial on - sign
      * non-trivial on + sign, = non-trivial on - sign
    """
    if not myd:
        return '(trivial)'
    rows = _str_irr_myd(myd)
    if not rows:
        return '(trivial)'
    return '\n'.join(rows)


def str_myd_ac(ac_list):
    """
    Draw the associated cycle (list of (coeff, myd)) in visual format.
    Multiple MYD components are shown side by side separated by ' | '.
    """
    if not ac_list:
        return '(empty)'

    all_row_blocks = []
    for coeff, myd in ac_list:
        rows = _str_irr_myd(myd) if myd else ['(triv)']
        all_row_blocks.append(rows)

    if not all_row_blocks:
        return '(empty)'

    # Align blocks side by side
    max_rows = max(len(b) for b in all_row_blocks)
    max_cols = [max((len(r) for r in b), default=0) for b in all_row_blocks]

    result = []
    for row_idx in range(max_rows):
        parts = []
        for blk_idx, block in enumerate(all_row_blocks):
            r = block[row_idx] if row_idx < len(block) else ''
            parts.append(r + ' ' * (max_cols[blk_idx] - len(r)))
        result.append(' | '.join(parts))
    return '\n'.join(result)


def _format_myd_multiline(ac_list):
    """Format AC (list of (coeff, myd)) as multiline string for graph label."""
    if not ac_list:
        return ['(empty)']

    all_row_blocks = []
    for coeff, myd in ac_list:
        rows = _str_irr_myd(myd) if myd else ['(triv)']
        all_row_blocks.append(rows)

    max_rows = max(len(b) for b in all_row_blocks)
    max_cols = [max((len(r) for r in b), default=0) for b in all_row_blocks]

    result = []
    for row_idx in range(max_rows):
        parts = []
        for blk_idx, block in enumerate(all_row_blocks):
            r = block[row_idx] if row_idx < len(block) else ''
            parts.append(r + ' ' * (max_cols[blk_idx] - len(r)))
        result.append(' | '.join(parts))
    return result


def gen_descent_tree(dpart, rtype, format='pdf', filename='descent_tree'):
    """
    Generate a Graphviz directed graph showing the descent tree
    for all PBPs attached to (dpart, rtype).

    Each node shows:
      - DRC diagram
      - Type ★, signature (p,q), ε
      - Associated cycle AC(τ) as marked Young diagram

    Edges:
      - Blue: descent map ∇ (vertical)
      - Red (dashed, bidirectional): det twist for orthogonal types (B, D)

    Returns the Graphviz Digraph object.
    """
    from graphviz import Digraph

    drcs = dpart2drc(dpart, rtype)

    g = Digraph(name='Descent Tree',
                filename=filename,
                node_attr={'shape': 'box', 'fontname': 'Courier New',
                           'fontsize': '8'},
                graph_attr={'rankdir': 'TB', 'newrank': 'true',
                            'ranksep': '1.2', 'nodesep': '0.4',
                            'concentrate': 'false',
                            'dpi': '150'},
                engine='dot', format=format)

    # Group nodes by (rtype, total_size) for rank alignment
    levels = {}     # (rtype, size) -> list of node_ids
    node_id_map = {}  # (drc, rt) -> node_id
    descent_edges = set()
    det_twist_edges = set()

    node_counter = [0]
    # Cache AC computations
    ac_cache = {}

    def get_ac(drc, rt):
        key = (drc, rt)
        if key not in ac_cache:
            ac_cache[key] = compute_AC(drc, rt)
        return ac_cache[key]

    def get_node_id(drc, rt):
        key = (drc, rt)
        if key not in node_id_map:
            nid = f'n{node_counter[0]}'
            node_counter[0] += 1
            node_id_map[key] = nid

            sig = signature(drc, rt)
            eps = epsilon(drc, rt)
            drcL, drcR = drc
            total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)

            # Format DRC diagram
            drc_str = str_dgms(drc).replace('\n', '\\l')

            # Format group label
            gp = RTYPE_GP.get(rt, rt + '(%d)')
            if rt in ('C', 'M'):
                gp_label = gp % (2 * sig[0],)
            else:
                gp_label = gp % (sig[0], sig[1])

            # Format AC / MYD in visual LS-style format
            ac = get_ac(drc, rt)
            ac_lines = _format_myd_multiline(ac)
            ac_str = '\\l'.join(ac_lines)

            # Build label: DRC on top, then ε, then AC visual
            label = (f'{drc_str}\\l'
                     f'ε={eps}\\l'
                     f'─────\\l'
                     f'{ac_str}\\l')

            # Color by type
            colors = {'C': '#e6f3ff', 'D': '#fff3e6',
                      'M': '#e6ffe6', 'B+': '#ffe6e6', 'B-': '#ffe6f3'}
            fillcolor = colors.get(rt, '#ffffff')

            g.node(nid, label=label, style='filled', fillcolor=fillcolor,
                   labeljust='l')

            level_key = (rt, total)
            levels.setdefault(level_key, []).append(nid)

        return node_id_map[key]

    # Build the tree: descent edges
    for drc in drcs:
        ch = descent_chain(drc, rtype)
        for i in range(len(ch) - 1):
            src_drc, src_rt, _, _ = ch[i]
            dst_drc, dst_rt, _, _ = ch[i + 1]
            src_id = get_node_id(src_drc, src_rt)
            dst_id = get_node_id(dst_drc, dst_rt)
            edge_key = (src_id, dst_id)
            if edge_key not in descent_edges:
                descent_edges.add(edge_key)
                g.edge(src_id, dst_id, color='blue',
                       tailport='s', headport='n')
        # Register last node
        if ch:
            last_drc, last_rt, _, _ = ch[-1]
            get_node_id(last_drc, last_rt)

    # Add det-twist edges for orthogonal types (B+/B-, D)
    # Two DRCs are det-twist pairs if they have the same DRC but
    # differ only by ε (i.e., d↔c in the first column)
    for (drc, rt), nid in list(node_id_map.items()):
        if rt in ('B+', 'B-', 'D'):
            # For D type: det twist changes ε
            # For B+/B-: the pair is B+ ↔ B- with same DRC shape
            # Find the det-twist partner
            if rt == 'D':
                # Det twist for D: sign_twist with (1,1) on the MYD
                # The partner DRC has the same shape but different ε
                # Look for another node with same DRC and opposite ε
                eps = epsilon(drc, rt)
                for (drc2, rt2), nid2 in node_id_map.items():
                    if rt2 == rt and drc2 == drc:
                        continue
                    if rt2 == rt and epsilon(drc2, rt2) != eps:
                        # Check if they are truly det-twist pairs
                        sig1 = signature(drc, rt)
                        sig2 = signature(drc2, rt2)
                        if sig1 == sig2:
                            edge = tuple(sorted([nid, nid2]))
                            if edge not in det_twist_edges:
                                det_twist_edges.add(edge)
                                g.edge(nid, nid2, color='red',
                                       style='dashed', dir='both',
                                       arrowsize='0.3',
                                       constraint='false')
            elif rt == 'B+':
                # B+ ↔ B- partner: same underlying DRC
                partner_key = (drc, 'B-')
                if partner_key in node_id_map:
                    nid2 = node_id_map[partner_key]
                    edge = tuple(sorted([nid, nid2]))
                    if edge not in det_twist_edges:
                        det_twist_edges.add(edge)
                        g.edge(nid, nid2, color='red',
                               style='dashed', dir='both',
                               arrowsize='0.3',
                               constraint='false')

    # Add group labels on the left and rank constraints
    # Compute the group label from signatures:
    #   C: Sp(2|τ|), M: Mp(2|τ|), B±: O(p,q), D: SO(p,q)
    gp_nodes = []  # list of (size, gp_node_id)
    for (rt, size), nids in sorted(levels.items(), key=lambda x: -x[0][1]):
        if rt in ('C', 'M'):
            # |τ| = size (total boxes), group is Sp(2*size) or Mp(2*size)
            gp_label = RTYPE_GP[rt] % (2 * size,)
        elif rt in ('B+', 'B-', 'D'):
            # Collect all distinct signatures at this level
            sigs = set()
            for (drc, drt), nid in node_id_map.items():
                if nid in nids:
                    sigs.add(signature(drc, drt))
            if len(sigs) == 1:
                p, q = sigs.pop()
                gp_label = RTYPE_GP[rt] % (p, q)
            else:
                # Multiple signatures: show the dimension
                p, q = next(iter(sigs))
                dim = p + q
                if rt in ('B+', 'B-'):
                    gp_label = f'O({dim})'
                else:
                    gp_label = f'SO({dim})'
        else:
            gp_label = rt

        gp_nid = f'gp_{rt}_{size}'
        g.node(gp_nid, label=gp_label, shape='plaintext',
               fontname='Helvetica', fontsize='11', fontcolor='#333333')
        gp_nodes.append((size, gp_nid))

        # Rank constraint: group label + all nodes at this level
        with g.subgraph() as s:
            s.attr(rank='same')
            s.node(gp_nid)
            for nid in nids:
                s.node(nid)

    # Chain group label nodes vertically
    gp_nodes_sorted = sorted(gp_nodes, key=lambda x: -x[0])
    for i in range(len(gp_nodes_sorted) - 1):
        g.edge(gp_nodes_sorted[i][1], gp_nodes_sorted[i + 1][1],
               style='invis')

    return g


# ============================================================================
# Phase 14: Main API
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
    parser.add_argument('--tree', action='store_true',
                        help='Generate descent tree diagram (PDF/SVG)')
    parser.add_argument('-f', '--format', default='svg',
                        choices=['pdf', 'svg', 'png'],
                        help='Output format for tree (default: svg)')
    parser.add_argument('-o', '--output', default=None,
                        help='Output filename (default: descent_tree)')

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

    if args.tree:
        fname = args.output or 'descent_tree'
        print(f"\nGenerating descent tree...")
        g = gen_descent_tree(parts, rtype, format=args.format, filename=fname)
        outfile = g.render()
        print(f"Output: {outfile}")


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
