#!/usr/bin/env python3
"""
standalone.py — Descent-based computation of painted bipartitions (DRC diagrams)

Implements the combinatorics of special unipotent representations following:
  [BMSZ]  Barbasch–Ma–Sun–Zhu, "Special unipotent representations of real
          classical groups: construction and unitarity", arXiv:1712.05552v6
  [BMSZb] Barbasch–Ma–Sun–Zhu, "Special unipotent representations of real
          classical groups: counting and reduction", arXiv:2205.05266v4

This file is self-contained.

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
from multiset import FrozenMultiset


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

def dpart_to_bipartition(dpart, rtype):
    """
    Compute the special-shape bipartition (ι_Ǒ, j_Ǒ) from dual partition Ǒ.

    Reference: [BMSZb] Equation (2.16), (8.9) with ℘ = ∅.
    Returns (tauL, tauR): column lengths of the two Young diagrams.
    tauL = (c₁(ι_Ǒ), c₂(ι_Ǒ), ...), tauR = (c₁(j_Ǒ), c₂(j_Ǒ), ...).

    Reference: [BMSZb] Section 2.8, equation (2.7).
    """
    rows = reg_part(dpart)  # r_1 >= r_2 >= ...
    n = len(rows)

    if rtype == 'B':
        # ★ = B: Ǒ is type C (even rows only).
        # c₁(j_Ǒ) = r₁(Ǒ)/2
        # For i ≥ 1: (cᵢ(ι_Ǒ), cᵢ₊₁(j_Ǒ)) = (r₂ᵢ(Ǒ)/2, r₂ᵢ₊₁(Ǒ)/2)
        # Reference: [BMSZb] equation (2.7), case ★ = B.
        tauL = []  # ι columns: c₁(ι)=r₂/2, c₂(ι)=r₄/2, ...
        tauR = [getz(rows, 0, 0) // 2]  # j columns: c₁(j)=r₁/2
        i = 1
        while True:
            r_2i = getz(rows, 2 * i - 1, 0)    # r_{2i}
            r_2i1 = getz(rows, 2 * i, 0)       # r_{2i+1}
            if r_2i == 0 and r_2i1 == 0:
                break
            tauL.append(r_2i // 2)              # cᵢ(ι) = r_{2i}/2
            tauR.append(r_2i1 // 2)             # cᵢ₊₁(j) = r_{2i+1}/2
            i += 1
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


# Backward compatibility alias
orbit_to_bipartition = dpart_to_bipartition


# ============================================================================
# Phase 3: Primitive pairs  (Definition 2.21 of [BMSZb])
# ============================================================================

def classify_star_pairs(dpart, rtype):
    """
    Classify all ★-pairs (i, i+1) in Ǒ.

    Reference: Definition 2.5 of [BMSZb].

    A ★-pair (i, i+1) is a pair of consecutive positive integers where:
      i is odd  if ★ ∈ {C, C̃(=M)}
      i is even if ★ ∈ {B, D}

    Classification based on r_i(Ǒ) and r_{i+1}(Ǒ):
      vacant:    r_i = r_{i+1} = 0
      balanced:  r_i = r_{i+1} > 0
      tailed:    r_i - r_{i+1} is positive and odd
      primitive: r_i - r_{i+1} is positive and even

    Returns a dict mapping (i, i+1) → 'vacant'|'balanced'|'tailed'|'primitive'
    for all ★-pairs up to the length of Ǒ.
    """
    rows = reg_part(dpart)
    n = len(rows) + 2  # check a few beyond the partition length

    if rtype in ('C', 'M'):
        need_odd_i = True
    elif rtype in ('B', 'D'):
        need_odd_i = False
    else:
        raise ValueError(f"Unknown rtype: {rtype}")

    result = {}
    for i in range(1, n + 1):
        if need_odd_i and i % 2 == 0:
            continue
        if not need_odd_i and i % 2 == 1:
            continue

        r_i = getz(rows, i - 1, 0)      # 1-indexed → 0-indexed
        r_next = getz(rows, i, 0)
        diff = r_i - r_next

        if r_i == 0 and r_next == 0:
            kind = 'vacant'
        elif r_i == r_next and r_i > 0:
            kind = 'balanced'
        elif diff > 0 and diff % 2 == 1:
            kind = 'tailed'
        elif diff > 0 and diff % 2 == 0:
            kind = 'primitive'
        else:
            continue  # r_i < r_next shouldn't happen for a valid partition

        result[(i, i + 1)] = kind

    # Remove trailing vacant pairs
    result = {k: v for k, v in result.items() if v != 'vacant'}

    return result


def primitive_pairs(dpart, rtype):
    """
    Compute PP_★(Ǒ): the set of primitive ★-pairs in Ǒ.

    Reference: Definition 2.5 of [BMSZb].

    Returns a set of pairs (i, i+1) that are primitive (1-indexed).
    """
    classified = classify_star_pairs(dpart, rtype)
    return {k for k, v in classified.items() if v == 'primitive'}


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


def _remove_tail_symbols(dg, symbols):
    """
    Remove trailing characters from each column that are in the given set.
    Returns the stripped diagram, or None if any column has more than one
    such symbol (violating the one-per-column constraint for c/d).
    """
    result = []
    for col in dg:
        stripped = col.rstrip(''.join(symbols))
        result.append(stripped)
    return tuple(result)


def verify_drc(drc, rtype):
    # Reference: [BMSZb] Definition 2.25, Proposition 2.26.
    """
    Verify that a DRC diagram satisfies all structural constraints.

    Checks:
    - Definition 3.1 of [BMSZ] (painting constraints):
      (1) Removing {d}, {c,d}, {r,c,d}, or {s,r,c,d} leaves valid Young diagram
      (2) Each row has at most one s and at most one r
      (3) Each column has at most one c and at most one d
    - Definition 2.3/2.24 of [BMSZb] (painted bipartition):
      (1) P and Q have identical set of •-boxes
      (2) P symbols ⊆ allowed set for γ
      (3) Q symbols ⊆ allowed set for γ
    """
    drcL, drcR = drc
    gamma = rtype

    # For type B, caller should use 'B+' or 'B-' (same symbol rules)
    if gamma == 'B':
        gamma = 'B+'

    # Both must be valid Young diagrams (column lengths decrease)
    if not test_young_dg(drcL) or not test_young_dg(drcR):
        return False

    # Definition 2.3 (2)+(3): symbol constraints by type
    p_sym = P_SYMBOLS.get(gamma, None)
    q_sym = Q_SYMBOLS.get(gamma, None)
    if p_sym is None or q_sym is None:
        return False
    if not verify_painting(drcL, p_sym):
        return False
    if not verify_painting(drcR, q_sym):
        return False

    # Definition 2.3 (1): P and Q have identical •-boxes
    for i in range(max(len(drcL), len(drcR))):
        cL = getz(drcL, i, '')
        cR = getz(drcR, i, '')
        if cL.count('*') != cR.count('*'):
            return False

    # Definition 3.1 (2): each row has at most one s and at most one r
    r_max = max(len(getz(drcL, 0, '')), len(getz(drcR, 0, '')))
    for row in range(r_max):
        s_count = sum(1 for col in chain(drcL, drcR)
                      if row < len(col) and col[row] == 's')
        r_count = sum(1 for col in chain(drcL, drcR)
                      if row < len(col) and col[row] == 'r')
        if s_count > 1 or r_count > 1:
            return False

    # Definition 3.1 (3): each column has at most one c and at most one d
    for col in chain(drcL, drcR):
        if col.count('c') > 1 or col.count('d') > 1:
            return False

    # Definition 3.1 (1): removing symbol layers leaves valid Young diagrams
    # Check for BOTH P (drcL) and Q (drcR):
    # Strip d → must be valid YD
    # Strip c,d → must be valid YD
    # Strip r,c,d → must be valid YD
    # Strip s,r,c,d → must be valid YD (= just •-boxes)
    for dg in (drcL, drcR):
        for sym_set in [{'d'}, {'c', 'd'}, {'r', 'c', 'd'}, {'s', 'r', 'c', 'd'}]:
            stripped = _remove_tail_symbols(dg, sym_set)
            if not test_young_dg(stripped):
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
    Compute all DRC diagrams for the special shape (℘ = ∅) of a dual partition.

    Only uses the special bipartition (ι_Ǒ, j_Ǒ) from dpart_to_bipartition.
    Returns a list of regularized DRC diagrams (untagged).

    For type B, the same DRC diagrams are valid for both B+ and B-.
    Use rtype='B+' or 'B-' to specify gamma when computing signature, etc.

    The number of DRCs equals countPBP(dpart, rtype) for all types.
    """
    tauL, tauR = dpart_to_bipartition(dpart, rtype)
    tau = (list(tauL), list(tauR))
    drcs = fill_drc(tau, rtype)
    return [reg_drc(drc) for drc in drcs]


# ============================================================================
# Phase 7: Signature and group form  (Equations 3.3-3.6 / 2.17 of [BMSZb])
# ============================================================================

def signature(drc, rtype):
    """
    Compute (p_τ, q_τ) for the painted bipartition τ = (drc, rtype).
    Reference: Equation (3.3) of [BMSZ] / (2.17) of [BMSZb].

    rtype must be one of: C, D, B+, B-, M.
    """
    n_dot = count_symbol(drc, '*')
    n_r = count_symbol(drc, 'r')
    n_s = count_symbol(drc, 's')
    n_c = count_symbol(drc, 'c')
    n_d = count_symbol(drc, 'd')

    if rtype in ('B+', 'B-', 'D'):
        p = n_dot + 2 * n_r + n_c + n_d + (1 if rtype == 'B+' else 0)
        q = n_dot + 2 * n_s + n_c + n_d + (1 if rtype == 'B-' else 0)
        return (p, q)
    elif rtype in ('C', 'M'):
        n = n_dot + n_r + n_s + n_c + n_d
        return (n, n)
    else:
        raise ValueError(f"Unknown rtype: {rtype} (use B+/B- instead of B)")


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
    """Redistribute dots/s for D-type (used in C→D descent, Lemma 3.7a)."""
    from itertools import zip_longest
    drcL, drcR = drc
    ndrcL, ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL = _count_ds(colL)   # •+s prefix length in P column
        cR = len(colR)         # total Q column length (all • in C-type Q)
        ndrcL.append('*' * cR + 's' * (cL - cR) + colL[cL:])
        ndrcR.append('*' * cR)
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

def descent(drc, rtype, dpart=None, wp=None):
    """
    Compute the descent ∇(τ) of a painted bipartition.

    Implements [BMSZb] Section 10.4 for general ℘.
    When wp is None, uses DRC shape to infer (2,3)∈℘ vs ∉℘.
    When wp is provided, uses it directly (PPidx 1 ∈ wp ⟺ (2,3)∈℘).

    Args:
        drc: painted bipartition (drcL, drcR)
        rtype: γ ∈ {'B+', 'B-', 'C', 'D', 'M'}
        dpart: dual partition (optional, unused)
        wp: frozenset of PPidx values (optional)

    Returns (drc', rtype').
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')  # first column of P
    fR = getz(drcR, 0, '')  # first column of Q
    sL = getz(drcL, 1, '')  # second column of P

    # Compute naive descent first
    res, rtype_prime = naive_descent(drc, rtype)
    resL, resR = res

    # B+ corrections (Section 10.4):
    if rtype == 'B+':
        c1 = len(fL)   # c₁(ι)
        sR = getz(drcR, 1, '')  # second column of Q
        c2_j = len(sR)  # c₂(j)

        # Determine (2,3) ∈ ℘: from wp if provided, otherwise from DRC shape
        if wp is not None:
            has_23 = (1 in wp)  # PPidx 1 ⟺ (2,3) pair
        else:
            has_23 = (c2_j >= c1 + 2)  # shape-based fallback

        # B case (b): (2,3) ∈ ℘
        # Paper: γ=B+, (2,3)∈℘, Q(c₂(j_℘), 1) ∈ {r, d}
        # Action: Q'(c₁(j_{℘'}), 1) := r
        if has_23:
            q_c2j_1 = fR[c2_j - 1] if c2_j > 0 and c2_j <= len(fR) else ''
            if q_c2j_1 in ('r', 'd'):
                col0R = resR[0] if len(resR) > 0 else ''
                if col0R:
                    resR = (col0R[:-1] + 'r', *resR[1:])

        # B case (a): (2,3) ∉ ℘, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}
        # Action: P'(c₁(ι'), 1) = s
        # r₂(Ǒ) > 0 ⟺ DRC has at least 2 non-empty columns
        elif not has_23:
            ncols = sum(1 for c in drcL if c) + sum(1 for c in drcR if c)
            r2_pos = (ncols >= 2)
            q_c1_1 = fR[c1 - 1] if 0 < c1 <= len(fR) else ''
            if r2_pos and q_c1_1 in ('r', 'd'):
                col0 = resL[0]
                resL = (col0[:-1] + 's', *resL[1:])

        # B+ additional correction: reverse the lift's tR='r' → nsR='d' conversion.
        # When B+ and P is "shorter" than Q's second column, the lift algorithm
        # converts tR='r' to nsR='d'. Descent must reverse this: d → r.
        # Ported from combunipotent.drclift.descent_drc (lines 256-268).
        if len(sR) > 0 and len(resR) > 0:
            nL_src = len(resL[0]) if len(resL) > 0 else 0
            t_src = max(nL_src, len(sR)) - 1
            tL_empty = (len(sR) > nL_src)
            fR_at_tsrc = fR[t_src] if t_src < len(fR) else ''
            if (tL_empty and t_src >= 0 and t_src < len(resR[0])
                    and resR[0][t_src] == 'd'
                    and fR_at_tsrc in ('r', 'd')):
                r0 = resR[0]
                resR = (r0[:t_src] + 'r' + r0[t_src + 1:], *resR[1:])

    # D case (a) correction: [BMSZb] Section 10.4
    # Conditions:
    #   (1) γ = D
    #   (2) r₂(Ǒ) = r₃(Ǒ) > 0 ⟺ c₂(ι) = c₁(j) + 1
    #   (3) P(c₂(ι), 2) = c
    #   (4) P(i, 1) ∈ {r, d} for ALL c₂(ι) ≤ i ≤ c₁(ι)
    # Action: P'(c₁(ι'), 1) = r
    elif rtype == 'D':
        c1 = len(fL)
        c2 = len(sL)
        c1_j = len(fR)

        # Determine (2,3) ∈ ℘: from wp if provided, otherwise from DRC shape
        if wp is not None:
            has_23_D = (1 in wp)
        else:
            has_23_D = (c2 >= c1_j + 2)

        # D case (a): (2,3) ∉ ℘, r₂=r₃>0, P(c₂,2)=c, all P(i,1)∈{r,d}
        if not has_23_D and c2 > 0 and c2 == c1_j + 1:
            p_c2_2 = sL[-1] if sL else ''
            all_rd = all(fL[i] in ('r', 'd') for i in range(c2 - 1, c1))
            if p_c2_2 == 'c' and all_rd:
                col0 = resL[0]
                resL = (col0[:-1] + 'r', *resL[1:])

        # D case (b): (2,3) ∈ ℘
        # Paper: P(c₂(ι)-1, 1) ∈ {r, c} → P'(c₁(ι')-1, 1) = r,
        #        P'(c₁(ι'), 1) = P(c₂(ι)-1, 1)
        if has_23_D and c2 >= 2:
            x0 = fL[c2 - 2]  # P(c₂(ι)-1, 1), 0-based: fL[c₂-2]
            if x0 in ('r', 'c'):
                col0 = resL[0]
                resL = (col0[:-2] + 'r' + x0, *resL[1:])

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


def twist_C_nonspecial(drc):
    """
    Type C: map special-shape DRC to non-special-shape DRC (det twist).

    Special shape means 0 < c₁(τ_L) ≤ c₁(τ_R).
    The twist extends the left diagram's first column and shortens the right's.

    Reference: Section 10.2 of [BMSZb], analogous to combunipotent.drclift.twist_C_nonspecial.
    """
    drcL, drcR = drc
    fL = getz(drcL, 0, '')
    sL = getz(drcL, 1, '')
    fR = getz(drcR, 0, '')
    l = len(fR) - len(fL)
    # Check drc has special shape
    if l < 0 or len(fL) == 0:
        return None  # not a special-shape DRC
    fRR = fR[:-(l + 1)]
    x3 = fR[-(l + 1)]
    if x3 == 's':
        if len(fL) == 1 or fL[-2] != 'c':
            fLL = fL[:-1] + 'r' * (l + 1) + fL[-1:]
        else:
            # fL[-2:] = 'cd'
            fLL = fL[:-2] + 'r' * (l + 1) + fL[-2:]
        nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    else:
        # fR[-(l+1)] == '*'
        if len(sL) > len(fL) - 1 and getz(sL, len(fL) - 1, '') == 'r':
            fLL = fL[:-1] + 'r' * l + 'rd'
            sLL = sL[:-1] + 'c'
        else:
            fLL = fL[:-1] + 'r' * l + 'cd'
            sLL = sL
        nspdrc = ((fLL, sLL, *drcL[2:]), (fRR, *drcR[1:]))
    return reg_drc(nspdrc)


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


def twist_nsp2sp(drc, rtype):
    """
    Inverse of twist_C_nonspecial / twist_M_nonspecial: non-special → special shape.

    For C: non-special means c₁(P) ≥ c₁(Q) + 2. Shortens P, extends Q.
    For M: same as twist_M_nonspecial (self-inverse).

    Reference: Section 10.2 of [BMSZb], inverse of T_{℘,℘↑}.
    Ported from combunipotent.drclift.twist_nsp2sp.
    """
    if rtype == 'C':
        drcL, drcR = drc
        fL = getz(drcL, 0, '')
        sL = getz(drcL, 1, '')
        fR = getz(drcR, 0, '')
        l = len(fL) - len(fR) - 2
        assert l >= 0, f"twist_nsp2sp: not non-special shape, l={l}"
        if fL[-2] == 'c':
            if len(fR) > 0 and fL[len(fR) - 1] == 'r':
                fLL = fL[:len(fR) - 1] + 'cd'
                sLL = sL
                fRR = fR + 's' * (l + 1)
            else:
                fLL = fL[:len(fR)] + '*'
                sLL = sL
                fRR = fR + '*' + 's' * l
        else:
            # fL[-2] == 'r'
            if len(fR) + 1 == len(sL) and (sL[-1], fL[-1]) == ('c', 'd'):
                fLL = fL[:len(fR)] + '*'
                sLL = sL[:len(fR)] + 'r'
                fRR = fR + '*' + 's' * l
            else:
                fLL = fL[:len(fR)] + fL[-1]
                sLL = sL
                fRR = fR + 's' * (l + 1)
        spdrc = ((fLL, sLL, *drcL[2:]), (fRR, *drcR[1:]))
    elif rtype == 'M':
        spdrc = twist_M_nonspecial(drc)
    else:
        raise ValueError(f"twist_nsp2sp: unsupported rtype {rtype}")
    return reg_drc(spdrc)


# ============================================================================
# Phase 11b: General shape shifting at arbitrary position p
#            and bijection ⊔_℘ PBP(Ǒ,℘) ↔ PBP(Ǒ,∅) × 2^PP
# ============================================================================

def twistpbpup_at(pbp, p, rtype):
    """
    Shape shift up at column position p: PBP(Ǒ, ℘) → PBP(Ǒ, ℘∪{p}).

    For M: swap column p between L and R with translate c↔d, r↔s.
    For C: extend column p of L, shorten column p of R, with p-1 correction.

    Ported from combunipotent.drc.twistpbpup.
    Reference: [BMSZb] Section 10.2, Lemma 10.3.
    """
    pbp = reg_drc(pbp)
    pbpL, pbpR = pbp
    cols = max(len(pbpL), len(pbpR))

    if rtype == 'M':
        # Swap column p with translate c↔d, r↔s
        pbppL = tuple(
            getz(pbpL, i, '') if i != p else getz(pbpR, p, '').translate(_TR_M)
            for i in range(cols)
        )
        pbppR = tuple(
            getz(pbpR, i, '') if i != p else getz(pbpL, p, '').translate(_TR_M)
            for i in range(cols)
        )
        res = reg_drc((pbppL, pbppR))

    elif rtype == 'C':
        # Complex column extension at position p
        pbppL = list(getz(pbpL, i, '') if i != p else '' for i in range(cols))
        pbppR = list(getz(pbpR, i, '') if i != p else '' for i in range(cols))
        Lo = getz(pbpL, p, '')   # original column p of L
        Ro = getz(pbpR, p, '')   # original column p of R
        assert len(Ro) > 0
        s = len(Ro) - len(Lo)
        x2 = getz(getz(pbpL, p + 1, ''), len(Lo) - 1, '')
        x1 = Lo[-1] if Lo else ''
        Rn = Ro[:-(s + 1)]

        if x1 == '*':
            if x2 == 'r':
                Ln = Lo[:-1] + 'r' * s + 'rd'
                pbppL[p + 1] = pbppL[p + 1][:-1] + 'c'
            else:
                Ln = Lo[:-1] + 'r' * s + 'cd'
        else:
            x0 = getz(Lo, -2, '')
            if x0 == 'c':
                Ln = Lo[:-2] + 'r' * (s + 1) + 'cd'
            else:
                Ln = Lo[:-1] + 'r' * (s + 1) + Lo[-1]

        # p-1 column correction (only when p > 0)
        if p != 0:
            LLn = pbppL[p - 1]
            LRn = pbppR[p - 1]
            if len(LRn) == len(Ln) - 1:
                rs = 1
            else:
                rs = 2
            y2 = Ln[-1]
            y1 = LLn[len(Ln) - 1] if len(Ln) - 1 < len(LLn) else ''
            if (y1, y2) == ('r', 'r'):
                LLn = LLn[:len(Ln) - 2] + 'rr' + LLn[len(Ln):]
                LRn = LRn[:len(Ln) - 2] + 's' * rs + LRn[len(Ln):]
                Ln = Ln[:len(Ln) - 2] + 'cd'
            elif (y1, y2) == ('c', 'r'):
                LLn = LLn[:len(Ln) - 2] + 'rc' + LLn[len(Ln):]
                LRn = LRn[:len(Ln) - 2] + 's' * rs + LRn[len(Ln):]
                Ln = Ln[:len(Ln) - 2] + 'cd'
            elif (y1, y2) == ('d', 'r'):
                LLn = LLn[:len(Ln) - 2] + 'rd' + LLn[len(Ln):]
                LRn = LRn[:len(Ln) - 2] + 's' * rs + LRn[len(Ln):]
                Ln = Ln[:len(Ln) - 2] + 'cd'
            elif (y1, y2) == ('d', 'c'):
                LLn = LLn[:len(Ln) - 2] + 'cd' + LLn[len(Ln):]
                LRn = LRn[:len(Ln) - 2] + 's' * rs + LRn[len(Ln):]
                Ln = Ln[:len(Ln) - 2] + 'cd'
            pbppL[p - 1] = LLn
            pbppR[p - 1] = LRn

        pbppL[p] = Ln
        pbppR[p] = Rn
        res = reg_drc((tuple(pbppL), tuple(pbppR)))

    else:
        raise ValueError(f"twistpbpup_at: unsupported rtype {rtype}")

    if not verify_drc(res, rtype):
        raise ValueError(f"twistpbpup_at produced invalid DRC at p={p}")
    return res


def compute_PPidx(dpart, rtype):
    """
    Compute the list of primitive pair indices for the dual partition Ǒ.

    Returns a list of indices i such that the i-th pair is primitive.
    For C/M: index i corresponds to pair (2i+1, 2i+2) in 1-based row numbering.
    For B/D: index i corresponds to pair (2i+2, 2i+3) (after removing first row).

    Reference: [BMSZb] Definition 2.21.
    """
    rows = list(reg_part(dpart))
    a, res = divmod(len(rows), 2)
    if rtype == 'M' and res == 1:
        rows.append(0); a += 1
    elif rtype == 'C' and res == 1:
        rows.append(-1); a += 1
    elif rtype == 'B' and res == 0:
        rows.append(0)
    elif rtype == 'D' and res == 0:
        rows.append(-1)

    if rtype in ('B', 'D'):
        return [i for i in range(a)
                if rows[2 * i + 1] > rows[2 * i + 2] and rows[2 * i + 2] >= 0]
    elif rtype in ('C', 'M'):
        return [i for i in range(a)
                if rows[2 * i] > rows[2 * i + 1] and rows[2 * i + 1] >= 0]
    else:
        raise ValueError(f"compute_PPidx: unsupported rtype {rtype}")


def _allsubsets(lst):
    """Yield all subsets of lst as frozensets."""
    n = len(lst)
    for mask in range(1 << n):
        yield frozenset(lst[j] for j in range(n) if mask & (1 << j))


def drc_shape(drc):
    """Extract the W-representation bipartition (column lengths) from a DRC."""
    drcL, drcR = drc
    tauL = tuple(len(c) for c in drcL if len(c) > 0)
    tauR = tuple(len(c) for c in drcR if len(c) > 0)
    return (tauL, tauR)


def dpart2Wrepns_with_wp(dpart, rtype):
    """
    Compute W-representations labelled by ℘.

    Returns dict: frozenset(PPidx subset) → bipartition (tauL, tauR).
    Reference: [BMSZb] Section 8.3, equation (8.9).
    """
    rows = list(reg_part(dpart))
    a, res = divmod(len(rows), 2)
    if rtype == 'M' and res == 1:
        rows.append(0); a += 1
    elif rtype == 'C' and res == 1:
        rows.append(-1); a += 1
    elif rtype == 'B' and res == 0:
        rows.append(0)
    elif rtype == 'D' and res == 0:
        rows.append(-1)

    if rtype in ('B', 'D'):
        PPidx = [i for i in range(a)
                 if rows[2 * i + 1] > rows[2 * i + 2] and rows[2 * i + 2] >= 0]
    else:
        PPidx = [i for i in range(a)
                 if rows[2 * i] > rows[2 * i + 1] and rows[2 * i + 1] >= 0]

    result = {}
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
            tau = (tuple(sorted([x for x in otauL + tauL if x > 0], reverse=True)),
                   tuple(sorted([x for x in otauR + tauR if x > 0], reverse=True)))
            result[P] = tau

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
            tau = (tuple(sorted([x for x in otauL + tauL if x > 0], reverse=True)),
                   tuple(sorted([x for x in otauR + tauR if x > 0], reverse=True)))
            result[P] = tau

    return result


def _descend_wp(wp, rtype):
    """
    Compute ℘' = ∇̃(℘) in PPidx terms.

    For C/M → D/B: PPidx i maps to PPidx (i-1) in Howe dual.
    For D/B → C/M: PPidx i maps to PPidx i in Howe dual.

    Reference: [BMSZb] equation (3.15).
    """
    if rtype in ('C', 'M'):
        return frozenset(i - 1 for i in wp if i >= 1)
    elif rtype in ('B', 'D', 'B+', 'B-'):
        return frozenset(wp)
    else:
        raise ValueError(f"_descend_wp: unsupported rtype {rtype}")


def build_pbp_bijection(dpart, rtype):
    """
    Build bijection ⊔_℘ PBP(Ǒ,℘) ↔ PBP(Ǒ,∅) × {℘ | ℘ ⊆ PP_★(Ǒ)}.

    Inductive definition (all types C, M, D, B):

    For τ ∈ PBP(Ǒ, ℘):
      Case 1: ℘ = ∅ → τ₀ = τ.
      Case 2: ★ ∈ {C,M} and (1,2) ∈ ℘ → shape shift to get
              τ₁ ∈ PBP(Ǒ, ℘\\{(1,2)}), then reduce to Case 3.
      Case 3: (1,2) ∉ ℘ (or ★ ∈ {B,D}) → descent ∇(τ) ∈ PBP(Ǒ', ℘').
              Inductively biject ∇(τ) → τ'' ∈ PBP(Ǒ', ∅).
              Find τ₀ ∈ PBP(Ǒ, ∅) with ∇(τ₀) = τ'' (Prop 10.8).

    Returns:
        bijection: dict mapping drc → (special_shape_drc, frozenset(℘))
        table: dict mapping frozenset(℘) → list of DRCs in PBP(Ǒ,℘).

    Reference: [BMSZb] Propositions 10.2, 10.8, 10.9.
    """
    PPidx = compute_PPidx(dpart, rtype)
    wp_to_tau = dpart2Wrepns_with_wp(dpart, rtype)

    # Generate DRCs for all ℘
    all_drcs = {}
    for wp, tau in wp_to_tau.items():
        all_drcs[wp] = [reg_drc(d) for d in fill_drc(list(tau), rtype)]
    sp_drcs = all_drcs[frozenset()]

    table = dict(all_drcs)
    bijection = {drc: (drc, frozenset()) for drc in sp_drcs}

    if not PPidx:
        return bijection, table

    eff_rtype = 'B+' if rtype == 'B' else rtype

    if rtype in ('C', 'M'):
        # Inductive definition using Prop 10.8:
        # Build descent lookup: (∇(τ₀), γ') → τ₀ for τ₀ ∈ PBP(Ǒ, ∅)
        # Include γ' (B+/B- for M type) in key to avoid collisions
        descent_lookup = {}
        for tau0 in sp_drcs:
            d_tau0, d_rt = descent(tau0, eff_rtype)
            descent_lookup[(d_tau0, d_rt)] = tau0

        # Recursively build bijection at the descended level
        dpart_prime, rtype_prime = orbit_descent(dpart, rtype)
        rec_bij, _ = build_pbp_bijection(dpart_prime, rtype_prime)

        for wp, drcs in all_drcs.items():
            if wp == frozenset():
                continue
            for drc in drcs:
                current = drc
                current_wp = wp

                # Shape shift to remove PPidx 0 if present
                if 0 in current_wp:
                    if rtype == 'C':
                        current = twist_nsp2sp(current, 'C')
                    else:
                        current = reg_drc(twist_M_nonspecial(current))
                    current_wp = current_wp - {0}

                    if not current_wp:
                        bijection[drc] = (current, wp)
                        continue

                # Descent ∇ (include γ' tag)
                tau_prime, tau_prime_rt = descent(current, eff_rtype)

                # Recursively biject τ' → τ'' ∈ PBP(Ǒ', ∅)
                tau_double_prime, _ = rec_bij[tau_prime]

                # Inverse descent: find τ₀ with (∇(τ₀), γ') = (τ'', γ')
                tau_0 = descent_lookup[(tau_double_prime, tau_prime_rt)]
                bijection[drc] = (tau_0, wp)

    elif rtype in ('B', 'D'):
        # Cor 10.10: τ ↦ (∇τ, p_τ, q_τ, ε_τ) is injective for ★ ∈ {B, D}.
        # Descent to Howe dual (C/M), recursively biject there,
        # then inverse descent using (∇, sig, ε) lookup.
        descent_lookup = {}
        for tau0 in sp_drcs:
            d_tau0, d_rt0 = descent(tau0, eff_rtype)
            sig0 = signature(tau0, eff_rtype)
            xt0 = compute_tail_symbol(tau0, eff_rtype, dpart)
            eps0 = 0 if xt0 == 'd' else 1
            key = (d_tau0, sig0, eps0)
            descent_lookup[key] = tau0

        dpart_prime, rtype_prime = orbit_descent(dpart, rtype)
        rec_bij, _ = build_pbp_bijection(dpart_prime, rtype_prime)

        for wp, drcs in all_drcs.items():
            if wp == frozenset():
                continue
            for drc in drcs:
                tau_prime, tau_prime_rt = descent(drc, eff_rtype)
                sig = signature(drc, eff_rtype)
                xt = compute_tail_symbol(drc, eff_rtype, dpart)
                eps = 0 if xt == 'd' else 1

                tau_prime_0, _ = rec_bij[tau_prime]

                key = (tau_prime_0, sig, eps)
                if key in descent_lookup:
                    bijection[drc] = (descent_lookup[key], wp)
                else:
                    raise ValueError(
                        f"PBP bijection failed: no match for "
                        f"drc={drc}, wp={set(wp)}, key=({tau_prime_0}, {sig}, {eps})"
                    )

    return bijection, table


def verify_pbp_bijection(dpart, rtype, legacy_dpart2drc=None):
    """
    Verify the PBP bijection for a given dual partition and type.

    Checks:
    1. Each ℘-level has the same count as PBP(Ǒ,∅).
    2. The bijection dictionary is injective.
    3. Total count = #PBP(∅) × 2^|PP|.
    4. Cross-check with legacy dpart2drc if provided.
    """
    bijection, table = build_pbp_bijection(dpart, rtype)
    PPidx = compute_PPidx(dpart, rtype)
    n_sp = len(table[frozenset()])

    for wp, drcs in table.items():
        assert len(drcs) == n_sp, \
            f"℘={set(wp)}: got {len(drcs)}, expected {n_sp}"

    total = sum(len(drcs) for drcs in table.values())
    expected_total = n_sp * (2 ** len(PPidx))
    assert total == expected_total, \
        f"total={total}, expected {n_sp}×2^{len(PPidx)}={expected_total}"

    assert len(bijection) == total, \
        f"bijection has {len(bijection)} entries, expected {total}"

    if legacy_dpart2drc is not None:
        legacy_drcs = set(reg_drc(d) for d in legacy_dpart2drc(dpart, rtype))
        our_drcs = set(bijection.keys())
        missing = legacy_drcs - our_drcs
        extra = our_drcs - legacy_drcs
        assert not missing, f"missing from bijection: {len(missing)} DRCs"
        assert not extra, f"extra in bijection: {len(extra)} DRCs"

    return True


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


def myd_to_ils(myd):
    """Convert MYD dict {i: (p_i, q_i)} to ILS tuple ((p_1,n_1), ..., (p_k,n_k))."""
    if not myd:
        return ()
    max_idx = max(myd.keys())
    return tuple(myd.get(i + 1, (0, 0)) for i in range(max_idx))


def ils_to_myd(ils):
    """Convert ILS tuple to MYD dict."""
    return {i + 1: v for i, v in enumerate(ils) if v != (0, 0)}


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
    Returns None if the condition is not satisfied.
    """
    p1, q1 = E.get(1, (0, 0))
    # Check condition (9.19): E ⊒ (p₀, q₀)
    p_ok = (p1 >= p0 >= 0) or (p1 <= p0 <= 0)
    q_ok = (q1 >= q0 >= 0) or (q1 <= q0 <= 0)
    if not (p_ok and q_ok):
        return None  # truncation not valid
    result = dict(E)
    result[1] = (p1 - p0, q1 - q0)
    return _myd_clean(result)


def _myd_clean(E):
    """Remove entries with (0, 0)."""
    return {i: v for i, v in E.items() if v != (0, 0)}


def myd_size(E):
    """Total size |E| = sum of |p_i| + |q_i|."""
    return sum(abs(p) + abs(q) for p, q in E.values())


def myd_signature(E):
    """
    Compute the signature Sign(V ∘ E) of a marked Young diagram.

    Uses |p_i|, |q_i| (absolute values) per the map V from equation (9.13)
    of [BMSZ], composed with the Sign formula (9.10).

    Returns (p, q) where:
      (p,q) = Σ_{i∈N+} (i·|p_{2i}| + i·|q_{2i}|, i·|p_{2i}| + i·|q_{2i}|)
            + Σ_{i∈N+} (i·|p_{2i-1}| + (i-1)·|q_{2i-1}|, (i-1)·|p_{2i-1}| + i·|q_{2i-1}|)
    """
    sp, sq = 0, 0
    for idx, (pi, qi) in E.items():
        api, aqi = abs(pi), abs(qi)
        if idx % 2 == 0:
            i = idx // 2
            sp += i * api + i * aqi
            sq += i * api + i * aqi
        else:
            i = (idx + 1) // 2
            sp += i * api + (i - 1) * aqi
            sq += (i - 1) * api + i * aqi
    return (sp, sq)


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

    Oprime here is the signed Young diagram of O' as a dict {i: (p_i, q_i)}.
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


def _orbit_signed_yd(O_rows, p_total, q_total, rtype):
    """
    Compute the signed Young diagram of orbit O with row lengths O_rows
    and real form signature (p_total, q_total) of type rtype.

    Returns dict {i: (p_i, q_i)} where p_i = number of + rows of length i,
    q_i = number of - rows of length i.

    Reference: Definition 9.1, equation (9.8)-(9.9) of [BMSZ].

    Parity constraints (Definition 9.1):
      ★ ∈ {B, D}: p_i = q_i when i is even
      ★ ∈ {C, C̃}: p_i = q_i when i is odd

    Signature formula (9.9):
      (p,q) = Σ_{k≥1} (k·p_{2k} + k·q_{2k}, k·p_{2k} + k·q_{2k})
            + Σ_{k≥1} (k·p_{2k-1} + (k-1)·q_{2k-1}, (k-1)·p_{2k-1} + k·q_{2k-1})
    """
    from collections import Counter
    row_counts = Counter(O_rows)
    result = {}

    # Determine which levels are "free" (can split) vs "forced" (p=q)
    if rtype in ('B', 'B+', 'B-', 'D'):
        # Even levels forced: p_i = q_i = ι(i)/2
        # Odd levels free: p_i + q_i = ι(i), choose split
        forced_even = True
    elif rtype in ('C', 'M'):
        # Odd levels forced: p_i = q_i = ι(i)/2
        # Even levels free: p_i + q_i = ι(i), choose split
        forced_even = False
    else:
        forced_even = True

    # First pass: set forced levels
    forced_p, forced_q = 0, 0
    free_levels = []
    for length, count in sorted(row_counts.items()):
        is_even = (length % 2 == 0)
        if (forced_even and is_even) or (not forced_even and not is_even):
            # Forced: p_i = q_i = count/2
            half = count // 2
            result[length] = (half, half)
            # Contribution to signature
            k = length // 2 if is_even else (length + 1) // 2
            if is_even:
                forced_p += k * count
                forced_q += k * count
            else:
                forced_p += k * half + (k - 1) * half
                forced_q += (k - 1) * half + k * half
        else:
            # Free: need to determine split
            free_levels.append((length, count))

    # Remaining signature to distribute among free levels
    rem_p = p_total - forced_p
    rem_q = q_total - forced_q

    # For free levels, each unit of p_i contributes differently than q_i.
    # At odd level i=2k-1: p_i contributes (k, k-1), q_i contributes (k-1, k)
    # At even level i=2k: p_i contributes (k, k), q_i contributes (k, k)
    # So for free odd levels (B/D): p_i → (k, k-1), q_i → (k-1, k)
    # For free even levels (C/M): p_i → (k, k), q_i → (k, k) — no difference!

    if forced_even:
        # Free levels are odd: i=2k-1
        # p-q = Σ (p_i - q_i) for free levels
        target_diff = rem_p - rem_q

        # Assignment: process levels from SMALLEST to LARGEST
        # This matches the sl₂ decomposition structure where
        # smaller representations are assigned first.
        for length, count in sorted(free_levels):
            k = (length + 1) // 2
            diff_i = max(-count, min(count, target_diff))
            if (diff_i + count) % 2 != 0:
                diff_i += 1 if diff_i < count else -1
            p_i = (count + diff_i) // 2
            q_i = count - p_i
            result[length] = (p_i, q_i)
            target_diff -= diff_i
    else:
        # Free levels are even: i=2k
        # At even i=2k: both p_i and q_i contribute (k,k) — same!
        # So the split doesn't affect the signature.
        # Just split evenly or use any valid split.
        for length, count in free_levels:
            # Any split works since contribution is symmetric
            result[length] = (count, 0)  # arbitrary

    # Clean up zeros
    result = {i: (p, q) for i, (p, q) in result.items() if p != 0 or q != 0}
    return result


def _compute_sig_from_syd(syd):
    """
    Compute signature (p, q) from a signed Young diagram.
    Formula (9.9)/(9.10) of [BMSZ].
    """
    sp, sq = 0, 0
    for idx, (pi, qi) in syd.items():
        if idx % 2 == 0:
            i = idx // 2
            sp += i * pi + i * qi
            sq += i * pi + i * qi
        else:
            i = (idx + 1) // 2
            sp += i * pi + (i - 1) * qi
            sq += (i - 1) * pi + i * qi
    return (sp, sq)


def _compute_descended_syd(O_syd, p_source, q_source):
    """
    Compute O' = ∇^s_{s'}(O) via Lemma 9.2 of [BMSZ].

    O' is the geometric descent of the SYD O.
    O'(1) = O(2) + (p₀, q₀) where (p₀,q₀) = (p',q') - Sign(∇_naive(O))
    O'(i) = O(i+1) for i ≥ 2.

    Args:
        O_syd: the signed Young diagram O as dict {i: (p_i, q_i)}
        p_source, q_source: (p', q') source signature

    Returns the descended SYD O' as dict.
    """
    # ∇_naive(O)(i) = O(i+1)
    nabla = {}
    for i, (pi, qi) in O_syd.items():
        if i >= 2:
            nabla[i - 1] = (pi, qi)

    # Sign(∇_naive(O))
    sign_nabla = _compute_sig_from_syd(nabla)

    # (p₀, q₀) from equation (9.12)
    p0_912 = p_source - sign_nabla[0]
    q0_912 = q_source - sign_nabla[1]

    # O'(1) = O(2) + (p₀, q₀)
    o2 = O_syd.get(2, (0, 0))
    Oprime = dict(nabla)  # copy ∇_naive(O) for i ≥ 1
    Oprime[1] = (o2[0] + p0_912, o2[1] + q0_912)

    return _myd_clean(Oprime)


def _compute_lsign_from_orbit(O_rows, p_target, q_target, target_rtype,
                               p_source, q_source):
    """
    Compute ˡSign(O') for use in formula (9.29)/(9.30) of [BMSZ].

    O is the BV dual orbit with row lengths O_rows and TARGET signature (p,q).
    O' = ∇(O) is the descended SYD, computed via Lemma 9.2.

    Args:
        O_rows: row lengths of the orbit O (BV dual of Ǒ)
        p_target, q_target: target signature (p, q) of the current step
        target_rtype: type ★ of the current step
        p_source, q_source: source signature (p', q')

    Returns (ˡSign_p, ˡSign_q).
    """
    # 1. Build SYD O from orbit and target signature
    O_syd = _orbit_signed_yd(O_rows, p_target, q_target, target_rtype)

    # 2. Compute descended SYD O' via Lemma 9.2
    Oprime = _compute_descended_syd(O_syd, p_source, q_source)

    # 3. Compute ˡSign(O')
    return _lsign(Oprime)


def _ils_sign(irr_s):
    """Compute signature (p, n) of an ILS tuple.
    Reference: [BMSZ] Section 9.3, LS._sign_ILS in LS.py."""
    p, n = 0, 0
    for i, (pp, nn) in enumerate(irr_s):
        dii, rii = divmod(i + 1, 2)
        p += abs(pp) * (dii + rii) + abs(nn) * dii
        n += abs(nn) * (dii + rii) + abs(pp) * dii
    return (p, n)


def _ils_firstcol_sign(irr_s):
    """Compute first-column signature of an ILS.
    Reference: [BMSZ] Section 9.3, LS._sign_ILS_firstcol in LS.py."""
    p, n = 0, 0
    for i, (pp, nn) in enumerate(irr_s):
        if i % 2 == 0:
            p += abs(pp)
            n += abs(nn)
        else:
            p += abs(nn)
            n += abs(pp)
    return (p, n)


def _ils_twist_BD(irr_s, twist):
    """
    Determinant twist on an ILS.
    Reference: [BMSZ] Section 9.4, LS._char_twist_D / _char_twist_B.

    twist = (tp, tn) where tp, tn ∈ {1, -1}.
    Acts on odd-length rows (0-based index i where (i+1) is odd).

    Common cases:
      (1, -1): sign twist ⊗ (0, 1) for B/D post-twist
      (-1, -1): sign twist ⊗ (1, 1) for C/M pre-twist
      (1, 1): identity
    """
    tp, tn = twist
    irr_ss = []
    for i, (pp, nn) in enumerate(irr_s):
        hrl, rrl = divmod(i + 1, 2)
        if rrl == 0:
            irr_ss.append((pp, nn))
        else:
            tpp = (tp ** (hrl + 1)) * (tn ** hrl)
            tnn = (tn ** (hrl + 1)) * (tp ** hrl)
            irr_ss.append((tpp * pp, tnn * nn))
    return tuple(irr_ss)


def _ils_char_twist_CM(irr_s, j):
    """
    Character twist T^j on an ILS.
    Negate entries at positions i ≡ 2 (mod 4) when j is odd.
    T² = identity, so only parity of j matters.

    Reference: [BMSZ] Section 9.4, LS._char_twist_C / _char_twist_CM.
      _char_twist_C(irr_s, ps, ns) = _ils_char_twist_CM(irr_s, (ps-ns)//2)
      _char_twist_CM(irr_s, j)     = _ils_char_twist_CM(irr_s, j)
    """
    if int(j) % 2 == 1:
        return tuple((-pp, -nn) if (i + 1) % 4 == 2 else (pp, nn)
                     for i, (pp, nn) in enumerate(irr_s))
    return irr_s


def theta_lift_ils(irr_s, rtype, p, q):
    """
    Theta lift a single ILS to target type ★ with signature (p, q).

    Reference: [BMSZ] Section 11.1-11.3.
    Ported from LS.py: lift_irr_D_C, lift_irr_C_D, lift_irr_B_M, lift_irr_M_B.

    Lift directions:
      D → C:  target Sp(2n), n = p = q
      C → D:  target O(p, q), p+q even
      B → M:  target Mp(2n), n = p = q
      M → B:  target O(p, q), p+q odd

    Args:
        irr_s: source ILS tuple ((p_1,n_1), (p_2,n_2), ...)
        rtype: target type ★ ∈ {C, D, M, B+, B-}
        p, q: target signature

    Returns:
        List of ILS tuples (may be empty or have multiple terms).
    """
    ps, ns = _ils_sign(irr_s)
    fps, fns = _ils_firstcol_sign(irr_s)

    if rtype == 'C':
        # D → C: target Sp(2n), sig = (n, n)
        n = p
        addp, addn = n - ps - fns, n - ns - fps
        if addp >= 0 and addn >= 0:
            irr_ss = ((addp, addn),) + irr_s
            return [_ils_char_twist_CM(irr_ss, (ps - ns) // 2)]
        elif (addp, addn) in [(-1, -1), (-2, 0), (0, -2)]:
            pp0, nn0 = irr_s[0]
            ss = []
            if pp0 > 0:
                irr_ss = ((0, 0), (pp0 - 1, nn0)) + irr_s[1:]
                ss.append(_ils_char_twist_CM(irr_ss, (ps - ns) // 2))
            if nn0 > 0:
                irr_ss = ((0, 0), (pp0, nn0 - 1)) + irr_s[1:]
                ss.append(_ils_char_twist_CM(irr_ss, (ps - ns) // 2))
            return ss
        else:
            return []

    elif rtype == 'D':
        # C → D: target O(p, q), p+q even
        addp, addn = p - ps - fns, q - ns - fps
        if addp >= 0 and addn >= 0:
            irr_s_tw = _ils_char_twist_CM(irr_s, (p - q) // 2)
            return [((addp, addn),) + irr_s_tw]
        else:
            return []

    elif rtype == 'M':
        # B → M: target Mp(2n), sig = (n, n)
        n = p
        addp, addn = n - ps - fns, n - ns - fps
        if addp >= 0 and addn >= 0:
            irr_ss = ((addp, addn),) + irr_s
            return [_ils_char_twist_CM(irr_ss, (ps - ns - 1) // 2)]
        elif (addp, addn) in [(-1, -1), (-2, 0), (0, -2)]:
            pp0, nn0 = irr_s[0]
            ss = []
            if pp0 > 0:
                irr_ss = ((0, 0), (pp0 - 1, nn0)) + irr_s[1:]
                ss.append(_ils_char_twist_CM(irr_ss, (ps - ns - 1) // 2))
            if nn0 > 0:
                irr_ss = ((0, 0), (pp0, nn0 - 1)) + irr_s[1:]
                ss.append(_ils_char_twist_CM(irr_ss, (ps - ns - 1) // 2))
            return ss
        else:
            return []

    elif rtype in ('B+', 'B-'):
        # M → B: target O(p, q), p+q odd
        addp, addn = p - ps - fns, q - ns - fps
        if addp >= 0 and addn >= 0:
            irr_s_tw = _ils_char_twist_CM(irr_s, (p - q + 1) // 2)
            return [((addp, addn),) + irr_s_tw]
        else:
            return []

    else:
        raise ValueError(f"theta_lift_ils: unsupported target rtype {rtype}")


def theta_lift_ls(ls, rtype, p, q):
    """
    Theta lift a local system (FrozenMultiset of ILS tuples).

    Lifts each ILS component independently. Returns a FrozenMultiset.

    Args:
        ls: FrozenMultiset of ILS tuples
        rtype: target type ★
        p, q: target signature

    Returns:
        FrozenMultiset of lifted ILS tuples.
    """
    result = []
    for irr_s in ls:
        lifted = theta_lift_ils(irr_s, rtype, p, q)
        result.extend(lifted)
    return FrozenMultiset(result)


def twist_ls(ls, twist):
    """Apply character twist to every ILS in a LS (FrozenMultiset)."""
    return FrozenMultiset(_ils_twist_BD(irr_s, twist) for irr_s in ls)


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
        # Return ROW lengths (not column lengths)
        return reg_part(dualBVW(dpart, bv_rtype, partrc='r'))
    except ImportError:
        # Fallback: for purely even orbits, the BV dual has a simpler form
        # This is a placeholder — full BV duality requires Springer correspondence
        raise NotImplementedError("BV duality requires combunipotent package")


def compute_AC(drc, wp, rtype, cache=None):
    """
    Compute the associated cycle AC(τ̂) for extended PBP τ̂ = (τ, ℘, ★).

    Reference: [BMSZ] Equation (3.16), Section 11.2.
    - Base case (|τ| = 0): trivial/det/genuine ILS
    - ★ ∈ {B,D}: AC(τ̂) = ϑ̂(AC(∇τ̂)) ⊗ (0, ε_τ)     (Eq. 3.16 case 1)
    - ★ ∈ {C,M}: AC(τ̂) = ϑ̂(AC(∇τ̂) ⊗ (ε_℘, ε_℘))  (Eq. 3.16 case 2)
      where ε_℘ = 1 iff (1,2) ∈ ℘  (below Eq. 3.16).

    The descent ∇ acts on BOTH the DRC and ℘:
    - DRC: ∇(drc) via the descent function
    - ℘:   ∇̃(℘) = {(j-1, j) : (j, j+1) ∈ ℘, j ≥ 2}

    Args:
        drc: painted bipartition (drcL, drcR)
        wp: frozenset of primitive pairs ℘, or None for ℘ = ∅
        rtype: B+, B-, C, D, or M
        cache: shared dict for memoization

    Returns list of (coefficient, ILS tuple) pairs.
    """
    if rtype == 'B':
        raise ValueError("compute_AC requires rtype='B+' or 'B-', not 'B'.")

    # --- Base case: DRC is empty ---
    drcL, drcR = drc
    total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
    if total == 0:
        if rtype == 'B+':
            return [(1, ((1, 0),))]
        elif rtype == 'B-':
            return [(1, ((0, -1),))]
        else:
            return [(1, ())]

    if cache is None:
        cache = {}

    # ε_℘ for this step: 1 if PPidx 0 is in ℘
    e_wp = 1 if (wp is not None and 0 in wp) else 0

    # Descend ℘ using _descend_wp (integer PPidx representation)
    wp_prime = None
    if wp is not None and len(wp) > 0:
        new_wp = _descend_wp(wp, rtype)
        wp_prime = new_wp if new_wp else None

    # Descent of DRC
    tau_p, tau_q = signature(drc, rtype)
    tau_eps = epsilon(drc, rtype)
    next_drc, next_rtype = descent(drc, rtype)

    # Cache key includes wp because ℘ affects the recursion
    cache_key = (drc, rtype, wp if wp else None)

    if cache_key not in cache:
        # Recursively compute AC of descended extended PBP
        source_AC = compute_AC(next_drc, wp_prime, next_rtype, cache=cache)

        new_AC = []
        for coeff, ils in source_AC:
            # C/M pre-twist: ⊗ (ε_℘, ε_℘) on source ILS
            source_ils = ils
            if rtype in ('C', 'M') and e_wp != 0:
                source_ils = _ils_twist_BD(ils, (-1, -1))

            # Theta lift
            lifted = theta_lift_ils(source_ils, rtype, tau_p, tau_q)

            for lifted_ils in lifted:
                # B/D post-twist: ⊗ (0, ε_τ)
                if rtype in ('B+', 'B-', 'D') and tau_eps != 0:
                    lifted_ils = _ils_twist_BD(lifted_ils, (1, -1))
                new_AC.append((coeff, lifted_ils))

        cache[cache_key] = new_AC

    return cache[cache_key]


def print_AC(drc, wp, rtype):
    """Print the associated cycle for an extended PBP."""
    ac = compute_AC(drc, wp, rtype)
    print(f"AC ({rtype}, ℘={set(wp) if wp else '∅'}):")
    for coeff, ils in ac:
        print(f"  {coeff} × {ils}")


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

        result.append((cur_drc, cur_rtype, sig, eps, cur_dpart))

        # Base case: trivial group
        # B/M chain ends at Mp(0): type M, empty DRC
        # C/D chain ends at SO(0) or Sp(0): type C or D, empty DRC
        drcL, drcR = cur_drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        if total == 0 and cur_rtype in ('C', 'M', 'D'):
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
# ============================================================================
# Phase 12e: Tail of a painted bipartition (for ★ ∈ {B, D})
#            ([BMSZb] Section 10.5, equation 10.7)
# ============================================================================

def compute_tail_signature(drc, rtype):
    """
    Compute the tail signature (p_τt, q_τt) for ★ ∈ {B, D}.

    The tail τ_t consists of the cells in the "extra" columns of the
    longer diagram beyond the shorter diagram.

    For B type: tail = cells in Q's first column beyond P's first column.
    For D type: tail = cells in P's first column beyond Q's first column.

    The tail signature sums per-cell contributions to (p, q):
      '*': (1, 1), 'r': (2, 0), 's': (0, 2), 'c': (1, 1), 'd': (1, 1)

    Reference: [BMSZ] Lemma 11.3, equation (11.10).
    """
    drcL, drcR = drc
    c1_iota = len(getz(drcL, 0, ''))
    c1_j = len(getz(drcR, 0, ''))

    # Per-cell contribution to (p, q)
    _CELL_CONTRIB = {'*': (1, 1), 'r': (2, 0), 's': (0, 2), 'c': (1, 1), 'd': (1, 1)}

    p_tail, q_tail = 0, 0

    if rtype in ('B', 'B+', 'B-'):
        # Tail is in Q (right diagram), rows c₁(ι) to c₁(j)-1 (0-indexed)
        first_col_Q = getz(drcR, 0, '')
        for row in range(c1_iota, c1_j):
            sym = first_col_Q[row] if row < len(first_col_Q) else '*'
            dp, dq = _CELL_CONTRIB.get(sym, (1, 1))
            p_tail += dp
            q_tail += dq
    elif rtype == 'D':
        # Tail is in P (left diagram), rows c₁(j) to c₁(ι)-1 (0-indexed)
        first_col_P = getz(drcL, 0, '')
        for row in range(c1_j, c1_iota):
            sym = first_col_P[row] if row < len(first_col_P) else '*'
            dp, dq = _CELL_CONTRIB.get(sym, (1, 1))
            p_tail += dp
            q_tail += dq

    return (p_tail, q_tail)


def compute_tail_symbol(drc, rtype, dpart=None):
    """
    Compute the tail symbol x_τ for ★ ∈ {B, D}.

    x_τ := P_{τ_t}(k, 1), the symbol in the last box of the tail τ_t.
    x_τ ∈ {c, d, r, s}.

    For ★ = B: x_τ is determined by the last entry in the Q (right) diagram's
    first column, plus the B+/B- correction.
    For ★ = D: x_τ is determined by the last entry in the P (left) diagram's
    first column, plus special cases for balanced pairs.

    Reference: [BMSZb] Section 10.5.
    """
    drcL, drcR = drc

    if rtype in ('B', 'B+', 'B-'):
        # ★ = B: c₁(ι) ≤ c₁(j)
        # x_τ = x_k where k = (r₁-r₂)/2 + 1 (paper definition).
        # Tail multiset: {x₁, ..., x_k} where
        #   Set A = {Q(j,1) | c₁(ι)+1 ≤ j ≤ c₁(j)} has c₁(j)-c₁(ι) elements
        #   Correction adds 1 element (x₁)
        #   Total = c₁(j) - c₁(ι) + 1 = k
        # x_τ = x_k = last element of Set A = Q(c₁(j), 1) = fR[-1]
        # UNLESS k = 1 (Set A is empty), then x_τ = x₁ = correction.
        c1_iota = len(getz(drcL, 0, ''))  # first column of P
        c1_j = len(getz(drcR, 0, ''))     # first column of Q
        setA_size = c1_j - c1_iota  # = k - 1

        if setA_size <= 0:
            # k ≤ 1: x_τ = correction element
            q_c1 = getz(drcR, 0, '')[c1_iota - 1] if c1_iota > 0 and c1_iota <= c1_j else ''
            if c1_iota == 0 or q_c1 in ('*', 's'):
                if rtype == 'B+' or (rtype == 'B' and verify_drc(drc, 'B+')):
                    return 'c'
                else:
                    return 's'
            else:
                return q_c1
        else:
            # k > 1: x_τ = x_k = Q(c₁(j), 1) = fR[-1]
            return getz(drcR, 0, '')[-1] if c1_j > 0 else ''

    elif rtype == 'D':
        # ★ = D: c₁(ι) > c₁(j) when |Ǒ| > 0
        # x_τ = x_k where k = (r₁-r₂)/2 + 1 (paper definition).
        # Tail multiset: {x₁, ..., x_k} where
        #   Set A = {P(j,1) | c₁(j)+2 ≤ j ≤ c₁(ι)} has c₁(ι)-c₁(j)-1 elements
        #   Correction adds 1 element (x₁)
        #   Total = c₁(ι) - c₁(j) = k
        # x_τ = x_k = last element of Set A = P(c₁(ι), 1) = fL[-1]
        # UNLESS Set A is empty (k = 1), then x_τ = x₁ = correction.
        c1_iota = len(getz(drcL, 0, ''))
        c1_j = len(getz(drcR, 0, ''))

        if c1_iota == 0 and c1_j == 0:
            return 'd'  # |Ǒ| = 0

        setA_size = c1_iota - c1_j - 1  # = k - 1

        if setA_size <= 0:
            # k ≤ 1: x_τ = correction element
            p_c1j1 = getz(drcL, 0, '')[c1_j] if c1_j < c1_iota else ''
            # Check scattered case: r₂ = r₃ > 0
            if dpart is not None:
                rows = reg_part(dpart)
                r2 = getz(rows, 1, 0)
                r3 = getz(rows, 2, 0)
                if r2 == r3 and r2 > 0:
                    p_c1_1 = getz(drcL, 0, '')[c1_iota - 1] if c1_iota > 0 else ''
                    sL = getz(drcL, 1, '')
                    p_c1j1_2 = sL[c1_j] if c1_j < len(sL) else ''
                    if p_c1_1 in ('r', 'd') and (p_c1j1, p_c1j1_2) == ('r', 'c'):
                        return 'c'
            return p_c1j1
        else:
            # k > 1: x_τ = x_k = P(c₁(ι), 1) = fL[-1]
            return getz(drcL, 0, '')[-1] if c1_iota > 0 else ''

    else:
        return ''  # tail only defined for B, D


# ============================================================================
# Phase 12f: Recursive counting of PBPs
#            (Propositions 10.11-10.12 of [BMSZb])
# ============================================================================

def countPBP(dpart, rtype):
    """
    Count the number of painted bipartitions #PBP_★(Ǒ, ∅) using the
    recursive formulas from [BMSZb] Propositions 10.11 and 10.12.

    This counts PBPs for ℘ = ∅ (special shape). Since #PBP is independent
    of ℘ (Proposition 10.2), this also gives #PBP for any ℘.

    For ★ ∈ {B, D}: returns the generating function f(p,q) evaluated at (1,1).
    For ★ ∈ {C, M}: returns the count directly.

    The recursive formula relates #PBP_★(Ǒ) to #PBP_{★'}(∇̃(Ǒ))
    where ★' is the Howe dual:
      B ↔ M,  C ↔ D.
    """
    dpart = reg_part(dpart)

    if rtype == 'C':
        return _countPBP_C(dpart)
    elif rtype == 'M':
        return _countPBP_M(dpart)
    elif rtype == 'D':
        DD, RC, SS = _countPBP_D(dpart)
        return DD + RC + SS
    elif rtype == 'B':
        DD, RC, SS = _countPBP_B(dpart)
        # f_B(1,1) counts both B+ and B-; they have equal count.
        return (DD + RC + SS) // 2
    else:
        raise ValueError(f"Unknown rtype: {rtype}")


def _countPBP_D(dpart):
    """
    Count PBPs for type D using Proposition 10.11 of [BMSZb].
    Ǒ has all odd rows, total even.

    Returns (DD, RC, SS) triple:
      DD = count of PBPs with tail symbol d
      RC = count of PBPs with tail symbol in {c, r}
      SS = count of PBPs with tail symbol s

    Total = DD + RC + SS.
    """
    if len(dpart) == 0:
        return (1, 0, 0)  # base case: f^{d}=1, f^{c,r}=0, f^{s}=0

    R1 = dpart[0]
    R2 = dpart[1] if len(dpart) > 1 else 0
    R3 = dpart[2] if len(dpart) > 2 else -1
    k = (R1 - R2) // 2 + 1  # k from Proposition 10.11

    # Tail polynomials for D,[2k-1,1]_row (evaluated at p=q=1: r=s=c=d=1)
    # ν_k at (1,1) = k+1
    def nu(n):
        return n + 1 if n >= 0 else 0

    TDD = nu(k - 1) * 1 + nu(k - 2) * 1  # ν_{k-1}·d + ν_{k-2}·cd
    TRC = nu(k - 1) * 1 + 1 * nu(k - 1)  # ν_{k-1}·c + r·ν_{k-1}
    TSS = 1  # s^k = 1 at p=q=1

    if R2 > R3:
        # (2,3) is primitive: Prop 10.11(a)
        C2 = R2 - 1
        DDp, RCp, SSp = _countPBP_D(dpart[2:])
        resp = 1 * (DDp + RCp + SSp)  # (pq)^{c₁} at (1,1) = 1
        return (resp * TDD, resp * TRC, resp * TSS)
    else:
        # (2,3) is balanced: Prop 10.11(b)
        scDD = nu(k - 2) * 1 + 1 * nu(k - 2) * 1  # ν_{k-2}·cd + s·ν_{k-2}·d
        scRC = nu(k - 1) * 1 + 1 * nu(k - 2) * 1  # ν_{k-1}·c + s·ν_{k-2}·r
        scSS = 1  # s^k

        DDp, RCp, SSp = _countPBP_D(dpart[2:])
        DD = DDp * TDD + RCp * scDD
        RC = DDp * TRC + RCp * scRC
        SS = DDp * TSS + RCp * scSS
        return (DD, RC, SS)


def _countPBP_B(dpart):
    """
    Count PBPs for type B using Proposition 10.11 of [BMSZb].
    Ǒ has all even rows, total even.

    Returns (DD, RC, SS) triple.
    """
    # Remove trailing zeros
    dpart = tuple(r for r in dpart if r > 0)

    if len(dpart) <= 1:
        # Base case: single even row [2k] or empty
        c1 = dpart[0] // 2 if len(dpart) == 1 else 0

        def nu(n):
            return n + 1 if n >= 0 else 0

        DD = 1 * 2 * nu(c1 - 1)       # d·(p+q)·ν_{c1-1} at (1,1)
        RC = 1 * nu(c1) + 1 * nu(c1 - 1)  # p·ν_{c1} + q·r·ν_{c1-1}
        SS = 1                         # q·s^{c1}
        return (DD, RC, SS)

    R1 = dpart[0]
    R2 = dpart[1]
    R3 = dpart[2] if len(dpart) > 2 else 0
    k = (R1 - R2) // 2 + 1

    def nu(n):
        return n + 1 if n >= 0 else 0

    TDD = nu(k - 1) + nu(k - 2)
    TRC = nu(k - 1) + nu(k - 1)
    TSS = 1

    if R2 > R3:
        C2 = R2 - 1
        DDp, RCp, SSp = _countPBP_B(dpart[2:])
        resp = DDp + RCp + SSp
        return (resp * TDD, resp * TRC, resp * TSS)
    else:
        scDD = nu(k - 2) + nu(k - 2)
        scRC = nu(k - 1) + nu(k - 2)
        scSS = 1

        DDp, RCp, SSp = _countPBP_B(dpart[2:])
        DD = DDp * TDD + RCp * scDD
        RC = DDp * TRC + RCp * scRC
        SS = DDp * TSS + RCp * scSS
        return (DD, RC, SS)


def _countPBP_C(dpart):
    """
    Count PBPs for type C, ℘=∅, using Proposition 10.12 of [BMSZb].
    Ǒ has all odd rows, total odd.

    Proposition 10.12:
    (a) If (1,2) ∈ PP_★(Ǒ): #PBP_★(Ǒ, ℘) = f_{★',∇̃(Ǒ),∇̃(℘)}(1,1)
    (b) If (1,2) ∉ PP_★(Ǒ): #PBP_★(Ǒ, ℘) = f^{c,r}_{★',∇̃(Ǒ),∇̃(℘)}(1,1) + f^{d}_{★',∇̃(Ǒ),∇̃(℘)}(1,1)

    Returns the count #PBP_C(Ǒ, ∅).
    """
    if len(dpart) == 0:
        return 0
    if len(dpart) == 1:
        return 1

    R1 = dpart[0]
    R2 = dpart[1]

    # Howe dual: C ↔ D
    DDp, RCp, SSp = _countPBP_D(dpart[1:])

    if R1 > R2:
        # (1,2) is primitive: Prop 10.12(a)
        # #PBP = f_D(1,1) = DD + RC + SS (for ONE ℘)
        return DDp + RCp + SSp
    else:
        # (1,2) balanced: Prop 10.12(b)
        # #PBP = f^{c,r} + f^{d} = DD + RC (no SS)
        return DDp + RCp


def _countPBP_M(dpart):
    """
    Count PBPs for type M (= C̃), ℘=∅, using Proposition 10.12 of [BMSZb].
    Ǒ has all even rows, total even.

    Returns the count #PBP_M(Ǒ, ∅).
    """
    dpart = tuple(r for r in dpart if r > 0)

    if len(dpart) == 0:
        return 1

    R1 = dpart[0]
    R2 = dpart[1] if len(dpart) > 1 else 0

    # Howe dual: M ↔ B
    DDp, RCp, SSp = _countPBP_B(dpart[1:])

    if R1 > R2:
        # (1,2) is primitive: Prop 10.12(a)
        return DDp + RCp + SSp
    else:
        # (1,2) balanced: Prop 10.12(b)
        return DDp + RCp


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
    Draw one irreducible MYD/ILS component as rows of +-*/=- symbols.

    Accepts either:
      - MYD dict: {i: (p_i, q_i)}
      - ILS tuple: ((p_1,q_1), (p_2,q_2), ...)

    Row patterns follow the alternating sign convention from [BMSZ]:
      odd-length rows:  +, -+, +-+, -+-+, ...
      even-length rows: -, +-, -+-, +-+-, ...
    """
    # Normalize to list of (level, (pi, qi)) pairs
    if isinstance(myd_entry, dict):
        entries = sorted(myd_entry.items(), reverse=True)
    else:
        # ILS tuple: index j (0-based) → level i = j+1
        entries = [(j + 1, pq) for j, pq in enumerate(myd_entry) if pq != (0, 0)]
        entries.sort(reverse=True)

    rows = []
    for i, (pi, qi) in entries:
        hii, rii = divmod(i, 2)
        if qi != 0:
            if qi > 0:
                onerow = _PNPN[1] * rii + _PNPN[0:2] * hii
            else:
                onerow = _QMQM[1] * rii + _QMQM[0:2] * hii
            rows.extend([onerow] * abs(qi))
        if pi != 0:
            if pi > 0:
                onerow = _PNPN[0] * rii + _PNPN[1:3] * hii
            else:
                onerow = _QMQM[0] * rii + _QMQM[1:3] * hii
            rows.extend([onerow] * abs(pi))
    return rows


def str_ils(ils):
    """
    Draw a single ILS (irreducible local system) in visual LS format.

    Uses the same display convention as combunipotent.LS.str_LS:
      + trivial on + sign, - trivial on - sign
      * non-trivial on + sign, = non-trivial on - sign
    """
    if not ils or ils == ():
        return '(trivial)'
    rows = _str_irr_myd(ils)
    if not rows:
        return '(trivial)'
    return '\n'.join(rows)


def str_ls(ls):
    """
    Draw a local system (list/set of ILS tuples) in visual format.
    Multiple ILS components are shown side by side separated by ' | '.
    """
    if not ls:
        return '(empty)'

    ls_list = list(ls) if not isinstance(ls, list) else ls
    all_row_blocks = []
    for ils in ls_list:
        rows = _str_irr_myd(ils) if (ils and ils != ()) else ['(triv)']
        all_row_blocks.append(rows)

    if not all_row_blocks:
        return '(empty)'

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


# Keep old names as aliases
str_myd = str_ils
str_myd_ac = lambda ac_list: str_ls([ils for _, ils in ac_list]) if ac_list else '(empty)'


def _format_myd_multiline(ac_list):
    """Format AC (list of (coeff, myd)) as multiline string for graph label."""
    if not ac_list:
        return ['(empty)']

    all_row_blocks = []
    for coeff, myd in ac_list:
        rows = _str_irr_myd(myd) if (myd and myd != ()) else ['(triv)']
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


def gen_lift_tree(dpart, rtype, format='svg', filename=None):
    """
    Generate the lifting tree graph.

    Two structures:
    1. Extended PBP tree: nodes = (drc, ℘, ★), edges = descent/lift
    2. LS tree: nodes = distinct LS values (FrozenMultiset of ILS),
       edges = theta lift (blue), det twist (red), 1⁺⁻ (green), 1⁻⁺ (purple)

    Each LS box contains:
    - The local system (ILS visual)
    - All extended PBPs τ with L_τ = this LS, shown with:
      - DRC diagram (℘ marked with red columns)
      - B+/B- label (type B)
      - ε_τ (type B/D) or ε_℘ (type C/M)
    """
    from graphviz import Digraph

    if filename is None:
        filename = f'{rtype}{",".join(str(x) for x in dpart)}'

    drcs = dpart2drc(dpart, rtype)
    PPidx = compute_PPidx(dpart, rtype)

    # --- Step 1 & 2: Build extended PBP tree by recursive descent ---
    # Start from top-level extended PBPs and descend, creating all nodes.
    tree_nodes = {}  # (drc, wp_fs, rt) → {parent, children, ls}

    def ensure_node(key):
        if key not in tree_nodes:
            tree_nodes[key] = {
                'parent': None, 'children': [], 'ls': None,
                'drc': key[0], 'wp': key[1], 'rtype': key[2],
            }

    def build_tree(drc, wp_fs, rt):
        """Recursively build tree from this extended PBP down to root."""
        key = (drc, wp_fs, rt)
        if key in tree_nodes:
            return  # already built
        ensure_node(key)

        drcL, drcR = drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        # Base case: trivial group
        # B/M chain ends at Mp(0) = type M, empty DRC
        # C/D chain ends at Sp(0)/SO(0) = type C/D, empty DRC
        if total == 0 and rt in ('C', 'M', 'D'):
            return  # root, no parent

        # Descent
        next_drc, next_rt = descent(drc, rt)
        next_wp = None
        if wp_fs is not None and len(wp_fs) > 0:
            nw = _descend_wp(wp_fs, rt)
            next_wp = nw if nw else None

        parent_key = (next_drc, next_wp, next_rt)
        build_tree(next_drc, next_wp, next_rt)  # ensure parent exists

        tree_nodes[key]['parent'] = parent_key
        tree_nodes[parent_key]['children'].append(key)

    # Start from all top-level extended PBPs
    rtypes_expand = ['B+', 'B-'] if rtype == 'B' else [rtype]
    for drc in drcs:
        for wp in _allsubsets(PPidx):
            wp_fs = frozenset(wp) if wp else None
            for rt in rtypes_expand:
                build_tree(drc, wp_fs, rt)

    # --- Step 3: Compute LS bottom-up ---
    # BFS from roots (empty DRC nodes)
    from collections import deque
    queue = deque()
    for key, node in tree_nodes.items():
        drc, wp_fs, rt = key
        drcL, drcR = drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        if total == 0 and rt in ('C', 'M', 'D'):
            # True root: trivial group
            node['ls'] = FrozenMultiset([()])
            queue.append(key)

    while queue:
        parent_key = queue.popleft()
        parent_node = tree_nodes[parent_key]
        parent_ls = parent_node['ls']
        parent_rt = parent_key[2]

        for child_key in parent_node['children']:
            child_drc, child_wp, child_rt = child_key
            child_node = tree_nodes[child_key]

            tau_p, tau_q = signature(child_drc, child_rt)

            # Pre-twist for C/M with PPidx 0 ∈ ℘
            source_ls = parent_ls
            e_wp = 1 if (child_wp is not None and 0 in child_wp) else 0
            if child_rt in ('C', 'M') and e_wp != 0:
                source_ls = twist_ls(parent_ls, (-1, -1))

            # Theta lift
            target_ls = theta_lift_ls(source_ls, child_rt, tau_p, tau_q)

            # Post-twist for B/D
            if child_rt in ('B+', 'B-', 'D'):
                tau_eps = epsilon(child_drc, child_rt)
                if tau_eps != 0:
                    target_ls = twist_ls(target_ls, (1, -1))

            child_node['ls'] = target_ls
            queue.append(child_key)

    # --- Step 4: Collect all LS values and group ext PBPs by LS ---
    # Group by (ls_value, total_boxes) — NO rtype, so B+/B- can merge
    ls_groups = {}  # (ls, total) → list of (drc, wp, rt) keys
    for key, node in tree_nodes.items():
        drc, wp_fs, rt = key
        ls = node['ls']
        if ls is None:
            continue
        drcL, drcR = drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        group_key = (ls, total)
        ls_groups.setdefault(group_key, []).append(key)

    # Character twist definitions for B/D levels
    twist_defs = [
        ((-1, -1), 'red',     'det'),
        ((1, -1),  'green',   '1⁺⁻'),
        ((-1, 1),  '#9933cc', '1⁻⁺'),
    ]

    # Build ghost LS nodes: twist variants of B/D LS that are not realized
    ghost_ls = {}  # ghost_gk → source_gk
    for gk, members in list(ls_groups.items()):
        ls_val, total = gk
        has_bd = any(k[2] in ('B+', 'B-', 'D') for k in members)
        if not has_bd:
            continue
        for twist, color, label in twist_defs:
            twisted = twist_ls(ls_val, twist)
            twisted_gk = (twisted, total)
            if twisted_gk != gk and twisted_gk not in ls_groups:
                if twisted_gk not in ghost_ls:
                    ghost_ls[twisted_gk] = gk

    # --- Step 5: Build Graphviz graph ---
    g = Digraph(name='Lifting Tree',
                filename=filename,
                node_attr={'shape': 'box', 'fontname': 'Courier New',
                           'fontsize': '8'},
                graph_attr={'rankdir': 'TB', 'newrank': 'true',
                            'ranksep': '1.2', 'nodesep': '0.4',
                            'dpi': '150'},
                engine='dot', format=format)

    node_counter = [0]
    gv_node_map = {}  # group_key → graphviz node id
    levels = {}       # (rt_norm, total) → [nids]

    def make_nid():
        nid = f'n{node_counter[0]}'
        node_counter[0] += 1
        return nid

    def _wp_red_cols(wp_fs, rt):
        """Compute which columns of drcL and drcR to color red for ℘."""
        red_L = set()
        red_R = set()
        if not wp_fs:
            return red_L, red_R
        for idx in wp_fs:
            # idx is a PPidx integer
            if rt in ('C', 'M'):
                # PPidx i → column i of both L and R (0-based)
                red_L.add(idx)
                red_R.add(idx)
            elif rt == 'D':
                # PPidx i → col i+1 of L, col i of R (0-based)
                red_L.add(idx + 1)
                red_R.add(idx)
            elif rt in ('B', 'B+', 'B-'):
                # PPidx i → col i of L, col i+1 of R (0-based)
                red_L.add(idx)
                red_R.add(idx + 1)
        return red_L, red_R

    def _drc_html_colored(drc, wp_fs, rt):
        """Format DRC with red-colored columns for ℘ (HTML for Graphviz)."""
        drcL, drcR = drc
        red_L, red_R = _wp_red_cols(wp_fs, rt)

        def _col_str(columns, red_set):
            rows = 0
            for c in columns:
                rows = max(rows, len(c))
            if rows == 0:
                return ''
            lines = []
            for r in range(rows):
                parts = []
                for ci, c in enumerate(columns):
                    ch = c[r] if r < len(c) else ' '
                    if ci in red_set:
                        parts.append(f'<font color="red">{ch}</font>')
                    else:
                        parts.append(ch)
                lines.append(''.join(parts))
            return '<br align="left"/>'.join(lines)

        left = _col_str(drcL, red_L)
        right = _col_str(drcR, red_R)
        # Always show the vertical bar separator
        lrows = left.split('<br align="left"/>') if left else []
        rrows = right.split('<br align="left"/>') if right else []
        maxr = max(len(lrows), len(rrows), 1)
        lines = []
        for i in range(maxr):
            l = lrows[i] if i < len(lrows) else ' '
            r = rrows[i] if i < len(rrows) else ' '
            lines.append(f'{l}|{r}')
        return '<br align="left"/>'.join(lines)

    def format_ext_pbp_html(drc, wp_fs, rt):
        """Format one extended PBP as HTML for Graphviz."""
        drc_html = _drc_html_colored(drc, wp_fs, rt)
        # B+/B- label
        rt_str = f' {rt}' if rt in ('B+', 'B-') else ''
        # Unified ε
        if rt in ('B+', 'B-', 'D'):
            eps = epsilon(drc, rt)
        elif rt in ('C', 'M'):
            eps = 1 if (wp_fs is not None and 0 in wp_fs) else 0
        else:
            eps = 0
        return f'{drc_html}{rt_str} ε={eps}'

    # Create nodes for real LS groups
    for gk, members in ls_groups.items():
        ls_val, total = gk
        nid = make_nid()
        gv_node_map[gk] = nid

        # LS visual: respect FrozenMultiset multiplicities
        ac_pairs = [(ls_val[ils], ils) for ils in ls_val.distinct_elements()]
        ac_lines = _format_myd_multiline(ac_pairs)
        ac_str = '<br align="left"/>'.join(ac_lines)

        # List all ext PBPs with their individual signatures
        pbp_parts = []
        for mk in members:
            drc_m, wp_m, rt_m = mk
            sig_m = signature(drc_m, rt_m)
            sig_line = f'({sig_m[0]},{sig_m[1]})'
            pbp_html = format_ext_pbp_html(*mk)
            pbp_parts.append(f'{sig_line}<br align="left"/>{pbp_html}')
        pbp_str = '<br align="left"/>'.join(pbp_parts)

        label = (f'<{ac_str}<br align="left"/>'
                 f'═════<br align="left"/>'
                 f'{pbp_str}<br align="left"/>>')

        # Color based on what types appear in this node
        rts_in_node = set(k[2] for k in members)
        if rts_in_node <= {'C'}:
            fillcolor = '#e6f3ff'
        elif rts_in_node <= {'M'}:
            fillcolor = '#e6ffe6'
        elif rts_in_node <= {'D'}:
            fillcolor = '#fff3e6'
        elif rts_in_node <= {'B+', 'B-'}:
            fillcolor = '#ffe6e6'
        else:
            fillcolor = '#f5f5f5'  # mixed types

        g.node(nid, label=label, style='filled',
               fillcolor=fillcolor)

        rt_norm = 'B' if rts_in_node <= {'B+', 'B-'} else next(iter(rts_in_node))
        levels.setdefault((rt_norm, total), []).append(nid)

    # Create ghost nodes for twisted LS not realized by any ext PBP
    for gk, source_gk in ghost_ls.items():
        ls_val, total = gk
        nid = make_nid()
        gv_node_map[gk] = nid

        ac_pairs = [(ls_val[ils], ils) for ils in ls_val.distinct_elements()]
        ac_lines = _format_myd_multiline(ac_pairs)
        ac_str = '<br align="left"/>'.join(ac_lines)
        label = f'<{ac_str}<br align="left"/>>'

        g.node(nid, label=label, style='filled',
               fillcolor='#f8f8f8')

        # Same level as source
        rt_norm = None
        for mk in ls_groups.get(source_gk, []):
            r = mk[2]
            rt_norm = 'B' if r in ('B+', 'B-') else r
            break
        if rt_norm is None:
            rt_norm = 'B' if rtype in ('M', 'B') else 'D'
        levels.setdefault((rt_norm, total), []).append(nid)

    # --- Step 6: Lift edges (blue, solid) ---
    # Blue edge = source → theta_lift_ls(source, ★, p, q).
    # B/D ε_τ=0: parent_LS → child_LS (= theta_lift result)
    # B/D ε_τ≠0: parent_LS → θ(parent_LS) (undo post-twist, may be ghost)
    # C/M ε_℘=0: parent_LS → child_LS
    # C/M ε_℘=1: ghost(det·parent_LS) → child_LS
    lift_edges = set()
    for key, node in tree_nodes.items():
        if node['parent'] is None:
            continue
        child_drc, child_wp, child_rt = key
        parent_key = node['parent']

        child_ls = node['ls']
        parent_ls = tree_nodes[parent_key]['ls']
        drcL, drcR = child_drc
        child_total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        pdrc = parent_key[0]
        parent_total = sum(len(c) for c in pdrc[0]) + sum(len(c) for c in pdrc[1])

        if child_rt in ('B+', 'B-', 'D'):
            src_gk = (parent_ls, parent_total)
            if epsilon(child_drc, child_rt) != 0:
                # ε_τ≠0: target is theta_lift result (undo post-twist)
                dst_gk = (twist_ls(child_ls, (1, -1)), child_total)
            else:
                dst_gk = (child_ls, child_total)
        elif child_rt in ('C', 'M'):
            e_wp = 1 if (child_wp is not None and 0 in child_wp) else 0
            if e_wp == 1:
                src_gk = (twist_ls(parent_ls, (-1, -1)), parent_total)
            else:
                src_gk = (parent_ls, parent_total)
            dst_gk = (child_ls, child_total)
        else:
            src_gk = (parent_ls, parent_total)
            dst_gk = (child_ls, child_total)

        src_nid = gv_node_map.get(src_gk)
        dst_nid = gv_node_map.get(dst_gk)
        if src_nid and dst_nid and src_nid != dst_nid:
            edge_key = (src_nid, dst_nid)
            if edge_key not in lift_edges:
                lift_edges.add(edge_key)
                g.edge(src_nid, dst_nid, color='blue', headport='n')

    # --- Step 7: Character twist edges (B/D, same level, solid) ---
    # Draw between all LS nodes (real and ghost) at B/D levels
    twist_edges = set()
    all_ls_keys = set(ls_groups.keys()) | set(ghost_ls.keys())
    for gk in all_ls_keys:
        ls_val, total = gk
        # Check if this is a B/D level node
        has_bd = any(k[2] in ('B+', 'B-', 'D') for k in ls_groups.get(gk, []))
        if not has_bd and gk not in ghost_ls:
            continue
        if gk not in gv_node_map:
            continue
        nid_a = gv_node_map[gk]
        for twist, color, label in twist_defs:
            twisted = twist_ls(ls_val, twist)
            target_gk = (twisted, total)
            if target_gk == gk or target_gk not in gv_node_map:
                continue
            nid_b = gv_node_map[target_gk]
            edge = tuple(sorted([nid_a, nid_b]))
            ek = (edge, color)
            if ek not in twist_edges:
                twist_edges.add(ek)
                g.edge(nid_a, nid_b, color=color,
                       dir='both', arrowsize='0.3', constraint='false')

    # --- Step 8: Layout ---
    # Build twist orbits: group LS nodes connected by character twists
    # so they are placed adjacently in the graph.
    all_gk_set = set(ls_groups.keys()) | set(ghost_ls.keys())
    gk_to_orbit = {}  # gk → orbit_id
    orbits = []       # orbit_id → set of gks
    for gk in all_gk_set:
        if gk in gk_to_orbit:
            continue
        # BFS to find all gks in this twist orbit
        orbit = set()
        bfs = [gk]
        while bfs:
            cur = bfs.pop()
            if cur in orbit:
                continue
            if cur not in all_gk_set:
                continue
            orbit.add(cur)
            ls_val, total = cur
            for twist, _, _ in twist_defs:
                tw = twist_ls(ls_val, twist)
                nbr = (tw, total)
                if nbr in all_gk_set and nbr not in orbit:
                    bfs.append(nbr)
        oid = len(orbits)
        orbits.append(orbit)
        for member in orbit:
            gk_to_orbit[member] = oid

    gp_nodes = []
    cluster_counter = [0]
    # Sort: by total, then C/M before B/D (parent above child)
    def _level_key(item):
        rt, total = item[0]
        rt_order = 0 if rt in ('C', 'M') else 1
        return (total, rt_order, rt)

    for (rt_norm, total), nids in sorted(levels.items(), key=_level_key):
        if rt_norm in ('C', 'M'):
            gp_label = RTYPE_GP[rt_norm] % (2 * total,)
        elif rt_norm == 'B':
            gp_label = f'O({2 * total + 1})'
        elif rt_norm == 'D':
            gp_label = f'SO({2 * total})'
        else:
            gp_label = rt_norm

        gp_nid = f'gp_{rt_norm}_{total}'
        g.node(gp_nid, label=gp_label, shape='plaintext',
               fontname='Helvetica', fontsize='11', fontcolor='#333333',
               group='gp_labels')
        rt_order = 0 if rt_norm in ('C', 'M') else 1
        gp_nodes.append((total, rt_order, gp_nid))

        # Group nids by twist orbit for clustering
        orbit_nids = {}  # orbit_id → [nids]
        for gk in all_gk_set:
            ls_val, t = gk
            if t != total:
                continue
            if gk not in gv_node_map:
                continue
            nid = gv_node_map[gk]
            if nid not in nids:
                continue
            oid = gk_to_orbit.get(gk)
            if oid is not None:
                orbit_nids.setdefault(oid, []).append(nid)

        # Nids not in any orbit (C/M levels with no twists)
        clustered_nids = set()
        for onids in orbit_nids.values():
            clustered_nids.update(onids)
        unclustered = [n for n in nids if n not in clustered_nids]

        # Create cluster subgraphs for multi-node orbits
        for oid, onids in orbit_nids.items():
            if len(onids) > 1:
                cname = f'cluster_tw_{cluster_counter[0]}'
                cluster_counter[0] += 1
                with g.subgraph(name=cname) as c:
                    c.attr(style='dotted', color='#999999', penwidth='0.8')
                    for nid in onids:
                        c.node(nid)
            else:
                unclustered.extend(onids)

        # Rank constraint: all nids at this level on the same rank
        # Add invisible edge from gp label to first LS node to pin label left
        with g.subgraph() as s:
            s.attr(rank='same')
            s.node(gp_nid)
            for nid in nids:
                s.node(nid)
        if nids:
            g.edge(gp_nid, nids[0], style='invis')

    gp_nodes_sorted = sorted(gp_nodes, key=lambda x: (x[0], x[1]))
    for i in range(len(gp_nodes_sorted) - 1):
        g.edge(gp_nodes_sorted[i][2], gp_nodes_sorted[i + 1][2],
               style='invis')

    # --- Also generate the extended PBP descent tree ---
    ext_filename = filename + '_ext'
    g_ext = _gen_ext_pbp_tree(tree_nodes, rtype, format=format,
                              filename=ext_filename)
    g_ext.render()

    # --- Also generate combined LS + DRC descent tree ---
    comb_filename = filename + '_comb'
    g_comb = _gen_combined_tree(tree_nodes, ls_groups, ghost_ls, rtype,
                                format=format, filename=comb_filename,
                                drc_html_fn=_drc_html_colored)
    g_comb.render()

    return g


def _gen_ext_pbp_tree(tree_nodes, rtype, format='svg', filename='ext_pbp_tree'):
    """
    Generate the extended PBP descent/lift tree.

    Each node = one extended PBP (drc, ℘, ★).
    Edges = descent (parent→child = lift direction, top-down).
    """
    from graphviz import Digraph

    g = Digraph(name='Extended PBP Tree',
                filename=filename,
                node_attr={'shape': 'box', 'fontname': 'Courier New',
                           'fontsize': '8'},
                graph_attr={'rankdir': 'TB', 'newrank': 'true',
                            'ranksep': '0.8', 'nodesep': '0.3',
                            'dpi': '150'},
                engine='dot', format=format)

    nid_map = {}  # key → nid
    levels = {}   # (rt_norm, total) → [nids]
    counter = [0]

    for key, node in tree_nodes.items():
        drc, wp_fs, rt = key
        drcL, drcR = drc
        total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)

        nid = f'e{counter[0]}'
        counter[0] += 1
        nid_map[key] = nid

        # Signature
        sig = signature(drc, rt)
        # ε
        if rt in ('B+', 'B-', 'D'):
            eps = epsilon(drc, rt)
        elif rt in ('C', 'M'):
            eps = 1 if (wp_fs is not None and 0 in wp_fs) else 0
        else:
            eps = 0
        # B+/B- label
        rt_str = f' {rt}' if rt in ('B+', 'B-') else ''
        # ℘ label
        wp_str = ''
        if wp_fs:
            wp_str = f' ℘={set(wp_fs)}'

        # DRC as text
        drc_str = str_dgms(drc).replace('\n', '\\l')
        label = f'({sig[0]},{sig[1]}){rt_str} ε={eps}{wp_str}\\l{drc_str}\\l'

        # Color by type
        colors = {'C': '#e6f3ff', 'D': '#fff3e6', 'M': '#e6ffe6',
                  'B+': '#ffe6e6', 'B-': '#ffe6f3'}
        fillcolor = colors.get(rt, '#f5f5f5')

        g.node(nid, label=label, style='filled', fillcolor=fillcolor,
               labeljust='l')

        rt_norm = 'B' if rt in ('B+', 'B-') else rt
        levels.setdefault((rt_norm, total), []).append(nid)

    # Edges: parent → child (lift direction, top-down in TB)
    for key, node in tree_nodes.items():
        if node['parent'] is None:
            continue
        parent_key = node['parent']
        if parent_key in nid_map and key in nid_map:
            g.edge(nid_map[parent_key], nid_map[key], color='blue')

    # Layout: group labels on left, rank constraints
    gp_nodes = []
    RTYPE_GP_local = {'C': 'Sp(%d)', 'M': 'Mp(%d)'}
    for (rt_norm, total), nids in sorted(levels.items(), key=lambda x: x[0][1]):
        if rt_norm in ('C', 'M'):
            gp_label = RTYPE_GP_local.get(rt_norm, rt_norm) % (2 * total,)
        elif rt_norm == 'B':
            gp_label = f'O({2 * total + 1})'
        elif rt_norm == 'D':
            gp_label = f'SO({2 * total})'
        else:
            gp_label = rt_norm

        gp_nid = f'gp_{rt_norm}_{total}'
        g.node(gp_nid, label=gp_label, shape='plaintext',
               fontname='Helvetica', fontsize='11', fontcolor='#333333',
               group='gp_labels')
        gp_nodes.append((total, gp_nid))

        with g.subgraph() as s:
            s.attr(rank='same')
            s.node(gp_nid)
            for nid in nids:
                s.node(nid)
        if nids:
            g.edge(gp_nid, nids[0], style='invis')

    gp_nodes_sorted = sorted(gp_nodes, key=lambda x: x[0])
    for i in range(len(gp_nodes_sorted) - 1):
        g.edge(gp_nodes_sorted[i][1], gp_nodes_sorted[i + 1][1],
               style='invis')

    return g


def _gen_combined_tree(tree_nodes, ls_groups, ghost_ls, rtype,
                      format='svg', filename='combined', drc_html_fn=None):
    """
    Generate combined LS + DRC descent tree with layered structure.

    C/M levels: LS box (with signature and MYD) on top, extended PBPs below.
    B/D levels: 1⁻⁺ twist on top (if different), LS + 1⁺⁻ in middle,
                extended PBPs below.
    DRC descent edges (gray dashed) connect individual ext PBP nodes.
    """
    from graphviz import Digraph

    g = Digraph(name='Combined Lift Tree',
                filename=filename,
                node_attr={'shape': 'box', 'fontname': 'Courier New',
                           'fontsize': '7'},
                graph_attr={'rankdir': 'TB', 'newrank': 'true',
                            'ranksep': '0.8', 'nodesep': '0.15',
                            'dpi': '150'},
                engine='dot', format=format)

    counter = [0]
    drc_nid_map = {}   # tree_node key -> nid
    ls_nid_map = {}    # gk -> LS header nid
    ghost_nid_map = {} # gk -> ghost nid
    levels = {}        # (level_type, total) -> [nids]

    def make_nid(prefix='n'):
        nid = f'{prefix}{counter[0]}'
        counter[0] += 1
        return nid

    # --- For each LS group, create: LS header + ext PBP nodes ---
    for gk, members in ls_groups.items():
        ls_val, total = gk
        rts_in = set(k[2] for k in members)
        is_bd = rts_in <= {'B+', 'B-'} or rts_in <= {'D'}

        # MYD label
        ac_pairs = [(ls_val[ils], ils) for ils in ls_val.distinct_elements()]
        ac_lines = _format_myd_multiline(ac_pairs)
        myd_str = '\\l'.join(ac_lines)

        # LS header node
        ls_nid = make_nid('ls')
        ls_nid_map[gk] = ls_nid

        colors_map = {'C': '#e6f3ff', 'D': '#fff3e6', 'M': '#e6ffe6'}
        if rts_in <= {'B+', 'B-'}:
            bgcolor = '#ffe6e6'
        else:
            bgcolor = colors_map.get(next(iter(rts_in)), '#f5f5f5')

        # Collect distinct signatures for this LS
        sigs = set()
        for mk in members:
            drc_m, _, rt_m = mk
            sigs.add(signature(drc_m, rt_m))
        sig_strs = ', '.join(f'({p},{q})' for p, q in sorted(sigs))

        g.node(ls_nid, label=f'{sig_strs}\\l{myd_str}\\l', style='filled',
               fillcolor=bgcolor, labeljust='l')

        # Determine level keys
        if is_bd:
            rt_base = 'B' if rts_in <= {'B+', 'B-'} else 'D'
            levels.setdefault((f'{rt_base}_mid', total), []).append(ls_nid)
        else:
            rt_base = next(iter(rts_in))
            levels.setdefault((rt_base, total), []).append(ls_nid)

        # Create ext PBP nodes
        for mk in members:
            drc, wp_fs, rt = mk
            nid = make_nid('d')
            drc_nid_map[mk] = nid

            sig = signature(drc, rt)
            if rt in ('B+', 'B-', 'D'):
                eps = epsilon(drc, rt)
            elif rt in ('C', 'M'):
                eps = 1 if (wp_fs is not None and 0 in wp_fs) else 0
            else:
                eps = 0

            rt_str = f'{rt} ' if rt in ('B+', 'B-') else ''
            # Use HTML label with red-colored columns for ℘
            drc_html = drc_html_fn(drc, wp_fs, rt) if drc_html_fn else str_dgms(drc).replace('\n', '<br align="left"/>')
            label = (f'<{rt_str}ε={eps}'
                     f'<br align="left"/>'
                     f'{drc_html}<br align="left"/>>')

            g.node(nid, label=label, style='filled',
                   fillcolor='white')

            # LS header -> ext PBP (solid line, force below)
            g.edge(ls_nid, nid, color='#aaaaaa', arrowsize='0.4',
                   weight='10')

            if is_bd:
                levels.setdefault((f'{rt_base}_bot', total), []).append(nid)
            else:
                levels.setdefault((f'{rt_base}_bot', total), []).append(nid)

    # --- Ghost nodes (1^{-,+} twists) on top level ---
    for gk, source_gk in ghost_ls.items():
        ls_val, total = gk
        if gk in ghost_nid_map:
            continue
        gnid = make_nid('g')
        ghost_nid_map[gk] = gnid

        ac_pairs = [(ls_val[ils], ils) for ils in ls_val.distinct_elements()]
        ac_lines = _format_myd_multiline(ac_pairs)
        glabel = '\\l'.join(ac_lines) + '\\l'
        g.node(gnid, label=glabel, style='filled',
               fillcolor='#f0f0f0', labeljust='l')

        # Determine source type
        rt_norm = None
        for mk in ls_groups.get(source_gk, []):
            r = mk[2]
            rt_norm = 'B' if r in ('B+', 'B-') else r
            break
        if rt_norm is None:
            rt_norm = 'B' if rtype in ('M', 'B') else 'D'
        levels.setdefault((f'{rt_norm}_mid', total), []).append(gnid)

    # --- Build twist orbits and wrap in dashed clusters ---
    twist_defs = [
        ((-1, -1), 'red'),
        ((1, -1),  'green'),
        ((-1, 1),  '#9933cc'),
    ]
    all_nid_map = {}
    all_nid_map.update({gk: ls_nid_map[gk] for gk in ls_nid_map})
    all_nid_map.update({gk: ghost_nid_map[gk] for gk in ghost_nid_map})

    # Collect all ext PBP nids for each gk
    gk_ext_nids = {}  # gk → [ext PBP nids]
    for gk, members in ls_groups.items():
        gk_ext_nids[gk] = [drc_nid_map[mk] for mk in members
                           if mk in drc_nid_map]

    # Build orbits
    all_gk_set = set(ls_nid_map.keys()) | set(ghost_nid_map.keys())
    visited = set()
    orbit_counter = [0]
    for gk in all_gk_set:
        if gk in visited:
            continue
        orbit = set()
        bfs = [gk]
        while bfs:
            cur = bfs.pop()
            if cur in orbit or cur not in all_gk_set:
                continue
            orbit.add(cur)
            ls_val, total = cur
            for twist, _ in twist_defs:
                tw = twist_ls(ls_val, twist)
                nbr = (tw, total)
                if nbr in all_gk_set and nbr not in orbit:
                    bfs.append(nbr)
        visited.update(orbit)

        if len(orbit) > 1:
            # Wrap all nids of this orbit in a dashed cluster
            cname = f'cluster_tw_{orbit_counter[0]}'
            orbit_counter[0] += 1
            with g.subgraph(name=cname) as c:
                c.attr(style='dashed', color='#bbbbbb',
                       penwidth='0.8', label='')
                for ogk in orbit:
                    if ogk in all_nid_map:
                        c.node(all_nid_map[ogk])
                    for enid in gk_ext_nids.get(ogk, []):
                        c.node(enid)

    # --- Twist edges ---
    twist_edges = set()
    for gk in all_nid_map:
        ls_val, total = gk
        is_bd = False
        if gk in ls_groups:
            rts = set(k[2] for k in ls_groups[gk])
            is_bd = rts <= {'B+', 'B-'} or rts <= {'D'}
        elif gk in ghost_ls:
            is_bd = True
        if not is_bd:
            continue

        nid_a = all_nid_map[gk]
        for twist, color in twist_defs:
            twisted = twist_ls(ls_val, twist)
            target_gk = (twisted, total)
            if target_gk == gk or target_gk not in all_nid_map:
                continue
            nid_b = all_nid_map[target_gk]
            edge = tuple(sorted([nid_a, nid_b]))
            ek = (edge, color)
            if ek not in twist_edges:
                twist_edges.add(ek)
                g.edge(nid_a, nid_b, color=color,
                       dir='both', arrowsize='0.3', constraint='false')

    # --- DRC descent edges (gray dashed) ---
    for key, node in tree_nodes.items():
        if node['parent'] is None:
            continue
        parent_key = node['parent']
        if key in drc_nid_map and parent_key in drc_nid_map:
            g.edge(drc_nid_map[parent_key], drc_nid_map[key],
                   color='#888888', style='dashed', arrowsize='0.5')

    # --- LS theta lift edges (blue) ---
    # Same logic as original lift graph (Step 6).
    combined_nid = {}
    combined_nid.update(ls_nid_map)
    combined_nid.update(ghost_nid_map)

    lift_edges = set()
    for key, node in tree_nodes.items():
        if node['parent'] is None:
            continue
        child_drc, child_wp, child_rt = key
        parent_key = node['parent']

        child_ls = node['ls']
        parent_ls = tree_nodes[parent_key]['ls']
        drcL, drcR = child_drc
        child_total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
        pdrc = parent_key[0]
        parent_total = sum(len(c) for c in pdrc[0]) + sum(len(c) for c in pdrc[1])

        if child_rt in ('B+', 'B-', 'D'):
            src_gk = (parent_ls, parent_total)
            if epsilon(child_drc, child_rt) != 0:
                dst_gk = (twist_ls(child_ls, (1, -1)), child_total)
            else:
                dst_gk = (child_ls, child_total)
        elif child_rt in ('C', 'M'):
            e_wp = 1 if (child_wp is not None and 0 in child_wp) else 0
            if e_wp == 1:
                src_gk = (twist_ls(parent_ls, (-1, -1)), parent_total)
            else:
                src_gk = (parent_ls, parent_total)
            dst_gk = (child_ls, child_total)
        else:
            src_gk = (parent_ls, parent_total)
            dst_gk = (child_ls, child_total)

        src_nid = combined_nid.get(src_gk)
        dst_nid = combined_nid.get(dst_gk)
        if src_nid and dst_nid and src_nid != dst_nid:
            edge_key = (src_nid, dst_nid)
            if edge_key not in lift_edges:
                lift_edges.add(edge_key)
                g.edge(src_nid, dst_nid, color='blue')

    # --- Layout ---
    def level_sort_key(item):
        rt, total = item[0]
        order = {'C': 0, 'M': 0,
                 'D_mid': 1, 'B_mid': 1,
                 'D_bot': 2, 'B_bot': 2,
                 'C_bot': 3, 'M_bot': 3}
        return (total, order.get(rt, 5), rt)

    gp_nodes = []
    for (rt, total), nids in sorted(levels.items(), key=level_sort_key):
        if rt in ('C', 'M'):
            gp_label = RTYPE_GP[rt] % (2 * total,)
        elif rt == 'B_mid':
            gp_label = f'O({2 * total + 1})'
        elif rt == 'D_mid':
            gp_label = f'SO({2 * total})'
        else:
            gp_label = ''

        gp_nid = f'gp_{rt}_{total}'
        if gp_label:
            g.node(gp_nid, label=gp_label, shape='plaintext',
                   fontname='Helvetica', fontsize='10', fontcolor='#333333',
                   group='gp_labels')
        else:
            g.node(gp_nid, label='', shape='none', width='0', height='0',
                   group='gp_labels')
        gp_nodes.append(gp_nid)

        with g.subgraph() as s:
            s.attr(rank='same')
            s.node(gp_nid)
            for nid in nids:
                s.node(nid)
        if nids:
            g.edge(gp_nid, nids[0], style='invis')

    for i in range(len(gp_nodes) - 1):
        g.edge(gp_nodes[i], gp_nodes[i + 1], style='invis')

    return g



def gen_descent_tree(dpart, rtype, format='pdf', filename='descent_tree'):
    """
    Generate a Graphviz directed graph showing the theta lifting tree.

    Each node = one LS (local system). Multiple DRCs mapping to the same LS
    are grouped into the same node.

    Edges:
      - Blue arrows (up → down): theta lift direction
      - Red/green/purple dashed: det / 1⁺⁻ / 1⁻⁺ character twists (B/D)

    Layout: small groups at top, large groups at bottom (BT).
    """
    from graphviz import Digraph

    drcs = dpart2drc(dpart, rtype)

    g = Digraph(name='Lifting Graph',
                filename=filename,
                node_attr={'shape': 'box', 'fontname': 'Courier New',
                           'fontsize': '8'},
                graph_attr={'rankdir': 'BT', 'newrank': 'true',
                            'ranksep': '1.2', 'nodesep': '0.4',
                            'dpi': '150'},
                engine='dot', format=format)

    levels = {}          # (rt_normalized, size) → [nids]
    ls_node_map = {}     # (ls_key, rt) → nid
    drc_to_ls_nid = {}   # (drc, rt) → nid  (which LS node a DRC belongs to)
    node_counter = [0]
    ac_cache = {}
    lift_edges = set()
    twist_edges = set()

    def get_ac(drc, rt):
        key = (drc, rt)
        if key not in ac_cache:
            ac_cache[key] = compute_AC(drc, None, rt)
        return ac_cache[key]

    def ac_key(ac):
        """Hashable key for an AC result (list of (coeff, ILS))."""
        return tuple(sorted(ac))

    def get_ls_node(drc, rt, is_ghost=False, ghost_ac=None):
        """Get or create the LS node for this DRC's AC result."""
        ac = ghost_ac if ghost_ac is not None else get_ac(drc, rt)
        lsk = (ac_key(ac), rt)

        if lsk not in ls_node_map:
            nid = f'n{node_counter[0]}'
            node_counter[0] += 1
            ls_node_map[lsk] = nid

            drcL, drcR = drc
            total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
            sig = _ils_sign(ac[0][1]) if ac else (0, 0)

            # LS visual
            ac_lines = _format_myd_multiline(ac)
            sep = '\\l'
            ac_str = sep.join(ac_lines)

            sig_str = f'{rt} ({sig[0]},{sig[1]})'
            label = f'{sig_str}\\l─────\\l{ac_str}\\l'

            if not is_ghost:
                colors = {'C': '#e6f3ff', 'D': '#fff3e6',
                          'M': '#e6ffe6', 'B+': '#ffe6e6', 'B-': '#ffe6f3'}
                style = 'filled'
            else:
                colors = {'B+': '#fff0f0', 'B-': '#fff0f5', 'D': '#fff8ee'}
                style = 'filled,dashed'
            fillcolor = colors.get(rt, '#ffffff')

            g.node(nid, label=label, style=style, fillcolor=fillcolor,
                   labeljust='l')

            rt_norm = 'B' if rt in ('B+', 'B-') else rt
            levels.setdefault((rt_norm, total), []).append(nid)

        return ls_node_map[lsk]

    # Build ℘ map
    wp_map = {}
    try:
        bij, _ = build_pbp_bijection(dpart, rtype)
        for drc_bij, (sp_drc, wp) in bij.items():
            wp_map[drc_bij] = wp
    except Exception:
        pass

    # Phase 1: build all LS nodes and map DRCs to them
    chain_rtypes = ['B+', 'B-'] if rtype == 'B' else [rtype]
    all_chains = []
    for drc in drcs:
        for crt in chain_rtypes:
            ch = descent_chain(drc, crt, dpart)
            all_chains.append(ch)
            for step_drc, step_rt, _, _, _ in ch:
                nid = get_ls_node(step_drc, step_rt)
                drc_to_ls_nid[(step_drc, step_rt)] = nid

    # Phase 2: add DRC info to LS nodes (list DRCs that share the same LS)
    ls_drcs = {}  # nid → list of (drc_str, wp_str, sig)
    for (drc, rt), nid in drc_to_ls_nid.items():
        drc_str = str_dgms(drc).replace('\n', '\\l')
        wp_str = ''
        if drc in wp_map:
            wp = wp_map[drc]
            wp_str = f'℘={set(wp)}' if wp else '℘=∅'
        sig = signature(drc, rt)
        ls_drcs.setdefault(nid, []).append((drc_str, wp_str, sig, rt))

    # Re-create nodes with DRC listings
    for lsk, nid in ls_node_map.items():
        if nid not in ls_drcs:
            continue
        drc_entries = ls_drcs[nid]
        ac = [k for k, v in ac_cache.items() if drc_to_ls_nid.get(k) == nid]
        if ac:
            ac_result = ac_cache[ac[0]]
        else:
            ac_result = []

        rt = drc_entries[0][3]
        sig = _ils_sign(ac_result[0][1]) if ac_result else (0, 0)
        ac_lines = _format_myd_multiline(ac_result)
        sep = '\\l'
        ac_str = sep.join(ac_lines)

        # List DRCs (compact)
        drc_lines = []
        for drc_str, wp_str, dsig, drt in drc_entries:
            drc_lines.append(f'{drc_str} {wp_str}')
        drcs_str = sep.join(drc_lines)

        sig_str = f'{rt} ({sig[0]},{sig[1]})'
        label = f'{sig_str}\\l─────\\l{ac_str}\\l═════\\l{drcs_str}\\l'

        colors = {'C': '#e6f3ff', 'D': '#fff3e6',
                  'M': '#e6ffe6', 'B+': '#ffe6e6', 'B-': '#ffe6f3'}
        g.node(nid, label=label, style='filled', fillcolor=colors.get(rt, '#ffffff'),
               labeljust='l')

    # Phase 3: lift edges (small → large, arrow points down)
    for ch in all_chains:
        for i in range(len(ch) - 1):
            src_drc, src_rt, _, _, _ = ch[i]      # larger
            dst_drc, dst_rt, _, _, _ = ch[i + 1]  # smaller
            src_nid = drc_to_ls_nid[(src_drc, src_rt)]
            dst_nid = drc_to_ls_nid[(dst_drc, dst_rt)]
            edge_key = (dst_nid, src_nid)
            if dst_nid != src_nid and edge_key not in lift_edges:
                lift_edges.add(edge_key)
                g.edge(dst_nid, src_nid, color='blue', headport='s')

    # Phase 4: character twist edges for B/D
    twist_defs = [
        ((-1, -1), 'red',     'det'),
        ((1, -1),  'green',   '1⁺⁻'),
        ((-1, 1),  '#9933cc', '1⁻⁺'),
    ]
    for lsk, nid in list(ls_node_map.items()):
        ac_sorted, rt = lsk
        if rt not in ('B+', 'B-', 'D'):
            continue
        ac_list = list(ac_sorted)

        # Find total for ghost node level
        total = 0
        for (d, r), n in drc_to_ls_nid.items():
            if n == nid:
                drcL, drcR = d
                total = sum(len(c) for c in drcL) + sum(len(c) for c in drcR)
                break

        for twist, color, twist_label in twist_defs:
            twisted = tuple(sorted((c, _ils_twist_BD(ils, twist)) for c, ils in ac_list))
            if twisted == ac_sorted:
                continue  # self-twist, skip
            twisted_lsk = (twisted, rt)
            if twisted_lsk in ls_node_map:
                # Connect to existing LS node
                target_nid = ls_node_map[twisted_lsk]
                edge = tuple(sorted([nid, target_nid]))
                ek = (edge, color)
                if ek not in twist_edges:
                    twist_edges.add(ek)
                    g.edge(nid, target_nid, color=color, style='dashed',
                           dir='both', arrowsize='0.3', constraint='false')
            else:
                # Ghost node (no DRC)
                if twisted_lsk not in ls_node_map:
                    gnid = f'g{node_counter[0]}'
                    node_counter[0] += 1
                    ls_node_map[twisted_lsk] = gnid

                    sig_tw = _ils_sign(twisted[0][1]) if twisted else (0, 0)
                    ac_lines = _format_myd_multiline(list(twisted))
                    sep = '\\l'
                    ac_str = sep.join(ac_lines)
                    label = f'{rt} ({sig_tw[0]},{sig_tw[1]})\\l─────\\l{ac_str}\\l'
                    cm = {'B+': '#fff0f0', 'B-': '#fff0f5', 'D': '#fff8ee'}
                    g.node(gnid, label=label, style='filled,dashed',
                           fillcolor=cm.get(rt, '#fafafa'), labeljust='l')
                    rt_norm = 'B' if rt in ('B+', 'B-') else rt
                    levels.setdefault((rt_norm, total), []).append(gnid)

                target_nid = ls_node_map[twisted_lsk]
                edge = tuple(sorted([nid, target_nid]))
                ek = (edge, color)
                if ek not in twist_edges:
                    twist_edges.add(ek)
                    g.edge(nid, target_nid, color=color, style='dashed',
                           dir='both', arrowsize='0.3', constraint='false')

    # Phase 5: group labels and rank constraints
    gp_nodes = []
    for (rt, size), nids in sorted(levels.items(), key=lambda x: -x[0][1]):
        if rt in ('C', 'M'):
            gp_label = RTYPE_GP[rt] % (2 * size,)
        elif rt == 'B':
            gp_label = f'O({2 * size + 1})'
        elif rt == 'D':
            gp_label = f'SO({2 * size})'
        else:
            gp_label = rt

        gp_nid = f'gp_{rt}_{size}'
        g.node(gp_nid, label=gp_label, shape='plaintext',
               fontname='Helvetica', fontsize='11', fontcolor='#333333')
        gp_nodes.append((size, gp_nid))

        with g.subgraph() as s:
            s.attr(rank='same')
            s.node(gp_nid)
            for nid in nids:
                s.node(nid)

    gp_nodes_sorted = sorted(gp_nodes, key=lambda x: x[0])
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

    For B type, generates both B+ and B- entries for each DRC.
    Returns a list of (drc, effective_rtype, (p, q), epsilon) tuples.
    """
    drcs = dpart2drc(dpart, rtype)
    results = []
    rtypes_to_use = ['B+', 'B-'] if rtype == 'B' else [rtype]
    for drc in drcs:
        for rt in rtypes_to_use:
            sig = signature(drc, rt)
            eps = epsilon(drc, rt)
            results.append((drc, rt, sig, eps))
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
    tauL, tauR = dpart_to_bipartition(parts, rtype)
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

    # Always generate lift tree (default behavior)
    fname = args.output or f'{rtype}{",".join(str(x) for x in parts)}'
    print(f"\nGenerating lift tree...")
    g = gen_lift_tree(parts, rtype, format=args.format, filename=fname)
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
