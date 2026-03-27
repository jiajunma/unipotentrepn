#!/usr/bin/env python3
"""
Compare LS (local system) values between standalone.py and lsdrcgraph.py.

For each dual partition up to a given size, verify that:
  standalone.compute_AC(drc, None, rtype) == drclift.test_purelyeven LS

The two systems use different representations:
  - drclift: DRCs may use ('',) for empty columns; LS is frozenset of ILS tuples
  - standalone: DRCs use () for empty columns; LS is list of (coeff, ILS)

This test normalizes both representations and compares.
"""
import sys
import time

# Add parent directory to path
sys.path.insert(0, '.')

from standalone import (
    dpart2drc, compute_AC, reg_drc, signature, epsilon,
    reg_part, part_size, build_pbp_bijection, compute_PPidx,
)
from multiset import FrozenMultiset


def normalize_drc(drc):
    """Normalize DRC to standalone format: strip empty strings."""
    drcL, drcR = drc
    drcL = tuple(c for c in drcL if c and c != '')
    drcR = tuple(c for c in drcR if c and c != '')
    return reg_drc((drcL, drcR))


def normalize_ils(ils):
    """Strip trailing (0,0) entries from an ILS tuple."""
    lst = list(ils)
    while lst and lst[-1] == (0, 0):
        lst.pop()
    return tuple(lst)


def normalize_ls(ls_frozenset):
    """Normalize a frozenset of ILS tuples by stripping trailing (0,0)."""
    return frozenset(normalize_ils(ils) for ils in ls_frozenset)


def ac_to_frozenset(ac_list):
    """Convert compute_AC result [(coeff, ILS)] to frozenset of ILS tuples."""
    result = []
    for coeff, ils in ac_list:
        for _ in range(coeff):
            result.append(normalize_ils(ils))
    return frozenset(result)


def dpart_to_spart(dpart, rtype):
    """Convert dual partition (orbit side) to special partition (group side)."""
    from combunipotent.tool import dualBVW
    bv_rtype = 'B' if rtype in ('B+', 'B-') else rtype
    return tuple(sorted(dualBVW(dpart, bv_rtype, partrc='r'), reverse=True))


def get_reference_drc_ls(dpart, rtype):
    """
    Get DRC → LS mapping from drclift.test_dpart2drcLS.

    Works for all types (B, C, D, M) using dual partition convention.
    Returns dict: (normalized_drc, effective_rtype) → frozenset_of_ILS
    """
    from combunipotent.drclift import test_dpart2drcLS, split_extdrc_B
    import io
    import contextlib

    with contextlib.redirect_stdout(io.StringIO()):
        lDRCLS, lLSDRC = test_dpart2drcLS(dpart, rtype, test=False)

    DRCLS = lDRCLS[0]

    result = {}
    for drc, ls in DRCLS.items():
        if rtype == 'B':
            base_drc, btype = split_extdrc_B(drc)
            ndrc = normalize_drc(base_drc)
            result[(ndrc, btype)] = ls
        else:
            ndrc = normalize_drc(drc)
            result[(ndrc, rtype)] = ls

    return result


def get_standalone_ls_for_drc(drc, rtype):
    """
    Compute LS for a single DRC via standalone.compute_AC.

    Returns frozenset of ILS tuples.
    """
    ndrc = normalize_drc(drc)
    ac = compute_AC(ndrc, None, rtype)
    return ac_to_frozenset(ac)


def get_standalone_ls_via_bijection(dpart, rtype):
    """
    Compute LS for ALL DRCs (all ℘) via build_pbp_bijection + compute_AC.

    Uses build_pbp_bijection to map each non-special DRC back to
    (special_drc, ℘), then calls compute_AC(special_drc, ℘, rtype).

    Returns dict: (normalized_drc, effective_rtype) → frozenset_of_ILS
    """
    try:
        bijection, table = build_pbp_bijection(dpart, rtype)
    except Exception:
        return {}

    rtypes = ['B+', 'B-'] if rtype == 'B' else [rtype]
    result = {}
    cache = {}

    for drc, (sp_drc, wp) in bijection.items():
        ndrc = normalize_drc(drc)
        nsp = normalize_drc(sp_drc)
        wp_fs = frozenset(wp) if wp else None

        for rt in rtypes:
            ac = compute_AC(nsp, wp_fs, rt, cache=cache)
            ls = ac_to_frozenset(ac)
            result[(ndrc, rt)] = ls

    return result


def dparts_for_type(rtype, max_size):
    """Generate all valid dual partitions for the given type up to max_size.

    Dual partition parity rules:
      C: all parts odd, total ODD  (Sp(2n), orbit size = 2n+1)
      D: all parts odd, total EVEN (SO(2n), orbit size = 2n)
      B: all parts even, total even (SO(2n+1))
      M: all parts even, total even (Mp(2n))
    """
    if rtype == 'C':
        # All parts odd, total odd
        for n in range(1, max_size + 1, 2):
            for p in _odd_partitions(n):
                yield p
    elif rtype == 'D':
        # All parts odd, total even
        for n in range(2, max_size + 1, 2):
            for p in _odd_partitions(n):
                yield p
    elif rtype in ('B', 'M'):
        # All parts even, total even
        for n in range(2, max_size + 1, 2):
            for p in _even_partitions(n):
                yield p


def _odd_partitions(n, max_part=None):
    """Generate all partitions of n with all parts odd."""
    if n == 0:
        yield ()
        return
    if max_part is None:
        max_part = n if n % 2 == 1 else n - 1
    for p in range(max_part, 0, -2):
        if p > n:
            continue
        for rest in _odd_partitions(n - p, p):
            yield (p,) + rest


def _even_partitions(n, max_part=None):
    """Generate all partitions of n with all parts even."""
    if n == 0:
        yield ()
        return
    if max_part is None:
        max_part = n
    for p in range(max_part, 0, -2):
        if p > n:
            continue
        for rest in _even_partitions(n - p, p):
            yield (p,) + rest


def verify_partition(dpart, rtype, verbose=False):
    """
    Verify LS values match between standalone and drclift for one partition.

    For D/B: per-DRC comparison using build_pbp_bijection.
    For C/M: compare the multiset of all LS values (DRC sets differ
             between dpart2drc and part2drc conventions).

    Returns (n_checked, n_passed, n_failed, failures).
    """
    try:
        ref = get_reference_drc_ls(dpart, rtype)
    except Exception as e:
        if verbose:
            print(f'  SKIP {rtype}{dpart}: reference error: {e}')
        return 0, 0, 0, []

    if not ref:
        return 0, 0, 0, []

    # Compute LS for all DRCs (all ℘) via bijection + compute_AC
    try:
        ours = get_standalone_ls_via_bijection(dpart, rtype)
    except Exception as e:
        if verbose:
            print(f'  SKIP {rtype}{dpart}: standalone error: {e}')
        return 0, 0, 0, []

    n_checked = 0
    n_passed = 0
    n_failed = 0
    failures = []

    for (ndrc, rt), ref_ls in ref.items():
        n_checked += 1
        if (ndrc, rt) not in ours:
            n_failed += 1
            failures.append((ndrc, rt, 'MISSING', normalize_ls(ref_ls), None))
            continue
        our_ls = ours[(ndrc, rt)]
        ref_ls_norm = normalize_ls(ref_ls)
        our_ls_norm = normalize_ls(our_ls)
        if ref_ls_norm == our_ls_norm:
            n_passed += 1
        else:
            n_failed += 1
            failures.append((ndrc, rt, 'MISMATCH', ref_ls_norm, our_ls_norm))

    return n_checked, n_passed, n_failed, failures


def main():
    max_size = 20
    if len(sys.argv) > 1:
        max_size = int(sys.argv[1])

    print(f'Comparing standalone vs drclift LS values for partitions up to size {max_size}')
    print()

    total_checked = 0
    total_passed = 0
    total_failed = 0
    all_failures = []

    for rtype in ['C', 'D', 'M', 'B']:
        type_checked = 0
        type_passed = 0
        type_failed = 0
        t0 = time.time()

        for dpart in dparts_for_type(rtype, max_size):
            nc, np, nf, fails = verify_partition(dpart, rtype)
            type_checked += nc
            type_passed += np
            type_failed += nf
            if fails:
                all_failures.extend([(dpart, rtype, *f) for f in fails])
                if len(fails) <= 2:
                    for ndrc, rt, kind, ref_ls, our_ls in fails:
                        print(f'  {kind}: {rtype}{dpart} {rt}')
                        if kind == 'MISMATCH':
                            print(f'    ref: {ref_ls}')
                            print(f'    ours: {our_ls}')
                else:
                    print(f'  {len(fails)} failures in {rtype}{dpart}')

        elapsed = time.time() - t0
        total_checked += type_checked
        total_passed += type_passed
        total_failed += type_failed

        status = 'PASSED' if type_failed == 0 else 'FAILED'
        print(f'→Type {rtype}: {type_passed}/{type_checked} passed, '
              f'{type_failed} failed  ({elapsed:.1f}s)')

    print()
    if total_failed == 0:
        print(f'ALL PASSED: {total_passed}/{total_checked} LS values match')
    else:
        print(f'FAILED: {total_passed}/{total_checked} passed, '
              f'{total_failed} failed')
        print(f'\nFirst 5 failures:')
        for f in all_failures[:5]:
            dpart, rtype, ndrc, rt, kind, ref_ls, our_ls = f
            print(f'  {kind}: {rtype}{dpart} {rt}')
            if ref_ls is not None:
                print(f'    ref:  {ref_ls}')
            if our_ls is not None:
                print(f'    ours: {our_ls}')


if __name__ == '__main__':
    main()
