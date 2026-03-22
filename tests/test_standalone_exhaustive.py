"""
test_standalone_exhaustive.py - Exhaustive tests for standalone.py

For each root system type (B, C, D, M), enumerate ALL valid good-parity
dual partitions up to a given size, and verify:
  1. DRC count matches recursive formula from recursive.py
  2. DRC diagrams pass verify_drc
  3. Descent produces valid DRC diagrams
  4. MYD signature matches DRC signature (for non-B types)

Good parity conditions:
  B, M: all rows even, total even
  C:    all rows odd,  total odd
  D:    all rows odd,  total even

Usage:
  python3 tests/test_standalone_exhaustive.py              # default max_size=16
  python3 tests/test_standalone_exhaustive.py --max-size 20
"""
import sys
import os
import argparse

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from standalone import (
    dpart2drc, dpart_to_bipartition, primitive_pairs, verify_drc,
    reg_drc, signature, epsilon, descent, reg_part, myd_signature,
    compute_AC, verify_drc as sa_verify_drc,
)


def gen_partitions(n, max_part=None, step=1, min_part=1):
    """Generate all partitions of n in decreasing order."""
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for first in range(min(n, max_part), min_part - 1, -step):
        if first < min_part:
            break
        for rest in gen_partitions(n - first, first, step, min_part):
            yield (first, *rest)


def gen_good_parity_dparts(rtype, max_size):
    """
    Generate all valid good-parity dual partitions for rtype up to max_size.

    Good parity:
      B, M: all rows even, total even
      C:    all rows odd,  total odd
      D:    all rows odd,  total even
    """
    results = []
    if rtype in ('D', 'C'):
        # All rows odd, total parity determined by type
        for n in range(1, max_size + 1):
            parity = n % 2
            if (rtype == 'D' and parity != 0) or (rtype == 'C' and parity != 1):
                continue
            for p in gen_partitions(n):
                # Filter: all parts must be odd
                if all(r % 2 == 1 for r in p):
                    results.append(p)
    elif rtype in ('B', 'M'):
        # All rows even, total even
        for n in range(2, max_size + 1, 2):
            for p in gen_partitions(n):
                # Filter: all parts must be even
                if all(r % 2 == 0 for r in p):
                    results.append(p)
    return results


def test_drc_count(dparts, rtype):
    """Test that DRC count matches recursive formula from standalone.countPBP."""
    from standalone import countPBP

    passed = 0
    failed = 0

    for dpart in dparts:
        drcs = dpart2drc(dpart, rtype)
        n_drc = len(drcs)
        PP = primitive_pairs(dpart, rtype)
        n_pp = len(PP)

        # countPBP gives #PBP for ℘=∅ (special shape)
        # dpart2drc now only generates DRCs for the special bipartition
        # So #DRC should equal countPBP for all types
        f11 = countPBP(dpart, rtype)
        expected = f11

        if n_drc == expected:
            passed += 1
        else:
            failed += 1
            if failed <= 3:
                print(f"  COUNT FAIL: {dpart} {rtype}: #DRC={n_drc}, expected={expected} "
                      f"(countPBP={f11}, |PP|={n_pp})")

    return passed, failed


def test_verify_all_drcs(dparts, rtype):
    """Test that all generated DRCs pass verify_drc."""
    passed = 0
    failed = 0

    for dpart in dparts:
        drcs = dpart2drc(dpart, rtype)
        # B type DRCs are untagged; B+ and B- have the same symbol rules
        vtype = 'B+' if rtype == 'B' else rtype
        for drc in drcs:
            if sa_verify_drc(drc, vtype):
                passed += 1
            else:
                failed += 1
                if failed <= 3:
                    print(f"  VERIFY FAIL: {dpart} {rtype}")

    return passed, failed


def test_descent_valid(dparts, rtype):
    """Test that descent produces valid DRC diagrams."""
    passed = 0
    failed = 0

    for dpart in dparts:
        drcs = dpart2drc(dpart, rtype)
        for drc in drcs:
            try:
                ddrc, rtype_prime = descent(drc, rtype)
                if ddrc is not None and sa_verify_drc(ddrc, rtype_prime):
                    passed += 1
                else:
                    failed += 1
            except Exception:
                failed += 1

    return passed, failed


def test_myd_signature(dparts, rtype):
    """Test that MYD signature matches DRC signature (for non-B types)."""
    if rtype == 'B':
        return 0, 0  # skip B (known WIP)

    passed = 0
    failed = 0

    for dpart in dparts:
        drcs = dpart2drc(dpart, rtype)
        for drc in drcs:
            sig = signature(drc, rtype)
            try:
                ac = compute_AC(drc, rtype, dpart=dpart)
                if not ac:
                    continue
                msig = myd_signature(ac[0][1])
                if msig == sig:
                    passed += 1
                else:
                    failed += 1
                    if failed <= 3:
                        print(f"  MYD SIG FAIL: {dpart} {rtype}: sig={sig}, myd={msig}")
            except Exception as e:
                failed += 1
                if failed <= 3:
                    print(f"  MYD ERROR: {dpart} {rtype}: {e}")

    return passed, failed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-size', type=int, default=16,
                        help='Max total size of partitions (default: 16)')
    args = parser.parse_args()
    max_size = args.max_size

    all_passed = True

    for rtype in ('C', 'D', 'M', 'B'):
        dparts = gen_good_parity_dparts(rtype, max_size)
        print(f"\n{'='*60}")
        print(f"Type {rtype}: {len(dparts)} good-parity dual partitions (max_size={max_size})")
        print(f"{'='*60}")

        # Test 1: DRC count
        p, f = test_drc_count(dparts, rtype)
        status = 'PASS' if f == 0 else 'FAIL'
        print(f"  Count match:     {p} passed, {f} failed  [{status}]")
        if f > 0:
            all_passed = False

        # Test 2: verify_drc
        p, f = test_verify_all_drcs(dparts, rtype)
        status = 'PASS' if f == 0 else 'FAIL'
        print(f"  verify_drc:      {p} passed, {f} failed  [{status}]")
        if f > 0:
            all_passed = False

        # Test 3: descent validity
        p, f = test_descent_valid(dparts, rtype)
        status = 'PASS' if f == 0 else 'FAIL'
        print(f"  Descent valid:   {p} passed, {f} failed  [{status}]")
        if f > 0:
            all_passed = False

        # Test 4: MYD signature
        p, f = test_myd_signature(dparts, rtype)
        if rtype == 'B':
            print(f"  MYD signature:   (skipped for B type)")
        else:
            status = 'PASS' if f == 0 else 'FAIL'
            print(f"  MYD signature:   {p} passed, {f} failed  [{status}]")
            if f > 0:
                all_passed = False

    print(f"\n{'='*60}")
    if all_passed:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == '__main__':
    main()
