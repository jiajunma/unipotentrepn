"""
test_standalone.py - Cross-check standalone.py against combunipotent package.

Compares the DRC diagram sets produced by standalone.dpart2drc against
combunipotent.dpart2drc for all test cases from test_unip_BM.ipynb.

Also verifies that standalone's descent produces valid DRC diagrams.

Usage:
  python3 tests/test_standalone.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from standalone import (
    dpart2drc as sa_dpart2drc,
    verify_descent as sa_verify_descent,
    reg_drc as sa_reg_drc,
    orbit_to_bipartition,
    primitive_pairs,
    dpart2Wrepns,
)
from combunipotent import (
    dpart2drc as ref_dpart2drc,
    reg_drc as ref_reg_drc,
    part2drc as ref_part2drc,
)


# ---------------------------------------------------------------------------
# Test cases extracted from test_unip_BM.ipynb
# dpart2drc uses dual partitions; part2drc uses special partitions.
# We test with dpart2drc (dual partition side).
# ---------------------------------------------------------------------------

# Purely even dual partitions from notebook cells
DPART_CASES = [
    # Cell 2: large D case
    ((7, 7, 7, 7, 7, 5, 3, 3, 1, 1), 'D'),
    # Cell 3: B case
    ((4, 4, 4, 4, 2), 'B'),
    # Cell 4: M cases
    ((5, 5, 2, 2), 'M'),
    # Cell 5: M case
    ((3, 3, 1, 1), 'M'),
    # Cell 6: large M case
    ((4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2), 'M'),
    # Cell 8: M case
    ((8, 8, 7, 7, 5, 5, 1, 1), 'M'),
    # Cell 9: M case
    ((2, 2, 2, 2, 2, 2, 2, 2, 1, 1), 'M'),
    # Cell 19: large C case
    ((7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 1, 1, 1, 1, 1, 1), 'C'),
    # Cell 20: large M case
    ((4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2), 'M'),
    # Cell 21: C case
    ((3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2), 'C'),
    # Cell 22: D case
    ((4, 2, 2), 'D'),
    # Cell 23: D case
    ((2, 1, 1), 'D'),
    # Cell 24: D case
    ((3, 1, 1), 'D'),

    # Additional standard test cases
    ((1, 1), 'D'),
    ((3, 1), 'D'),
    ((3, 3), 'D'),
    ((5, 1), 'D'),
    ((5, 3), 'D'),
    ((5, 5), 'D'),
    ((5, 3, 1, 1), 'D'),
    ((7, 5, 3, 1), 'D'),
    ((7, 7, 3, 3), 'D'),
    ((5, 5, 3, 3), 'D'),

    ((1,), 'C'),
    ((3,), 'C'),
    ((5,), 'C'),
    ((3, 1, 1), 'C'),
    ((5, 1, 1), 'C'),
    ((5, 3, 1), 'C'),
    ((5, 3, 3), 'C'),
    ((7, 3, 1), 'C'),
    ((7, 5, 3), 'C'),
    ((7, 7, 1), 'C'),

    ((2, 2), 'M'),
    ((4, 2), 'M'),
    ((4, 4), 'M'),
    ((6, 2), 'M'),
    ((6, 4), 'M'),
    ((6, 6), 'M'),
    ((6, 4, 2, 2), 'M'),
    ((8, 6, 4, 2), 'M'),

    ((2, 2), 'B'),
    ((4, 2), 'B'),
    ((4, 4), 'B'),
    ((6, 2), 'B'),
    ((6, 4), 'B'),
    ((6, 6), 'B'),
    ((6, 4, 2, 2), 'B'),
    ((8, 6, 4, 2), 'B'),
]

# Special partition cases from notebook (using part2drc)
PART_CASES = [
    # Cell 4
    ((2, 2), 'C'),
    ((5, 5, 2, 2), 'M'),
    # Cell 5
    ((3, 3, 1, 1), 'M'),
    # Cell 33
    ((10, 8, 6, 4, 2), 'C'),
    # Cell 34
    ((6, 6, 5, 5, 2, 2), 'C'),
    # Cell 35
    ((1, 1, 1, 1, 1, 1), 'C'),
]


def test_dpart2drc_crosscheck():
    """Compare standalone.dpart2drc vs combunipotent.dpart2drc."""
    passed = 0
    failed = 0
    skipped = 0

    for dpart, rtype in DPART_CASES:
        label = f"dpart2drc({dpart}, '{rtype}')"
        try:
            sa_drcs = set(sa_dpart2drc(dpart, rtype))
            ref_drcs = set(ref_reg_drc(d) for d in ref_dpart2drc(dpart, rtype, report=False))

            if sa_drcs == ref_drcs:
                passed += 1
            else:
                failed += 1
                extra = sa_drcs - ref_drcs
                missing = ref_drcs - sa_drcs
                print(f"\n  MISMATCH: {label}")
                print(f"    standalone: {len(sa_drcs)}, reference: {len(ref_drcs)}")
                if extra:
                    print(f"    extra in standalone: {len(extra)}")
                if missing:
                    print(f"    missing from standalone: {len(missing)}")
        except Exception as e:
            failed += 1
            print(f"\n  ERROR: {label}: {e}")

    return passed, failed


def test_descent_validity():
    """Verify that standalone's descent produces valid DRC diagrams."""
    passed = 0
    failed = 0

    # Use a subset of cases to keep runtime reasonable
    descent_cases = [
        ((3, 1), 'D'), ((5, 3), 'D'), ((5, 3, 1, 1), 'D'),
        ((7, 5, 3, 1), 'D'), ((7, 7, 3, 3), 'D'),
        ((1,), 'C'), ((3,), 'C'), ((5, 3, 1), 'C'), ((7, 5, 3), 'C'),
        ((2, 2), 'M'), ((4, 2), 'M'), ((6, 4, 2, 2), 'M'),
        ((8, 6, 4, 2), 'M'),
        ((2, 2), 'B'), ((4, 2), 'B'), ((6, 4), 'B'), ((6, 4, 2, 2), 'B'),
    ]
    for dpart, rtype in descent_cases:
        p, f = sa_verify_descent(dpart, rtype)
        passed += p
        failed += f
        if f > 0:
            print(f"  DESCENT FAIL: {dpart} {rtype}: {p} passed, {f} failed")

    return passed, failed


def test_orbit_to_bipartition():
    """Check orbit_to_bipartition produces correct shapes."""
    passed = 0
    failed = 0

    cases = [
        # (dpart, rtype, expected_tauL, expected_tauR)
        ((2, 2), 'B', (1,), (1, 1)),
        ((4, 2), 'B', (2,), (2, 1)),
        ((2, 2), 'M', (1,), (1,)),
        ((4, 2), 'M', (2,), (1,)),
        ((1, 1), 'D', (1,), ()),
        ((3, 1), 'D', (2,), ()),
        ((1,), 'C', (), ()),
        ((3,), 'C', (), (1,)),
    ]
    for dpart, rtype, exp_L, exp_R in cases:
        tauL, tauR = orbit_to_bipartition(dpart, rtype)
        if tauL == exp_L and tauR == exp_R:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL orbit_to_bipartition({dpart}, '{rtype}')")
            print(f"    got: ({tauL}, {tauR}), expected: ({exp_L}, {exp_R})")

    return passed, failed


def test_Wrepn_count():
    """Check that the number of W-representations matches reference."""
    passed = 0
    failed = 0

    for dpart, rtype in DPART_CASES:
        try:
            sa_wrepns = dpart2Wrepns(dpart, rtype)
            ref_drcs = list(ref_dpart2drc(dpart, rtype, report=False))
            sa_drcs = list(sa_dpart2drc(dpart, rtype))

            if len(sa_drcs) == len(ref_drcs):
                passed += 1
            else:
                failed += 1
                print(f"  COUNT MISMATCH: {dpart} {rtype}: "
                      f"standalone={len(sa_drcs)}, ref={len(ref_drcs)}")
        except Exception as e:
            failed += 1
            print(f"  ERROR: {dpart} {rtype}: {e}")

    return passed, failed


def main():
    all_passed = True

    # Test 1: orbit_to_bipartition
    print(f"\n{'='*60}")
    print("Test 1: orbit_to_bipartition")
    print(f"{'='*60}")
    p, f = test_orbit_to_bipartition()
    print(f"  {p} passed, {f} failed")
    if f > 0:
        all_passed = False

    # Test 2: DRC count match
    print(f"\n{'='*60}")
    print("Test 2: DRC count match (standalone vs combunipotent)")
    print(f"{'='*60}")
    p, f = test_Wrepn_count()
    print(f"  {p} passed, {f} failed")
    if f > 0:
        all_passed = False

    # Test 3: DRC exact match
    print(f"\n{'='*60}")
    print("Test 3: DRC exact match (standalone vs combunipotent)")
    print(f"{'='*60}")
    p, f = test_dpart2drc_crosscheck()
    print(f"  {p} passed, {f} failed")
    if f > 0:
        all_passed = False

    # Test 4: Descent validity
    print(f"\n{'='*60}")
    print("Test 4: Descent produces valid DRC diagrams")
    print(f"{'='*60}")
    p, f = test_descent_validity()
    print(f"  {p} passed, {f} failed")
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
