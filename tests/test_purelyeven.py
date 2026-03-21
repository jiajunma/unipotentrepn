"""
test_purelyeven.py - Purely even induction test for DRC-LS matching.

Calls test_purelyeven(part, rtype) which inductively lifts DRC diagrams
and local systems through the theta correspondence chain, and at each
step verifies:
  1. Lifted DRCs match those produced by the definition (part2drc).
  2. Lifted LS match those produced by part2LS.
  3. For types D and B, det-twisted LS are disjoint from original LS.

This tests the older lift_pedrcs induction path (as opposed to
test_dpart2drcLS which uses lift_DRCLS).

The partition must be a valid general partition (column lengths in
decreasing order). The function internally handles alternating
type reduction (e.g. C <-> D, M <-> B).

Usage:
  python3 tests/test_purelyeven.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import test_purelyeven


TEST_CASES = [
    # --- Type C (from notebook cells 17,19,21) ---
    ((2, 2), 'C'),
    ((1, 1, 1, 1), 'C'),
    ((3, 3, 2, 2), 'C'),
    ((5, 5, 1, 1), 'C'),
    ((3, 3, 1, 1), 'C'),
    ((3, 3, 3, 3, 2, 2), 'C'),

    # --- Type D ---
    ((4, 2, 2), 'D'),
    ((6, 4, 2, 2), 'D'),
    ((6, 4, 4, 2), 'D'),
    ((8, 6, 4, 2), 'D'),

    # --- Type M (from notebook cells 6,8,9,20) ---
    ((3, 3), 'M'),
    ((5, 5, 2, 2), 'M'),
    ((3, 3, 1, 1), 'M'),
    ((4, 4, 2, 2), 'M'),
    ((4, 4, 3, 3, 2, 2, 2, 2), 'M'),
    ((8, 8, 7, 7, 5, 5, 1, 1), 'M'),
    ((2, 2, 2, 2, 2, 2, 2, 2, 1, 1), 'M'),

    # --- Type B ---
    # (test_purelyeven for B is not fully supported in the current codebase)
]


def main():
    passed = 0
    failed = 0

    for part, rtype in TEST_CASES:
        label = f"test_purelyeven({part}, '{rtype}')"
        try:
            test_purelyeven(part, rtype=rtype, report=False, reportann=False)
            passed += 1
        except Exception as e:
            failed += 1
            print(f"\n  FAILED: {label}")
            print(f"  Error: {e}")

    print(f"\n{'='*60}")
    print(f"test_purelyeven: {passed} passed, {failed} failed, {passed+failed} total")
    if failed:
        print("SOME TESTS FAILED")
        sys.exit(1)
    else:
        print("ALL TESTS PASSED")


if __name__ == '__main__':
    main()
