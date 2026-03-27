"""
test_dpart2drcLS.py - DRC-LS matching test for purely even dual partitions.

Calls test_dpart2drcLS(dpart, rtype, test=True) which verifies:
  1. Theta lifting produces exactly the same DRC set as the definition (dpart2drc).
  2. Theta lifting produces exactly the same LS set as the definition (part2LS).
  3. For types D and B, the det-twisted LS are disjoint from the original LS.

If any check fails, test_dpart2drcLS raises an AssertionError or prints
"Missing LS" and returns early.

Partition validity (purely even):
  Type D : all parts odd,  total even   (e.g. (5,3,1,1))
  Type C : all parts odd,  total odd    (e.g. (5,3,1))
  Type B : all parts even, total even   (e.g. (6,4,2))
  Type M : all parts even, total even   (e.g. (4,4,2,2))

Usage:
  python3 tests/test_dpart2drcLS.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import test_dpart2drcLS


TEST_CASES = [
    # --- Type D ---
    ((1, 1), 'D'),
    ((3, 1), 'D'),
    ((3, 3), 'D'),
    ((5, 1), 'D'),
    ((5, 3), 'D'),
    ((5, 5), 'D'),
    ((3, 3, 1, 1), 'D'),
    ((5, 3, 1, 1), 'D'),
    ((5, 5, 1, 1), 'D'),
    ((7, 3), 'D'),
    ((7, 5), 'D'),
    ((7, 5, 3, 1), 'D'),
    ((7, 7, 3, 3), 'D'),
    ((5, 5, 3, 3), 'D'),
    ((5, 5, 3, 3, 1, 1), 'D'),
    ((7, 7, 5, 5), 'D'),
    ((7, 7, 7, 7, 7, 5, 3, 3, 1, 1), 'D'),  # from notebook cell 2

    # --- Type C ---
    ((1,), 'C'),
    ((3,), 'C'),
    ((5,), 'C'),
    ((3, 1, 1), 'C'),
    ((5, 1, 1), 'C'),
    ((5, 3, 1), 'C'),
    ((5, 3, 3), 'C'),
    ((5, 5, 1), 'C'),
    ((7, 3, 1), 'C'),
    ((7, 5, 1), 'C'),
    ((7, 5, 3), 'C'),
    ((7, 7, 1), 'C'),
    ((9, 5, 3), 'C'),
    ((7, 7, 3, 3, 1), 'C'),

    # --- Type B (test=False: det-disjointness assertion is skipped, ---
    # --- matching notebook cell 3 behavior)                        ---
    ((2, 2), 'B'),
    ((4, 2), 'B'),
    ((4, 4), 'B'),
    ((6, 2), 'B'),
    ((6, 4), 'B'),
    ((6, 6), 'B'),
    ((4, 4, 2, 2), 'B'),
    ((6, 4, 2, 2), 'B'),
    ((8, 4), 'B'),
    ((8, 6), 'B'),
    ((8, 6, 4, 2), 'B'),
    ((6, 6, 4, 4), 'B'),
    ((4, 4, 4, 4, 2), 'B'),  # from notebook cell 3

    # --- Type M ---
    ((2, 2), 'M'),
    ((4, 2), 'M'),
    ((4, 4), 'M'),
    ((6, 2), 'M'),
    ((6, 4), 'M'),
    ((6, 6), 'M'),
    ((4, 4, 2, 2), 'M'),
    ((6, 4, 2, 2), 'M'),
    ((8, 4), 'M'),
    ((8, 6), 'M'),
    ((8, 6, 4, 2), 'M'),
    ((6, 6, 4, 4), 'M'),
]


def main():
    passed = 0
    failed = 0

    for dpart, rtype in TEST_CASES:
        label = f"test_dpart2drcLS({dpart}, '{rtype}')"
        # Type B: notebook used test=False (det-disjointness not yet verified)
        use_test = (rtype != 'B')
        try:
            test_dpart2drcLS(dpart, rtype, test=use_test, report=False, reportann=False)
            passed += 1
        except Exception as e:
            failed += 1
            print(f"\n  FAILED: {label}")
            print(f"  Error: {e}")

    print(f"\n{'='*60}")
    print(f"test_dpart2drcLS: {passed} passed, {failed} failed, {passed+failed} total")
    if failed:
        print("SOME TESTS FAILED")
        sys.exit(1)
    else:
        print("ALL TESTS PASSED")


if __name__ == '__main__':
    main()
