"""
test_LSDRC.py - DRC-LS matching test for general (non-purely-even) partitions.

Calls test_LSDRC(part, rtype) which uses the older lift_drcs induction path
to match DRC diagrams with local systems, and verifies:
  1. Lifted DRCs are a subset of all DRCs from part2drc.
  2. Lifted LS cover all LS from part2LS (no missing LS).

test_LSDRC returns True on success and False if any LS are missing.

Usage:
  python3 tests/test_LSDRC.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import test_LSDRC


TEST_CASES = [
    # --- Type D ---
    ((8, 3, 3, 1, 1), 'D'),
    ((4, 3, 3, 2, 2, 1, 1), 'D'),
    ((6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1), 'D'),
    ((4, 3, 3, 1, 1), 'D'),
    ((3, 2, 2, 1, 1), 'D'),
    ((5, 4, 4, 3, 3, 2, 2, 1, 1), 'D'),
    ((2, 1, 1), 'D'),
    ((4, 2, 2), 'D'),

    # --- Type B ---
    ((9, 6, 6, 3, 3, 2, 2, 1, 1), 'B'),
    ((7, 6, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1), 'B'),
    ((5, 4, 4, 3, 3, 2, 2, 1, 1), 'B'),
    ((3, 2, 2, 1, 1), 'B'),

    # --- Type M ---
    ((6, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1), 'M'),
    ((4, 4, 3, 3, 2, 2, 1, 1), 'M'),
    ((2, 2, 1, 1), 'M'),

    # --- Type C ---
    ((1, 1, 1, 1, 1, 1, 1, 1, 1, 1), 'C'),
    ((3, 3, 2, 2, 1, 1), 'C'),
    ((5, 5, 4, 4, 3, 3, 2, 2, 1, 1), 'C'),
    ((2, 2, 1, 1), 'C'),
]


def main():
    passed = 0
    failed = 0

    for part, rtype in TEST_CASES:
        label = f"test_LSDRC({part}, '{rtype}')"
        try:
            result = test_LSDRC(part, rtype, report=False, reportann=False)
            if result is False:
                failed += 1
                print(f"\n  FAILED: {label} (missing LS)")
            else:
                passed += 1
        except Exception as e:
            failed += 1
            print(f"\n  FAILED: {label}")
            print(f"  Error: {e}")

    print(f"\n{'='*60}")
    print(f"test_LSDRC: {passed} passed, {failed} failed, {passed+failed} total")
    if failed:
        print("SOME TESTS FAILED")
        sys.exit(1)
    else:
        print("ALL TESTS PASSED")


if __name__ == '__main__':
    main()
