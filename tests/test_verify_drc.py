"""
test_verify_drc.py - Exhaustive verification of DRC diagrams for all types.

For each root system type (B, B+, B-, C, D, M), this test:
  1. Enumerates ALL valid purely-even dual partitions up to a given total size.
  2. Generates every DRC diagram via dpart2drc(dpart, rtype).
  3. Verifies each diagram passes verify_drc(drc, rtype).

For type B, dpart2drc produces extended DRC diagrams (with 'a'/'b' tag).
We use split_extdrc_B to strip the tag and verify with rtype='B+' or 'B-'.

Partition validity rules (dual partition side):
  Type C : all parts odd,  total odd   (e.g. (5, 3, 1))
  Type D : all parts odd,  total even  (e.g. (5, 3))
  Type B : all parts even, total even  (e.g. (6, 4, 2))
  Type M : all parts even, total even  (e.g. (4, 4))

verify_drc checks the structural constraints of a DRC diagram:
  - Both (drcL, drcR) are valid Young diagrams (column lengths decrease).
  - After stripping the tail symbols layer by layer (in the order prescribed
    by the root system type), each intermediate diagram remains a valid
    Young diagram.
  - After all non-dot symbols are stripped, the remaining dot-only diagrams
    satisfy the bullet matching condition (equal column lengths, all dots).

Usage:
  python3 tests/test_verify_drc.py              # default: max_size=20
  python3 tests/test_verify_drc.py --max-size 24  # larger coverage
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from combunipotent import dpart2drc, verify_drc, reg_drc, str_dgms
from combunipotent import test_dpart2drcLS, split_extdrc_B, make_extdrc_B


# ---------------------------------------------------------------------------
# Enumerate all valid dual partitions for each type up to a given total size.
# ---------------------------------------------------------------------------

def gen_partitions(n, max_part=None, step=1, min_part=1):
    """
    Generate all partitions of n in decreasing order,
    with parts being multiples of step, >= min_part, <= max_part.
    """
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


def gen_valid_dparts(rtype, max_size):
    """
    Generate all valid purely-even dual partitions for the given rtype
    up to total size max_size.
    """
    results = []
    if rtype in ('D', 'C'):
        # All parts odd
        for n in range(1, max_size + 1):
            parity = n % 2
            # D: total even, C: total odd
            if (rtype == 'D' and parity != 0) or (rtype == 'C' and parity != 1):
                continue
            for p in gen_partitions(n, step=2, min_part=1):
                results.append(p)
    elif rtype in ('B', 'M'):
        # All parts even, total even
        for n in range(2, max_size + 1, 2):
            for p in gen_partitions(n, step=2, min_part=2):
                results.append(p)
    return results


def test_verify_drc_for_type(rtype, partitions, gen_rtype=None):
    """
    For every partition, generate all DRC diagrams via dpart2drc,
    and check each one passes verify_drc.

    Args:
        rtype: the rtype passed to verify_drc (e.g. 'C', 'D', 'M', 'B+', 'B-').
        partitions: list of dual partitions to test.
        gen_rtype: the rtype passed to dpart2drc for generation.
                   Defaults to rtype. Use e.g. gen_rtype='B' when rtype='B+'.

    Returns (total_tested, failures).
    """
    if gen_rtype is None:
        gen_rtype = rtype
    total = 0
    failures = []

    for dpart in partitions:
        try:
            drcs = dpart2drc(dpart, rtype=gen_rtype, report=False)
        except Exception as e:
            failures.append((dpart, None, f"dpart2drc raised: {e}"))
            continue

        for drc in drcs:
            drc = reg_drc(drc)
            total += 1
            try:
                result = verify_drc(drc, rtype=rtype)
            except Exception as e:
                failures.append((dpart, drc, f"verify_drc raised: {e}"))
                continue

            if not result:
                failures.append((dpart, drc, "verify_drc returned False"))

    return total, failures


def test_verify_drc_type_B_ext(partitions):
    """
    For type B, generate extended DRC diagrams via test_dpart2drcLS,
    split into (drc, B+/B-) via split_extdrc_B, verify with verify_drc,
    and test roundtrip with make_extdrc_B.
    Returns (total_tested, failures).
    """
    total = 0
    failures = []

    for dpart in partitions:
        try:
            lDRCLS, _ = test_dpart2drcLS(dpart, 'B', test=False, report=False)
        except Exception as e:
            failures.append((dpart, None, f"test_dpart2drcLS raised: {e}"))
            continue

        # Collect all extended DRCs from all induction steps
        for step_drcls in lDRCLS:
            for edrc in step_drcls:
                # Skip trivial empty diagrams
                if edrc == (('',), ('',)):
                    continue
                # Only process extended DRCs (last char is 'a' or 'b')
                try:
                    drcR0 = edrc[1][0]
                except (IndexError, TypeError):
                    continue
                if not drcR0 or drcR0[-1] not in ('a', 'b'):
                    continue

                total += 1
                # Test split
                try:
                    drc, srtype = split_extdrc_B(edrc)
                except Exception as e:
                    failures.append((dpart, edrc, f"split_extdrc_B raised: {e}"))
                    continue

                # Test verify_drc with B+ or B-
                try:
                    result = verify_drc(drc, srtype)
                except Exception as e:
                    failures.append((dpart, drc, f"verify_drc('{srtype}') raised: {e}"))
                    continue
                if not result:
                    failures.append((dpart, drc, f"verify_drc('{srtype}') returned False"))
                    continue

                # Test roundtrip make_extdrc_B
                try:
                    edrc2 = make_extdrc_B(drc, srtype)
                except Exception as e:
                    failures.append((dpart, drc, f"make_extdrc_B raised: {e}"))
                    continue
                if edrc2 != edrc:
                    failures.append((dpart, drc,
                        f"roundtrip mismatch: {edrc} != {edrc2}"))

    return total, failures


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-size', type=int, default=20,
                        help='Max total size of partitions to test (default: 20)')
    args = parser.parse_args()

    max_size = args.max_size
    all_passed = True

    # Test C, D, M with verify_drc directly
    for rtype in ('C', 'D', 'M'):
        partitions = gen_valid_dparts(rtype, max_size)
        print(f"\n{'='*60}")
        print(f"Type {rtype}: {len(partitions)} partitions (max_size={max_size})")
        print(f"{'='*60}")

        total, failures = test_verify_drc_for_type(rtype, partitions)

        if failures:
            all_passed = False
            print(f"  FAILED: {len(failures)}/{total} diagrams failed")
            for dpart, drc, info in failures[:10]:
                print(f"\n  Partition: {dpart}")
                print(f"  Error: {info}")
                if drc is not None:
                    print(f"  DRC diagram:\n{str_dgms(drc)}")
            if len(failures) > 10:
                print(f"\n  ... and {len(failures)-10} more failures")
        else:
            print(f"  PASSED: all {total} diagrams verified")

    # Test B with verify_drc('B+') on plain DRCs from dpart2drc.
    # dpart2drc('B') produces plain DRCs (no a/b tag), which are verified
    # as 'B+' (B+ and B- share the same structural constraints).
    partitions_B = gen_valid_dparts('B', max_size)
    print(f"\n{'='*60}")
    print(f"Type B (plain, verify as B+): {len(partitions_B)} partitions (max_size={max_size})")
    print(f"{'='*60}")
    total, failures = test_verify_drc_for_type('B+', partitions_B, gen_rtype='B')
    if failures:
        all_passed = False
        print(f"  FAILED: {len(failures)}/{total} diagrams failed")
        for dpart, drc, info in failures[:10]:
            print(f"\n  Partition: {dpart}")
            print(f"  Error: {info}")
            if drc is not None:
                print(f"  DRC diagram:\n{str_dgms(drc)}")
    else:
        print(f"  PASSED: all {total} diagrams verified")

    # Test B+/B- with split/make roundtrip on extended DRCs
    # Use a smaller max_size since test_dpart2drcLS is slower
    ext_max = min(max_size, 14)
    partitions_B_ext = gen_valid_dparts('B', ext_max)
    print(f"\n{'='*60}")
    print(f"Type B+/B- (extended): {len(partitions_B_ext)} partitions (max_size={ext_max})")
    print(f"{'='*60}")
    total, failures = test_verify_drc_type_B_ext(partitions_B_ext)
    if failures:
        all_passed = False
        print(f"  FAILED: {len(failures)}/{total} diagrams failed")
        for dpart, drc, info in failures[:10]:
            print(f"\n  Partition: {dpart}")
            print(f"  Error: {info}")
            if drc is not None:
                print(f"  DRC diagram:\n{str_dgms(drc)}")
    else:
        print(f"  PASSED: all {total} ext-DRC diagrams verified (split/make roundtrip)")

    print(f"\n{'='*60}")
    if all_passed:
        print("ALL TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == '__main__':
    main()
