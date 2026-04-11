"""
test_myd_det_disjoint.py - Verify MYD det-disjointness for type B and D.

For B/D types, the det twist on MYD is sign_twist(1, 1) — equation (9.15).
This negates (p_i, q_i) at all odd levels i.

Claim: for each orbit Ǒ,
  S₁ = { L_τ̂ : τ̂ = (τ, ℘) ∈ PBP^ext_★(Ǒ) }
  S₂ = { L_τ̂ ⊗ (-1,-1) : τ̂ ∈ PBP^ext_★(Ǒ) }
are disjoint: S₁ ∩ S₂ = ∅.

For B: τ̂ ranges over all DRCs × {B+, B-} × all ℘ ⊆ PP.
For D: τ̂ ranges over all DRCs × all ℘ ⊆ PP.

Usage:
  python3 tests/test_myd_det_disjoint.py              # default max_size=16
  python3 tests/test_myd_det_disjoint.py --max-size 20
"""
import sys
import os
import argparse
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from standalone import (
    dpart2drc, compute_AC, myd_to_tuple, myd_sign_twist,
    reg_part, primitive_pairs,
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
    """Generate all valid good-parity dual partitions for rtype up to max_size."""
    results = []
    if rtype in ('D', 'C'):
        for n in range(1, max_size + 1):
            parity = n % 2
            if (rtype == 'D' and parity != 0) or (rtype == 'C' and parity != 1):
                continue
            for p in gen_partitions(n):
                if all(r % 2 == 1 for r in p):
                    results.append(p)
    elif rtype in ('B', 'M'):
        for n in range(2, max_size + 1, 2):
            for p in gen_partitions(n):
                if all(r % 2 == 0 for r in p):
                    results.append(p)
    return results


def powerset(s):
    """Generate all subsets of a set."""
    s = list(s)
    result = [set()]
    for x in s:
        result = result + [sub | {x} for sub in result]
    return result


def _collect_myds(ac_list):
    """Collect MYD tuples from a list of (coeff, myd) pairs."""
    return set(myd_to_tuple(myd) for _, myd in ac_list)


def _det_twist_myds(myd_set, rtype):
    """Apply sign_twist(1, 1) to all MYDs in the set."""
    result = set()
    for mt in myd_set:
        E = dict(mt)
        twisted = myd_sign_twist(E, 1, 1, rtype)
        result.add(myd_to_tuple(twisted))
    return result


def test_det_disjoint_D(dparts):
    """
    Test MYD det-disjointness for type D.

    For each orbit, collect all MYDs from all (drc, ℘) extended PBPs,
    apply sign_twist(1,1), and check disjointness.
    """
    passed = 0
    failed = 0
    errors = 0

    for dpart in dparts:
        try:
            drcs = dpart2drc(dpart, 'D')
            PP = primitive_pairs(dpart, 'D')
            all_wp = powerset(PP)

            all_myds = set()
            for drc in drcs:
                for wp in all_wp:
                    ac = compute_AC(drc, 'D', dpart=dpart, wp=wp if wp else None)
                    all_myds.update(_collect_myds(ac))

            det_myds = _det_twist_myds(all_myds, 'D')
            overlap = all_myds & det_myds
            if len(overlap) == 0:
                passed += 1
            else:
                failed += 1
                if failed <= 5:
                    print(f"  D FAIL: dpart={dpart}, |PP|={len(PP)}")
                    print(f"    #MYDs={len(all_myds)}, overlap={len(overlap)}")
                    for mt in list(overlap)[:2]:
                        print(f"    fixed by det: {dict(mt)}")
        except Exception as e:
            errors += 1
            if errors <= 3:
                import traceback
                print(f"  D ERROR: dpart={dpart}: {e}")
                traceback.print_exc()

    return passed, failed, errors


def test_det_disjoint_B(dparts):
    """
    Test MYD det-disjointness for type B.

    For each orbit, collect all MYDs from all (drc, B+/B-, ℘) extended PBPs,
    apply sign_twist(1,1), and check disjointness.
    """
    passed = 0
    failed = 0
    errors = 0

    for dpart in dparts:
        try:
            drcs = dpart2drc(dpart, 'B')
            PP = primitive_pairs(dpart, 'B')
            all_wp = powerset(PP)

            all_myds = set()
            for drc in drcs:
                for wp in all_wp:
                    wp_arg = wp if wp else None
                    for rt in ('B+', 'B-'):
                        ac = compute_AC(drc, rt, dpart=dpart, wp=wp_arg)
                        all_myds.update(_collect_myds(ac))

            det_myds = _det_twist_myds(all_myds, 'B')
            overlap = all_myds & det_myds
            if len(overlap) == 0:
                passed += 1
            else:
                failed += 1
                if failed <= 5:
                    print(f"  B FAIL: dpart={dpart}, |PP|={len(PP)}")
                    print(f"    #MYDs={len(all_myds)}, overlap={len(overlap)}")
                    for mt in list(overlap)[:2]:
                        print(f"    fixed by det: {dict(mt)}")
        except Exception as e:
            errors += 1
            if errors <= 3:
                import traceback
                print(f"  B ERROR: dpart={dpart}: {e}")
                traceback.print_exc()

    return passed, failed, errors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-size', type=int, default=16,
                        help='Max total size of partitions (default: 16)')
    args = parser.parse_args()
    max_size = args.max_size

    all_passed = True

    # Type D
    dparts_D = gen_good_parity_dparts('D', max_size)
    print(f"\n{'='*60}")
    print(f"Type D: {len(dparts_D)} good-parity dual partitions (max_size={max_size})")
    print(f"{'='*60}")
    p, f, e = test_det_disjoint_D(dparts_D)
    status = 'PASS' if f == 0 and e == 0 else 'FAIL'
    print(f"  Det-disjoint: {p} passed, {f} failed, {e} errors  [{status}]")
    if f > 0 or e > 0:
        all_passed = False

    # Type B
    dparts_B = gen_good_parity_dparts('B', max_size)
    print(f"\n{'='*60}")
    print(f"Type B: {len(dparts_B)} good-parity dual partitions (max_size={max_size})")
    print(f"{'='*60}")
    p, f, e = test_det_disjoint_B(dparts_B)
    status = 'PASS' if f == 0 and e == 0 else 'FAIL'
    print(f"  Det-disjoint: {p} passed, {f} failed, {e} errors  [{status}]")
    if f > 0 or e > 0:
        all_passed = False

    print(f"\n{'='*60}")
    if all_passed:
        print("ALL DET-DISJOINTNESS TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == '__main__':
    main()
