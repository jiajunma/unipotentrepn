"""
Comprehensive verification of all 5 focused lemmas for B balanced step.

Tests:
- A1: |{σ ∈ B⁺ ∪ B⁻ : Q_bot = d}| = countPBP_B(dp).1
- A2: |{σ ∈ B⁺ : Q_bot ≠ d}| + |{σ ∈ B⁻ : Q_bot = r}| = countPBP_B(dp).2.1
- A3: |{σ ∈ B⁻ : Q_bot.lo ≤ 1}| = countPBP_B(dp).2.2
- γ-swap: |{σ ∈ B⁺ : Q_bot.lo ≤ 1}| = |{σ ∈ B⁻ : Q_bot.lo ≤ 1}|
- Balanced step: card(B⁺⊔B⁻ on r₁::r₂::rest) = dd'·4k + rc'·(4k-2)
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from standalone import dpart2drc, verify_drc, _countPBP_B, getz


def Q_bot_layerOrd(drc):
    """Return layerOrd of Q bottom cell (drcR[0][-1]). -1 if Q empty."""
    q_col0 = getz(drc[1], 0, '')
    if not q_col0:
        return -1
    sym = q_col0[-1]
    return {'*': 0, 's': 1, 'r': 2, 'c': 3, 'd': 4}.get(sym, -1)


def Q_bot_sym(drc):
    q_col0 = getz(drc[1], 0, '')
    return q_col0[-1] if q_col0 else ''


def enum_all(dp):
    """All PBPs on dp as list of (drc, gamma)."""
    drcs = dpart2drc(list(dp), rtype='B')
    result = []
    for drc in drcs:
        for γ in ('B+', 'B-'):
            if verify_drc(drc, γ):
                result.append((drc, γ))
    return result


def verify_A1(dp):
    """A1: |Q_bot=d combined| = countPBP_B.dd"""
    pbps = enum_all(dp)
    count = sum(1 for drc, _ in pbps if Q_bot_sym(drc) == 'd')
    return count == _countPBP_B(list(dp))[0]


def verify_A2(dp):
    """A2: |B+ Q_bot≠d| + |B- Q_bot=r| = countPBP_B.rc"""
    pbps = enum_all(dp)
    bp_nond = sum(1 for drc, γ in pbps if γ == 'B+' and Q_bot_sym(drc) != 'd')
    bm_r = sum(1 for drc, γ in pbps if γ == 'B-' and Q_bot_sym(drc) == 'r')
    return bp_nond + bm_r == _countPBP_B(list(dp))[1]


def verify_A3(dp):
    """A3: |B- Q_bot.lo ≤ 1| = countPBP_B.ss"""
    pbps = enum_all(dp)
    count = sum(1 for drc, γ in pbps if γ == 'B-' and Q_bot_layerOrd(drc) <= 1)
    return count == _countPBP_B(list(dp))[2]


def verify_swap(dp):
    """γ-swap: |B+ Q_bot.lo≤1| = |B- Q_bot.lo≤1|"""
    pbps = enum_all(dp)
    bp = sum(1 for drc, γ in pbps if γ == 'B+' and Q_bot_layerOrd(drc) <= 1)
    bm = sum(1 for drc, γ in pbps if γ == 'B-' and Q_bot_layerOrd(drc) <= 1)
    return bp == bm


def verify_balanced_step(dp_new):
    """Main: card(B⁺⊔B⁻ on dp_new) = dd'·4k + rc'·(4k-2), balanced case only."""
    if len(dp_new) < 2:
        return None
    r1, r2 = dp_new[0], dp_new[1]
    r3 = dp_new[2] if len(dp_new) > 2 else 0
    if r2 > r3:  # primitive
        return None
    k = (r1 - r2) // 2 + 1
    rest = tuple(dp_new[2:])
    dd_rest, rc_rest, _ = _countPBP_B(list(rest))
    expected = dd_rest * 4 * k + rc_rest * (4 * k - 2)
    actual = len(enum_all(dp_new))
    return expected == actual


def main():
    tests = [
        (2,), (4,), (6,), (8,), (10,),
        (4, 2), (6, 2), (6, 4), (8, 2), (8, 4), (8, 6), (10, 2), (10, 4),
        (4, 4), (6, 6), (8, 8), (10, 10),
        (4, 4, 2), (6, 4, 2), (6, 4, 4), (6, 6, 2), (6, 6, 4), (6, 6, 6),
        (8, 4, 2), (8, 4, 4), (8, 6, 2), (8, 6, 4), (8, 6, 6),
        (8, 8, 2), (8, 8, 4), (8, 8, 6), (8, 8, 8),
        (4, 4, 4, 2), (4, 4, 4, 4), (6, 4, 4, 2), (6, 4, 4, 4),
        (6, 6, 4, 2), (6, 6, 4, 4), (6, 6, 6, 2), (6, 6, 6, 4), (6, 6, 6, 6),
        (8, 4, 4, 2), (8, 4, 4, 4), (8, 6, 4, 2), (8, 6, 4, 4),
        (8, 6, 6, 2), (8, 6, 6, 4), (8, 6, 6, 6),
        (8, 8, 4, 2), (8, 8, 4, 4), (8, 8, 6, 2), (8, 8, 6, 4),
        (8, 8, 6, 6), (8, 8, 8, 2), (8, 8, 8, 4), (8, 8, 8, 6), (8, 8, 8, 8),
        (8, 8, 6, 4, 2), (8, 8, 8, 6, 4, 2),
        (10, 8, 6, 4, 2),
    ]

    print(f"Testing {len(tests)} dp values...\n")

    results = {'A1': [], 'A2': [], 'A3': [], 'swap': [], 'bal_step': []}

    for dp in tests:
        results['A1'].append((dp, verify_A1(dp)))
        results['A2'].append((dp, verify_A2(dp)))
        results['A3'].append((dp, verify_A3(dp)))
        results['swap'].append((dp, verify_swap(dp)))
        bs = verify_balanced_step(dp)
        if bs is not None:
            results['bal_step'].append((dp, bs))

    for lemma, rs in results.items():
        total = len(rs)
        passed = sum(1 for _, ok in rs if ok)
        failed = [dp for dp, ok in rs if not ok]
        status = "PASS" if not failed else "FAIL"
        print(f"  {lemma:10}: {passed}/{total} {status}")
        if failed:
            for dp in failed:
                print(f"    ❌ {dp}")

    print()
    all_ok = all(all(ok for _, ok in rs) for rs in results.values())
    print(f"OVERALL: {'✓ ALL MATHEMATICAL IDENTITIES VERIFIED' if all_ok else '✗ FAILURES FOUND'}")

    # Additional: sanity check the total card
    print("\n--- Additional: tripleSum = card(B⁺⊔B⁻) ---")
    for dp in tests[:20]:
        count = _countPBP_B(list(dp))
        tsum = sum(count)
        actual = len(enum_all(dp))
        ok = tsum == actual
        print(f"  {str(dp):16} tripleSum={tsum:4} card={actual:4} {'✓' if ok else '✗'}")


if __name__ == "__main__":
    main()
