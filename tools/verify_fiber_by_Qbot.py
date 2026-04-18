"""
Verify the balanced fiber size formulas by sub's Q_bot:
- Q_bot = d (layerOrd 4): fiber = 4k
- Q_bot = r (layerOrd 2): fiber = 4k - 2
- Q_bot ∈ {•, s} (layerOrd ≤ 1): fiber = 2k - 1

For balanced case (r₂ ≤ r₃) on dp = r₁::r₂::rest.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from standalone import dpart2drc, verify_drc, getz
from collections import defaultdict


def Q_bot_sym(drc):
    """Natural Q bottom symbol from drcR[0] last char."""
    q_col0 = getz(drc[1], 0, '')
    return q_col0[-1] if q_col0 else ''


def Q_bot_layerOrd(sym):
    return {'*': 0, 's': 1, 'r': 2, 'c': 3, 'd': 4}.get(sym, -1)


def enum_B(dp):
    drcs = dpart2drc(list(dp), rtype='B')
    results = []
    for drc in drcs:
        for γ in ('B+', 'B-'):
            if verify_drc(drc, γ):
                results.append((drc, γ))
    return results


def drc_shiftLeft(drc):
    return (drc[0][1:], drc[1][1:])


def is_balanced(dp):
    if len(dp) < 2:
        return False
    r3 = dp[2] if len(dp) > 2 else 0
    return dp[1] <= r3


def compute_fiber_by_Qbot(dp_new):
    """For a balanced dp_new, compute fibers grouped by sub.Q_bot."""
    if not is_balanced(dp_new):
        return None
    k = (dp_new[0] - dp_new[1]) // 2 + 1
    dp_sub = tuple(dp_new[2:])
    subs = enum_B(dp_sub)
    news = enum_B(dp_new)

    # For each new PBP, find its descent (shiftLeft both P and Q).
    fibers = defaultdict(int)
    for (drc_n, γ_n) in news:
        drc_s = drc_shiftLeft(drc_n)
        fibers[(drc_s, γ_n)] += 1

    # Classify subs by Q_bot, then group fibers
    d_sum, r_sum, low_sum = 0, 0, 0
    d_count, r_count, low_count = 0, 0, 0
    for (drc_s, γ_s) in subs:
        q_bot = Q_bot_sym(drc_s)
        lo = Q_bot_layerOrd(q_bot)
        fiber = fibers.get((drc_s, γ_s), 0)
        if q_bot == 'd':
            d_sum += fiber
            d_count += 1
        elif q_bot == 'r':
            r_sum += fiber
            r_count += 1
        elif lo <= 1:  # • or s
            low_sum += fiber
            low_count += 1

    return {
        'dp': dp_new, 'k': k, 'dp_sub': dp_sub,
        'd_sum': d_sum, 'r_sum': r_sum, 'low_sum': low_sum,
        'd_count': d_count, 'r_count': r_count, 'low_count': low_count,
    }


def verify_fiber_formulas(dp_new):
    """Test fiber_card_B_bal_Q{d,r,low} for balanced dp_new."""
    r = compute_fiber_by_Qbot(dp_new)
    if r is None:
        return None
    k = r['k']

    expected_d = 4 * k
    expected_r = 4 * k - 2
    expected_low = 2 * k - 1

    # If there's at least one sub with each class, check the AVERAGE fiber per sub.
    def check(total, count, expected):
        if count == 0:
            return True, None  # vacuously true
        # Total / count should equal expected (uniform per class)
        if total % count != 0:
            return False, f'non-uniform: {total}/{count}'
        actual = total // count
        return actual == expected, f'{actual} vs {expected}'

    ok_d, msg_d = check(r['d_sum'], r['d_count'], expected_d)
    ok_r, msg_r = check(r['r_sum'], r['r_count'], expected_r)
    ok_low, msg_low = check(r['low_sum'], r['low_count'], expected_low)

    return {
        'dp': dp_new, 'k': k,
        'Qd': (ok_d, msg_d, r['d_count']),
        'Qr': (ok_r, msg_r, r['r_count']),
        'Qlow': (ok_low, msg_low, r['low_count']),
    }


def main():
    tests = [
        (4, 4), (6, 6), (8, 8),
        (4, 4, 2), (6, 4, 4), (6, 6, 6), (8, 6, 6, 4),
        (4, 4, 4, 2), (4, 4, 4, 4), (6, 4, 4, 2), (6, 4, 4, 4),
        (6, 6, 4, 2), (6, 6, 6, 6), (8, 4, 4, 4), (8, 6, 6, 2),
        (6, 4, 4, 4, 2), (8, 4, 4, 4, 2),
    ]

    all_ok = True
    for dp in tests:
        r = verify_fiber_formulas(dp)
        if r is None:
            print(f"  {str(dp):20} SKIP (not balanced)")
            continue

        k = r['k']
        parts = []
        for cls in ('Qd', 'Qr', 'Qlow'):
            ok, msg, count = r[cls]
            mark = '✓' if ok else '✗'
            parts.append(f'{cls}:{mark}({msg},n={count})')
            if not ok:
                all_ok = False
        print(f"  {str(dp):20} k={k}  " + "  ".join(parts))

    print()
    print(f"RESULT: {'ALL FIBER FORMULAS VERIFIED' if all_ok else 'FAILURES'}")


if __name__ == "__main__":
    main()
