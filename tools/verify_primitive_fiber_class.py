"""
Verify primitive case fiber class counts:
For each sub σ (any γ), in primitive case, of 4k fibers:
- tDD give new Q_bot = d
- tRC give new Q_bot = r
- tSS give new Q_bot.lo ≤ 1
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from standalone import dpart2drc, verify_drc, getz
from collections import defaultdict


def Q_bot_sym(drc):
    q_col0 = getz(drc[1], 0, '')
    return q_col0[-1] if q_col0 else ''


def Q_bot_lo(sym):
    return {'*': 0, 's': 1, 'r': 2, 'c': 3, 'd': 4}.get(sym, -1)


def enum_B(dp):
    drcs = dpart2drc(list(dp), rtype='B')
    r = []
    for drc in drcs:
        for γ in ('B+', 'B-'):
            if verify_drc(drc, γ):
                r.append((drc, γ))
    return r


def drc_shiftLeft(drc):
    return (drc[0][1:], drc[1][1:])


def is_primitive(dp):
    if len(dp) < 2:
        return False
    r3 = dp[2] if len(dp) > 2 else 0
    return dp[1] > r3


def tailCoeffs(k):
    """Returns (tDD, tRC, tSS, scDD, scRC, scSS) for primitive + balanced."""
    nu = lambda n: n + 1 if n >= 0 else 0
    tDD = nu(k-1) + (nu(k-2) if k >= 2 else 0)
    tRC = 2 * nu(k-1)
    tSS = 1
    scDD = 2 * (nu(k-2) if k >= 2 else 0)
    scRC = nu(k-1) + (nu(k-2) if k >= 2 else 0)
    scSS = 1
    return tDD, tRC, tSS, scDD, scRC, scSS


def check_primitive(dp_new):
    """For primitive dp_new, check fiber class counts per sub."""
    if not is_primitive(dp_new):
        return None
    k = (dp_new[0] - dp_new[1]) // 2 + 1
    dp_sub = tuple(dp_new[2:])
    tDD, tRC, tSS, _, _, _ = tailCoeffs(k)

    subs = enum_B(dp_sub)
    news = enum_B(dp_new)

    # For each new PBP, find its descent
    fibers_by_class = defaultdict(lambda: defaultdict(int))  # [sub_key][new_class] -> count
    for (drc_n, γ_n) in news:
        drc_s = drc_shiftLeft(drc_n)
        sym_n = Q_bot_sym(drc_n)
        lo_n = Q_bot_lo(sym_n)
        if sym_n == 'd':
            cls = 'd'
        elif sym_n == 'r':
            cls = 'r'
        elif lo_n <= 1:
            cls = 'low'
        else:  # c
            cls = 'c'
        fibers_by_class[(drc_s, γ_n)][cls] += 1

    # Check each sub has uniform distribution matching tDD, tRC, tSS
    ok = True
    issues = []
    for (drc_s, γ_s) in subs:
        counts = fibers_by_class[(drc_s, γ_s)]
        d_n = counts.get('d', 0)
        r_n = counts.get('r', 0)
        low_n = counts.get('low', 0)
        c_n = counts.get('c', 0)
        # In primitive, no correction at new level (k ≥ 2 or specific), so c should be 0
        # UNLESS k = 1 at new AND boundary condition triggers correction for B+
        if d_n != tDD or (r_n + c_n) != tRC or low_n != tSS:
            ok = False
            issues.append(f'sub γ={γ_s} Q_bot={Q_bot_sym(drc_s)}: d={d_n}, r={r_n}, c={c_n}, low={low_n} vs tDD={tDD}, tRC={tRC}, tSS={tSS}')

    return ok, issues, k, tDD, tRC, tSS, len(subs)


def main():
    tests = [
        (2,), (4,), (6,),
        (4, 2), (6, 2), (6, 4), (8, 4), (8, 6),
        (6, 4, 2), (8, 4, 2), (8, 6, 2), (8, 6, 4),
        (6, 6, 2), (8, 8, 2), (8, 8, 4),
        (8, 6, 4, 2), (10, 8, 6, 4, 2),
    ]

    all_ok = True
    for dp in tests:
        if len(dp) < 2:
            print(f"  {str(dp):20} SKIP (singleton)")
            continue
        r = check_primitive(dp)
        if r is None:
            print(f"  {str(dp):20} SKIP (balanced)")
            continue
        ok, issues, k, tDD, tRC, tSS, n_subs = r
        mark = '✓' if ok else '✗'
        print(f"  {str(dp):20} k={k} t=({tDD},{tRC},{tSS}) n_subs={n_subs} {mark}")
        if not ok:
            all_ok = False
            for iss in issues[:3]:
                print(f"    ! {iss}")

    print()
    print(f"RESULT: {'ALL PRIMITIVE FIBER CLASS COUNTS VERIFIED' if all_ok else 'MISMATCHES FOUND'}")


if __name__ == "__main__":
    main()
