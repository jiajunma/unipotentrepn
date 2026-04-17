"""
Numerical verification of the key identity ss = |B- SS| for countPBP_B.

For Type B, the countPBP_B(dp).ss component equals the number of B- PBPs
with tail class SS (x_tau ∈ {s, •} via alpha-corrected tail symbol).

This identity is the crux of the M balanced case proof:
  card(M) = dd + rc
follows from Prop 10.8(b) + B counting theorem + this identity.

Reference: [BMSZb] Proposition 10.9 with gamma-dependent correction rule.
"""

import sys
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from standalone import (  # noqa: E402
    compute_tail_symbol,
    dpart2drc,
    verify_drc,
    _countPBP_B,
)


def classify(x: str) -> str:
    """Tail class: DD if x_tau=d, RC if x_tau in {r,c}, else SS."""
    if x == "d":
        return "DD"
    if x in ("r", "c"):
        return "RC"
    return "SS"


def analyze(dp: tuple) -> dict:
    """Return per-gamma tail class counts and countPBP_B for dp."""
    count_B = _countPBP_B(list(dp))

    is_balanced = False
    if len(dp) >= 2:
        r3 = dp[2] if len(dp) > 2 else 0
        is_balanced = dp[1] <= r3
    k = (dp[0] - dp[1]) // 2 + 1 if len(dp) >= 2 else None

    drcs = dpart2drc(list(dp), rtype="B")
    all_pbps = []
    for drc in drcs:
        if verify_drc(drc, "B+"):
            all_pbps.append((drc, "B+"))
        if verify_drc(drc, "B-"):
            all_pbps.append((drc, "B-"))

    cls_Bp: Counter = Counter()
    cls_Bm: Counter = Counter()
    for drc, gamma in all_pbps:
        x = compute_tail_symbol(drc, gamma, list(dp))
        (cls_Bp if gamma == "B+" else cls_Bm)[x] += 1

    def agg(c: Counter) -> Counter:
        a: Counter = Counter()
        for x, n in c.items():
            a[classify(x)] += n
        return a

    a_Bp, a_Bm = agg(cls_Bp), agg(cls_Bm)
    return {
        "dp": dp,
        "k": k,
        "is_balanced": is_balanced,
        "countPBP_B": count_B,
        "Bp_tc": (a_Bp["DD"], a_Bp["RC"], a_Bp["SS"]),
        "Bm_tc": (a_Bm["DD"], a_Bm["RC"], a_Bm["SS"]),
        "ss_eq_Bm_SS": count_B[2] == a_Bm["SS"],
    }


def main() -> None:
    """Verify ss = |B- SS| over a battery of dual partitions."""
    tests = [
        (2,), (4,), (6,), (8,),
        (4, 2), (6, 2), (6, 4), (8, 2), (8, 4), (8, 6),
        (4, 4), (6, 6),
        (4, 4, 2), (6, 4, 2), (6, 4, 4),
        (6, 6, 2), (6, 6, 4), (6, 6, 6),
        (4, 4, 4, 2), (6, 4, 4, 2), (6, 6, 4, 2),
        (8, 6, 4, 2),
    ]
    all_ok = True
    for dp in tests:
        r = analyze(dp)
        status = "bal " if r["is_balanced"] else "prim"
        ok = "OK" if r["ss_eq_Bm_SS"] else "FAIL"
        print(
            f"{str(dp):16} {status} k={r['k']} "
            f"count={r['countPBP_B']} "
            f"B+={r['Bp_tc']} B-={r['Bm_tc']}  "
            f"ss=|B-SS|? {ok}"
        )
        if not r["ss_eq_Bm_SS"]:
            all_ok = False

    print()
    print("=" * 60)
    print(f"RESULT: {'ALL PASS' if all_ok else 'FAILURES'} — "
          f"ss = |B- SS| verified over {len(tests)} cases")


if __name__ == "__main__":
    main()
