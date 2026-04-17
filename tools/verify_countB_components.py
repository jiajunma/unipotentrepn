"""
Verify the combinatorial meaning of countPBP_B(dp) components.

Key questions:
1. What does countPBP_B(dp) = (dd, rc, ss) count at the PBP level?
2. Is it per-γ (e.g., rc = f(B+), ss = f(B-))? per-tail-class combined?
   α-corrected per-tc?
3. What identity closes the B balanced recursion:
   card(B+) + card(B-) on (r1::r2::rest) = dd' * 4k + rc' * (4k-2)
   where (dd', rc', _) = countPBP_B(rest)?

Test hypotheses:
H1: ss = |B- SS_natural| (where SS is x_tau ∈ {•, s}).
H2: dd = combined |DD_natural|.
H3: rc = combined |RC_natural| + |B+ SS_natural with correction to c|.
H4: countPBP_B is stable under a specific α-correction scheme.
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
    getz,
)


def classify_natural(x):
    """Natural tail class from x_tau."""
    if x == "d":
        return "DD"
    if x in ("r", "c"):
        return "RC"
    return "SS"  # s, dot, empty


def get_tail_details(drc, gamma, dpart):
    """Extract tail info: (k_size, q_boundary, correction_applied, x_tau, class)."""
    drcL, drcR = drc
    c1_iota = len(getz(drcL, 0, ""))
    c1_j = len(getz(drcR, 0, ""))
    setA_size = c1_j - c1_iota
    # k - 1 = setA_size, so k = setA_size + 1
    k = setA_size + 1

    if c1_iota > 0 and c1_iota <= c1_j:
        q_c1 = getz(drcR, 0, "")[c1_iota - 1]
    else:
        q_c1 = ""

    # Correction applies when setA_size <= 0 (i.e., k=1) AND boundary in {*, s}
    correction = False
    if setA_size <= 0:
        if c1_iota == 0 or q_c1 in ("*", "s"):
            correction = True

    x_tau = compute_tail_symbol(drc, gamma, list(dpart))
    return k, q_c1, correction, x_tau, classify_natural(x_tau)


def enumerate_pbps(dp):
    """Return list of (drc, gamma, tail_info) for all B PBPs on dp."""
    drcs = dpart2drc(list(dp), rtype="B")
    results = []
    for drc in drcs:
        for gamma in ("B+", "B-"):
            if verify_drc(drc, gamma):
                info = get_tail_details(drc, gamma, dp)
                results.append((drc, gamma, info))
    return results


def analyze(dp):
    """Test all hypotheses for a given dp."""
    count = _countPBP_B(list(dp))
    pbps = enumerate_pbps(dp)

    # Split by gamma and class
    by_key = Counter()
    for _, gamma, (k, q_bd, corr, x, cls) in pbps:
        by_key[(gamma, cls)] += 1
        by_key[(gamma, cls, "corr" if corr else "nocorr")] += 1
        by_key[(gamma, "x", x)] += 1

    # Natural per-tc (symmetric between γ)
    def g(gamma, cls):
        return by_key[(gamma, cls)]

    Bp_dd, Bp_rc, Bp_ss = g("B+", "DD"), g("B+", "RC"), g("B+", "SS")
    Bm_dd, Bm_rc, Bm_ss = g("B-", "DD"), g("B-", "RC"), g("B-", "SS")

    # Check various hypotheses
    h_ss_eq_Bm_SS = count[2] == Bm_ss
    h_dd_eq_combined = count[0] == Bp_dd + Bm_dd
    h_dd_eq_Bm = count[0] == Bm_dd
    h_dd_eq_Bp = count[0] == Bp_dd
    h_rc_eq_combined = count[1] == Bp_rc + Bm_rc
    h_rc_eq_Bp_plus_something = None

    # What is count[1] - combined RC?
    rc_excess = count[1] - (Bp_rc + Bm_rc)

    # Is rc_excess = |B+ with correction (SS→RC)|? (B+ SS nat with correction)
    Bp_ss_corr = sum(1 for _, g_, (_, _, c, _, cl) in pbps
                     if g_ == "B+" and cl == "SS" and c)
    h_rc_excess_eq_Bp_ss_corr = rc_excess == Bp_ss_corr

    # Is ss_deficit = |B+ SS corr|?
    ss_deficit = (Bp_ss + Bm_ss) - count[2]
    h_ss_deficit_eq_Bp_ss_corr = ss_deficit == Bp_ss_corr

    # Top-level k
    if len(dp) >= 2:
        k = (dp[0] - dp[1]) // 2 + 1
        is_bal = dp[1] <= (dp[2] if len(dp) > 2 else 0)
    else:
        k = None
        is_bal = False

    return {
        "dp": dp,
        "k": k,
        "bal": is_bal,
        "count": count,
        "Bp_natural": (Bp_dd, Bp_rc, Bp_ss),
        "Bm_natural": (Bm_dd, Bm_rc, Bm_ss),
        "combined_natural": (Bp_dd + Bm_dd, Bp_rc + Bm_rc, Bp_ss + Bm_ss),
        "Bp_ss_corr": Bp_ss_corr,
        "rc_excess": rc_excess,
        "ss_deficit": ss_deficit,
        "H1_ss=|Bm_SS|": h_ss_eq_Bm_SS,
        "H2_dd=combined": h_dd_eq_combined,
        "H3a_dd=|Bm_DD|": h_dd_eq_Bm,
        "H3b_dd=|Bp_DD|": h_dd_eq_Bp,
        "H4_rc=combined": h_rc_eq_combined,
        "H5_rc-combined=Bp_ss_corr": h_rc_excess_eq_Bp_ss_corr,
        "H6_combined-ss=Bp_ss_corr": h_ss_deficit_eq_Bp_ss_corr,
    }


def main():
    tests = [
        (2,), (4,), (6,), (8,),
        (4, 2), (6, 2), (6, 4), (8, 2), (8, 4), (8, 6),
        (4, 4), (6, 6),
        (4, 4, 2), (6, 4, 2), (6, 4, 4),
        (6, 6, 2), (6, 6, 4), (6, 6, 6),
        (4, 4, 4, 2), (6, 4, 4, 2), (6, 6, 4, 2),
        (8, 6, 4, 2), (8, 8, 6, 4, 2),
    ]
    hyp_keys = [k for k in analyze(tests[0]).keys() if k.startswith("H")]

    for dp in tests:
        r = analyze(dp)
        status = "bal" if r["bal"] else "prim"
        print(f"\n=== dp={dp} k={r['k']} {status} ===")
        print(f"  countPBP_B = {r['count']}")
        print(f"  B+ per-tc:  {r['Bp_natural']}")
        print(f"  B- per-tc:  {r['Bm_natural']}")
        print(f"  combined:   {r['combined_natural']}")
        print(f"  B+_SS_corr: {r['Bp_ss_corr']}")
        print(f"  rc_excess (count.rc - combined.RC) = {r['rc_excess']}")
        print(f"  ss_deficit (combined.SS - count.ss) = {r['ss_deficit']}")
        for hk in hyp_keys:
            print(f"  {hk}: {r[hk]}")


if __name__ == "__main__":
    main()
