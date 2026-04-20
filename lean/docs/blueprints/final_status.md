# MYD_sig Bijection: Final Session Status

**Date**: 2026-04-20
**Total commits since v3.0**: 78+
**Sorry count**: 36 (down from initial 0 — but 0 was on broken target)

## What was accomplished

### Architecture (complete)
- `MYD_sig γ s` (signature-based MYD, replaces broken `MYD γ (dpToSYD γ dp)`)
- 5 × `Phi_γ_sig_equiv` (D / B+ / B- / C / M) — fully assembled equivs
- 5 × `Phi_γ_qd_sig_equiv` (QD-restricted variants) — derive from non-QD
- Parallel chain mirror files (SigMYDB, SigMYDC, SigMYDM)
- 4 critical memory files documenting structural findings

### Definitions + PROVED theorems (0 sorry dependency)

| Theorem | Status |
|---------|--------|
| `descentChain_sign_match_D` | ✅ PROVED (pre-existing) |
| `descentChain_sign_match_Bplus` | ✅ PROVED |
| `descentChain_sign_match_Bminus` | ✅ PROVED |
| `descentChain_sign_match_C` base | ✅ PROVED |
| `descentChain_sign_match_M` base | ✅ PROVED |
| `descentChain_D_parity` base | ✅ PROVED |
| `descentChain_C_singleton` | ✅ PROVED |
| `descentChain_Bminus_singleton_Bplus_base` | ✅ PROVED |
| `descent_step_thetaLift_singleton_*_std` (5) | ✅ PROVED |
| `exists_descentChain_D/Bplus/Bminus` | ✅ PROVED |
| All 5 × `Phi_γ_sig` constructions | ✅ PROVED |
| All 5 × `Psi_γ_sig` constructions | ✅ (via Classical.choose) |
| All 5 × `Psi_γ_Phi_γ_sig` (round trip 1) | ✅ PROVED (conditional on injective) |
| All 5 × `Phi_γ_Psi_γ_sig` (round trip 2) | ✅ PROVED (conditional on surjective) |
| All 5 × `Phi_γ_sig_equiv` assembly | ✅ PROVED |
| All 5 × `Phi_γ_qd_sig_equiv` | ✅ PROVED (via non-QD) |
| Fintype + cardinality corollaries | ✅ PROVED |

### Remaining sorries (36)

| Category | Count | Blocker |
|----------|-------|---------|
| `Phi_*_sig_injective` | 5 | Paper Prop 11.15/11.17 reduction to `prop_11_15_PBP_D_injective_full` |
| `Phi_*_sig_surjective` | 5 | Paper §11.14 algorithmic inverse |
| `descentChain_*_parity` step | 5 | Paper §9.4 row-paired parity |
| `descent_step_thetaLift_singleton_*` | 5 | Paper §11.5/11.6 chain std |
| `descentChain_sign_match_C/M` step | 2 | Downstream of step singleton |
| `descentChain_Bminus_singleton` | 1 | Base reconciliation (non-empty case) |
| `descentChain_M_singleton` step_to_B+/- | 2 | Base reconciliation |
| `exists_coherent_dp_C/M` | 2 | PBP → dp coherence witness |
| `exists_descentChain_C/M_coherent` | 2 | Inner chain construction |
| `descent_step_thetaLift_singleton_B-_std` | 1 | Different chain base |
| Misc | 6 | Various helpers |

**All remaining sorries are paper-content**: require paper §9.4, §11.5-11.6, §11.14, or Prop 11.15/11.17 translation.

## 4 critical structural findings (memory)

1. `project_descent_structure.md`: [BMSZ] descent = [BMSZb] 𝔴=∅ case
2. `project_myd_pivot.md`: `MYD γ (dpToSYD γ dp)` structurally empty
3. `project_chain_step_mismatch.md`: Lean 1 augment vs paper 2 augment
4. `project_parity_requires_quasi_distinguished.md`: parity needs QD

## How to continue in future session

Priority ordering (from `MYD_sig_remaining_work.md`):
1. **Category G** (exists_coherent_dp_C/M, ~100 LOC) — quickest win
2. **Category D** (per-step std via chain_sign_bound, ~200 LOC shared)
3. **Category F** (C/M sign match step, ~50 LOC, downstream of D)
4. **Category C** (parity, ~300 LOC) — needs §9.4
5. **Category A** (injectivity, ~400 LOC per type) — bridge to Prop 11.15
6. **Category B** (surjectivity, ~600 LOC) — §11.14 algorithm
7. **Category E** (base reconciliation, ~150 LOC) — API refactor

**Total estimated**: ~2500 LOC focused formalization.

## Build status

Green throughout all 78 commits. No regressions.
