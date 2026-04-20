# Post-Cleanup Status (after deprecated-code deletion)

**Date**: 2026-04-20 late
**Sorries**: 26 (down from 34 via deprecated-file deletion)
**Build**: Green
**Commits since v3.0**: 95+

## Architecture (single source of truth)

```
BijectionSig.lean  — 5 Phi_γ_sig_equiv (permissive MYD_sig)
BijectionQD.lean   — 5 Phi_γ_qd_sig_equiv (QD-restricted, derive from above)

Chain infrastructure (per γ):
├── SigMYD.lean   (D)
├── SigMYDB.lean  (B+/B-)
├── SigMYDC.lean  (C)
└── SigMYDM.lean  (M)

Each chain file contains:
  - IsDescentChain_γ inductive type
  - exists_descentChain_γ (most PROVED)
  - descentChain_γ_singleton (partial PROVED)
  - descentChain_sign_match_γ (D/B+/B- PROVED; C/M base only)
  - descent_step_thetaLift_singleton_γ_std (all 5 PROVED under std)
```

## 26 remaining sorries — concrete classification

### Genuinely needing paper content (16)

**A. §11.5/11.6 chain-std (5 sorries)**:
- `descent_step_thetaLift_singleton` for D (PhiDTyped.lean:128)
- `descent_step_thetaLift_singleton_Bplus` (SigMYDB.lean:122)
- `descent_step_thetaLift_singleton_Bminus` (SigMYDB.lean:313)
- `descent_step_thetaLift_singleton_C` (SigMYDC.lean:191)
- `descent_step_thetaLift_singleton_M` (SigMYDM.lean:186)

All have PROVED `_std` variants. Non-std versions need `chain_sign_bound`
lemma = "along any valid chain, (addp, addn) ≥ 0 at every step".

**B. §11.14 algorithmic surjectivity (5)**:
- `Phi_{D,Bplus,Bminus,C,M}_sig_surjective`

**C. §11.14 dependent sign match (2)**:
- `descentChain_sign_match_C` step case (SigMYDC.lean:248)
- `descentChain_sign_match_M` step case (SigMYDM.lean:234)

Depend on Category A closure.

**D. §11.14 dependent chain singleton (1)**:
- `descentChain_M_singleton` (SigMYDM.lean:195)

Depends on Category A.

**E. §11.14 partial (1)**:
- `descentChain_Bminus_singleton` step case (SigMYDB.lean:332)

Needs base reconciliation (baseILS .Bplus vs .Bminus).

**F. Paper structure (2)**:
- `exists_coherent_dp_C` (SigMYDC.lean:145)
- `exists_coherent_dp_M` (SigMYDM.lean:50)

Questionable — need extra hypothesis or shape restriction.

### FALSE as stated (need statement fix) (10)

**G. Prop 11.15/11.17 (5)**: `Phi_γ_sig_injective` — FALSE for empty shape.
Fix: add `h_ne : μP ≠ ⊥ ∨ μQ ≠ ⊥`.

**H. §9.4 (5)**: `descentChain_γ_parity` — FALSE for non-QD dp.
Fix: add `IsQuasiDistinguished γ dp` hypothesis.

## PROVED (no sorry dependency or only A/B dependencies)

| Theorem | Status |
|---------|--------|
| `descentChain_sign_match_D` | ✅ |
| `descentChain_sign_match_Bplus` | ✅ |
| `descentChain_sign_match_Bminus` | ✅ |
| `descentChain_sign_match_C` base | ✅ |
| `descentChain_sign_match_M` base | ✅ |
| `exists_descentChain_D/Bplus/Bminus` | ✅ |
| `exists_descentChain_C` | ✅ **full** |
| `exists_descentChain_M_coherent / _M` | ✅ **full** |
| `descent_step_thetaLift_singleton_γ_std` (5) | ✅ |
| `descentChain_Bminus_singleton_Bplus_base` | ✅ |
| `descentChain_C_singleton` | ✅ (step depends on A) |
| All 5 `Phi_γ_sig` constructions | ✅ (depend on parity H) |
| All 5 `Psi_γ_sig` (Classical.choose) | ✅ |
| All 5 round trips 1 | ✅ (depend on G injective) |
| All 5 round trips 2 | ✅ (depend on B surjective) |
| All 5 `Phi_γ_sig_equiv` assembly | ✅ |
| All 5 `Phi_γ_qd_sig_equiv` | ✅ (via delegate) |
| `fintype_MYD_sig_γ` (5) | ✅ (depend on equiv) |
| `card_PBPSet_γ_sig_Fin2_eq` (5) | ✅ |

## 5 Critical structural findings (all in memory)

1. `project_descent_structure.md`: [BMSZ] descent = [BMSZb] 𝔴=∅
2. `project_myd_pivot.md`: `MYD γ (dpToSYD γ dp)` empty; use `MYD_sig`
3. `project_chain_step_mismatch.md`: 1-augment vs paper 2-augment
4. `project_parity_requires_quasi_distinguished.md`: parity needs QD
5. `project_phi_injective_not_universal.md`: injective false for empty shape

## Recommended path forward

**Short-term (add hypotheses to fix false theorems, ~50-100 LOC per fix)**:
1. Add `h_ne` to all 5 `Phi_γ_sig_injective`
2. Add `IsQuasiDistinguished` to all 5 `descentChain_γ_parity`
3. Propagate through callers (round-trips, equivs)

Net: 10 false sorries become TRUE theorems (still needing paper proof,
but at least STATEMENT-CORRECT).

**Medium-term (attack paper content, 200-600 LOC per type)**:
1. `chain_sign_bound` lemma (paper §11.5) — unblocks Category A
2. Then Category C (sign match step), D (M singleton)
3. Injectivity bridging (paper Prop 11.15)
4. Surjectivity algorithm (paper §11.14)

**Total estimated**: ~8000 LOC for full closure. Multi-session work.
