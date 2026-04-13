# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

### Priority 1: Lemma 11.5 — Two-step AC formula
File: `CombUnipotent/MYD.lean`

Prove that applying AC recursion (11.2) twice yields formula (11.11):
```
L_τ = T^{γ_τ}(L_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)
```

Operation order (⊗ always last):
1. L_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) — sign twist
2. · ⊕ (n₀, n₀) — augment
3. T^{γ_τ}(·) — character twist
4. · ⊕ (p_{τ_t}, q_{τ_t}) — augment
5. · ⊗ (0, ε_τ) — sign twist (LAST)

Key ingredients already proved:
- `signature_fst_decomp_D` / `signature_snd_decomp_D`: signature decomposition (Eq 11.7)
- `AC.step`: one-step AC recursion
- `ILS.thetaLift_{DC,CD}`: theta lift formulas
- `ILS.charTwistCM_sign`, `ILS.twistBD_sign`: twists preserve signature

n₀ = (c₁(O') - c₂(O'))/2 computationally verified.

### Priority 2: Fill AC.step_multiplicityFree_BD sorry
File: `CombUnipotent/MYD.lean` line ~1192

Needs Lemma 11.5 to prove multiplicity-free preservation under AC.step.

### Priority 3: Lemma 11.6 — First entry of L_τ
Depends on Lemma 11.5. Direct read-off from formula (11.11).

## Background

Paper: `papers/BMSZ_construction_unitarity.pdf` Section 11 (pages 61-72).
Blueprint: `docs/blueprints/section11_complete.md`
Blueprint (LaTeX): `blueprint/src/content.tex`

All orbit-level arithmetic is already formalized in `CombUnipotent/Tail.lean`.
