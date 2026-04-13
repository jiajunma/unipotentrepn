# User Hints

## Critical: Paper reference
The paper is at `papers/BMSZ_construction_unitarity.pdf`. Section 11, pages 61-72.
The companion paper [BMSZb] is at `papers/BMSZ_counting_reduction_v4.pdf`.

## Blueprint files
- `docs/blueprints/section11_complete.md` — overview of all theorems
- `docs/blueprints/lemma_11_5_detailed.md` — detailed proof of Lemma 11.5
- `docs/blueprints/section11_proofs_11_9_to_11_17.md` — proofs of downstream theorems
- `blueprint/src/content.tex` — LeanBlueprint LaTeX source

## Key formula verified computationally
Formula (11.11) operation order: ⊗ (sign twist/tensor) ALWAYS acts LAST.
```
L_τ = T^{γ_τ}(L_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)
```
Steps: twist → augment(n₀) → T^γ → augment(p_t,q_t) → twist(0,ε_τ)
Verified on ALL D-type test orbits via Python (see lemma_11_5_detailed.md).

## Existing infrastructure (already proved, 0 sorry)
- `signature_fst_decomp_D`, `signature_snd_decomp_D`: Prop 11.4, signature decomposition
- `charTwistCM_sign`, `twistBD_sign`: twists preserve sign
- `charTwistCM_involutive`, `twistBD_involutive`: T²=id, twist involution
- `thetaLift_{CD,DC,MB,BM}_sign_{,std,split}`: theta lift sign matching
- `AC.step_sign_{D,Bplus,Bminus,C,M}`: AC step sign for all types
- `AC.base_multiplicityFree`, `ACResult.{twistBD,charTwistCM,augment}_multiplicityFree`
- `tail_all_s_of_tailSymbol_s`, `tailSymbol_d_iff_d_in_col0`

## Lemma 11.3(c) — SKIP
q_{τ_t} = 0 iff x_τ = r — this claim needs refinement. Skip it.
Does NOT affect downstream proofs (verified).
