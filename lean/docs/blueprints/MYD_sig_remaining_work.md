# MYD_sig: Remaining sorry roadmap

**Date**: 2026-04-20
**Context**: follow-up to `MYD_sig_pivot.md` progress log.

After the multi-commit MYD_sig pivot session, the scaffolding for all 5
`Phi_γ_sig_equiv` is in place. The 34 remaining sorries are paper-content
blockers. This document maps each to specific paper lemmas and indicates
existing Lean infrastructure for bridging.

## Sorry categories

### A. `Phi_*_sig_injective` (5 sorries)

For each γ ∈ {D, B+, B-, C, M}:
```
Function.Injective (fun p => Phi_γ_sig p.1 p.2)
```

**Paper reduction**: Prop 11.15 (D/B±) / 11.17 (C/M).
- D: `prop_11_15_PBP_D_injective_full` (MYD.lean:5034) — full injectivity
  proved at ACResult level with many hypotheses.
- B+/B-: `prop_11_15_PBP_Bplus_complete` / `Bminus_complete` (MYD.lean:5393, 5399)
  — abstract wrappers, same shape as D.

**Bridge needed**:
1. Package chain-extracted `E : ILS` as `L_σ : ACResult = [(1, E)]`
2. Show `h_first₁`: chain-extraction always produces ILS with specific
   first-entry pattern matching `tailSignature_D`. This follows from
   `ILS.thetaLift_CD_first_entry` (MYD.lean:2288) + induction on chain.
3. Show `h_no_det` / `h_no_det'`: uses Lemma 11.11 content.
4. Show `hp_nn`, `hq_nn`, `h_nt`: tail signature non-neg + non-trivial.
   Uses `tailSig_nonneg_D`, `tailSig_fst_zero_iff_tailSymbol_s`.

**Estimated effort**: ~400 lines per type. Reducing one D-type could
serve as template for B+/B- (pure mirror). C/M different structure.

### B. `right_inv` / surjectivity (5 sorries)

For each γ: `Phi_γ_sig (Psi_γ_sig M) = M` for all `M : MYD_sig γ s`.

**Paper reduction**: Lemma 11.14 (algorithmic inverse).

Paper algorithm (from /tmp/bmsz.txt):
1. Base: |Ǒ| ≤ 1 → trivial (Lemma 11.2)
2. Inductive: given `E ∈ MYD_γ(Ǒ)` with `r₂(Ǒ) > r₃(Ǒ)`:
   a. Recover `(τ₀, ε)` from `E(1)` via Lemma 11.2 formula
   b. Compute `E″ ∈ MYD_γ(Ǒ″)` by row-strip formula (eq. 11.14)
   c. Recurse to get `(τ″, ε')` with `L_{τ″} ⊗ (ε', ε') = E″`
   d. Assemble `τ = combine(τ₀, τ″, ε, ε')` via formula 11.13

**Missing Lean infrastructure**:
- Inverse of `liftCD_PBP` at ILS level (peel one row)
- Paper eq. 11.14 formula as a Lean function `E → E″`
- Recursive construction terminating on |Ǒ|

**Alternative**: use abstract `surjectivity_from_counting` (MYD.lean:4866)
which gives surjectivity from injectivity + cardinality witness. Requires
`Fintype.card` equality between `PBPSet_γ_sig × Fin 2` and `MYD_sig γ s`
proved independently.

**Estimated effort**: ~600 lines for algorithmic version; ~200 lines for
cardinality-based if independent MYD counting exists.

### C. `descentChain_*_parity` (5 sorries, step cases)

For each γ: chain-extracted E satisfies `MYDRowValid γ (j+1) E[j]`.

**Paper reduction**: §9.4 theta-lift preserves MYD parity.

**Key subtlety**: the invariant `MYDRowValid γ (j+1) E[j]` appears to NOT
be directly inductively preserved by chain steps (positions shift,
forcing different ℓ). Needs a "row-paired" formulation OR paper's exact
§9.4 argument using thetaLift's specific (addp, addn) values.

For `γ = D`:
- Base case: E = [], vacuous. ✓
- Step case: E_outer = twistBD(augment(addp, addn)(charTwistCM E_inner ...))
  - Position 0 of E_outer: (addp, addn), ℓ=1, vacuous for D (forced at even ℓ)
  - Position k ≥ 1: shifted from E_inner, needs parity at NEW ℓ=k+1
  - Inductive invariant mismatch: IH at E_inner[k-1] checks ℓ=k (old), not k+1 (new)

**Fix**: reformulate as forward invariant over chain length, using
specific paper §9.4 relations between (addp, addn) and sign/firstColSign.

**Estimated effort**: ~300 lines if inductive invariant can be fixed;
~600 lines if requires full paper §9.4 algebraic argument.

### D. `descent_step_thetaLift_singleton_*` (3 sorries)

For D, B+, B-: each chain step's thetaLift is a singleton (not empty, not split).

**Paper reduction**: §11.5/§11.6 sign bound (Lemma 11.5 + 11.6).

**Content**:
- thetaLift_CD produces singleton iff std case (`addp ≥ 0 ∧ addn ≥ 0`)
- std case follows from sign bound on chain ILS (paper §11.5)
- Specifically: `sign(E_inner) ≤ signTarget` component-wise implies `addp, addn ≥ 0`
  where `signTarget = (p, q)` from chain step's PBP.

**Key Lean lemma needed**:
```
theorem chain_sign_bound (chain : List ACStepData) (E : ILS)
    (h : IsDescentChain_γ τ chain) (h_sing : ChainSingleton ... E) :
    ILS.sign E ≤ componentwise signTarget_γ τ
```
This is then combined with `firstColSign` bounds to get std.

**Estimated effort**: ~200 lines. Shared across D/B+/B- (single generic lemma
via target-type parameter).

### E. Structural: B-/M singleton base reconciliation (3 sorries)

For Bminus/M chain: inner chain (B+ or B-) has different `baseILS` than
outer chain. Step case requires threading through the base transition.

**Fix 1**: generalize `ChainSingleton` to take arbitrary starting ILS
(not just `baseILS γ`). This allows inner chain's base to be `baseILS .Bplus`
while outer processes from `baseILS .Bminus` via a "base-translation" step.

**Fix 2**: separate empty and non-empty PBP cases at the IsDescentChain
level. Empty has `base = γ_original`; non-empty has `base = γ_descended`.

**Estimated effort**: Fix 1 is ~150 lines (API change); Fix 2 is ~200 lines
(case splitting).

### F. C/M sign match step cases (2 sorries)

`descentChain_sign_match_C/M` step case depends on:
- thetaLift_DC_sign (needs std hypothesis) — but sorry on per-step std
- thetaLift_BM_sign (for M-step, goes to B)

**Depends on category D** (per-step singleton + std).

### G. `exists_descentChain_C/M` (2 sorries)

Need witness for `h_sub : shiftLeft μQ ≤ μP` for C chain existence.

**Existing infra**: `shiftLeft_Q_le_P_of_dp` in CorrespondenceC.lean:88
establishes this under (dp-coherence + sort + odd). For generic PBP,
need to thread dp coherence through PBPSet.

**Estimated effort**: ~100 lines. Mostly bookkeeping.

## Prioritized next actions

1. **Category G** (~100 lines, shallow) — quickest win for `exists_descentChain_C/M`.
2. **Category D** (~200 lines, shared) — single lemma enables 3 sorries.
3. **Category F** (~50 lines, downstream of D) — quick after D.
4. **Category C** (~300 lines) — substantial but concrete algebraic argument.
5. **Category A** (~400 lines per type) — most substantial single task.
6. **Category B** (~600 lines) — paper algorithm implementation.
7. **Category E** (~150 lines) — API refactor.

Total: ~2500 lines of focused formalization to fully close all sorries.

## Current status

- Scaffolding: ✅ complete for all 5 types
- Sign matches proved: D ✅, B+ ✅, B- ✅, C/M base ✅
- Round trip 1: all 5 PROVED (modulo Phi_*_sig_injective)
- Round trip 2: all 5 sorry (paper §11.14)
- Parity: all 5 base proved, step sorry
- Build: GREEN throughout
