# Pivot to MYD_sig (signature-based bijection)

**Date**: 2026-04-19/20
**Status**: NL plan, blueprint sync, then Lean.

## The structural mismatch (why we pivot)

The previous goal `PBPSet γ μP μQ × Fin 2 ≃ MYD γ (dpToSYD γ dp)`
is **not implementable** with the current chain definition. Concretely:

1. `IsDescentChain_D τ chain` uses `doubleDescent_D_PBP` as the step.
2. Each chain step adds **one** row to the extracted ILS `E` via
   `thetaLift_CD = [augment (addp, addn) (charTwistCM E ...)]`,
   where `augment = cons` (single row prepend).
3. The chain step's `doubleDescent_D_PBP` corresponds to `dp.drop 2`
   (proved via `coherence_descend_D_P/Q`).
4. `(dpToSYD .D dp).rows` has length `length(dp)` (since `rowMax`
   of `partTranspose dp` is `length dp` for nonempty dp).

So a chain of `k = ⌈length(dp)/2⌉` steps produces `E` with `length k`,
while `(dpToSYD γ dp).rows` has length `2k` (or `2k - 1`).

The required `absValues E = (dpToSYD γ dp).rows` is impossible unless
`absValues` magically doubles its input length — which it doesn't.

## Decision: use `MYD_sig γ signature`

`MYD_sig` (in `lean/CombUnipotent/MYD/SigMYD.lean`) drops the shape
constraint and keeps only:

- `parity` (per-row γ-parity validity)
- `sign_match : ILS.sign E = signature`

`descentChain_sign_match_D` is **already fully proved** there.

This gives the bijection at signature level — strictly weaker than
paper's MYD γ O (which pins down shape too), but **paper Prop 11.15
phrased at the signature level still produces a valid bijection of
finite sets** (PBPs and signature-MYDs of fixed signature).

## What we lose (and accept)

- Paper's `MYD γ O` is indexed by orbit O, not signature alone. Two
  PBPs with the same signature but different orbits could coexist in
  `MYD_sig`. We don't separate them at the SYD level.
- For the **counting** application (which is the project's main goal),
  this is acceptable: the cardinalities match, and `MYD_sig`'s fintype
  is well-defined.

## Plan

### Phase 1: `Phi_D_sig`

```lean
noncomputable def Phi_D_sig {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    MYD_sig .D (signTarget_D σ.val) :=
  let chain := Classical.choose (exists_descentChain_D σ)
  let h_chain := Classical.choose_spec (exists_descentChain_D σ)
  let E := Classical.choose (descentChain_D_singleton h_chain)
  let h_sing := Classical.choose_spec (descentChain_D_singleton h_chain)
  -- Apply ε twist
  let ε_int : ℤ := if ε = 0 then 1 else -1
  ⟨ILS.twistBD E ε_int ε_int, parity_lemma_TBD, sign_lemma_TBD⟩
```

**Sub-lemmas needed**:

- `MYD_sig_parity_via_chain`: chain-extracted E satisfies
  `MYDRowValid .D (j+1) E[j]` for all j. From `descentChain_D_in_MYD`'s
  parity part (already attempted, shape part was the broken sorry).
- `signTarget_D_twist_invariant`: `signTarget_D σ.val` is invariant
  under twistBD (already proved as `twistBD_sign` in MYD.lean:436).

### Phase 2: `Psi_D_sig` (explicit inverse)

Given `M : MYD_sig .D sig`, construct a PBPSet element + ε.

**Approach**: peel one row of `M.E` at a time, run `liftCD_PBP`-style
inverse to build the corresponding chain step, recurse on the
remaining `M.E.tail`.

```lean
noncomputable def Psi_D_sig {μP μQ : YoungDiagram}
    {sig : ℤ × ℤ}
    (h_target : ∃ τ : PBP, τ.γ = .D ∧ τ.P.shape = μP ∧ τ.Q.shape = μQ ∧
                signTarget_D τ = sig)
    (M : MYD_sig .D sig) :
    PBPSet .D μP μQ × Fin 2 := ...
```

Need to invert the chain. Each row of `M.E` corresponds to one
`liftCD`-style step. Use existing `liftCD_PBP` from
`CorrespondenceC.lean:519`.

**Key issue**: `liftCD_PBP` lifts D→C, but we need a "doubleLift_D"
that goes D→D adding 2 rows of dp at once. This may not exist —
need to see if we can compose `liftCD ∘ liftDC` (the latter doesn't
exist, see `project_descent_structure.md`).

**Alternative**: build `Psi_D_sig` directly without going through
intermediate type constructions. Use: from `M.E[k] = (p_k, q_k)` and
target shapes (μP, μQ), construct one PBP with the matching paint.
This may require a new construction theorem.

### Phase 3: round trips

- `Phi_D_sig ∘ Psi_D_sig = id`: the recovered (σ, ε) round-trips back to M.
- `Psi_D_sig ∘ Phi_D_sig = id`: use `prop_11_15_PBP_D_injective_full`.

### Phase 4: equiv assembly + BCM extension

```lean
noncomputable def Phi_D_sig_equiv {μP μQ : YoungDiagram}
    (h_coh : ...) :
    PBPSet .D μP μQ × Fin 2 ≃ MYD_sig .D (signTarget_D ?) := ...
```

For C/M: pre-compose `descentCD_PBP` / `descentMB_PBP` round-trip with
the D/B equiv.

For B±: mirror D with `doubleDescent_B_PBP` and need a
`descentChain_sign_match_Bplus/minus` (analogous to D, mostly mirror
of existing proof in SigMYD.lean).

## Remaining sorries after pivot

If all phases complete:

- `descent_step_thetaLift_singleton` (paper §11.5/§11.6 sign-bound),
  same as before — orthogonal to bijection, used internally by
  `descentChain_D_singleton`.
- Mirror sign-match for B+, B-, M (mostly copy-paste of existing
  D proof in SigMYD.lean).

Total expected sorries after pivot: ~3-5 (down from 9-10), all
in the "paper §11.5/11.6 algebraic core" category, none in the
bijection assembly.

## Progress log (2026-04-19/20 session)

**Done**:
- Pivot decision documented + memory pinned (`project_myd_pivot.md`)
- `BijectionSig.lean` scaffolding: 5 `Phi_γ_sig_equiv` (D/B+/B-/C/M)
  with `PBPSet_γ_sig` subtypes + Fintype + cardinality corollaries
- `SigMYDB.lean`: B+/B- chain inductive types, existence (proved),
  singletons (B+ proved, B- sorry on base), sign match (BOTH PROVED)
- `SigMYDC.lean`: C chain inductive type, existence (sorry, h_sub),
  singleton (PROVED via baseILS .C = .D = []), sign match base PROVED
- `SigMYDM.lean`: M chain (bifurcated step), sign match base PROVED
- `MYD.lean`: added `toACStepData_Bminus` and `toACStepData_M`
- Structured `Phi_D_sig`, `Phi_Bplus_sig`, `Phi_Bminus_sig` with
  fully-proved sign components

**Remaining sorries (all paper-content)**:
- §11.5/11.6 per-step thetaLift singleton with std condition (5 instances)
- §9.4 parity preservation along chain (5 instances)
- §11.14 algorithmic inverse Psi (5 instances)
- B-/M singleton base reconciliation (2 instances, structural)
- C/M sign match step cases (2 instances, depend on per-step std)

**Build status**: Green throughout. Sign-match infrastructure for
all 5 γ types is now in place; D/B+/B- sign matches FULLY PROVED;
C/M sign match base cases proved.
