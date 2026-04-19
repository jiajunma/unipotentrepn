# Option A: paper-aligned alternating-type descent chain

**Date**: 2026-04-19
**Status**: NL plan (per workflow rule: NL proof → blueprint → Lean)
**Decision**: chosen over Options B/C/D for maximum paper fidelity.

## Paper framework (verbatim from [BMSZ] §10 + §11)

Paper's PBP descent alternates types:
- **D ↔ C** pair: single-descent $\nabla_D : \PBP_D(\check{O}) \to \PBP_C(\check{O}_{DC})$
  and $\nabla_C : \PBP_C \to \PBP_D$.
- **B ↔ M** pair: similarly.

Each single descent corresponds to **ONE** theta-lift, adding **ONE**
row to the MYD via augment. Chain length = number of descent levels =
paper's orbit row count.

## Existing infrastructure in repo

Already present:
- `descentPaintL_DC`, `descentPaintR_DC` (Descent.lean:116, 122)
- `descentPaintL_CD`, `descentPaintR_CD` (Descent.lean:131, 139)
- `descentPaintL_BM`, `_R_BM`, `_L_MB`, `_R_MB` (B/M variants)
- `descentType γ` function: returns C/D/M/Bplus alternation (Descent.lean:180)

**Missing**:
- Single-descent PBP constructors: `singleDescent_DC_PBP`,
  `singleDescent_CD_PBP`, `singleDescent_BM_PBP`, `singleDescent_MB_PBP`
  (only `doubleDescent_*_PBP` exists = composition of two singles)
- `toACStepData_DC/CD/BM/MB` for single-step data (only
  `toACStepData_D/Bplus/C/M` exist)

## Plan

### Step 1: Single-descent PBP constructors

For each direction (DC, CD, BM, MB), define:
```lean
noncomputable def singleDescent_DC_PBP (τ : PBP) (hγ : τ.γ = .D) : PBP where
  γ := .C
  P := { shape := ..., paint := descentPaintL_DC τ, paint_outside := ... }
  Q := { shape := ..., paint := descentPaintR_DC τ, paint_outside := ... }
  -- 13 PBP constraints to discharge
```

Shape: for D → C, the new shapes are derived from τ's shapes via
paper's formulas (Section 10.1 of [BMSZb]). For D-type τ with
`μP.colLens = dpartColLensP_D dp = [c_1, c_2, ...]`, the descended
τ_C has `μP.colLens` related to `c_2`-based data (odd-length handling).

**Note**: existing `doubleDescent_D_PBP` = `singleDescent_CD_PBP ∘ singleDescent_DC_PBP`.
We can verify: doubleDescent τ = singleDescent_CD (singleDescent_DC τ).

### Step 2: Alternating `IsDescentChain`

```lean
inductive IsDescentChain : PBP → List ACStepData → Prop
  | base_D (τ : PBP) (hγ : τ.γ = .D) (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain τ []
  | base_C (τ : PBP) (hγ : τ.γ = .C) (h_empty : ...) :
      IsDescentChain τ []
  -- ... similar for B/M bases
  | step_DC {τ : PBP} (hγ : τ.γ = .D) {chain}
      (h_rest : IsDescentChain (singleDescent_DC_PBP τ hγ) chain) :
      IsDescentChain τ (chain ++ [toACStepData_DC τ hγ])
  | step_CD {τ : PBP} (hγ : τ.γ = .C) {chain}
      (h_rest : IsDescentChain (singleDescent_CD_PBP τ hγ) chain) :
      IsDescentChain τ (chain ++ [toACStepData_CD τ hγ])
  -- similar for BM, MB
```

Chain alternates: `D, C, D, C, ..., base`. Length = paper's chain length =
number of orbit row-length classes.

### Step 3: Sign match (analogous to current `descentChain_sign_match_D`)

For each γ-base, prove:
```lean
theorem descentChain_sign_match (τ : PBP) (chain : List ACStepData)
    (E : ILS) (h : IsDescentChain τ chain)
    (h_sing : ChainSingleton (baseILS τ.γ) chain E) :
    ILS.sign E = signTarget τ
```

Similar structure to current proof, but each step uses the appropriate
single theta-lift (CD, DC, BM, or MB). Each has its own sign lemma
already in MYD.lean:
- `ILS.thetaLift_CD_sign` (MYD.lean:564)
- `ILS.thetaLift_DC_sign_split` (MYD.lean:611)
- `ILS.thetaLift_MB_sign` (MYD.lean:655)
- `ILS.thetaLift_BM_sign_split` (MYD.lean:668)

### Step 4: Shape match

Now with corrected chain, `E.length = orbit.rows.length`, so
`absValues E = O.rows` becomes a tractable invariant. Step case:
- IH: `absValues E_mid = O_mid.rows`
- Step: `absValues E = (new_row) :: absValues E_mid = (new_row) :: O_mid.rows`
- Need: `O_outer.rows = (new_row) :: O_mid.rows`

Here `O_outer = dpToSYD of_τ_shape` and `O_mid = dpToSYD of_τ'_shape`,
where τ' = `singleDescent τ`. After ONE single descent, the dp at the
orbit level shifts (paper §9.2, but for single-descent the shift is
cleaner than double).

**This requires**: proving `dpToSYD .γ dp_outer .rows = (new_row) :: dpToSYD .γ_descent dp_inner .rows`
for the single-descent pair (dp_outer, dp_inner). This is a
combinatorial fact about `partTranspose + rowMultiplicities` under
single-row removal.

## Scope

**Phase 1 (next session, 1-2 sessions)**: build single-descent
PBP constructors (4 directions). Verify
`doubleDescent_D_PBP = singleDescent_CD_PBP ∘ singleDescent_DC_PBP`.

**Phase 2**: refactor `IsDescentChain_D` to
`IsDescentChain` (alternating types). Redo `descentChain_sign_match`.

**Phase 3**: prove shape match via `dpToSYD` single-descent relation.

**Phase 4**: assemble `Phi_D_equiv` + extend to B/C/M.

Each phase is a separate session. Phase 1 is mostly mechanical
(shape + 13 PBP constraints per direction); Phases 2-4 have real
math content.

## Remaining sorries after Option A

If all 4 phases complete:
- `descent_step_thetaLift_singleton` — still paper §11.5/11.6 (sign bound)
- Main result: `Phi_D_equiv` = `Equiv.ofBijective` composition of
  injectivity (existing `prop_11_15_PBP_D_injective_full`) + chain
  surjectivity (new, from single-descent chain + explicit Psi).

No orbit-descent Lemma 9.2 needed (avoided via single-descent structure).

## Review of NL plan

**Pass 1 (correctness)**: Single-descent PBP exists in paper, matches
`descentPaint*` primitives. Chain alternation matches paper's chain
structure. Sign preservation uses existing thetaLift_*_sign lemmas. ✓

**Pass 2 (feasibility)**: Phase 1 (constructors) similar in size to
existing `doubleDescent_D_PBP` × 4. Phase 2-3 leverage existing
sub-lemmas (snoc_inv, coherence_descend_D_P/Q, twistBD_* preservations).
Phase 4 is assembly. Each phase ~1 session. ✓

**Pass 3 (scope)**: 4 new constructors + 1 refactored chain + shape
proofs. Larger than current `doubleDescent` infrastructure but
paper-faithful. ✓

**Verdict**: proceed to Phase 1 after user approval.
