# Hypothesis Discharge Plan

**Status**: MYD_sig bijection layer has 0 sorries but takes **11 paper-content hypotheses** on `Phi_γ_sig_equiv`. This plan enumerates concrete work to discharge each, yielding unconditional bijection theorems.

**Total estimated effort**: ~1600 LOC across 5 focused sessions.

---

## Current hypotheses (by γ)

| γ | Hypotheses | Paper reference |
|---|-----|-----|
| D | `h_step_D`, `h_inj`, `h_surj` | §11.5/§11.6, Prop 11.15, §11.14 |
| B⁺ | `h_step_Bplus`, `h_inj`, `h_surj` | §11.5/§11.6, Prop 11.15, §11.14 |
| B⁻ | `h_sing_Bminus`, `h_inj`, `h_surj` | §11.5/§11.6 + base recon, Prop 11.15, §11.14 |
| C | `h_step_D`, `h_step_C`, `h_chain_C`, `h_sm_C`, `h_inj`, `h_surj` | §11.5/§11.6, §9.4, Prop 11.17, §11.14 |
| M | `h_chain_M`, `h_sing_M`, `h_sm_M`, `h_inj`, `h_surj` | §11.5/§11.6 + base recon, §9.4, Prop 11.17, §11.14 |

---

## PHASE A — chain-existence (~150 LOC, 1 session)

**Goal**: discharge `ChainExists_C`, `ChainExists_M`.

### A.1 PBP → DualPart reconstruction

For any PBP σ with γ = C (resp. M), extract the dual partition from column shapes:

```lean
def PBP.toDualPart_C (τ : PBP) (hγ : τ.γ = .C) : DualPart := ...
-- With properties:
--   colLens τ.P.shape = dpartColLensP_C (toDualPart_C τ)
--   colLens τ.Q.shape = dpartColLensQ_C (toDualPart_C τ)
--   (toDualPart_C τ).SortedGE
--   ∀ r ∈ toDualPart_C τ, Odd r
```

Same for M (with `Even` instead of `Odd`).

### A.2 Assemble ChainExists_{C,M}

```lean
theorem chainExists_C_of_pbp_dp : ChainExists_C μP μQ := by
  intro σ
  exact exists_descentChain_C σ (PBP.toDualPart_C σ.val σ.prop.1) ...
```

**Files**: new `PBPToDualPart.lean` (~120 LOC) + add theorems to `SigMYDC/M.lean` (~30 LOC).

**Blockers**: need to show column-length construction is well-defined on PBP.

---

## PHASE B — per-step singleton (~400 LOC, 1-2 sessions)

**Goal**: discharge `DescentStepSingleton_{D, B+, B-, C, M}`.

**Key insight**: Reductions `descentStepSingleton_γ_of_std` already exist (D, B+, B-, C). Reduces problem to proving universal std sign-bound.

### B.1 Universal std bound

```lean
theorem std_bound_D : ∀ (τ : PBP) (hγ : τ.γ = .D) (E_inner : ILS),
  (toACStepData_D τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2 ≥ 0 ∧
  (toACStepData_D τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1 ≥ 0 := by
  sorry  -- paper §11.5/§11.6
```

This **cannot be universally true** — it depends on E_inner. The right statement is CHAIN-CONDITIONAL:

### B.2 Chain-conditional std + refactor of current hypothesis

Need to REFORMULATE `DescentStepSingleton_γ` to only quantify over E_inner that arises from a valid chain. Options:

**Option 1**: Add chain-validity hypothesis:
```lean
abbrev DescentStepSingleton_D' : Prop :=
  ∀ (τ_outer : PBP) (hγ : τ_outer.γ = .D)
    (τ_inner : PBP) (h_desc : descentDD_PBP τ_outer hγ = τ_inner)
    (chain : List ACStepData) (h_chain : IsDescentChain_D τ_inner chain)
    (E_inner : ILS) (h_sing : ChainSingleton (baseILS .D) chain E_inner),
    ∃ E', thetaLift ... = [E']
```

This makes the hypothesis chain-restricted and thus discharging is about chain-invariant sign bound.

**Option 2**: Prove the current (too-strong) hypothesis by showing std holds for ALL E_inner when PBP is "well-formed" (dp-coherent). Needs inventory of what E_inner values arise in practice.

**Recommendation**: Option 1. Requires refactor of current `DescentStepSingleton_γ` → `DescentStepSingleton_γ'` with chain-validity. Cost: ~100 LOC refactor + ~300 LOC proof of std invariant using:
- `ILS.thetaLift_CD_first_entry` (MYD.lean:2288)
- `sign_cons_nonneg`, `firstColSign` invariants
- Chain-step signature decomposition (paper Prop 11.4)

### B.3 Downstream: sign match

`DescentChainSignMatch_{C,M}` discharged via `thetaLift_DC_sign_std` / `thetaLift_BM_sign_std` under the std bound from B.2. ~50 LOC.

---

## PHASE C — injectivity bridge (~400 LOC, 1 session)

**Goal**: discharge `h_inj` for all γ.

**Core paper result**: `prop_11_15_PBP_D_injective_full` (MYD.lean:5034) is already proved for D. Takes ACResult-level hypotheses.

### C.1 ACResult bridge

Show that `Phi_D_sig σh ε` corresponds to ACResult `[(1, E_twisted)]`:

```lean
theorem Phi_D_sig_to_ACResult (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    ∃ L : ACResult, L = [(1, (Phi_D_sig h_step σh ε).1)] ∧ ... := ...
```

### C.2 Instantiate prop_11_15_PBP_D_injective_full

Given `Phi_D_sig h_step σh₁ ε₁ = Phi_D_sig h_step σh₂ ε₂`:
1. Extract E₁, E₂ ILS.
2. Package as L₁ = [(1, E₁_pre_twist)], L₂ = [(1, E₂_pre_twist)].
3. Apply twist-equality equivalence.
4. Invoke `prop_11_15_PBP_D_injective_full` with `h_first`, `hp_nn`, `hq_nn`, `h_nt` (these follow from chain-extraction properties).
5. Conclude σ₁ = σ₂ and ε₁ = ε₂.

**Blockers**: The `h_first`, `hp_nn`, `hq_nn`, `h_nt` hypotheses require chain-invariant reasoning — overlaps with Phase B's chain-wise analysis.

### C.3 B⁺/B⁻/C/M mirrors

Same pattern for B+ (mirror of D), B- (mirror of D), C/M (Prop 11.17). ~80 LOC each.

**Total**: ~400 LOC across 5 types.

---

## PHASE D — surjectivity algorithm (~500 LOC, 1-2 sessions)

**Goal**: discharge `h_surj` for all γ.

**Paper §11.14**: given M : MYD_sig γ s, construct a PBP σ + ε with `Phi_γ_sig σ ε = M`.

Paper's algorithm: row-peel the ILS from top, recursively constructing dp and PBP.

### D.1 ILS → dp inversion

```lean
def ILS.toDualPart (E : ILS) (γ : RootType) (parity : ...) : DualPart := ...
```

### D.2 ILS → PBP construction

```lean
def ILS.toPBP (E : ILS) (μP μQ : YoungDiagram) (γ : RootType) : Option PBP := ...
-- Verifies shape matches μP, μQ; produces canonical PBP.
```

### D.3 Surjectivity proof

Show `Phi_γ_sig (ILS.toPBP E ...) ε = ⟨E, h_sign⟩` for some ε. ~200 LOC per type.

**Complexity**: most substantial phase. Not a simple reduction — genuine algorithmic content.

---

## PHASE E — Bminus/M base reconciliation (~150 LOC, 1 session)

**Goal**: discharge `DescentChainBminusSingleton`, `DescentChainMSingleton`.

**Issue**: `baseILS .Bminus = [(0, -1)]` ≠ `baseILS .Bplus = [(1, 0)]`. The inner Bplus chain under `doubleDescent_B` starts from `baseILS .Bplus`, but Phi_Bminus expects `baseILS .Bminus`.

**Strategy**: prove that the FIRST step of a Bminus chain specifically takes `baseILS .Bminus` to `baseILS .Bplus`-adjacent data via a twist. Formally:

```lean
theorem descentChain_Bminus_singleton_main (h_step_Bminus h_step_Bplus : ...) :
    DescentChainBminusSingleton := by
  intro τ chain h_chain
  cases h_chain with
  | base ... => ⟨baseILS .Bminus, ChainSingleton.nil _⟩
  | step hγ h_rest =>
    -- Key lemma: first thetaLift from baseILS .Bminus
    -- produces E equivalent to baseILS .Bplus post-twist.
    sorry  -- paper §11.3 + twistBD analysis
```

Requires: per-step first-thetaLift lemma (paper §11.3 on Mp ↔ Bminus correspondence). ~100 LOC.

Same for M. ~50 LOC.

---

## RECOMMENDED EXECUTION ORDER

| Phase | Effort | Prereq | Benefit |
|---|---|---|---|
| **A** (chain existence) | ~150 LOC | none | Discharges 2 hypotheses; simplifies C/M signatures |
| **B.1/B.2** (std bound) | ~400 LOC | chain-refactor | Discharges 4 step-singleton + 2 sign-match |
| **C** (injectivity bridge) | ~400 LOC | none | Discharges 5 injectivity hypotheses |
| **E** (base reconciliation) | ~150 LOC | B.1 | Discharges 2 bundled singleton hypotheses |
| **D** (surjectivity algorithm) | ~500 LOC | C | Discharges 5 surjectivity hypotheses |

**Total**: ~1600 LOC.

**Ordering rationale**:
- A is quick and independent — good warm-up.
- B needs refactor first; once refactored, C can proceed in parallel.
- E depends on B (both need std invariants).
- D is last — most substantial and requires C infrastructure.

---

## IMMEDIATE NEXT STEP (this session)

Start **Phase A** — construct `PBP.toDualPart_C` and `PBP.toDualPart_M`, then derive `ChainExists_C`/`_M` theorems. This is the smallest standalone win and demonstrates the discharge pattern.

Concrete deliverable:
- New file: `CombUnipotent/MYD/PBPToDualPart.lean` (~120 LOC)
- Updated `SigMYDC.lean`: `theorem chainExists_C : ChainExists_C μP μQ` (~15 LOC)
- Updated `SigMYDM.lean`: same for M (~15 LOC)
- 2 fewer hypotheses required by `Phi_{C,M}_sig_equiv` callers.
