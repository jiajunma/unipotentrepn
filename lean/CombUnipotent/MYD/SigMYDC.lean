/-
# C-type chain infrastructure for `MYD_sig .C`

Mirror of `IsDescentChain_Bminus` for C type: one outer C step
(via `descentCD_PBP`) followed by an inner D-chain.

Reference: `lean/CombUnipotent/MYD/SigMYD.lean` (D template),
`lean/CombUnipotent/MYD/SigMYDB.lean` (Bminus template).
-/
import CombUnipotent.MYD.SigMYD
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.CorrespondenceC
import CombUnipotent.CountingProof.Basic

namespace BMSZ

open PBPInstantiation (toACStepData_C)

/-! ## C chain inductive type

The chain steps from outer C-type τ to base via:
  - outer step: descentCD_PBP (C → D, requires `shiftLeft τ.Q.shape ≤ τ.P.shape`)
  - inner: IsDescentChain_D on the descended D-type PBP
-/

/-- Descent chain predicate for C type. -/
inductive IsDescentChain_C : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .C)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_C τ []
  | step {τ : PBP} (hγ : τ.γ = .C) (wp : PPSet) {chain : List ACStepData}
      (h_sub : YoungDiagram.shiftLeft τ.Q.shape ≤ τ.P.shape)
      (h_rest : IsDescentChain_D
        (descentCD_PBP ⟨τ, hγ, rfl, rfl⟩ h_sub).val chain) :
      IsDescentChain_C τ (chain ++ [toACStepData_C τ hγ wp])

/-! ## Existence with dp-coherence hypothesis

The chain existence requires, at each level, a witness for
`shiftLeft τ.Q.shape ≤ τ.P.shape` (needed by `descentCD_PBP`).
This is available from dp-coherence (`shiftLeft_Q_le_P_of_dp` in
CorrespondenceC.lean) when dp is sorted + odd. We parameterize
the theorem on the coherence package.
-/

/-- C-type PBP dp coherence. -/
def PBPIsCoherent_C (τ : PBP) (dp : DualPart) : Prop :=
  τ.P.shape.colLens = dpartColLensP_C dp ∧
  τ.Q.shape.colLens = dpartColLensQ_C dp

/-- Helper: for C-PBP coherent with empty dp, shapes are empty. -/
private theorem PBPIsCoherent_C_empty {τ : PBP} (h_coh : PBPIsCoherent_C τ []) :
    τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥ := by
  obtain ⟨hP, hQ⟩ := h_coh
  simp [dpartColLensP_C, dpartColLensQ_C] at hP hQ
  exact ⟨yd_of_colLens_nil hP, yd_of_colLens_nil hQ⟩

/-- Chain existence for C-type PBP under dp-coherence + sort + odd. -/
theorem exists_descentChain_C {μP μQ : YoungDiagram} (σ : PBPSet .C μP μQ)
    (dp : DualPart) (h_coh : PBPIsCoherent_C σ.val dp)
    (hsort : dp.SortedGE) (hodd : ∀ r ∈ dp, Odd r) :
    ∃ c : List ACStepData, IsDescentChain_C σ.val c := by
  match dp, h_coh, hsort, hodd with
  | [], h_coh, _, _ =>
    -- Empty dp → empty shapes → base chain
    have hγ : σ.val.γ = .C := σ.prop.1
    have h_empty := PBPIsCoherent_C_empty h_coh
    exact ⟨[], IsDescentChain_C.base σ.val hγ h_empty⟩
  | [r], h_coh, _, hodd =>
    -- Single-element dp:
    --   dpartColLensP_C [r] = [] → μP is ⊥
    --   dpartColLensQ_C [r] = if r > 1 then [(r-1)/2] else []
    -- For r = 1 (odd, sorted): both shapes empty → base case.
    -- For r ≥ 3 (odd): μQ has 1 column, shiftLeft μQ = ⊥ ≤ μP,
    --   descentCD_PBP → D-PBP with empty shapes → inner chain = [].
    have hγ : σ.val.γ = .C := σ.prop.1
    have hr_odd : Odd r := hodd r (by simp)
    have hP_empty : μP = ⊥ := by
      have hP_nil : μP.colLens = [] := by
        rw [← σ.prop.2.1]; simp [h_coh.1, dpartColLensP_C]
      exact yd_of_colLens_nil hP_nil
    by_cases hr : r = 1
    · -- r = 1: μQ also empty
      have hQ_empty : μQ = ⊥ := by
        have hQ_nil : μQ.colLens = [] := by
          rw [← σ.prop.2.2]; simp [h_coh.2, dpartColLensQ_C, hr]
        exact yd_of_colLens_nil hQ_nil
      have h_empty : σ.val.P.shape = ⊥ ∧ σ.val.Q.shape = ⊥ :=
        ⟨σ.prop.2.1.trans hP_empty, σ.prop.2.2.trans hQ_empty⟩
      exact ⟨[], IsDescentChain_C.base σ.val hγ h_empty⟩
    · -- r ≥ 3 (odd): μQ has 1 col of height (r-1)/2, shiftLeft μQ = ⊥
      have hr_gt : r > 1 := by
        -- r odd and r ≠ 1: must have r ≥ 3 > 1
        rcases hr_odd with ⟨k, hk⟩
        omega
      have hshQ_empty : YoungDiagram.shiftLeft μQ = ⊥ := by
        have hQ_colLens : μQ.colLens = [(r-1)/2] := by
          rw [← σ.prop.2.2]
          simp [h_coh.2, dpartColLensQ_C, hr_gt]
        have hshQ_nil : (YoungDiagram.shiftLeft μQ).colLens = [] := by
          rw [YoungDiagram.colLens_shiftLeft, hQ_colLens]; rfl
        exact yd_of_colLens_nil hshQ_nil
      have h_sub_μ : YoungDiagram.shiftLeft μQ ≤ μP := by
        rw [hshQ_empty]; exact bot_le
      -- Now descent and chain construction
      obtain ⟨τ_val, τ_γ, τ_P_eq, τ_Q_eq⟩ := σ
      subst τ_P_eq; subst τ_Q_eq
      let σ' : PBPSet .C τ_val.P.shape τ_val.Q.shape := ⟨τ_val, τ_γ, rfl, rfl⟩
      have h_sub' : YoungDiagram.shiftLeft τ_val.Q.shape ≤ τ_val.P.shape := h_sub_μ
      obtain ⟨chain_D, h_chain_D⟩ := exists_descentChain_D (descentCD_PBP σ' h_sub')
      refine ⟨chain_D ++ [toACStepData_C τ_val τ_γ ∅], ?_⟩
      exact IsDescentChain_C.step τ_γ ∅ h_sub' h_chain_D
  | r₁ :: r₂ :: rest, h_coh, hsort, hodd =>
    -- Get h_sub via shiftLeft_Q_le_P_of_dp
    have hP_raw : σ.val.P.shape.colLens = dpartColLensP_C (r₁ :: r₂ :: rest) := h_coh.1
    have hQ_raw : σ.val.Q.shape.colLens = dpartColLensQ_C (r₁ :: r₂ :: rest) := h_coh.2
    have hP_μ : μP.colLens = dpartColLensP_C (r₁ :: r₂ :: rest) := by
      rw [← σ.prop.2.1]; exact hP_raw
    have hQ_μ : μQ.colLens = dpartColLensQ_C (r₁ :: r₂ :: rest) := by
      rw [← σ.prop.2.2]; exact hQ_raw
    have h_sub_μ : YoungDiagram.shiftLeft μQ ≤ μP :=
      _root_.shiftLeft_Q_le_P_of_dp hP_μ hQ_μ hsort hodd
    -- Bridge h_sub_μ to h_sub over σ.val's shapes
    have hγ : σ.val.γ = .C := σ.prop.1
    have hPeq : σ.val.P.shape = μP := σ.prop.2.1
    have hQeq : σ.val.Q.shape = μQ := σ.prop.2.2
    have h_sub : YoungDiagram.shiftLeft σ.val.Q.shape ≤ σ.val.P.shape := by
      rw [hPeq, hQeq]; exact h_sub_μ
    -- Using subst to align μP, μQ with σ.val's shapes
    obtain ⟨τ_val, τ_γ, τ_P_eq, τ_Q_eq⟩ := σ
    -- Now τ_val : PBP, with τ_val.γ = .C, τ_val.P.shape = μP, τ_val.Q.shape = μQ
    subst τ_P_eq; subst τ_Q_eq
    -- Now μP = τ_val.P.shape, μQ = τ_val.Q.shape
    -- Apply descentCD_PBP
    let σ' : PBPSet .C τ_val.P.shape τ_val.Q.shape := ⟨τ_val, τ_γ, rfl, rfl⟩
    obtain ⟨chain_D, h_chain_D⟩ := exists_descentChain_D (descentCD_PBP σ' h_sub)
    -- h_chain_D : IsDescentChain_D (descentCD_PBP σ' h_sub).val chain_D
    -- IsDescentChain_C.step expects h_rest of same form
    refine ⟨chain_D ++ [toACStepData_C τ_val τ_γ ∅], ?_⟩
    exact IsDescentChain_C.step τ_γ ∅ h_sub h_chain_D

/-- Every C-PBP admits a dp witness that makes it coherent. Classical
    choice + PBP structure. Paper-level: every C-PBP corresponds to
    a quasi-distinguished or general orbit via BV duality. -/
theorem exists_coherent_dp_C {μP μQ : YoungDiagram} (σ : PBPSet .C μP μQ) :
    ∃ dp : DualPart,
      PBPIsCoherent_C σ.val dp ∧ dp.SortedGE ∧ (∀ r ∈ dp, Odd r) := by
  sorry

/-- Simplified signature that takes σ and derives the coherence
    via `exists_coherent_dp_C`. -/
theorem exists_descentChain_C_simple {μP μQ : YoungDiagram} (σ : PBPSet .C μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_C σ.val c := by
  obtain ⟨dp, h_coh, hsort, hodd⟩ := exists_coherent_dp_C σ
  exact exists_descentChain_C σ dp h_coh hsort hodd

/-! ## Per-step thetaLift singleton (paper §11.5/11.6) -/

/-- Per-step thetaLift singleton for C chain, under std hypothesis.
    For target .C, thetaLift dispatches to thetaLift_DC (takes p only;
    q ignored since C-type signature has p = q). -/
theorem descent_step_thetaLift_singleton_C_std {τ : PBP} (hγ : τ.γ = .C)
    (wp : PPSet) (E_inner : ILS)
    (h_std :
      (toACStepData_C τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).1 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).2 ≥ 0 ∧
      (toACStepData_C τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).2 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).1 ≥ 0) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_C τ hγ wp))
      (toACStepData_C τ hγ wp).γ
      (toACStepData_C τ hγ wp).p
      (toACStepData_C τ hγ wp).q = [E'] := by
  set E_pre := stepPreTwist E_inner (toACStepData_C τ hγ wp)
  refine ⟨?_, ?_⟩
  · exact ILS.charTwistCM (ILS.augment
      ((toACStepData_C τ hγ wp).p - (ILS.sign E_pre).1 - (ILS.firstColSign E_pre).2,
       (toACStepData_C τ hγ wp).p - (ILS.sign E_pre).2 - (ILS.firstColSign E_pre).1)
      E_pre)
      (((ILS.sign E_pre).1 - (ILS.sign E_pre).2) / 2)
  show ILS.thetaLift E_pre _ _ _ = _
  simp only [ILS.thetaLift]
  have hγ' : (toACStepData_C τ hγ wp).γ = .C := rfl
  rw [hγ']
  simp only [ILS.thetaLift_DC]
  rw [if_pos h_std]

/-- Per-step thetaLift singleton for C chain. Paper §11.5/11.6. -/
theorem descent_step_thetaLift_singleton_C {τ : PBP} (hγ : τ.γ = .C)
    (wp : PPSet) (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_C τ hγ wp))
      (toACStepData_C τ hγ wp).γ
      (toACStepData_C τ hγ wp).p
      (toACStepData_C τ hγ wp).q = [E'] := by
  sorry

theorem descentChain_C_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_C τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .C) chain E := by
  cases h_chain with
  | base hγ h_empty => exact ⟨baseILS .C, ChainSingleton.nil _⟩
  | step hγ wp h_sub h_rest =>
    -- inner chain is on D-type, baseILS .D = []
    -- C chain's base is baseILS .C = []
    -- Both empty bases agree, so we can apply descentChain_D_singleton
    -- and snoc the outer C step.
    obtain ⟨E_inner, h_inner⟩ := descentChain_D_singleton h_rest
    obtain ⟨E', h_theta⟩ := descent_step_thetaLift_singleton_C hγ wp E_inner
    -- Need to bridge: D-singleton starts from baseILS .D = [];
    -- C-singleton starts from baseILS .C = []. Both equal!
    have h_base_eq : (baseILS .C : ILS) = baseILS .D := rfl
    rw [h_base_eq]
    exact ⟨stepPostTwist E' (toACStepData_C τ hγ wp),
           ChainSingleton.snoc h_inner h_theta⟩

/-! ## Sign target + sign match -/

/-- Sign target for C PBP. -/
noncomputable def signTarget_C' (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))

private theorem signature_empty_C (τ : PBP) (hγ : τ.γ = .C)
    (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
    PBP.signature τ = (0, 0) := by
  unfold PBP.signature
  have hP_empty : ∀ s, τ.P.countSym s = 0 := by
    intro s
    unfold PaintedYoungDiagram.countSym
    rw [h_empty.1]; simp
  have hQ_empty : ∀ s, τ.Q.countSym s = 0 := by
    intro s
    unfold PaintedYoungDiagram.countSym
    rw [h_empty.2]; simp
  simp [hγ, hP_empty, hQ_empty]

private theorem sign_baseILS_C : ILS.sign (baseILS .C) = (0, 0) := by
  unfold baseILS ILS.sign
  simp

/-- Sign match for C chain. The key step: thetaLift_DC_sign_std
    requires the std-case hypothesis (addp, addn ≥ 0). For C chain
    in paper's framework, this is guaranteed; here we sorry it via
    per-step singleton's std witness. -/
theorem descentChain_sign_match_C {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_C τ chain)
    (h_sing : ChainSingleton (baseILS .C) chain E) :
    ILS.sign E = signTarget_C' τ := by
  cases h_chain with
  | base hγ h_empty =>
    cases h_sing
    show ILS.sign (baseILS .C) = signTarget_C' τ
    rw [sign_baseILS_C]
    unfold signTarget_C'
    rw [signature_empty_C τ hγ h_empty]
    rfl
  | step hγ wp h_sub h_rest =>
    rename_i chain_inner
    obtain ⟨E_mid, E', _h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- C has pre-twist if ε_wp = 1: stepPreTwist applies twistBD (-1, -1)
    -- twistBD preserves sign, so sign(stepPreTwist E_mid) = sign(E_mid)
    -- ILS.thetaLift target .C = thetaLift_DC, sign preservation needs std hypothesis
    -- Deferred: paper §11.5/11.6 std condition + sign match.
    sorry

end BMSZ
