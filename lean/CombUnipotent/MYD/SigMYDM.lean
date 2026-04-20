/-
# M-type chain infrastructure for `MYD_sig .M`

Mirror of `IsDescentChain_C` for M type: one outer M step (via
`descentMB_PBP`, which lands in either Bplus or Bminus depending
on `descentType_M τ hγ`), followed by an inner B-chain.

Reference: `lean/CombUnipotent/MYD/SigMYDC.lean` (C template).
-/
import CombUnipotent.MYD.SigMYDB
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.CorrespondenceM
import CombUnipotent.CountingProof.Basic

namespace BMSZ

open PBPInstantiation (toACStepData_M)

/-! ## M chain inductive type

M chain has two step cases based on `descentType_M τ hγ`:
  - to Bplus: inner uses IsDescentChain_Bplus
  - to Bminus: inner uses IsDescentChain_Bminus

This bifurcation is paper [BMSZb] §10.4 (★ = C̃).
-/

/-- Descent chain predicate for M type. -/
inductive IsDescentChain_M : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .M)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_M τ []
  | step_to_Bplus {τ : PBP} (hγ : τ.γ = .M) (wp : PPSet)
      (hd : PBP.descentType_M τ hγ = .Bplus)
      {chain : List ACStepData}
      (h_rest : IsDescentChain_Bplus (descentMB_PBP τ hγ) chain) :
      IsDescentChain_M τ (chain ++ [toACStepData_M τ hγ wp])
  | step_to_Bminus {τ : PBP} (hγ : τ.γ = .M) (wp : PPSet)
      (hd : PBP.descentType_M τ hγ = .Bminus)
      {chain : List ACStepData}
      (h_rest : IsDescentChain_Bminus (descentMB_PBP τ hγ) chain) :
      IsDescentChain_M τ (chain ++ [toACStepData_M τ hγ wp])

/-! ## Existence (sorry: needs h_sub witness for non-empty M-PBPs) -/

def PBPIsCoherent_M (τ : PBP) (dp : DualPart) : Prop :=
  τ.P.shape.colLens = dpartColLensP_M dp ∧
  τ.Q.shape.colLens = dpartColLensQ_M dp

theorem exists_coherent_dp_M {μP μQ : YoungDiagram} (σ : PBPSet .M μP μQ) :
    ∃ dp : DualPart,
      PBPIsCoherent_M σ.val dp ∧ dp.SortedGE ∧ (∀ r ∈ dp, Even r) := by
  sorry

/-- Helper: for M-PBP coherent with empty dp, shapes are empty. -/
private theorem PBPIsCoherent_M_empty {τ : PBP} (h_coh : PBPIsCoherent_M τ []) :
    τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥ := by
  obtain ⟨hP, hQ⟩ := h_coh
  simp [dpartColLensP_M, dpartColLensQ_M, dpartColLensP_B, dpartColLensQ_B] at hP hQ
  exact ⟨yd_of_colLens_nil hP, yd_of_colLens_nil hQ⟩

theorem exists_descentChain_M_coherent {μP μQ : YoungDiagram} (σ : PBPSet .M μP μQ)
    (dp : DualPart) (h_coh : PBPIsCoherent_M σ.val dp)
    (_hsort : dp.SortedGE) (_heven : ∀ r ∈ dp, Even r) :
    ∃ c : List ACStepData, IsDescentChain_M σ.val c := by
  match dp, h_coh with
  | [], h_coh =>
    have hγ : σ.val.γ = .M := σ.prop.1
    have h_empty := PBPIsCoherent_M_empty h_coh
    exact ⟨[], IsDescentChain_M.base σ.val hγ h_empty⟩
  | [r], h_coh =>
    -- dpartColLensP_M [r] = dpartColLensQ_B [r] = if r > 0 then [r/2] else []
    -- dpartColLensQ_M [r] = dpartColLensP_B [r] = []
    have hγ : σ.val.γ = .M := σ.prop.1
    have hQ_empty : μQ = ⊥ := by
      have hQ_nil : μQ.colLens = [] := by
        rw [← σ.prop.2.2]
        simp [h_coh.2, dpartColLensQ_M, dpartColLensP_B]
      exact yd_of_colLens_nil hQ_nil
    by_cases hr : r = 0
    · have hP_empty : μP = ⊥ := by
        have hP_nil : μP.colLens = [] := by
          rw [← σ.prop.2.1]
          simp [h_coh.1, dpartColLensP_M, dpartColLensQ_B, hr]
        exact yd_of_colLens_nil hP_nil
      have h_empty : σ.val.P.shape = ⊥ ∧ σ.val.Q.shape = ⊥ :=
        ⟨σ.prop.2.1.trans hP_empty, σ.prop.2.2.trans hQ_empty⟩
      exact ⟨[], IsDescentChain_M.base σ.val hγ h_empty⟩
    · -- r > 0 even: μP has 1 col of height r/2, μQ empty
      -- descentMB_PBP gives PBP with shape (shiftLeft μP, μQ) = (⊥, ⊥)
      -- Inner PBP is empty Bplus or Bminus depending on descentType_M
      have hr_pos : r > 0 := Nat.pos_of_ne_zero hr
      have h_descent_empty : (descentMB_PBP σ.val hγ).P.shape = ⊥ ∧
                              (descentMB_PBP σ.val hγ).Q.shape = ⊥ := by
        unfold descentMB_PBP
        dsimp only
        refine ⟨?_, ?_⟩
        · -- shiftLeft μP = ⊥
          have hP_colLens : σ.val.P.shape.colLens = [r/2] := by
            rw [h_coh.1]; simp [dpartColLensP_M, dpartColLensQ_B, hr_pos]
          have hshP_nil : (σ.val.P.shape.shiftLeft).colLens = [] := by
            rw [YoungDiagram.colLens_shiftLeft, hP_colLens]; rfl
          exact yd_of_colLens_nil hshP_nil
        · -- Q unchanged = μQ = ⊥
          exact σ.prop.2.2.trans hQ_empty
      -- Case split on descentType_M
      by_cases hd : PBP.descentType_M σ.val hγ = .Bplus
      · -- Bplus case
        have h_inner_γ : (descentMB_PBP σ.val hγ).γ = .Bplus := hd
        have h_inner_chain : IsDescentChain_Bplus (descentMB_PBP σ.val hγ) [] :=
          IsDescentChain_Bplus.base _ h_inner_γ h_descent_empty
        refine ⟨[] ++ [toACStepData_M σ.val hγ ∅], ?_⟩
        exact IsDescentChain_M.step_to_Bplus hγ ∅ hd h_inner_chain
      · -- Bminus case (by descentType_M returning Bminus or Bplus)
        have hd_bm : PBP.descentType_M σ.val hγ = .Bminus := by
          unfold PBP.descentType_M at hd ⊢
          split_ifs at hd ⊢ with h <;> simp_all
        have h_inner_γ : (descentMB_PBP σ.val hγ).γ = .Bminus := hd_bm
        have h_inner_chain : IsDescentChain_Bminus (descentMB_PBP σ.val hγ) [] :=
          IsDescentChain_Bminus.base _ h_inner_γ h_descent_empty
        refine ⟨[] ++ [toACStepData_M σ.val hγ ∅], ?_⟩
        exact IsDescentChain_M.step_to_Bminus hγ ∅ hd_bm h_inner_chain
  | _r₁ :: _r₂ :: _rest, _ =>
    -- Apply descentMB_PBP to get inner B-PBP (Bplus or Bminus)
    -- Recurse via exists_descentChain_Bplus or exists_descentChain_Bminus
    have hγ : σ.val.γ = .M := σ.prop.1
    by_cases hd : PBP.descentType_M σ.val hγ = .Bplus
    · have h_inner_γ : (descentMB_PBP σ.val hγ).γ = .Bplus := hd
      -- Package as PBPSet .Bplus to use exists_descentChain_Bplus
      let σ_inner : PBPSet .Bplus (descentMB_PBP σ.val hγ).P.shape
                              (descentMB_PBP σ.val hγ).Q.shape :=
        ⟨descentMB_PBP σ.val hγ, h_inner_γ, rfl, rfl⟩
      obtain ⟨chain_inner, h_chain_inner⟩ := exists_descentChain_Bplus σ_inner
      refine ⟨chain_inner ++ [toACStepData_M σ.val hγ ∅], ?_⟩
      exact IsDescentChain_M.step_to_Bplus hγ ∅ hd h_chain_inner
    · -- Bminus case
      have hd_bm : PBP.descentType_M σ.val hγ = .Bminus := by
        unfold PBP.descentType_M at hd ⊢
        split_ifs at hd ⊢ with h <;> simp_all
      have h_inner_γ : (descentMB_PBP σ.val hγ).γ = .Bminus := hd_bm
      let σ_inner : PBPSet .Bminus (descentMB_PBP σ.val hγ).P.shape
                                (descentMB_PBP σ.val hγ).Q.shape :=
        ⟨descentMB_PBP σ.val hγ, h_inner_γ, rfl, rfl⟩
      obtain ⟨chain_inner, h_chain_inner⟩ := exists_descentChain_Bminus σ_inner
      refine ⟨chain_inner ++ [toACStepData_M σ.val hγ ∅], ?_⟩
      exact IsDescentChain_M.step_to_Bminus hγ ∅ hd_bm h_chain_inner

theorem exists_descentChain_M {μP μQ : YoungDiagram} (σ : PBPSet .M μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_M σ.val c := by
  obtain ⟨dp, h_coh, hsort, heven⟩ := exists_coherent_dp_M σ
  exact exists_descentChain_M_coherent σ dp h_coh hsort heven

/-! ## Per-step thetaLift singleton (paper §11.5/11.6) -/

/-- Per-step thetaLift singleton for M chain, under std hypothesis.
    For target .M, thetaLift dispatches to thetaLift_BM (p-only,
    since M-type signature has p = q). -/
theorem descent_step_thetaLift_singleton_M_std {τ : PBP} (hγ : τ.γ = .M)
    (wp : PPSet) (E_inner : ILS)
    (h_std :
      (toACStepData_M τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_M τ hγ wp))).1 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_M τ hγ wp))).2 ≥ 0 ∧
      (toACStepData_M τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_M τ hγ wp))).2 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_M τ hγ wp))).1 ≥ 0) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_M τ hγ wp))
      (toACStepData_M τ hγ wp).γ
      (toACStepData_M τ hγ wp).p
      (toACStepData_M τ hγ wp).q = [E'] := by
  set E_pre := stepPreTwist E_inner (toACStepData_M τ hγ wp)
  refine ⟨?_, ?_⟩
  · exact ILS.charTwistCM (ILS.augment
      ((toACStepData_M τ hγ wp).p - (ILS.sign E_pre).1 - (ILS.firstColSign E_pre).2,
       (toACStepData_M τ hγ wp).p - (ILS.sign E_pre).2 - (ILS.firstColSign E_pre).1)
      E_pre)
      (((ILS.sign E_pre).1 - (ILS.sign E_pre).2 - 1) / 2)
  show ILS.thetaLift E_pre _ _ _ = _
  simp only [ILS.thetaLift]
  have hγ' : (toACStepData_M τ hγ wp).γ = .M := rfl
  rw [hγ']
  simp only [ILS.thetaLift_BM]
  rw [if_pos h_std]

theorem descent_step_thetaLift_singleton_M {τ : PBP} (hγ : τ.γ = .M)
    (wp : PPSet) (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_M τ hγ wp))
      (toACStepData_M τ hγ wp).γ
      (toACStepData_M τ hγ wp).p
      (toACStepData_M τ hγ wp).q = [E'] := by
  sorry

theorem descentChain_M_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_M τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .M) chain E := by
  cases h_chain with
  | base hγ h_empty => exact ⟨baseILS .M, ChainSingleton.nil _⟩
  | step_to_Bplus hγ wp hd h_rest =>
    -- Inner chain on Bplus, baseILS .Bplus = [(1, 0)] ≠ baseILS .M = []
    -- Base mismatch — same problem as Bminus singleton.
    sorry
  | step_to_Bminus hγ wp hd h_rest =>
    -- Same base mismatch issue (Bminus baseILS = [(0, -1)] ≠ M baseILS = [])
    sorry

/-! ## Sign target + sign match -/

noncomputable def signTarget_M' (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))

private theorem signature_empty_M (τ : PBP) (hγ : τ.γ = .M)
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

private theorem sign_baseILS_M : ILS.sign (baseILS .M) = (0, 0) := by
  unfold baseILS ILS.sign
  simp

/-- Sign match for M chain. Step cases sorry'd (depend on per-step
    singleton's std-hypothesis for thetaLift_BM, paper §11.5/11.6). -/
theorem descentChain_sign_match_M {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_M τ chain)
    (h_sing : ChainSingleton (baseILS .M) chain E) :
    ILS.sign E = signTarget_M' τ := by
  cases h_chain with
  | base hγ h_empty =>
    cases h_sing
    show ILS.sign (baseILS .M) = signTarget_M' τ
    rw [sign_baseILS_M]
    unfold signTarget_M'
    rw [signature_empty_M τ hγ h_empty]
    rfl
  | step_to_Bplus hγ wp hd h_rest =>
    sorry
  | step_to_Bminus hγ wp hd h_rest =>
    sorry

end BMSZ
