/-
# M-type chain infrastructure for `MYD_sig .M`

Mirror of `IsDescentChain_C` for M type: one outer M step (via
`descentMB_PBP`, which lands in either Bplus or Bminus depending
on `descentType_M τ hγ`), followed by an inner B-chain.

Reference: `lean/CombUnipotent/MYD/SigMYDC.lean` (C template).
-/
import CombUnipotent.MYD.SigMYDB
import CombUnipotent.MYD.SigMYDC
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

-- exists_coherent_dp_M was merged into exists_descentChain_M below
-- (see pattern in SigMYDC.lean).

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

/-- **Chain-existence hypothesis (M)**: every M-PBP in `PBPSet μP μQ`
    has a descent chain. Paper-level fact (requires PBP → dp
    reconstruction). Threaded as hypothesis to `Phi_M_sig` etc. to
    avoid a sorry. Can be discharged via `exists_descentChain_M_coherent`
    once a dp-witness is supplied. -/
abbrev ChainExists_M (μP μQ : YoungDiagram) : Prop :=
  ∀ σ : PBPSet .M μP μQ, ∃ c : List ACStepData, IsDescentChain_M σ.val c

/-- **Concrete discharge of `ChainExists_M` for the empty-shape case**. -/
theorem chainExists_M_empty : ChainExists_M (⊥ : YoungDiagram) ⊥ := by
  intro σ
  refine ⟨[], IsDescentChain_M.base σ.val σ.prop.1 ?_⟩
  exact ⟨σ.prop.2.1, σ.prop.2.2⟩

/-- The empty M-type PBP (analogous to emptyPBP_C). -/
def emptyPBP_M : PBP where
  γ := .M
  P := emptyPaintedYoungDiagram
  Q := emptyPaintedYoungDiagram
  sym_P := fun i j h => by simp [emptyPaintedYoungDiagram] at h
  sym_Q := fun i j h => by simp [emptyPaintedYoungDiagram] at h
  dot_match := fun _ _ => Iff.rfl
  mono_P := emptyPaintedYoungDiagram_layerMonotone
  mono_Q := emptyPaintedYoungDiagram_layerMonotone
  row_s := fun i s₁ s₂ j₁ j₂ h _ => by
    cases s₁ <;> simp [paintBySide, emptyPaintedYoungDiagram] at h
  row_r := fun i s₁ s₂ j₁ j₂ h _ => by
    cases s₁ <;> simp [paintBySide, emptyPaintedYoungDiagram] at h
  col_c_P := fun _ _ _ h _ => by simp [emptyPaintedYoungDiagram] at h
  col_c_Q := fun _ _ _ h _ => by simp [emptyPaintedYoungDiagram] at h
  col_d_P := fun _ _ _ h _ => by simp [emptyPaintedYoungDiagram] at h
  col_d_Q := fun _ _ _ h _ => by simp [emptyPaintedYoungDiagram] at h

theorem emptyPBP_M_γ : emptyPBP_M.γ = .M := rfl
theorem emptyPBP_M_P_shape : emptyPBP_M.P.shape = ⊥ := rfl
theorem emptyPBP_M_Q_shape : emptyPBP_M.Q.shape = ⊥ := rfl

/-- Empty M-PBP element of `PBPSet .M ⊥ ⊥`. -/
def emptyPBPSet_M : PBPSet .M (⊥ : YoungDiagram) ⊥ :=
  ⟨emptyPBP_M, emptyPBP_M_γ, emptyPBP_M_P_shape, emptyPBP_M_Q_shape⟩

/-- `emptyPBP_M`'s signature is `(0, 0)` (no painted cells). -/
theorem emptyPBP_M_signature : PBP.signature emptyPBP_M = (0, 0) := by
  unfold PBP.signature emptyPBP_M
  simp [emptyPaintedYoungDiagram, PaintedYoungDiagram.countSym]

/-- **Discharge of `ChainExists_M` from per-σ dp-coherence witness**. -/
theorem chainExists_M_of_coherent_dp
    (h : ∀ σ : PBPSet .M μP μQ, ∃ dp : DualPart,
        PBPIsCoherent_M σ.val dp ∧ dp.SortedGE ∧ ∀ r ∈ dp, Even r) :
    ChainExists_M μP μQ := by
  intro σ
  obtain ⟨dp, h_coh, hsort, heven⟩ := h σ
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

/-- **Chain-singleton hypothesis (M)**: every valid M descent chain
    yields a `ChainSingleton (baseILS .M)` witness.

    The step cases (both `step_to_Bplus` and `step_to_Bminus`) are
    paper-content: they require a base reconciliation between
    `baseILS .M = []` (empty-case base) and `baseILS .B± = [(1, 0)]`
    or `[(0, -1)]` (inner-chain bases from the bifurcated descent),
    plus the per-step `thetaLift_BM` singleton condition.

    Threaded as hypothesis to `Phi_M_sig` to avoid a sorry. Subsumes
    the per-step `descent_step_thetaLift_singleton_M` fact. -/
abbrev DescentChainMSingleton : Prop :=
  ∀ {τ : PBP} {chain : List ACStepData},
    IsDescentChain_M τ chain →
      ∃ E : ILS, ChainSingleton (baseILS .M) chain E

/-- `toACStepData_M τ hγ wp` has non-negative `p`. -/
theorem toACStepData_M_p_nonneg (τ : PBP) (hγ : τ.γ = .M) (wp : PPSet) :
    0 ≤ (toACStepData_M τ hγ wp).p := by
  unfold toACStepData_M
  simp only
  exact Int.natCast_nonneg _

/-- **Base case of std bound for M chain**: when `E_inner = baseILS .M = []`,
    the std bound at outer step trivializes to signature non-negativity. -/
theorem stepStdAndAugment_M_base_nil (τ : PBP) (hγ : τ.γ = .M) (wp : PPSet) :
    (toACStepData_M τ hγ wp).p -
      (ILS.sign (stepPreTwist [] (toACStepData_M τ hγ wp))).1 -
      (ILS.firstColSign (stepPreTwist [] (toACStepData_M τ hγ wp))).2 ≥ 0 ∧
    (toACStepData_M τ hγ wp).p -
      (ILS.sign (stepPreTwist [] (toACStepData_M τ hγ wp))).2 -
      (ILS.firstColSign (stepPreTwist [] (toACStepData_M τ hγ wp))).1 ≥ 0 := by
  have h_pre : stepPreTwist ([] : ILS) (toACStepData_M τ hγ wp) = [] := by
    unfold stepPreTwist
    split_ifs <;> rfl
  rw [h_pre]
  show (_ : ℤ) ≥ 0 ∧ (_ : ℤ) ≥ 0
  have hp := toACStepData_M_p_nonneg τ hγ wp
  refine ⟨?_, ?_⟩ <;> simp [ILS.sign, ILS.firstColSign] <;> omega

/-- **Chain trim for M-chains**.

    M chain has bifurcated step: outer M step + inner Bplus chain
    OR outer M step + inner Bminus chain. -/
theorem chainSingleton_IsTrim_M
    (h_step_std_M : StepStdAndAugment_M)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    {τ : PBP} {chain : List ACStepData} {E : ILS}
    (h_chain : IsDescentChain_M τ chain)
    (h_sing : ChainSingleton (baseILS .M) chain E) :
    ILS.IsTrim E := by
  cases h_chain with
  | base hγ h_empty =>
    cases h_sing
    exact baseILS_IsTrim .M
  | step_to_Bplus hγ wp hd h_rest =>
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Inner Bplus chain singleton starts from baseILS .M (not .Bplus)
    have h_trim_mid := chainSingleton_IsTrim_Bplus_init h_step_std_Bp
      (baseILS_IsTrim .M) h_rest h_inner_sing
    have h_d_γ : (toACStepData_M τ hγ wp).γ = .M := rfl
    have ⟨h_std, h_ne⟩ := h_step_std_M E_mid (toACStepData_M τ hγ wp) h_d_γ
    have h_trim_step :=
      step_trim_M E_mid (toACStepData_M τ hγ wp) h_d_γ
        h_std h_ne h_trim_mid h_theta
    rw [h_E_final]
    exact h_trim_step
  | step_to_Bminus hγ wp hd h_rest =>
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- We need a chainSingleton_IsTrim_Bminus_init helper here.
    -- Let's inline: for Bminus inner chain (which itself has Bplus
    -- inner steps), induct similarly.
    have h_trim_mid : ILS.IsTrim E_mid := by
      -- Bminus inner chain. Use cases on h_rest (which is IsDescentChain_Bminus).
      cases h_rest with
      | base hγ_b h_empty_b =>
        cases h_inner_sing
        exact baseILS_IsTrim .M
      | step hγ_b h_rest_b =>
        obtain ⟨E_mid_inner, E'_inner, h_inner_sing_inner,
                h_theta_inner, h_E_final_inner⟩ :=
          ChainSingleton.snoc_inv h_inner_sing
        have h_trim_inner :=
          chainSingleton_IsTrim_Bplus_init h_step_std_Bp
            (baseILS_IsTrim .M) h_rest_b h_inner_sing_inner
        have h_d_γ_inner :
            (PBPInstantiation.toACStepData_Bminus _ hγ_b).γ = .Bminus := rfl
        have ⟨h_std_inner, h_ne_inner⟩ :=
          h_step_std_Bm E_mid_inner (PBPInstantiation.toACStepData_Bminus _ hγ_b) h_d_γ_inner
        have h_trim_step_inner :=
          step_trim_Bminus E_mid_inner
            (PBPInstantiation.toACStepData_Bminus _ hγ_b) h_d_γ_inner
            h_std_inner h_ne_inner h_trim_inner h_theta_inner
        rw [h_E_final_inner]
        exact h_trim_step_inner
    have h_d_γ : (toACStepData_M τ hγ wp).γ = .M := rfl
    have ⟨h_std, h_ne⟩ := h_step_std_M E_mid (toACStepData_M τ hγ wp) h_d_γ
    have h_trim_step :=
      step_trim_M E_mid (toACStepData_M τ hγ wp) h_d_γ
        h_std h_ne h_trim_mid h_theta
    rw [h_E_final]
    exact h_trim_step

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

/-- **Chain sign-match hypothesis (M)**: along any valid M descent
    chain with singleton witness, the extracted ILS has signature
    matching `signTarget_M' τ`.

    Base case proved (empty chain + empty PBP). Step cases are paper
    §11.5/§11.6 content: per-step `thetaLift_BM` produces an ILS with
    signature (n, n) only under the std sign-bound condition.

    Threaded as hypothesis to `Phi_M_sig` to avoid a sorry. -/
abbrev DescentChainSignMatch_M : Prop :=
  ∀ {τ : PBP} {chain : List ACStepData} {E : ILS},
    IsDescentChain_M τ chain →
    ChainSingleton (baseILS .M) chain E →
    ILS.sign E = signTarget_M' τ

/-- Base case of `DescentChainSignMatch_M`, fully proved. -/
theorem descentChain_sign_match_M_base {τ : PBP} (hγ : τ.γ = .M)
    (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
    ILS.sign (baseILS .M) = signTarget_M' τ := by
  rw [sign_baseILS_M]
  unfold signTarget_M'
  rw [signature_empty_M τ hγ h_empty]
  rfl

end BMSZ
