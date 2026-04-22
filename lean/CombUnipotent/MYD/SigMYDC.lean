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

/-- **Chain-existence hypothesis (C)**: every C-PBP in `PBPSet μP μQ`
    has a descent chain. Paper-level fact (requires PBP → dp
    reconstruction). Threaded as hypothesis to `Phi_C_sig` etc. to
    avoid a sorry. Can be discharged via `exists_descentChain_C` once
    a dp-witness is supplied. -/
abbrev ChainExists_C (μP μQ : YoungDiagram) : Prop :=
  ∀ σ : PBPSet .C μP μQ, ∃ c : List ACStepData, IsDescentChain_C σ.val c

/-- **Concrete discharge of `ChainExists_C` for the empty-shape case**:
    when μP = ⊥ and μQ = ⊥, every σ : PBPSet .C ⊥ ⊥ has empty shapes
    by construction, and the empty chain witnesses `IsDescentChain_C`. -/
theorem chainExists_C_empty : ChainExists_C (⊥ : YoungDiagram) ⊥ := by
  intro σ
  refine ⟨[], IsDescentChain_C.base σ.val σ.prop.1 ?_⟩
  exact ⟨σ.prop.2.1, σ.prop.2.2⟩

/-- The empty PaintedYoungDiagram (shape ⊥, all paint = dot). -/
def emptyPaintedYoungDiagram : PaintedYoungDiagram where
  shape := ⊥
  paint := fun _ _ => .dot
  paint_outside := fun _ _ _ => rfl

/-- `layerMonotone` is vacuously satisfied for the empty diagram. -/
theorem emptyPaintedYoungDiagram_layerMonotone :
    emptyPaintedYoungDiagram.layerMonotone := by
  intro i₁ j₁ i₂ j₂ _ _ hmem
  simp [emptyPaintedYoungDiagram] at hmem

/-- The empty C-type PBP. -/
def emptyPBP_C : PBP where
  γ := .C
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

/-- `emptyPBP_C` has γ = .C. -/
theorem emptyPBP_C_γ : emptyPBP_C.γ = .C := rfl

/-- `emptyPBP_C` has empty P shape. -/
theorem emptyPBP_C_P_shape : emptyPBP_C.P.shape = ⊥ := rfl

/-- `emptyPBP_C` has empty Q shape. -/
theorem emptyPBP_C_Q_shape : emptyPBP_C.Q.shape = ⊥ := rfl

/-- `emptyPBP_C` element of `PBPSet .C ⊥ ⊥`. -/
def emptyPBPSet_C : PBPSet .C (⊥ : YoungDiagram) ⊥ :=
  ⟨emptyPBP_C, emptyPBP_C_γ, emptyPBP_C_P_shape, emptyPBP_C_Q_shape⟩

/-- `emptyPBP_C`'s signature is `(0, 0)` (no painted cells). -/
theorem emptyPBP_C_signature : PBP.signature emptyPBP_C = (0, 0) := by
  unfold PBP.signature emptyPBP_C
  simp [emptyPaintedYoungDiagram, PaintedYoungDiagram.countSym]

/-- **Discharge of `ChainExists_C` from per-σ dp-coherence witness**.
    Reduces the universal chain-existence to a simpler paper content:
    every PBP has a coherent dp. This mirrors paper §9.4 content. -/
theorem chainExists_C_of_coherent_dp
    (h : ∀ σ : PBPSet .C μP μQ, ∃ dp : DualPart,
        PBPIsCoherent_C σ.val dp ∧ dp.SortedGE ∧ ∀ r ∈ dp, Odd r) :
    ChainExists_C μP μQ := by
  intro σ
  obtain ⟨dp, h_coh, hsort, hodd⟩ := h σ
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

/-- **Paper §11.5/§11.6 per-step singleton hypothesis (C)**,
    chain-conditional.

    C's outer step takes both `wp : PPSet` (painted parameter) and
    `h_sub` (shape containment witness needed by `descentCD_PBP`).
    Inner chain is on the descended D-type PBP, so E_inner is from
    a `ChainSingleton (baseILS .D)`. -/
abbrev DescentStepSingleton_C : Prop :=
  ∀ (τ : PBP) (hγ : τ.γ = .C) (wp : PPSet)
    (h_sub : YoungDiagram.shiftLeft τ.Q.shape ≤ τ.P.shape)
    (chain_inner : List ACStepData) (E_inner : ILS),
    IsDescentChain_D (descentCD_PBP ⟨τ, hγ, rfl, rfl⟩ h_sub).val chain_inner →
    ChainSingleton (baseILS .D) chain_inner E_inner →
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_C τ hγ wp))
      (toACStepData_C τ hγ wp).γ
      (toACStepData_C τ hγ wp).p
      (toACStepData_C τ hγ wp).q = [E']

/-- **Reduction**: `DescentStepSingleton_C` follows from a
    chain-conditional std sign-bound hypothesis. -/
theorem descentStepSingleton_C_of_std
    (h_std : ∀ (τ : PBP) (hγ : τ.γ = .C) (wp : PPSet)
              (h_sub : YoungDiagram.shiftLeft τ.Q.shape ≤ τ.P.shape)
              (chain_inner : List ACStepData) (E_inner : ILS)
              (_h_chain : IsDescentChain_D
                (descentCD_PBP ⟨τ, hγ, rfl, rfl⟩ h_sub).val chain_inner)
              (_h_sing : ChainSingleton (baseILS .D) chain_inner E_inner),
      (toACStepData_C τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).1 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).2 ≥ 0 ∧
      (toACStepData_C τ hγ wp).p - (ILS.sign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).2 - (ILS.firstColSign (stepPreTwist E_inner
        (toACStepData_C τ hγ wp))).1 ≥ 0) :
    DescentStepSingleton_C := by
  intro τ hγ wp h_sub chain_inner E_inner h_chain h_sing
  exact descent_step_thetaLift_singleton_C_std hγ wp E_inner
    (h_std τ hγ wp h_sub chain_inner E_inner h_chain h_sing)

theorem descentChain_C_singleton
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_C τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .C) chain E := by
  cases h_chain with
  | base hγ h_empty => exact ⟨baseILS .C, ChainSingleton.nil _⟩
  | step hγ wp h_sub h_rest =>
    obtain ⟨E_inner, h_inner⟩ := descentChain_D_singleton h_step_D h_rest
    obtain ⟨E', h_theta⟩ := h_step_C τ hγ wp h_sub _ E_inner h_rest h_inner
    have h_base_eq : (baseILS .C : ILS) = baseILS .D := rfl
    rw [h_base_eq]
    exact ⟨stepPostTwist E' (toACStepData_C τ hγ wp),
           ChainSingleton.snoc h_inner h_theta⟩

/-- `toACStepData_C τ hγ wp` has non-negative `p` (signature is ℕ × ℕ). -/
theorem toACStepData_C_p_nonneg (τ : PBP) (hγ : τ.γ = .C) (wp : PPSet) :
    0 ≤ (toACStepData_C τ hγ wp).p := by
  unfold toACStepData_C
  simp only
  exact Int.natCast_nonneg _

/-- **Base case of std bound for C chain**: when `E_inner = baseILS .C = []`,
    the std bound at outer step trivializes to signature non-negativity. -/
theorem stepStdAndAugment_C_base_nil (τ : PBP) (hγ : τ.γ = .C) (wp : PPSet) :
    (toACStepData_C τ hγ wp).p -
      (ILS.sign (stepPreTwist [] (toACStepData_C τ hγ wp))).1 -
      (ILS.firstColSign (stepPreTwist [] (toACStepData_C τ hγ wp))).2 ≥ 0 ∧
    (toACStepData_C τ hγ wp).p -
      (ILS.sign (stepPreTwist [] (toACStepData_C τ hγ wp))).2 -
      (ILS.firstColSign (stepPreTwist [] (toACStepData_C τ hγ wp))).1 ≥ 0 := by
  -- stepPreTwist [] _ = [] (twistBD on [] is []) or = [] (identity)
  have h_pre : stepPreTwist ([] : ILS) (toACStepData_C τ hγ wp) = [] := by
    unfold stepPreTwist
    split_ifs <;> rfl
  rw [h_pre]
  show (_ : ℤ) ≥ 0 ∧ (_ : ℤ) ≥ 0
  have hp := toACStepData_C_p_nonneg τ hγ wp
  refine ⟨?_, ?_⟩ <;> simp [ILS.sign, ILS.firstColSign] <;> omega

/-- **Chain trim for C-chains**.

    C chain has structure: (D inner steps) ++ [outer C step].
    Note baseILS .C = baseILS .D = []. -/
theorem chainSingleton_IsTrim_C
    (h_step_std_C : StepStdAndAugment_C)
    (h_step_std_D : StepStdAndAugment_D)
    {τ : PBP} {chain : List ACStepData} {E : ILS}
    (h_chain : IsDescentChain_C τ chain)
    (h_sing : ChainSingleton (baseILS .C) chain E) :
    ILS.IsTrim E := by
  cases h_chain with
  | base hγ h_empty =>
    cases h_sing
    exact baseILS_IsTrim .C
  | step hγ wp h_sub h_rest =>
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Inner D chain singleton starts from baseILS .C = baseILS .D = []
    have h_trim_mid : ILS.IsTrim E_mid :=
      chainSingleton_IsTrim_D_init h_step_std_D (baseILS_IsTrim .C) h_rest h_inner_sing
    have h_d_γ : (toACStepData_C τ hγ wp).γ = .C := rfl
    have ⟨h_std, h_ne⟩ := h_step_std_C E_mid (toACStepData_C τ hγ wp) h_d_γ
    have h_trim_step :=
      step_trim_C E_mid (toACStepData_C τ hγ wp) h_d_γ
        h_std h_ne h_trim_mid h_theta
    rw [h_E_final]
    exact h_trim_step

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

/-- `signTarget_C' emptyPBP_C = (0, 0)`. -/
theorem signTarget_C'_emptyPBP : signTarget_C' emptyPBP_C = (0, 0) := by
  unfold signTarget_C'
  rw [emptyPBP_C_signature]
  rfl

/-- A PaintedYoungDiagram with shape ⊥ has paint = (fun _ _ => .dot)
    (forced by paint_outside). -/
theorem PaintedYoungDiagram_paint_of_shape_bot (D : PaintedYoungDiagram)
    (h : D.shape = ⊥) : D.paint = fun _ _ => .dot := by
  funext i j
  apply D.paint_outside
  rw [h]
  intro hmem
  simp at hmem

/-- Two PaintedYoungDiagrams with shape ⊥ are equal. -/
theorem PaintedYoungDiagram_subsingleton_of_bot
    (D₁ D₂ : PaintedYoungDiagram)
    (h₁ : D₁.shape = ⊥) (h₂ : D₂.shape = ⊥) : D₁ = D₂ := by
  cases D₁ with
  | mk shape₁ paint₁ paint_outside₁ =>
    cases D₂ with
    | mk shape₂ paint₂ paint_outside₂ =>
      simp only at h₁ h₂
      subst h₁; subst h₂
      have hp₁ : paint₁ = fun _ _ => .dot :=
        PaintedYoungDiagram_paint_of_shape_bot ⟨⊥, paint₁, paint_outside₁⟩ rfl
      have hp₂ : paint₂ = fun _ _ => .dot :=
        PaintedYoungDiagram_paint_of_shape_bot ⟨⊥, paint₂, paint_outside₂⟩ rfl
      simp only at hp₁ hp₂
      subst hp₁; subst hp₂
      rfl

/-- Two PBPs with same γ and shape ⊥ are equal. -/
theorem PBP_eq_of_shapes_bot {τ₁ τ₂ : PBP} (hγ : τ₁.γ = τ₂.γ)
    (hP₁ : τ₁.P.shape = ⊥) (hQ₁ : τ₁.Q.shape = ⊥)
    (hP₂ : τ₂.P.shape = ⊥) (hQ₂ : τ₂.Q.shape = ⊥) : τ₁ = τ₂ := by
  cases τ₁
  cases τ₂
  simp only at hγ
  subst hγ
  congr 1
  · exact PaintedYoungDiagram_subsingleton_of_bot _ _ hP₁ hP₂
  · exact PaintedYoungDiagram_subsingleton_of_bot _ _ hQ₁ hQ₂

/-- **Chain sign-match hypothesis (C)**: along any valid C descent
    chain with singleton witness, the extracted ILS has signature
    matching the paper-level `signTarget_C' τ`.

    Base case is proved (empty chain + empty PBP). Step case is
    paper §11.5/§11.6 content: depends on the per-step `thetaLift_DC`
    producing an ILS with signature (n, n), which requires the std
    sign-bound condition along valid chains.

    Threaded as hypothesis to `Phi_C_sig` to avoid a sorry. -/
abbrev DescentChainSignMatch_C : Prop :=
  ∀ {τ : PBP} {chain : List ACStepData} {E : ILS},
    IsDescentChain_C τ chain →
    ChainSingleton (baseILS .C) chain E →
    ILS.sign E = signTarget_C' τ

/-- Base case of `DescentChainSignMatch_C`, fully proved. -/
theorem descentChain_sign_match_C_base {τ : PBP} (hγ : τ.γ = .C)
    (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
    ILS.sign (baseILS .C) = signTarget_C' τ := by
  rw [sign_baseILS_C]
  unfold signTarget_C'
  rw [signature_empty_C τ hγ h_empty]
  rfl

/-! ## Concrete dp values for paper §9.4

Explicit witness: for `dp = [2k+1]` (k ≥ 1, odd), `dpartColLensP_C = []`
and `dpartColLensQ_C = [k]`. Matches shapes (⊥, single column of height k).
-/

/-- `dpartColLensP_C [r] = []` for any `r`. -/
theorem dpartColLensP_C_singleton (r : ℕ) : dpartColLensP_C [r] = [] := rfl

/-- `dpartColLensQ_C [r] = [(r-1)/2]` when `r > 1`. -/
theorem dpartColLensQ_C_singleton_pos {r : ℕ} (h : r > 1) :
    dpartColLensQ_C [r] = [(r - 1) / 2] := by
  unfold dpartColLensQ_C; simp [h]

/-- `dpartColLensQ_C [r] = []` when `r ≤ 1`. -/
theorem dpartColLensQ_C_singleton_le_one {r : ℕ} (h : r ≤ 1) :
    dpartColLensQ_C [r] = [] := by
  unfold dpartColLensQ_C; simp [Nat.not_lt.mpr h]

/-- For odd `r > 1`: `dpartColLensQ_C [r] = [(r-1)/2]` is a single-column
    witness. This gives: if `μP = ⊥` and `μQ.colLens = [(r-1)/2]`, then
    `dp = [r]` is C-coherent. -/
theorem PBPIsCoherent_C_singleton_witness (τ : PBP) {r : ℕ}
    (h_r : r > 1) (hP : τ.P.shape = ⊥) (hQ : τ.Q.shape.colLens = [(r - 1) / 2]) :
    PBPIsCoherent_C τ [r] := by
  refine ⟨?_, ?_⟩
  · rw [hP, dpartColLensP_C_singleton]
    exact _root_.colLens_bot
  · rw [hQ, dpartColLensQ_C_singleton_pos h_r]

/-- Single-element `[r]` is always `SortedGE`. -/
theorem singleton_sortedGE (r : ℕ) : ([r] : DualPart).SortedGE := by
  simp [List.SortedGE, Antitone]

/-- For C-PBP with P=⊥, Q cells are all painted `.s`. -/
theorem Q_all_s_of_C_P_bot {τ : PBP} (hγ : τ.γ = .C) (hP : τ.P.shape = ⊥)
    (i j : ℕ) (h : (i, j) ∈ τ.Q.shape) : τ.Q.paint i j = .s := by
  have h_not_dot : τ.Q.paint i j ≠ .dot := by
    intro hdot
    have := (τ.dot_match i j).mpr ⟨h, hdot⟩
    rw [hP] at this
    simp at this
  exact τ.Q_nonDot_eq_s_of_C hγ i j h h_not_dot

/-- For C-PBP with P=⊥, Q has at most 1 cell per row (from row_s). -/
theorem Q_rowLen_le_one_of_C_P_bot {τ : PBP} (hγ : τ.γ = .C)
    (hP : τ.P.shape = ⊥) (i : ℕ) : τ.Q.shape.rowLen i ≤ 1 := by
  by_contra h_not
  push_neg at h_not
  -- rowLen i ≥ 2, so (i, 0) ∈ Q and (i, 1) ∈ Q
  have h0 : (i, 0) ∈ τ.Q.shape := by
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  have h1 : (i, 1) ∈ τ.Q.shape := by
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  have hp0 : τ.Q.paint i 0 = .s := Q_all_s_of_C_P_bot hγ hP i 0 h0
  have hp1 : τ.Q.paint i 1 = .s := Q_all_s_of_C_P_bot hγ hP i 1 h1
  -- row_s: both .s at (i, 0) and (i, 1) on R side → j₁ = j₂
  have := τ.row_s i .R .R 0 1 hp0 hp1
  omega

/-- For C-PBP with P=⊥, Q.shape.colLens has length ≤ 1. -/
theorem Q_colLens_length_le_one_of_C_P_bot {τ : PBP} (hγ : τ.γ = .C)
    (hP : τ.P.shape = ⊥) : τ.Q.shape.colLens.length ≤ 1 := by
  rw [YoungDiagram.length_colLens]
  exact Q_rowLen_le_one_of_C_P_bot hγ hP 0

/-- `PBPSet .C ⊥ μQ` is empty when μQ has more than 1 column. -/
theorem PBPSet_C_P_bot_Q_multi_col_eq_empty {μQ : YoungDiagram}
    (h : μQ.colLens.length ≥ 2) : IsEmpty (PBPSet .C (⊥ : YoungDiagram) μQ) := by
  refine ⟨fun σ => ?_⟩
  have hγ : σ.val.γ = .C := σ.prop.1
  have hP : σ.val.P.shape = ⊥ := σ.prop.2.1
  have hQ : σ.val.Q.shape = μQ := σ.prop.2.2
  have h_len : σ.val.Q.shape.colLens.length ≤ 1 :=
    Q_colLens_length_le_one_of_C_P_bot hγ hP
  rw [hQ] at h_len
  omega

/-- **Concrete ChainExists_C for single-column Q**: given μP = ⊥ and
    μQ with single column of height k ≥ 1, the chain exists via dp = [2k+1].
    First non-trivial paper §9.4 case. -/
theorem chainExists_C_single_col_Q {μQ : YoungDiagram} {k : ℕ}
    (hk : k ≥ 1) (hQ : μQ.colLens = [k]) :
    ChainExists_C (⊥ : YoungDiagram) μQ := by
  intro σ
  let dp : DualPart := [2 * k + 1]
  have hr_gt : 2 * k + 1 > 1 := by omega
  have hr_half : (2 * k + 1 - 1) / 2 = k := by omega
  have hP_σ : σ.val.P.shape = ⊥ := σ.prop.2.1
  have hQ_σ : σ.val.Q.shape.colLens = [k] := by rw [σ.prop.2.2]; exact hQ
  have h_coh : PBPIsCoherent_C σ.val dp :=
    PBPIsCoherent_C_singleton_witness σ.val hr_gt hP_σ (by rw [hQ_σ, hr_half])
  have h_sort : dp.SortedGE := singleton_sortedGE _
  have h_odd : ∀ r ∈ dp, Odd r := by
    intro r hr
    simp [dp] at hr
    subst hr
    exact ⟨k, by ring⟩
  exact exists_descentChain_C σ dp h_coh h_sort h_odd

/-- 🎯🎯 **Full `chainExists_C ⊥ μQ` discharge for ANY μQ** (paper §9.4).
    Combines:
    - μQ.colLens = [] → μQ = ⊥ → chainExists_C_empty
    - μQ.colLens = [k] → chainExists_C_single_col_Q
    - μQ.colLens longer → PBPSet vacuously empty -/
theorem chainExists_C_P_bot (μQ : YoungDiagram) :
    ChainExists_C (⊥ : YoungDiagram) μQ := by
  intro σ
  have hγ : σ.val.γ = .C := σ.prop.1
  have hP_σ : σ.val.P.shape = ⊥ := σ.prop.2.1
  have hQ_σ : σ.val.Q.shape = μQ := σ.prop.2.2
  have h_len : μQ.colLens.length ≤ 1 := by
    rw [← hQ_σ]
    exact Q_colLens_length_le_one_of_C_P_bot hγ hP_σ
  match h : μQ.colLens with
  | [] =>
    have hμQ_bot : μQ = ⊥ := yd_of_colLens_nil h
    subst hμQ_bot
    exact chainExists_C_empty σ
  | [k] =>
    have hk_pos : k ≥ 1 := by
      have hk_pos' : 0 < k :=
        YoungDiagram.pos_of_mem_colLens μQ k (h ▸ List.mem_singleton.mpr rfl)
      omega
    exact chainExists_C_single_col_Q hk_pos h σ
  | _ :: _ :: _ =>
    rw [h] at h_len
    simp at h_len

end BMSZ
