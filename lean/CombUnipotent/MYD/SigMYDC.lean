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

/-- Chain existence for C-type PBP under dp-coherence + sort + odd.
    Deferred: the recursive construction requires propagating
    coherence through `descentCD_PBP` to the inner D-type chain.
    Structure is parallel to `exists_descentChain_Bplus_aux`. -/
theorem exists_descentChain_C {μP μQ : YoungDiagram} (σ : PBPSet .C μP μQ)
    (_dp : DualPart) (_h_coh : PBPIsCoherent_C σ.val _dp)
    (_hsort : _dp.SortedGE) (_hodd : ∀ r ∈ _dp, Odd r) :
    ∃ c : List ACStepData, IsDescentChain_C σ.val c := by
  sorry

/-- Simplified signature that takes σ and defers the coherence hypothesis
    via Classical.choice on existence of a matching dp. -/
theorem exists_descentChain_C_simple {μP μQ : YoungDiagram} (σ : PBPSet .C μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_C σ.val c := by
  sorry

/-! ## Per-step thetaLift singleton (paper §11.5/11.6) -/

/-- Per-step thetaLift singleton for C chain. The C step uses
    `thetaLift_DC` (target .C dispatches to D→C lift), which needs
    the std-case hypothesis `addp ≥ 0 ∧ addn ≥ 0` for sign preservation.
    Paper §11.5/11.6 provides this via the chain's structure. -/
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
