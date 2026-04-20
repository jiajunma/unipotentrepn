/-
# B+ chain infrastructure for `MYD_sig .Bplus`

Mirror of `IsDescentChain_D` + `descentChain_sign_match_D` for Bplus.

Reference: `lean/CombUnipotent/MYD/PhiDTyped.lean` (D-side template),
`lean/CombUnipotent/MYD/SigMYD.lean` (sign-match template).

The B-chain uses `doubleDescent_B_PBP` (which always outputs `.Bplus`).
For Bminus τ, the first descent step still produces a Bplus inner τ;
subsequent steps stay in Bplus.
-/
import CombUnipotent.MYD.SigMYD
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.CorrespondenceB
import CombUnipotent.CountingProof.Basic

namespace BMSZ

open PBPInstantiation (toACStepData_Bplus toACStepData_Bminus)

/-! ## Inductive chain predicate -/

/-- Inductive descent chain predicate for B+ type. Steps use
    `doubleDescent_B_PBP` (always produces Bplus inner). -/
inductive IsDescentChain_Bplus : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .Bplus)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_Bplus τ []
  | step {τ : PBP} (hγ : τ.γ = .Bplus) {chain : List ACStepData}
      (h_rest : IsDescentChain_Bplus
        (doubleDescent_B_PBP τ (Or.inl hγ))
        (by
          have : (doubleDescent_B_PBP τ (Or.inl hγ)).γ = .Bplus := rfl
          exact chain)) :
      IsDescentChain_Bplus τ (chain ++ [toACStepData_Bplus τ hγ])

/-! ## Existence -/

/-- For a B+ PBP, a descent chain exists by strong induction on
    combined shape size. Each `doubleDescent_B_PBP` strictly decreases
    the size (via `YoungDiagram.shiftLeft_card_lt`). -/
theorem exists_descentChain_Bplus_aux (n : ℕ) :
    ∀ (τ : PBP) (hγ : τ.γ = .Bplus),
      τ.P.shape.cells.card + τ.Q.shape.cells.card = n →
      ∃ c : List ACStepData, IsDescentChain_Bplus τ c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hγ hsize
    by_cases h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥
    · exact ⟨[], IsDescentChain_Bplus.base τ hγ h_empty⟩
    · -- At least one shape is non-empty
      have h_decrease :
          (doubleDescent_B_PBP τ (Or.inl hγ)).P.shape.cells.card +
          (doubleDescent_B_PBP τ (Or.inl hγ)).Q.shape.cells.card < n := by
        unfold doubleDescent_B_PBP
        dsimp only
        have hP_le := YoungDiagram.shiftLeft_card_le τ.P.shape
        have hQ_le := YoungDiagram.shiftLeft_card_le τ.Q.shape
        push_neg at h_empty
        by_cases hP_empty : τ.P.shape = ⊥
        · have hQ_ne : τ.Q.shape ≠ ⊥ := h_empty hP_empty
          have hQ_col0 : 0 < τ.Q.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hQ_ne ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hQ_lt := YoungDiagram.shiftLeft_card_lt τ.Q.shape hQ_col0
          omega
        · have hP_col0 : 0 < τ.P.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hP_empty ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hP_lt := YoungDiagram.shiftLeft_card_lt τ.P.shape hP_col0
          omega
      have hγ_inner : (doubleDescent_B_PBP τ (Or.inl hγ)).γ = .Bplus := rfl
      obtain ⟨c_inner, h_inner⟩ :=
        ih _ h_decrease (doubleDescent_B_PBP τ (Or.inl hγ)) hγ_inner rfl
      exact ⟨c_inner ++ [toACStepData_Bplus τ hγ],
             IsDescentChain_Bplus.step hγ h_inner⟩

/-- Every B+ PBPSet element admits a descent chain. -/
theorem exists_descentChain_Bplus {μP μQ : YoungDiagram} (σ : PBPSet .Bplus μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_Bplus σ.val c := by
  have hγ : σ.val.γ = .Bplus := σ.prop.1
  exact exists_descentChain_Bplus_aux _ σ.val hγ rfl

/-! ## Per-step thetaLift singleton (paper §11.5/11.6) -/

/-- Per-step thetaLift singleton for B+ chain: under the std hypothesis
    `addp ≥ 0 ∧ addn ≥ 0`, the thetaLift_MB output is a singleton. -/
theorem descent_step_thetaLift_singleton_Bplus_std {τ : PBP} (hγ : τ.γ = .Bplus)
    (E_inner : ILS)
    (h_std :
      (toACStepData_Bplus τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2 ≥ 0 ∧
      (toACStepData_Bplus τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1 ≥ 0) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_Bplus τ hγ))
      (toACStepData_Bplus τ hγ).γ
      (toACStepData_Bplus τ hγ).p
      (toACStepData_Bplus τ hγ).q = [E'] := by
  -- Bplus has no pre-twist
  have h_preTwist : stepPreTwist E_inner (toACStepData_Bplus τ hγ) = E_inner := by
    unfold stepPreTwist; simp [toACStepData_Bplus]
  -- target .Bplus dispatches to thetaLift_MB
  refine ⟨?_, ?_⟩
  · exact ILS.augment ((toACStepData_Bplus τ hγ).p - (ILS.sign E_inner).1 -
      (ILS.firstColSign E_inner).2,
      (toACStepData_Bplus τ hγ).q - (ILS.sign E_inner).2 -
      (ILS.firstColSign E_inner).1)
      (ILS.charTwistCM E_inner
        (((toACStepData_Bplus τ hγ).p - (toACStepData_Bplus τ hγ).q + 1) / 2))
  rw [h_preTwist]
  show ILS.thetaLift E_inner _ _ _ = _
  simp only [ILS.thetaLift]
  have hγ' : (toACStepData_Bplus τ hγ).γ = .Bplus := rfl
  rw [hγ']
  simp only [ILS.thetaLift_MB]
  rw [if_pos h_std]

/-- Per-step thetaLift singleton for B+ chain. Paper §11.5/11.6:
    along a valid chain, the std hypothesis holds, yielding singleton. -/
theorem descent_step_thetaLift_singleton_Bplus {τ : PBP} (hγ : τ.γ = .Bplus)
    (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_Bplus τ hγ))
      (toACStepData_Bplus τ hγ).γ
      (toACStepData_Bplus τ hγ).p
      (toACStepData_Bplus τ hγ).q = [E'] := by
  -- The std hypothesis holds along valid chains by paper §11.5/11.6.
  -- Deferred as a single sorry here; delegate via _std variant once
  -- the std-condition lemma is available.
  sorry

/-- Any valid B+ descent chain is `ChainSingleton`-valid. -/
theorem descentChain_Bplus_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_Bplus τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .Bplus) chain E := by
  induction h_chain with
  | base τ hγ h_empty => exact ⟨baseILS .Bplus, ChainSingleton.nil _⟩
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_inner, h_inner⟩ := ih
    obtain ⟨E', h_theta⟩ := descent_step_thetaLift_singleton_Bplus hγ E_inner
    exact ⟨stepPostTwist E' (toACStepData_Bplus τ_outer hγ),
           ChainSingleton.snoc h_inner h_theta⟩

/-! ## Sign target + sign match -/

/-- Sign target for B+ PBP. -/
noncomputable def signTarget_Bplus (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))

/-- For an empty B+ PBP, signature is (1, 0). -/
private theorem signature_empty_Bplus (τ : PBP) (hγ : τ.γ = .Bplus)
    (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
    PBP.signature τ = (1, 0) := by
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

/-- Sign of `baseILS .Bplus = [(1, 0)]` is `(1, 0)`. -/
private theorem sign_baseILS_Bplus : ILS.sign (baseILS .Bplus) = (1, 0) := by
  unfold baseILS ILS.sign
  decide

/-- **Theorem**: along a valid B+ descent chain, the extracted ILS
    has sign matching `signTarget_Bplus τ`. Mirror of
    `descentChain_sign_match_D`. -/
theorem descentChain_sign_match_Bplus {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_Bplus τ chain)
    (h_sing : ChainSingleton (baseILS .Bplus) chain E) :
    ILS.sign E = signTarget_Bplus τ := by
  induction h_chain generalizing E with
  | base τ hγ h_empty =>
    cases h_sing
    show ILS.sign (baseILS .Bplus) = signTarget_Bplus τ
    rw [sign_baseILS_Bplus]
    unfold signTarget_Bplus
    rw [signature_empty_Bplus τ hγ h_empty]
    rfl
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- B+ has no pre-twist (γ = .Bplus, not .C/.M)
    have h_preTwist : stepPreTwist E_mid (toACStepData_Bplus τ_outer hγ) = E_mid := by
      unfold stepPreTwist
      simp [toACStepData_Bplus]
    -- ILS.thetaLift with target .Bplus dispatches to thetaLift_MB
    have h_tl : ILS.thetaLift E_mid .Bplus
                  (toACStepData_Bplus τ_outer hγ).p
                  (toACStepData_Bplus τ_outer hγ).q = [E'] := by
      rw [← h_preTwist]
      show ILS.thetaLift (stepPreTwist E_mid (toACStepData_Bplus τ_outer hγ))
        (toACStepData_Bplus τ_outer hγ).γ
        (toACStepData_Bplus τ_outer hγ).p
        (toACStepData_Bplus τ_outer hγ).q = [E']
      exact h_theta
    have h_tl_mb : ILS.thetaLift_MB E_mid
                    (toACStepData_Bplus τ_outer hγ).p
                    (toACStepData_Bplus τ_outer hγ).q = [E'] := by
      simpa [ILS.thetaLift] using h_tl
    have h_sign_E' : ILS.sign E' =
        ((toACStepData_Bplus τ_outer hγ).p, (toACStepData_Bplus τ_outer hγ).q) :=
      ILS.thetaLift_MB_sign E_mid _ _ E' (by rw [h_tl_mb]; simp)
    -- Post-twist preserves sign for B+
    have h_sign_E : ILS.sign E = ILS.sign E' := by
      rw [h_E_final]
      unfold stepPostTwist
      split_ifs with hpost
      · exact ILS.twistBD_sign E' 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · rfl
    rw [h_sign_E, h_sign_E']
    unfold signTarget_Bplus toACStepData_Bplus
    simp

/-! ## B⁻ chain (single outer Bminus step + inner Bplus chain) -/

/-- Inductive descent chain predicate for B⁻ type. The single outer
    descent step uses `doubleDescent_B_PBP τ (Or.inr hγ)`; the inner
    chain is on the Bplus result. -/
inductive IsDescentChain_Bminus : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .Bminus)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_Bminus τ []
  | step {τ : PBP} (hγ : τ.γ = .Bminus) {chain : List ACStepData}
      (h_rest : IsDescentChain_Bplus
        (doubleDescent_B_PBP τ (Or.inr hγ)) chain) :
      IsDescentChain_Bminus τ (chain ++ [toACStepData_Bminus τ hγ])

theorem exists_descentChain_Bminus_aux (n : ℕ) :
    ∀ (τ : PBP) (hγ : τ.γ = .Bminus),
      τ.P.shape.cells.card + τ.Q.shape.cells.card = n →
      ∃ c : List ACStepData, IsDescentChain_Bminus τ c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hγ hsize
    by_cases h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥
    · exact ⟨[], IsDescentChain_Bminus.base τ hγ h_empty⟩
    · -- Use Bplus existence on the inner descent
      have h_decrease :
          (doubleDescent_B_PBP τ (Or.inr hγ)).P.shape.cells.card +
          (doubleDescent_B_PBP τ (Or.inr hγ)).Q.shape.cells.card < n := by
        unfold doubleDescent_B_PBP
        dsimp only
        have hP_le := YoungDiagram.shiftLeft_card_le τ.P.shape
        have hQ_le := YoungDiagram.shiftLeft_card_le τ.Q.shape
        push_neg at h_empty
        by_cases hP_empty : τ.P.shape = ⊥
        · have hQ_ne : τ.Q.shape ≠ ⊥ := h_empty hP_empty
          have hQ_col0 : 0 < τ.Q.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hQ_ne ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hQ_lt := YoungDiagram.shiftLeft_card_lt τ.Q.shape hQ_col0
          omega
        · have hP_col0 : 0 < τ.P.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hP_empty ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hP_lt := YoungDiagram.shiftLeft_card_lt τ.P.shape hP_col0
          omega
      have hγ_inner : (doubleDescent_B_PBP τ (Or.inr hγ)).γ = .Bplus := rfl
      obtain ⟨c_inner, h_inner⟩ :=
        exists_descentChain_Bplus_aux _ (doubleDescent_B_PBP τ (Or.inr hγ))
          hγ_inner rfl
      exact ⟨c_inner ++ [toACStepData_Bminus τ hγ],
             IsDescentChain_Bminus.step hγ h_inner⟩

theorem exists_descentChain_Bminus {μP μQ : YoungDiagram}
    (σ : PBPSet .Bminus μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_Bminus σ.val c := by
  have hγ : σ.val.γ = .Bminus := σ.prop.1
  exact exists_descentChain_Bminus_aux _ σ.val hγ rfl

/-- Per-step thetaLift singleton for Bminus outer step. Paper §11.5/11.6. -/
theorem descent_step_thetaLift_singleton_Bminus {τ : PBP} (hγ : τ.γ = .Bminus)
    (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_Bminus τ hγ))
      (toACStepData_Bminus τ hγ).γ
      (toACStepData_Bminus τ hγ).p
      (toACStepData_Bminus τ hγ).q = [E'] := by
  sorry

/-- Bminus chain singleton: extracted ILS starts from `baseILS .Bminus`.
    Base case OK; step case has a base-type mismatch (inner uses
    `baseILS .Bplus` but Bminus expects `baseILS .Bminus`).
    Reconciliation deferred — needs base-translation lemma between
    `baseILS .Bplus` and `baseILS .Bminus` via the outer Bminus step. -/
theorem descentChain_Bminus_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_Bminus τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .Bminus) chain E := by
  cases h_chain with
  | base hγ _h_empty =>
    exact ⟨baseILS .Bminus, ChainSingleton.nil _⟩
  | step hγ h_rest =>
    -- Inner Bplus chain singleton starts from baseILS .Bplus.
    -- Translating to baseILS .Bminus needs a base reconciliation lemma.
    sorry

/-- Sign target for B⁻ PBP. -/
noncomputable def signTarget_Bminus' (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))

private theorem signature_empty_Bminus (τ : PBP) (hγ : τ.γ = .Bminus)
    (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
    PBP.signature τ = (0, 1) := by
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

private theorem sign_baseILS_Bminus : ILS.sign (baseILS .Bminus) = (0, 1) := by
  unfold baseILS ILS.sign
  decide

/-- Sign match for Bminus chain: outer Bminus step lifts via thetaLift_MB
    + post-twist preserves sign. -/
theorem descentChain_sign_match_Bminus {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_Bminus τ chain)
    (h_sing : ChainSingleton (baseILS .Bminus) chain E) :
    ILS.sign E = signTarget_Bminus' τ := by
  cases h_chain with
  | base hγ h_empty =>
    cases h_sing
    show ILS.sign (baseILS .Bminus) = signTarget_Bminus' τ
    rw [sign_baseILS_Bminus]
    unfold signTarget_Bminus'
    rw [signature_empty_Bminus τ hγ h_empty]
    rfl
  | step hγ h_rest =>
    -- τ is from outer scope; chain is unified to chain_inner ++ [...]
    rename_i chain_inner
    obtain ⟨E_mid, E', _h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Bminus has no pre-twist
    have h_preTwist : stepPreTwist E_mid (toACStepData_Bminus τ hγ) = E_mid := by
      unfold stepPreTwist
      simp [toACStepData_Bminus]
    -- target .Bminus dispatches to thetaLift_MB
    have h_tl : ILS.thetaLift E_mid .Bminus
                  (toACStepData_Bminus τ hγ).p
                  (toACStepData_Bminus τ hγ).q = [E'] := by
      rw [← h_preTwist]
      show ILS.thetaLift (stepPreTwist E_mid (toACStepData_Bminus τ hγ))
        (toACStepData_Bminus τ hγ).γ
        (toACStepData_Bminus τ hγ).p
        (toACStepData_Bminus τ hγ).q = [E']
      exact h_theta
    have h_tl_mb : ILS.thetaLift_MB E_mid
                    (toACStepData_Bminus τ hγ).p
                    (toACStepData_Bminus τ hγ).q = [E'] := by
      simpa [ILS.thetaLift] using h_tl
    have h_sign_E' : ILS.sign E' =
        ((toACStepData_Bminus τ hγ).p, (toACStepData_Bminus τ hγ).q) :=
      ILS.thetaLift_MB_sign E_mid _ _ E' (by rw [h_tl_mb]; simp)
    have h_sign_E : ILS.sign E = ILS.sign E' := by
      rw [h_E_final]
      unfold stepPostTwist
      split_ifs with hpost
      · exact ILS.twistBD_sign E' 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · rfl
    rw [h_sign_E, h_sign_E']
    unfold signTarget_Bminus' toACStepData_Bminus
    simp

end BMSZ
