/-
# Counting Proof: B-type correspondence (Proposition 10.11 for B)

Reference: [BMSZb] Proposition 10.11, Section 10.5–10.6.

Proves: card(PBPSet .Bplus μP μQ) + card(PBPSet .Bminus μP μQ) = tripleSum(countPBP_B dp)

Proof strategy (mirrors Correspondence.lean for D-type):
1. Double descent B→M→B maps PBPSet_B(μP, μQ) → PBPSet_B(shiftLeft μP, shiftLeft μQ)
2. Combined with (signature, epsilon), the map is injective (ddescent_inj_B)
3. Fiber cardinality per tail class gives the tailCoeffs recursion
4. Primitive case: uniform fiber → multiply by total
5. Balanced case: matrix multiply by (tDD, tRC, tSS) / (scDD, scRC, scSS)
-/
import CombUnipotent.CountingProof.Basic
import CombUnipotent.CountingProof.Fiber
import CombUnipotent.CountingProof.LiftRC
import CombUnipotent.CountingProof.Correspondence
import Mathlib.Algebra.Ring.Parity

open Classical

/-! ## B-type recursion: dropping 2 rows = shiftLeft -/

/-- Recursion: tail of B-P columns = B-P columns of rest. -/
theorem dpartColLensP_B_tail (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensP_B (r₁ :: r₂ :: rest)).tail = dpartColLensP_B rest := by
  simp [dpartColLensP_B]

/-- Recursion: tail of B-Q columns = B-Q columns of rest. -/
theorem dpartColLensQ_B_tail (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensQ_B (r₁ :: r₂ :: rest)).tail = dpartColLensQ_B rest := by
  simp [dpartColLensQ_B]

/-! ## B⁺/B⁻ symmetry -/

/-- PBP equality follows from equality of the three data fields (γ, P, Q);
    proof fields are irrelevant by proof irrelevance. -/
private theorem PBP_eq_of_data (τ₁ τ₂ : PBP)
    (h1 : τ₁.γ = τ₂.γ) (h2 : τ₁.P = τ₂.P) (h3 : τ₁.Q = τ₂.Q) : τ₁ = τ₂ := by
  cases τ₁; cases τ₂; simp at h1 h2 h3; subst h1; subst h2; subst h3; rfl

/-- Swap B⁺ ↔ B⁻ in a PBP, preserving all constraints.
    This works because `DRCSymbol.allowed .Bplus s σ ↔ DRCSymbol.allowed .Bminus s σ`
    for all sides `s` and symbols `σ` (both have P∈{•,c}, Q∈{•,s,r,d}). -/
def PBP.swapBplusBminus (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) : PBP where
  γ := if τ.γ = .Bplus then .Bminus else .Bplus
  P := τ.P
  Q := τ.Q
  sym_P := by
    intro i j hmem; have := τ.sym_P i j hmem
    rcases hγ with h | h <;> simp [h, DRCSymbol.allowed] at this ⊢ <;> exact this
  sym_Q := by
    intro i j hmem; have := τ.sym_Q i j hmem
    rcases hγ with h | h <;> simp [h, DRCSymbol.allowed] at this ⊢ <;> exact this
  dot_match := τ.dot_match
  mono_P := τ.mono_P
  mono_Q := τ.mono_Q
  row_s := τ.row_s
  row_r := τ.row_r
  col_c_P := τ.col_c_P
  col_c_Q := τ.col_c_Q
  col_d_P := τ.col_d_P
  col_d_Q := τ.col_d_Q

/-- B⁺ and B⁻ have the same cardinality: the allowed symbol sets are identical,
    so swapping the γ tag gives a bijection PBPSet .Bplus μP μQ ≃ PBPSet .Bminus μP μQ. -/
theorem card_Bplus_eq_Bminus (μP μQ : YoungDiagram) :
    Fintype.card (PBPSet .Bplus μP μQ) = Fintype.card (PBPSet .Bminus μP μQ) := by
  apply Fintype.card_congr
  refine {
    toFun := fun ⟨τ, hγ, hP, hQ⟩ =>
      ⟨τ.swapBplusBminus (Or.inl hγ), by simp [PBP.swapBplusBminus, hγ], hP, hQ⟩
    invFun := fun ⟨τ, hγ, hP, hQ⟩ =>
      ⟨τ.swapBplusBminus (Or.inr hγ), by simp [PBP.swapBplusBminus, hγ], hP, hQ⟩
    left_inv := fun ⟨τ, hγ, hP, hQ⟩ => by
      simp only; congr 1
      exact PBP_eq_of_data _ _ (by simp [PBP.swapBplusBminus, hγ]) rfl rfl
    right_inv := fun ⟨τ, hγ, hP, hQ⟩ => by
      simp only; congr 1
      exact PBP_eq_of_data _ _ (by simp [PBP.swapBplusBminus, hγ]) rfl rfl
  }

/-! ## Base cases -/

/-- Base case: empty orbit → 1 B⁺ PBP and 1 B⁻ PBP. -/
theorem card_PBPSet_B_empty :
    Fintype.card (PBPSet .Bplus ⊥ ⊥) + Fintype.card (PBPSet .Bminus ⊥ ⊥) =
    tripleSum (countPBP_B []) := by
  simp [card_PBPSet_bot, tripleSum, countPBP_B]

/-- Single row base case. -/
theorem card_PBPSet_B_singleton (r₁ : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : Even r₁) (hr : r₁ > 0) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B [r₁]) := by
  -- Strategy: dpartColLensP_B [r₁] = [] so μP = ⊥ (empty P diagram).
  -- dpartColLensQ_B [r₁] = [r₁/2] so Q has one column of height r₁/2.
  -- P is empty, so all PBP constraints reduce to Q-only constraints.
  -- Q cells in col 0 must be from {•,s,r,d} with layer monotonicity.
  -- Direct enumeration of valid Q-paintings gives the count.
  -- Needs: card_PBPSet_bot-like lemma for single-column case.
  sorry

/-! ## Double descent B→M→B -/

/-! ### Helper lemmas for B-type double descent -/

/-- For B⁺/B⁻ type: dotScolLen(P) = dotDiag(P).colLen, since P only has {dot, c}
    and c has layerOrd = 3 > 1. So dotSdiag(P) = dotDiag(P). -/
private theorem dotScolLen_P_eq_dotDiag_colLen_B (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) (j : ℕ) :
    PBP.dotScolLen τ.P j = (PBP.dotDiag τ.P τ.mono_P).colLen j := by
  rw [PBP.dotScolLen_eq_dotSdiag_colLen τ.P τ.mono_P]
  congr 1; ext ⟨i, k⟩
  simp only [PBP.dotSdiag, PBP.dotDiag, Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · intro ⟨hmem, hlo⟩
    by_cases hd : τ.P.paint i k = .dot
    · exact ⟨hmem, hd⟩
    · exfalso
      have := PBP.P_nonDot_eq_c_of_B τ hγ i k hmem hd
      rw [this, DRCSymbol.layerOrd] at hlo; omega
  · intro ⟨hmem, hd⟩; exact ⟨hmem, by rw [hd]; decide⟩

/-- For B⁺/B⁻: dotScolLen(P, j) ≤ dotScolLen(Q, j).
    Because dotScolLen(P) = dotDiag(P).colLen = dotDiag(Q).colLen ≤ dotSdiag(Q).colLen = dotScolLen(Q). -/
private theorem dotScolLen_P_le_Q_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) (j : ℕ) :
    PBP.dotScolLen τ.P j ≤ PBP.dotScolLen τ.Q j := by
  rw [dotScolLen_P_eq_dotDiag_colLen_B τ hγ, PBP.dotScolLen_eq_dotSdiag_colLen τ.Q τ.mono_Q]
  -- dotDiag(P).colLen j ≤ dotSdiag(Q).colLen j because dotDiag(P) ⊆ dotSdiag(Q)
  by_contra hlt; push_neg at hlt
  set b := (PBP.dotSdiag τ.Q τ.mono_Q).colLen j
  have hmem : (b, j) ∈ PBP.dotDiag τ.P τ.mono_P := YoungDiagram.mem_iff_lt_colLen.mpr hlt
  simp only [PBP.dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  have ⟨hmemP, hpaint⟩ := hmem
  have ⟨hmemQ, hQpaint⟩ := (τ.dot_match b j).mp ⟨hmemP, hpaint⟩
  have hmemS : (b, j) ∈ PBP.dotSdiag τ.Q τ.mono_Q := by
    rw [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hmemQ, by rw [hQpaint]; decide⟩
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmemS) (by omega)

/-- For B⁺/B⁻: if i < dotScolLen(P, j) then (i,j) ∈ P.shape and P.paint(i,j) = dot. -/
private theorem P_dot_of_lt_dotScolLen_B (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) {i j : ℕ}
    (h : i < PBP.dotScolLen τ.P j) :
    (i, j) ∈ τ.P.shape ∧ τ.P.paint i j = .dot := by
  rw [dotScolLen_P_eq_dotDiag_colLen_B τ hγ] at h
  have hmem : (i, j) ∈ PBP.dotDiag τ.P τ.mono_P := YoungDiagram.mem_iff_lt_colLen.mpr h
  simp only [PBP.dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem

/-- B-type paintL outside P.shape gives dot. -/
private theorem doubleDescent_B_paintL_dot (τ : PBP)
    (_hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i j : ℕ} (h_ge : i ≥ τ.P.shape.colLen (j + 1)) :
    PBP.doubleDescent_B_paintL τ i j = .dot := by
  simp only [PBP.doubleDescent_B_paintL]
  have hds := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  rw [if_neg (by omega)]
  exact τ.P.paint_outside i (j + 1) (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

/-- B-type paintR outside Q.shape gives dot. -/
private theorem doubleDescent_B_paintR_dot (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i j : ℕ} (h_ge : i ≥ τ.Q.shape.colLen (j + 1)) :
    PBP.doubleDescent_B_paintR τ i j = .dot := by
  simp only [PBP.doubleDescent_B_paintR]
  have hdsP := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  have hdsQ := PBP.dotScolLen_le_colLen τ.Q τ.mono_Q (j + 1)
  have hPQ := dotScolLen_P_le_Q_of_B τ hγ (j + 1)
  rw [if_neg (by omega), if_neg (by omega)]
  exact τ.Q.paint_outside i (j + 1) (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

/-- The double descent PBP ∇²τ for B type. -/
noncomputable def doubleDescent_B_PBP (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) : PBP where
  γ := .Bplus  -- B⁺/B⁻ have identical allowed symbols; choose B⁺ as default
  P := {
    shape := τ.P.shape.shiftLeft
    paint := PBP.doubleDescent_B_paintL τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_B_paintL_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  Q := {
    shape := τ.Q.shape.shiftLeft
    paint := PBP.doubleDescent_B_paintR τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_B_paintR_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  sym_P := by
    intro i j hmem
    simp only [PBP.doubleDescent_B_paintL, DRCSymbol.allowed]
    by_cases h : i < PBP.dotScolLen τ.P (j + 1)
    · simp [if_pos h]
    · simp only [if_neg h]
      have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
      have hds := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
      -- P.paint(i, j+1) ∈ {dot, c} for B type
      have hP_in_shape : (i, j + 1) ∈ τ.P.shape := hmem'
      have := τ.sym_P i (j + 1) hP_in_shape
      rcases hγ with h₁ | h₁ <;> rw [h₁] at this <;> simp [DRCSymbol.allowed] at this ⊢ <;>
        exact this
  sym_Q := by
    intro i j hmem
    simp only [PBP.doubleDescent_B_paintR, DRCSymbol.allowed]
    by_cases h₁ : i < PBP.dotScolLen τ.P (j + 1)
    · simp [if_pos h₁]
    · simp only [if_neg h₁]
      by_cases h₂ : i < PBP.dotScolLen τ.Q (j + 1)
      · simp [if_pos h₂]
      · simp only [if_neg h₂]
        have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
        have := τ.sym_Q i (j + 1) hmem'
        rcases hγ with h₁ | h₁ <;> rw [h₁] at this <;> simp [DRCSymbol.allowed] at this ⊢ <;>
          exact this
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP, hpaint⟩
      have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
      simp only [PBP.doubleDescent_B_paintL] at hpaint
      by_cases h : i < PBP.dotScolLen τ.P (j + 1)
      · -- dot zone: P.paint(i, j+1) = dot → (i,j+1) ∈ Q.shape by dot_match
        have ⟨_, hpd⟩ := P_dot_of_lt_dotScolLen_B τ hγ h
        have ⟨hmemQ, _⟩ := (τ.dot_match i (j + 1)).mp ⟨hmemP', hpd⟩
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemQ, ?_⟩
        simp [PBP.doubleDescent_B_paintR, if_pos h]
      · -- non-dot zone: P.paint(i, j+1) = dot
        rw [if_neg h] at hpaint
        -- P.paint(i, j+1) = dot but i ≥ dotScolLen(P, j+1)
        -- This means (i, j+1) ∈ P.shape and paint = dot
        have hmemP2 : (i, j + 1) ∈ τ.P.shape := hmemP'
        have ⟨hmemQ, _⟩ := (τ.dot_match i (j + 1)).mp ⟨hmemP2, hpaint⟩
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemQ, ?_⟩
        simp only [PBP.doubleDescent_B_paintR, if_neg h]
        -- Q.paint(i, j+1) = dot by dot_match
        have hQd := ((τ.dot_match i (j + 1)).mp ⟨hmemP2, hpaint⟩).2
        -- need i ≥ dotScolLen(Q, j+1) too, then paintR gives Q.paint = dot
        -- Actually: if P.paint = dot at i ≥ dotScolLen(P), contradiction with
        -- the fact that dotScolLen(P) = dotDiag(P).colLen for B type
        exfalso
        have := PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp h) hmemP2
        exact this hpaint
    · intro ⟨hmemQ, hpaint⟩
      have hmemQ' := YoungDiagram.mem_shiftLeft.mp hmemQ
      simp only [PBP.doubleDescent_B_paintR] at hpaint
      by_cases h : i < PBP.dotScolLen τ.P (j + 1)
      · -- dot zone: Q.paint(i, j+1) = dot → (i,j+1) ∈ P.shape
        have ⟨_, hpd⟩ := P_dot_of_lt_dotScolLen_B τ hγ h
        have hmemP := (τ.dot_match i (j + 1)).mpr
          ⟨hmemQ', ((τ.dot_match i (j + 1)).mp
            ⟨(P_dot_of_lt_dotScolLen_B τ hγ h).1, hpd⟩).2⟩ |>.1
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemP, ?_⟩
        simp [PBP.doubleDescent_B_paintL, if_pos h]
      · rw [if_neg h] at hpaint
        by_cases h₂ : i < PBP.dotScolLen τ.Q (j + 1)
        · -- s zone: Q'(i,j) = s ≠ dot, contradiction
          rw [if_pos h₂] at hpaint; exact absurd hpaint (by decide)
        · -- pass-through zone: Q.paint(i, j+1) = dot
          rw [if_neg h₂] at hpaint
          have ⟨hmemP, hpPd⟩ := (τ.dot_match i (j + 1)).mpr ⟨hmemQ', hpaint⟩
          -- But i ≥ dotScolLen(P) and P.paint = dot → contradiction
          exfalso
          exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp h) hmemP hpPd
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_B_paintL]
    by_cases h₁ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · rw [if_neg h₁]
      have hds_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
      rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
          ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hds_anti
      by_cases h₂ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
      · -- impossible: i₁ ≥ dotScolLen(j₁+1) ≥ dotScolLen(j₂+1) > i₂ ≥ i₁
        omega
      · rw [if_neg h₂]
        exact τ.mono_P i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_B_paintR]
    by_cases h₁ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · rw [if_neg h₁]
      by_cases h₂ : i₁ < PBP.dotScolLen τ.Q (j₁ + 1)
      · rw [if_pos h₂]
        -- s has layerOrd 1
        have hdsP_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hdsP_anti
        have hdsQ_anti := (PBP.dotSdiag τ.Q τ.mono_Q).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at hdsQ_anti
        -- i₁ ≤ i₂ and dotScolLen(P) is anti-monotone, so i₂ ≥ dotScolLen(P, j₂+1) too
        -- (since i₁ ≥ dotScolLen(P, j₁+1) ≥ dotScolLen(P, j₂+1))
        have h₃ : ¬(i₂ < PBP.dotScolLen τ.P (j₂ + 1)) := by omega
        rw [if_neg h₃]
        by_cases h₄ : i₂ < PBP.dotScolLen τ.Q (j₂ + 1)
        · simp [if_pos h₄, DRCSymbol.layerOrd]
        · rw [if_neg h₄]
          have hlo := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.Q τ.mono_Q
            (Nat.not_lt.mp h₄) hmem'
          simp only [DRCSymbol.layerOrd] at hlo ⊢; omega
      · rw [if_neg h₂]
        have hdsP_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hdsP_anti
        have hdsQ_anti := (PBP.dotSdiag τ.Q τ.mono_Q).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at hdsQ_anti
        have hPQ := dotScolLen_P_le_Q_of_B τ hγ (j₁ + 1)
        have h₃ : ¬(i₂ < PBP.dotScolLen τ.P (j₂ + 1)) := by omega
        rw [if_neg h₃]
        have h₄ : ¬(i₂ < PBP.dotScolLen τ.Q (j₂ + 1)) := by omega
        rw [if_neg h₄]
        exact τ.mono_Q i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: s in P' = doubleDescent_B_paintL. But B-type P has {dot, c}.
      -- paintL gives dot or P.paint (∈ {dot, c}). s ∉ {dot, c}.
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        -- P.paint(i, j₁+1) = s, but P ∈ {dot, c} for B type
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- L,R: s in P' impossible (same as above)
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- R,L: s in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i < PBP.dotScolLen τ.P (j₂ + 1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₂+1) hmem (by rw [h₂]; decide)
        rw [this] at h₂; exact absurd h₂ (by decide)
    · -- Both R: s in Q' comes from doubleDescent_B_paintR
      simp only [PBP.doubleDescent_B_paintR] at h₁ h₂
      -- s comes from zone 2 (dotScolLen(P) ≤ i < dotScolLen(Q)) or zone 3 (Q.paint = s)
      by_cases ha₁ : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁
        by_cases ha₂ : i < PBP.dotScolLen τ.P (j₂ + 1)
        · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg ha₂] at h₂
          by_cases hb₁ : i < PBP.dotScolLen τ.Q (j₁ + 1)
          · rw [if_pos hb₁] at h₁  -- h₁ : s = s
            by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂ + 1)
            · rw [if_pos hb₂] at h₂  -- h₂ : s = s
              -- Both in zone 2: s came from the middle zone, row_s not constraining
              -- Actually row_s says: at most one s per row. But both are from zone 2.
              -- Need to use row_s of τ or argue differently.
              -- In zone 2: paintR = s (synthetic). The original Q.paint at those positions
              -- has layerOrd ≤ 1 (below dotScolLen(Q)) and ≥ dotScolLen(P).
              -- For Q with {dot, s, r, d}: layerOrd ≤ 1 means {dot, s}.
              -- And i ≥ dotScolLen(P, j+1) means P.paint ≠ dot (for B type, layerOrd > 1).
              -- By dot_match: P.paint ≠ dot ↔ Q.paint ≠ dot. So Q.paint = s.
              -- So both Q.paint(i, j₁+1) = s and Q.paint(i, j₂+1) = s.
              -- By row_s of τ on Q side: j₁+1 = j₂+1.
              have hQs₁ : τ.Q.paint i (j₁ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₁)
                have hne : τ.Q.paint i (j₁ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₁+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₁ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  have ⟨_, hpd⟩ := (τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₁)
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).1 hpd
                revert hlo hne; cases τ.Q.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
              have hQs₂ : τ.Q.paint i (j₂ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₂)
                have hne : τ.Q.paint i (j₂ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₂+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₂ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  have ⟨_, hpd⟩ := (τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₂)
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).1 hpd
                revert hlo hne; cases τ.Q.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact hQs₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact hQs₂)
              exact ⟨rfl, by omega⟩
            · rw [if_neg hb₂] at h₂
              -- h₂ : Q.paint(i, j₂+1) = s. Combined with Q zone 2 at j₁.
              -- Q.paint(i, j₁+1) = s (proved above). Q.paint(i, j₂+1) = s (= h₂).
              -- Use row_s of τ.
              have hQs₁ : τ.Q.paint i (j₁ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₁)
                have hne : τ.Q.paint i (j₁ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₁+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₁ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₁)
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).1
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).2
                revert hlo hne; cases τ.Q.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact hQs₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
          · rw [if_neg hb₁] at h₁
            by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂ + 1)
            · rw [if_pos hb₂] at h₂
              -- h₁ : Q.paint(i, j₁+1) = s, zone 2 at j₂.
              have hQs₂ : τ.Q.paint i (j₂ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₂)
                have hne : τ.Q.paint i (j₂ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₂+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₂ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₂)
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).1
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).2
                revert hlo hne; cases τ.Q.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact hQs₂)
              exact ⟨rfl, by omega⟩
            · rw [if_neg hb₂] at h₂
              -- Both in zone 3: Q.paint(i, j₁+1) = s and Q.paint(i, j₂+1) = s
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: r in P' impossible (P ∈ {dot, c} for B type, paintL gives dot or P.paint)
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- L: r in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- R: r in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i < PBP.dotScolLen τ.P (j₂ + 1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₂+1) hmem (by rw [h₂]; decide)
        rw [this] at h₂; exact absurd h₂ (by decide)
    · -- Both R: r in Q' from doubleDescent_B_paintR
      simp only [PBP.doubleDescent_B_paintR] at h₁ h₂
      by_cases ha₁ : i < PBP.dotScolLen τ.P (j₁+1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁; by_cases hb₁ : i < PBP.dotScolLen τ.Q (j₁+1)
        · rw [if_pos hb₁] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb₁] at h₁
          by_cases ha₂ : i < PBP.dotScolLen τ.P (j₂+1)
          · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
          · rw [if_neg ha₂] at h₂; by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂+1)
            · rw [if_pos hb₂] at h₂; exact absurd h₂ (by decide)
            · rw [if_neg hb₂] at h₂
              have := τ.row_r i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .r by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .r by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    -- c only from the P.paint branch of paintL
    have hc₁ : τ.P.paint i₁ (j+1) = .c := by
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; exact h₁
    have hc₂ : τ.P.paint i₂ (j+1) = .c := by
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i₂ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; exact h₂
    exact τ.col_c_P (j+1) i₁ i₂ hc₁ hc₂
  col_c_Q := by
    intro j i₁ i₂ h₁ h₂
    -- c in Q' from doubleDescent_B_paintR: can only come from zone 3 (Q.paint)
    -- But Q has {dot, s, r, d} for B type. c ∉ {dot, s, r, d}.
    exfalso
    simp only [PBP.doubleDescent_B_paintR] at h₁
    by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
    · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
    · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.Q (j+1)
      · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg hb] at h₁
        -- h₁ : Q.paint(i₁, j+1) = c. But Q ∈ {dot, s, r, d} for B type.
        have hmem : (i₁, j + 1) ∈ τ.Q.shape := by
          by_contra hout; exact absurd (τ.Q.paint_outside i₁ (j+1) hout) (by rw [h₁]; decide)
        have hsym := τ.sym_Q i₁ (j + 1) hmem
        rcases hγ with hγ' | hγ' <;> rw [hγ'] at hsym <;> simp [DRCSymbol.allowed] at hsym <;>
          rcases hsym with h' | h' | h' | h' <;> rw [h'] at h₁ <;> exact absurd h₁ (by decide)
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    -- d in P' from paintL: P.paint = d. But P ∈ {dot, c} for B type. Impossible.
    simp only [PBP.doubleDescent_B_paintL] at h₁
    by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
    · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
    · rw [if_neg ha] at h₁
      have hmem : (i₁, j + 1) ∈ τ.P.shape := by
        by_contra hout; exact absurd (τ.P.paint_outside i₁ (j+1) hout) (by rw [h₁]; decide)
      have := PBP.P_nonDot_eq_c_of_B τ hγ i₁ (j+1) hmem (by rw [h₁]; decide)
      rw [this] at h₁; exact absurd h₁ (by decide)
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂
    -- d from paintR zone 3: Q.paint(i₁, j+1) = d and Q.paint(i₂, j+1) = d
    have hd₁ : τ.Q.paint i₁ (j+1) = .d := by
      simp only [PBP.doubleDescent_B_paintR] at h₁
      by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.Q (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hd₂ : τ.Q.paint i₂ (j+1) = .d := by
      simp only [PBP.doubleDescent_B_paintR] at h₂
      by_cases ha : i₂ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.Q (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_d_Q (j+1) i₁ i₂ hd₁ hd₂

/-- Double descent map for B-type: B→M→B on PBPSet. -/
noncomputable def doubleDescent_B_map (μP μQ : YoungDiagram)
    (τ : PBPSet .Bplus μP μQ ⊕ PBPSet .Bminus μP μQ) :
    PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft) ⊕
    PBPSet .Bminus (μP.shiftLeft) (μQ.shiftLeft) := by
  rcases τ with ⟨τval, hγ, hP, hQ⟩ | ⟨τval, hγ, hP, hQ⟩
  · exact Sum.inl ⟨doubleDescent_B_PBP τval (Or.inl hγ), rfl,
      congrArg YoungDiagram.shiftLeft hP,
      congrArg YoungDiagram.shiftLeft hQ⟩
  · exact Sum.inl ⟨doubleDescent_B_PBP τval (Or.inr hγ), rfl,
      congrArg YoungDiagram.shiftLeft hP,
      congrArg YoungDiagram.shiftLeft hQ⟩

/-! ## Recursive step -/

/-- Primitive case (r₂ > r₃): fiber is uniform across all tail classes. -/
theorem card_PBPSet_B_primitive_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hprim : r₂ > rest.head?.getD 0) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    (Fintype.card (PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) +
     Fintype.card (PBPSet .Bminus (μP.shiftLeft) (μQ.shiftLeft))) *
    tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
  -- Strategy: use doubleDescent_B_map + ddescent_inj_B to show the map is injective.
  -- In the primitive case (r₂ > r₃), the fiber over each image element has uniform
  -- cardinality = tripleSum(tailCoeffs k).1 where k = (r₁-r₂)/2 + 1.
  -- This is because the tail painting choices (in Q col 0 and P col 0) are
  -- independent of the base painting when the gap is strict.
  -- Needs: doubleDescent_B_map, fiber cardinality analysis from Fiber.lean.
  sorry

/-- Balanced case (r₂ = r₃): per-tail-class matrix multiply. -/
theorem card_PBPSet_B_balanced_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hbal : ¬(r₂ > rest.head?.getD 0)) :
    -- The balanced case decomposes per tail class
    True := by  -- placeholder for matrix multiply statement
  trivial

/-! ## Main theorem -/

/-- **Proposition 10.11 for B type:**
    card(PBPSet .Bplus μP μQ) + card(PBPSet .Bminus μP μQ) = tripleSum(countPBP_B dp). -/
theorem card_PBPSet_B_eq_tripleSum_countPBP_B (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B dp) := by
  -- Induction on dp (list of even parts).
  match dp, hP, hQ, hsort, heven, hpos with
  | [], hP, hQ, _, _, _ =>
    -- Base case: empty orbit
    have h1 := yd_of_colLens_nil (by rw [hP]; rfl)
    have h2 := yd_of_colLens_nil (by rw [hQ]; rfl)
    subst h1; subst h2
    simp [card_PBPSet_bot, tripleSum, countPBP_B]
  | [r₁], hP, hQ, _, heven, hpos =>
    -- Base case: single row
    exact card_PBPSet_B_singleton r₁ μP μQ hP hQ (heven r₁ (by simp)) (hpos r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos =>
    -- Inductive step: set up IH on rest
    have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
      rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
    have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
      rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
    have hsort' := sorted_tail₂ hsort
    have heven' : ∀ r ∈ rest, Even r :=
      fun r hr => heven r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have hpos' : ∀ r ∈ rest, 0 < r :=
      fun r hr => hpos r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have h_ih := card_PBPSet_B_eq_tripleSum_countPBP_B rest
      μP.shiftLeft μQ.shiftLeft hP_sh hQ_sh hsort' heven' hpos'
    by_cases h_prim : r₂ > rest.head?.getD 0
    · -- Primitive case: uniform fiber
      have := card_PBPSet_B_primitive_step r₁ r₂ rest μP μQ hP hQ hsort heven h_prim
      rw [this, h_ih]
      simp only [countPBP_B, h_prim, ite_true, tripleSum]
      ring
    · -- Balanced case: per-tail-class matrix multiply
      -- Needs: card_PBPSet_B_balanced_step with per-tc counts
      simp only [countPBP_B, h_prim, ite_false, tripleSum]
      sorry

/-- Corollary: each of B⁺ and B⁻ has half the total. -/
theorem card_PBPSet_Bplus_eq (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) = tripleSum (countPBP_B dp) / 2 := by
  have h_eq := card_Bplus_eq_Bminus μP μQ
  have h_total := card_PBPSet_B_eq_tripleSum_countPBP_B dp μP μQ hP hQ hsort heven hpos
  omega

/-! ## Structural theorems for Counting.lean -/

theorem countPBP_B_primitive {r₁ r₂ : ℕ} {rest : DualPart}
    (h : r₂ > rest.head?.getD 0) :
    countPBP_B (r₁ :: r₂ :: rest) =
      let k := (r₁ - r₂) / 2 + 1
      let ((tDD, tRC, tSS), _) := tailCoeffs k
      let (dd', rc', ss') := countPBP_B rest
      let total := dd' + rc' + ss'
      (total * tDD, total * tRC, total * tSS) := by
  simp only [countPBP_B, h, ite_true]

theorem countPBP_B_balanced {r₁ r₂ : ℕ} {rest : DualPart}
    (h : ¬(r₂ > rest.head?.getD 0)) :
    countPBP_B (r₁ :: r₂ :: rest) =
      let k := (r₁ - r₂) / 2 + 1
      let ((tDD, tRC, tSS), (scDD, scRC, scSS)) := tailCoeffs k
      let (dd', rc', ss') := countPBP_B rest
      (dd' * tDD + rc' * scDD,
       dd' * tRC + rc' * scRC,
       dd' * tSS + rc' * scSS) := by
  simp only [countPBP_B, h, ite_false]
