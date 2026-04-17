/-
# Shape Shifting for M type — Lemma 10.3 / Proposition 10.2

Implements the shape-shifting bijection T_{℘,℘↑} for type M (= C̃).
For M type, shape shifting swaps column 0 between P and Q with
the translation s↔r, c↔d, •↔•. This is an involution (T∘T = id).

Reference: [BMSZb] Section 10.2, Lemma 10.3.
See lean/docs/blueprints/lemma_10_3_M_shape_shifting.md for the
complete natural-language proof.
-/
import CombUnipotent.CountingProof.Basic

open Classical

/-! ## translateM: the s↔r, c↔d, •↔• swap -/

namespace DRCSymbol

/-- M-type shape shifting translation: s↔r, c↔d, •↔•. -/
def translateM : DRCSymbol → DRCSymbol
  | .dot => .dot
  | .s   => .r
  | .r   => .s
  | .c   => .d
  | .d   => .c

@[simp] theorem translateM_dot : translateM .dot = .dot := rfl
@[simp] theorem translateM_s : translateM .s = .r := rfl
@[simp] theorem translateM_r : translateM .r = .s := rfl
@[simp] theorem translateM_c : translateM .c = .d := rfl
@[simp] theorem translateM_d : translateM .d = .c := rfl

@[simp] theorem translateM_invol (x : DRCSymbol) : translateM (translateM x) = x := by
  cases x <;> rfl

theorem translateM_eq_dot_iff {x : DRCSymbol} : translateM x = .dot ↔ x = .dot := by
  cases x <;> simp [translateM]

theorem translateM_eq_s_iff {x : DRCSymbol} : translateM x = .s ↔ x = .r := by
  cases x <;> simp [translateM]

theorem translateM_eq_r_iff {x : DRCSymbol} : translateM x = .r ↔ x = .s := by
  cases x <;> simp [translateM]

theorem translateM_eq_c_iff {x : DRCSymbol} : translateM x = .c ↔ x = .d := by
  cases x <;> simp [translateM]

theorem translateM_eq_d_iff {x : DRCSymbol} : translateM x = .d ↔ x = .c := by
  cases x <;> simp [translateM]

/-- translateM maps M-left {•,s,c} to M-right {•,r,d}. -/
theorem translateM_allowed_L_to_R {x : DRCSymbol}
    (h : allowed .M .L x) : allowed .M .R (translateM x) := by
  simp [allowed] at h ⊢; rcases h with rfl | rfl | rfl <;> simp [translateM]

/-- translateM maps M-right {•,r,d} to M-left {•,s,c}. -/
theorem translateM_allowed_R_to_L {x : DRCSymbol}
    (h : allowed .M .R x) : allowed .M .L (translateM x) := by
  simp [allowed] at h ⊢; rcases h with rfl | rfl | rfl <;> simp [translateM]

/-- translateM preserves order within M-left {•,s,c}. -/
theorem translateM_mono_L {a b : DRCSymbol}
    (ha : allowed .M .L a) (hb : allowed .M .L b)
    (hle : a.layerOrd ≤ b.layerOrd) : (translateM a).layerOrd ≤ (translateM b).layerOrd := by
  simp [allowed] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [translateM, layerOrd]

/-- translateM preserves order within M-right {•,r,d}. -/
theorem translateM_mono_R {a b : DRCSymbol}
    (ha : allowed .M .R a) (hb : allowed .M .R b)
    (hle : a.layerOrd ≤ b.layerOrd) : (translateM a).layerOrd ≤ (translateM b).layerOrd := by
  simp [allowed] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [translateM, layerOrd]

end DRCSymbol

/-! ## Shape shifting paint -/

/-- Shape-shifted P paint: col 0 from translated Q, cols ≥ 1 unchanged. -/
noncomputable def shiftPaintP (τ : PBP) (i j : ℕ) : DRCSymbol :=
  if j = 0 then (τ.Q.paint i 0).translateM else τ.P.paint i j

/-- Shape-shifted Q paint: col 0 from translated P, cols ≥ 1 unchanged. -/
noncomputable def shiftPaintQ (τ : PBP) (i j : ℕ) : DRCSymbol :=
  if j = 0 then (τ.P.paint i 0).translateM else τ.Q.paint i j

@[simp] theorem shiftPaintP_zero (τ : PBP) (i : ℕ) :
    shiftPaintP τ i 0 = (τ.Q.paint i 0).translateM := if_pos rfl

@[simp] theorem shiftPaintP_succ (τ : PBP) (i j : ℕ) :
    shiftPaintP τ i (j + 1) = τ.P.paint i (j + 1) := if_neg (by omega)

@[simp] theorem shiftPaintQ_zero (τ : PBP) (i : ℕ) :
    shiftPaintQ τ i 0 = (τ.P.paint i 0).translateM := if_pos rfl

@[simp] theorem shiftPaintQ_succ (τ : PBP) (i j : ℕ) :
    shiftPaintQ τ i (j + 1) = τ.Q.paint i (j + 1) := if_neg (by omega)

/-! ## Helper lemmas for row_s/row_r -/

/-- shiftPaintP never equals r (value set ⊆ {•,s,c}). -/
theorem shiftPaintP_ne_r (τ : PBP) (hγ : τ.γ = .M) (i j : ℕ) :
    shiftPaintP τ i j ≠ .r := by
  cases j with
  | zero =>
    simp only [shiftPaintP_zero]
    intro habs
    have : τ.Q.paint i 0 = .s := DRCSymbol.translateM_eq_r_iff.mp habs
    by_cases hmem : (i, 0) ∈ τ.Q.shape
    · have := τ.sym_Q i 0 hmem; rw [hγ, ‹τ.Q.paint i 0 = .s›] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.Q.paint_outside i 0 hmem] at this; exact DRCSymbol.noConfusion this
  | succ j' =>
    simp only [shiftPaintP_succ]
    intro habs
    by_cases hmem : (i, j' + 1) ∈ τ.P.shape
    · have := τ.sym_P i (j' + 1) hmem; rw [hγ, habs] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.P.paint_outside i (j' + 1) hmem] at habs; exact DRCSymbol.noConfusion habs

/-- shiftPaintQ never equals s (value set ⊆ {•,r,d}). -/
theorem shiftPaintQ_ne_s (τ : PBP) (hγ : τ.γ = .M) (i j : ℕ) :
    shiftPaintQ τ i j ≠ .s := by
  cases j with
  | zero =>
    simp only [shiftPaintQ_zero]
    intro habs
    have : τ.P.paint i 0 = .r := DRCSymbol.translateM_eq_s_iff.mp habs
    by_cases hmem : (i, 0) ∈ τ.P.shape
    · have := τ.sym_P i 0 hmem; rw [hγ, ‹τ.P.paint i 0 = .r›] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.P.paint_outside i 0 hmem] at this; exact DRCSymbol.noConfusion this
  | succ j' =>
    simp only [shiftPaintQ_succ]
    intro habs
    by_cases hmem : (i, j' + 1) ∈ τ.Q.shape
    · have := τ.sym_Q i (j' + 1) hmem; rw [hγ, habs] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.Q.paint_outside i (j' + 1) hmem] at habs; exact DRCSymbol.noConfusion habs

/-- If shiftPaintP is non-dot, the cell is in shape (via original paint_outside).
    For j=0: (i,0) ∈ τ.Q.shape (which should match μP'). For j≥1: (i,j) ∈ τ.P.shape. -/
theorem shiftPaintP_ne_dot_implies_in_shape (τ : PBP) (i j : ℕ)
    (h : shiftPaintP τ i j ≠ .dot) :
    (j = 0 ∧ (i, 0) ∈ τ.Q.shape) ∨ (j ≥ 1 ∧ (i, j) ∈ τ.P.shape) := by
  cases j with
  | zero =>
    left; refine ⟨rfl, ?_⟩
    simp only [shiftPaintP_zero] at h
    rw [Ne, DRCSymbol.translateM_eq_dot_iff] at h
    by_contra hmem
    exact h (τ.Q.paint_outside i 0 hmem)
  | succ j' =>
    right; refine ⟨by omega, ?_⟩
    simp only [shiftPaintP_succ] at h
    by_contra hmem
    exact h (τ.P.paint_outside i (j' + 1) hmem)

/-- Dual: shiftPaintQ non-dot → in shape. -/
theorem shiftPaintQ_ne_dot_implies_in_shape (τ : PBP) (i j : ℕ)
    (h : shiftPaintQ τ i j ≠ .dot) :
    (j = 0 ∧ (i, 0) ∈ τ.P.shape) ∨ (j ≥ 1 ∧ (i, j) ∈ τ.Q.shape) := by
  cases j with
  | zero =>
    left; refine ⟨rfl, ?_⟩
    simp only [shiftPaintQ_zero] at h
    rw [Ne, DRCSymbol.translateM_eq_dot_iff] at h
    by_contra hmem
    exact h (τ.P.paint_outside i 0 hmem)
  | succ j' =>
    right; refine ⟨by omega, ?_⟩
    simp only [shiftPaintQ_succ] at h
    by_contra hmem
    exact h (τ.Q.paint_outside i (j' + 1) hmem)

/-- shiftPaintP never equals d (value set ⊆ {•,s,c}). -/
theorem shiftPaintP_ne_d (τ : PBP) (hγ : τ.γ = .M) (i j : ℕ) :
    shiftPaintP τ i j ≠ .d := by
  cases j with
  | zero =>
    simp only [shiftPaintP_zero]
    intro habs
    have : τ.Q.paint i 0 = .c := DRCSymbol.translateM_eq_d_iff.mp habs
    by_cases hmem : (i, 0) ∈ τ.Q.shape
    · have := τ.sym_Q i 0 hmem; rw [hγ, ‹τ.Q.paint i 0 = .c›] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.Q.paint_outside i 0 hmem] at this; exact DRCSymbol.noConfusion this
  | succ j' =>
    simp only [shiftPaintP_succ]
    intro habs
    by_cases hmem : (i, j' + 1) ∈ τ.P.shape
    · have := τ.sym_P i (j' + 1) hmem; rw [hγ, habs] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.P.paint_outside i (j' + 1) hmem] at habs; exact DRCSymbol.noConfusion habs

/-- shiftPaintQ never equals c (value set ⊆ {•,r,d}). -/
theorem shiftPaintQ_ne_c (τ : PBP) (hγ : τ.γ = .M) (i j : ℕ) :
    shiftPaintQ τ i j ≠ .c := by
  cases j with
  | zero =>
    simp only [shiftPaintQ_zero]
    intro habs
    have : τ.P.paint i 0 = .d := DRCSymbol.translateM_eq_c_iff.mp habs
    by_cases hmem : (i, 0) ∈ τ.P.shape
    · have := τ.sym_P i 0 hmem; rw [hγ, ‹τ.P.paint i 0 = .d›] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.P.paint_outside i 0 hmem] at this; exact DRCSymbol.noConfusion this
  | succ j' =>
    simp only [shiftPaintQ_succ]
    intro habs
    by_cases hmem : (i, j' + 1) ∈ τ.Q.shape
    · have := τ.sym_Q i (j' + 1) hmem; rw [hγ, habs] at this
      simp [DRCSymbol.allowed] at this
    · rw [τ.Q.paint_outside i (j' + 1) hmem] at habs; exact DRCSymbol.noConfusion habs

/-! ## Main construction: shapeShiftM -/

/-- Shape-shifted M PBP (Lemma 10.3 / Prop 10.2).

    Given τ : PBP on (μP, μQ) with τ.γ = M, and target shapes (μP', μQ') such that:
      (i, 0) ∈ μP' ↔ (i, 0) ∈ μQ       (col 0 of P' comes from Q)
      (i, j+1) ∈ μP' ↔ (i, j+1) ∈ μP   (cols ≥ 1 of P' come from P)
      (i, 0) ∈ μQ' ↔ (i, 0) ∈ μP       (col 0 of Q' comes from P)
      (i, j+1) ∈ μQ' ↔ (i, j+1) ∈ μQ   (cols ≥ 1 of Q' come from Q)

    Produces a new M PBP on (μP', μQ').
    Paint: col 0 swapped via translateM; cols ≥ 1 unchanged.

    Reference: [BMSZb] Section 10.2, Lemma 10.3. -/
noncomputable def shapeShiftM (τ : PBP) (hγ : τ.γ = .M)
    (μP' μQ' : YoungDiagram)
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ τ.Q.shape)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ τ.P.shape)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ τ.P.shape)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ τ.Q.shape) : PBP where
  γ := .M
  P := { shape := μP'
         paint := shiftPaintP τ
         paint_outside := by
           intro i j hmem; cases j with
           | zero =>
             simp only [shiftPaintP_zero]
             rw [DRCSymbol.translateM_eq_dot_iff]
             have : (i, 0) ∉ τ.Q.shape := (hP'0 i).not.mp hmem
             exact τ.Q.paint_outside i 0 this
           | succ j' =>
             simp only [shiftPaintP_succ]
             have : (i, j' + 1) ∉ τ.P.shape := (hP'S i j').not.mp hmem
             exact τ.P.paint_outside i (j' + 1) this }
  Q := { shape := μQ'
         paint := shiftPaintQ τ
         paint_outside := by
           intro i j hmem; cases j with
           | zero =>
             simp only [shiftPaintQ_zero]
             rw [DRCSymbol.translateM_eq_dot_iff]
             have : (i, 0) ∉ τ.P.shape := (hQ'0 i).not.mp hmem
             exact τ.P.paint_outside i 0 this
           | succ j' =>
             simp only [shiftPaintQ_succ]
             have : (i, j' + 1) ∉ τ.Q.shape := (hQ'S i j').not.mp hmem
             exact τ.Q.paint_outside i (j' + 1) this }
  sym_P := by
    intro i j hmem; cases j with
    | zero =>
      simp only [shiftPaintP_zero]
      have hmemQ := (hP'0 i).mp hmem
      exact DRCSymbol.translateM_allowed_R_to_L (hγ ▸ τ.sym_Q i 0 hmemQ)
    | succ j' =>
      simp only [shiftPaintP_succ]
      have hmemP := (hP'S i j').mp hmem
      exact hγ ▸ τ.sym_P i (j' + 1) hmemP
  sym_Q := by
    intro i j hmem; cases j with
    | zero =>
      simp only [shiftPaintQ_zero]
      have hmemP := (hQ'0 i).mp hmem
      exact DRCSymbol.translateM_allowed_L_to_R (hγ ▸ τ.sym_P i 0 hmemP)
    | succ j' =>
      simp only [shiftPaintQ_succ]
      have hmemQ := (hQ'S i j').mp hmem
      exact hγ ▸ τ.sym_Q i (j' + 1) hmemQ
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP', hpaintP'⟩; cases j with
      | zero =>
        simp only [shiftPaintP_zero] at hpaintP'
        rw [DRCSymbol.translateM_eq_dot_iff] at hpaintP'
        have hmemQ := (hP'0 i).mp hmemP'
        have ⟨hmemP, hpaintP⟩ := (τ.dot_match i 0).mpr ⟨hmemQ, hpaintP'⟩
        exact ⟨(hQ'0 i).mpr hmemP, by simp [hpaintP]⟩
      | succ j' =>
        simp only [shiftPaintP_succ] at hpaintP'
        have hmemP := (hP'S i j').mp hmemP'
        have ⟨hmemQ, hpaintQ⟩ := (τ.dot_match i (j' + 1)).mp ⟨hmemP, hpaintP'⟩
        exact ⟨(hQ'S i j').mpr hmemQ, by simp [hpaintQ]⟩
    · intro ⟨hmemQ', hpaintQ'⟩; cases j with
      | zero =>
        simp only [shiftPaintQ_zero] at hpaintQ'
        rw [DRCSymbol.translateM_eq_dot_iff] at hpaintQ'
        have hmemP := (hQ'0 i).mp hmemQ'
        have ⟨hmemQ, hpaintQ⟩ := (τ.dot_match i 0).mp ⟨hmemP, hpaintQ'⟩
        exact ⟨(hP'0 i).mpr hmemQ, by simp [hpaintQ]⟩
      | succ j' =>
        simp only [shiftPaintQ_succ] at hpaintQ'
        have hmemQ := (hQ'S i j').mp hmemQ'
        have ⟨hmemP, hpaintP⟩ := (τ.dot_match i (j' + 1)).mpr ⟨hmemQ, hpaintQ'⟩
        exact ⟨(hP'S i j').mpr hmemP, by simp [hpaintP]⟩
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (shiftPaintP τ i₁ j₁).layerOrd ≤ (shiftPaintP τ i₂ j₂).layerOrd
    match j₁, j₂, hj with
    | 0, 0, _ =>
      -- Case 2: both col 0
      simp only [shiftPaintP_zero]
      have hmemQ₂ := (hP'0 i₂).mp hmem₂
      by_cases hmemQ₁ : (i₁, 0) ∈ τ.Q.shape
      · exact DRCSymbol.translateM_mono_R
          (hγ ▸ τ.sym_Q i₁ 0 hmemQ₁) (hγ ▸ τ.sym_Q i₂ 0 hmemQ₂)
          (τ.mono_Q i₁ 0 i₂ 0 hi le_rfl hmemQ₂)
      · rw [τ.Q.paint_outside i₁ 0 hmemQ₁]; simp [DRCSymbol.layerOrd]
    | j₁' + 1, j₂' + 1, hj =>
      -- Case 1: both col ≥ 1
      simp only [shiftPaintP_succ]
      exact τ.mono_P i₁ (j₁' + 1) i₂ (j₂' + 1) hi hj ((hP'S i₂ j₂').mp hmem₂)
    | 0, j₂' + 1, _ =>
      -- Case 4: col 0 → col ≥ 1 (hardest)
      simp only [shiftPaintP_zero, shiftPaintP_succ]
      have hmemP₂ : (i₂, j₂' + 1) ∈ τ.P.shape := (hP'S i₂ j₂').mp hmem₂
      by_cases hmemQ₁ : (i₁, 0) ∈ τ.Q.shape
      · by_cases hmemP₁ : (i₁, 0) ∈ τ.P.shape
        · -- Sub-case 4b: (i₁,0) ∈ μP ∩ μQ
          have hsymQ := hγ ▸ τ.sym_Q i₁ 0 hmemQ₁
          simp [DRCSymbol.allowed] at hsymQ
          rcases hsymQ with hQdot | hQr | hQd
          · rw [hQdot]; simp [DRCSymbol.layerOrd]
          · -- Q = r → translateM = s (lo=1)
            rw [hQr]; simp [DRCSymbol.translateM, DRCSymbol.layerOrd]
            have hP_ne_dot : τ.P.paint i₁ 0 ≠ .dot := by
              intro habs
              have := (τ.dot_match i₁ 0).mp ⟨hmemP₁, habs⟩
              rw [hQr] at this; exact DRCSymbol.noConfusion this.2
            have hsymP := hγ ▸ τ.sym_P i₁ 0 hmemP₁
            simp [DRCSymbol.allowed] at hsymP
            rcases hsymP with hPdot | hPs | hPc
            · exact absurd hPdot hP_ne_dot
            · calc 1 = (DRCSymbol.s).layerOrd := rfl
                _ = (τ.P.paint i₁ 0).layerOrd := by rw [hPs]
                _ ≤ (τ.P.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_P i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemP₂
            · calc 1 ≤ 3 := by omega
                _ = (DRCSymbol.c).layerOrd := rfl
                _ = (τ.P.paint i₁ 0).layerOrd := by rw [hPc]
                _ ≤ (τ.P.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_P i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemP₂
          · -- Q = d → translateM = c (lo=3). Hardest.
            rw [hQd]; simp [DRCSymbol.translateM, DRCSymbol.layerOrd]
            have hP_ne_dot : τ.P.paint i₁ 0 ≠ .dot := by
              intro habs
              have := (τ.dot_match i₁ 0).mp ⟨hmemP₁, habs⟩
              rw [hQd] at this; exact DRCSymbol.noConfusion this.2
            have hsymP := hγ ▸ τ.sym_P i₁ 0 hmemP₁
            simp [DRCSymbol.allowed] at hsymP
            rcases hsymP with hPdot | hPs | hPc
            · exact absurd hPdot hP_ne_dot
            · -- P(i₁,0) = s → row_s forces P(i₁,1) = c
              have hmemP₁_1 : (i₁, 1) ∈ τ.P.shape :=
                τ.P.shape.isLowerSet (show (i₁, 1) ≤ (i₂, j₂' + 1) from
                  Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hmemP₂
              have hP₁_ne_s : τ.P.paint i₁ 1 ≠ .s := by
                intro heq
                have := (τ.row_s i₁ .L .L 0 1
                  (by simp [paintBySide]; exact hPs)
                  (by simp [paintBySide]; exact heq)).2
                omega
              have hlo_ge := τ.mono_P i₁ 0 i₁ 1 le_rfl (by omega) hmemP₁_1
              rw [hPs] at hlo_ge
              have hsymP₁ := hγ ▸ τ.sym_P i₁ 1 hmemP₁_1
              simp [DRCSymbol.allowed] at hsymP₁
              have hP₁_eq_c : τ.P.paint i₁ 1 = .c := by
                rcases hsymP₁ with h | h | h
                · rw [h] at hlo_ge; simp [DRCSymbol.layerOrd] at hlo_ge
                · exact absurd h hP₁_ne_s
                · exact h
              calc 3 = (DRCSymbol.c).layerOrd := rfl
                _ = (τ.P.paint i₁ 1).layerOrd := by rw [hP₁_eq_c]
                _ ≤ (τ.P.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_P i₁ 1 i₂ (j₂' + 1) hi (by omega) hmemP₂
            · calc 3 = (DRCSymbol.c).layerOrd := rfl
                _ = (τ.P.paint i₁ 0).layerOrd := by rw [hPc]
                _ ≤ (τ.P.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_P i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemP₂
        · -- Sub-case 4c: (i₁,0) ∉ μP but (i₁,0) ∈ μQ. Impossible.
          exfalso
          exact hmemP₁ (τ.P.shape.isLowerSet (show (i₁, 0) ≤ (i₂, j₂' + 1) from
            Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hmemP₂)
      · -- Sub-case 4a: (i₁,0) ∉ μQ
        rw [τ.Q.paint_outside i₁ 0 hmemQ₁]
        simp [DRCSymbol.layerOrd]
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (shiftPaintQ τ i₁ j₁).layerOrd ≤ (shiftPaintQ τ i₂ j₂).layerOrd
    match j₁, j₂, hj with
    | 0, 0, _ =>
      simp only [shiftPaintQ_zero]
      have hmemP₂ := (hQ'0 i₂).mp hmem₂
      by_cases hmemP₁ : (i₁, 0) ∈ τ.P.shape
      · exact DRCSymbol.translateM_mono_L
          (hγ ▸ τ.sym_P i₁ 0 hmemP₁) (hγ ▸ τ.sym_P i₂ 0 hmemP₂)
          (τ.mono_P i₁ 0 i₂ 0 hi le_rfl hmemP₂)
      · rw [τ.P.paint_outside i₁ 0 hmemP₁]; simp [DRCSymbol.layerOrd]
    | j₁' + 1, j₂' + 1, hj =>
      simp only [shiftPaintQ_succ]
      exact τ.mono_Q i₁ (j₁' + 1) i₂ (j₂' + 1) hi hj ((hQ'S i₂ j₂').mp hmem₂)
    | 0, j₂' + 1, _ =>
      simp only [shiftPaintQ_zero, shiftPaintQ_succ]
      have hmemQ₂ : (i₂, j₂' + 1) ∈ τ.Q.shape := (hQ'S i₂ j₂').mp hmem₂
      by_cases hmemP₁ : (i₁, 0) ∈ τ.P.shape
      · by_cases hmemQ₁ : (i₁, 0) ∈ τ.Q.shape
        · -- Sub-case 4b
          have hsymP := hγ ▸ τ.sym_P i₁ 0 hmemP₁
          simp [DRCSymbol.allowed] at hsymP
          rcases hsymP with hPdot | hPs | hPc
          · rw [hPdot]; simp [DRCSymbol.layerOrd]
          · -- P = s → translateM = r (lo=2)
            rw [hPs]; simp [DRCSymbol.translateM, DRCSymbol.layerOrd]
            have hQ_ne_dot : τ.Q.paint i₁ 0 ≠ .dot := by
              intro habs
              have := (τ.dot_match i₁ 0).mpr ⟨hmemQ₁, habs⟩
              rw [hPs] at this; exact DRCSymbol.noConfusion this.2
            have hsymQ := hγ ▸ τ.sym_Q i₁ 0 hmemQ₁
            simp [DRCSymbol.allowed] at hsymQ
            rcases hsymQ with hQdot | hQr | hQd
            · exact absurd hQdot hQ_ne_dot
            · calc 2 = (DRCSymbol.r).layerOrd := rfl
                _ = (τ.Q.paint i₁ 0).layerOrd := by rw [hQr]
                _ ≤ (τ.Q.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_Q i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemQ₂
            · calc 2 ≤ 4 := by omega
                _ = (DRCSymbol.d).layerOrd := rfl
                _ = (τ.Q.paint i₁ 0).layerOrd := by rw [hQd]
                _ ≤ (τ.Q.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_Q i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemQ₂
          · -- P = c → translateM = d (lo=4). Hardest.
            rw [hPc]; simp [DRCSymbol.translateM, DRCSymbol.layerOrd]
            have hQ_ne_dot : τ.Q.paint i₁ 0 ≠ .dot := by
              intro habs
              have := (τ.dot_match i₁ 0).mpr ⟨hmemQ₁, habs⟩
              rw [hPc] at this; exact DRCSymbol.noConfusion this.2
            have hsymQ := hγ ▸ τ.sym_Q i₁ 0 hmemQ₁
            simp [DRCSymbol.allowed] at hsymQ
            rcases hsymQ with hQdot | hQr | hQd
            · exact absurd hQdot hQ_ne_dot
            · -- Q = r: row_r forces Q(i₁,1) = d
              have hmemQ₁_1 : (i₁, 1) ∈ τ.Q.shape :=
                τ.Q.shape.isLowerSet (show (i₁, 1) ≤ (i₂, j₂' + 1) from
                  Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hmemQ₂
              have hQ₁_ne_r : τ.Q.paint i₁ 1 ≠ .r := by
                intro heq
                have := (τ.row_r i₁ .R .R 0 1
                  (by simp [paintBySide]; exact hQr)
                  (by simp [paintBySide]; exact heq)).2
                omega
              have hlo_ge := τ.mono_Q i₁ 0 i₁ 1 le_rfl (by omega) hmemQ₁_1
              rw [hQr] at hlo_ge
              have hsymQ₁ := hγ ▸ τ.sym_Q i₁ 1 hmemQ₁_1
              simp [DRCSymbol.allowed] at hsymQ₁
              have hQ₁_eq_d : τ.Q.paint i₁ 1 = .d := by
                rcases hsymQ₁ with h | h | h
                · rw [h] at hlo_ge; simp [DRCSymbol.layerOrd] at hlo_ge
                · exact absurd h hQ₁_ne_r
                · exact h
              calc 4 = (DRCSymbol.d).layerOrd := rfl
                _ = (τ.Q.paint i₁ 1).layerOrd := by rw [hQ₁_eq_d]
                _ ≤ (τ.Q.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_Q i₁ 1 i₂ (j₂' + 1) hi (by omega) hmemQ₂
            · calc 4 = (DRCSymbol.d).layerOrd := rfl
                _ = (τ.Q.paint i₁ 0).layerOrd := by rw [hQd]
                _ ≤ (τ.Q.paint i₂ (j₂' + 1)).layerOrd :=
                    τ.mono_Q i₁ 0 i₂ (j₂' + 1) hi (by omega) hmemQ₂
        · -- Sub-case 4c: (i₁,0) ∉ μQ but ∈ μP. Impossible.
          exfalso
          exact hmemQ₁ (τ.Q.shape.isLowerSet (show (i₁, 0) ≤ (i₂, j₂' + 1) from
            Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hmemQ₂)
      · -- Sub-case 4a: (i₁,0) ∉ μP
        rw [τ.P.paint_outside i₁ 0 hmemP₁]
        simp [DRCSymbol.layerOrd]
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- Goal: s₁ = s₂ ∧ j₁ = j₂
    -- Key: shiftPaintQ never = s, so s₂ = L (and s₁ = L).
    -- Then: both shiftPaintP(i, j₁) = s and shiftPaintP(i, j₂) = s.
    -- Case analysis on j₁, j₂.
    have hs₁_L : s₁ = .L := by
      cases s₁ with
      | L => rfl
      | R => exfalso; exact shiftPaintQ_ne_s τ hγ i j₁ (by simpa [paintBySide] using h₁)
    have hs₂_L : s₂ = .L := by
      cases s₂ with
      | L => rfl
      | R => exfalso; exact shiftPaintQ_ne_s τ hγ i j₂ (by simpa [paintBySide] using h₂)
    subst hs₁_L; subst hs₂_L
    refine ⟨rfl, ?_⟩
    -- Now: shiftPaintP(i, j₁) = s and shiftPaintP(i, j₂) = s. Show j₁ = j₂.
    simp [paintBySide] at h₁ h₂
    -- Case analysis
    match j₁, j₂ with
    | 0, 0 => rfl
    | 0, j₂' + 1 =>
      -- shiftPaintP(i,0) = s → Q(i,0) = r.
      -- shiftPaintP(i,j₂'+1) = P(i,j₂'+1) = s. → (i,j₂'+1) ∈ μP → (i,0) ∈ μP (lower set).
      -- dot_match: Q(i,0) = r ≠ •, (i,0) ∈ μP → P(i,0) ≠ •. P(i,0) ∈ {s,c}.
      -- If P(i,0) = s: row_s at (i,0,L) and (i,j₂'+1,L) gives 0 = j₂'+1. Contradiction.
      -- If P(i,0) = c: mono_P: 3 ≤ 1. Contradiction.
      exfalso
      simp only [shiftPaintP_zero] at h₁
      simp only [shiftPaintP_succ] at h₂
      have hQr : τ.Q.paint i 0 = .r := DRCSymbol.translateM_eq_s_iff.mp h₁
      have hmemP_j2 : (i, j₂' + 1) ∈ τ.P.shape := by
        by_contra habs; rw [τ.P.paint_outside i (j₂' + 1) habs] at h₂
        exact DRCSymbol.noConfusion h₂
      have hmemP_0 : (i, 0) ∈ τ.P.shape :=
        τ.P.shape.isLowerSet (show (i, 0) ≤ (i, j₂' + 1) from
          Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hmemP_j2
      have hP_ne_dot : τ.P.paint i 0 ≠ .dot := by
        intro habs
        have := (τ.dot_match i 0).mp ⟨hmemP_0, habs⟩
        rw [hQr] at this; exact DRCSymbol.noConfusion this.2
      have hsymP := hγ ▸ τ.sym_P i 0 hmemP_0
      simp [DRCSymbol.allowed] at hsymP
      rcases hsymP with hPdot | hPs | hPc
      · exact hP_ne_dot hPdot
      · have := (τ.row_s i .L .L 0 (j₂' + 1)
          (by simp [paintBySide]; exact hPs)
          (by simp [paintBySide]; exact h₂)).2
        omega
      · have := τ.mono_P i 0 i (j₂' + 1) le_rfl (by omega) hmemP_j2
        rw [hPc, h₂] at this
        simp [DRCSymbol.layerOrd] at this
    | j₁' + 1, 0 =>
      -- Symmetric to above.
      exfalso
      simp only [shiftPaintP_zero] at h₂
      simp only [shiftPaintP_succ] at h₁
      have hQr : τ.Q.paint i 0 = .r := DRCSymbol.translateM_eq_s_iff.mp h₂
      have hmemP_j1 : (i, j₁' + 1) ∈ τ.P.shape := by
        by_contra habs; rw [τ.P.paint_outside i (j₁' + 1) habs] at h₁
        exact DRCSymbol.noConfusion h₁
      have hmemP_0 : (i, 0) ∈ τ.P.shape :=
        τ.P.shape.isLowerSet (show (i, 0) ≤ (i, j₁' + 1) from
          Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hmemP_j1
      have hP_ne_dot : τ.P.paint i 0 ≠ .dot := by
        intro habs
        have := (τ.dot_match i 0).mp ⟨hmemP_0, habs⟩
        rw [hQr] at this; exact DRCSymbol.noConfusion this.2
      have hsymP := hγ ▸ τ.sym_P i 0 hmemP_0
      simp [DRCSymbol.allowed] at hsymP
      rcases hsymP with hPdot | hPs | hPc
      · exact hP_ne_dot hPdot
      · have := (τ.row_s i .L .L 0 (j₁' + 1)
          (by simp [paintBySide]; exact hPs)
          (by simp [paintBySide]; exact h₁)).2
        omega
      · have := τ.mono_P i 0 i (j₁' + 1) le_rfl (by omega) hmemP_j1
        rw [hPc, h₁] at this
        simp [DRCSymbol.layerOrd] at this
    | j₁' + 1, j₂' + 1 =>
      -- Both ≥ 1. Original row_s.
      simp only [shiftPaintP_succ] at h₁ h₂
      have := (τ.row_s i .L .L (j₁' + 1) (j₂' + 1)
        (by simp [paintBySide]; exact h₁)
        (by simp [paintBySide]; exact h₂)).2
      exact this
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- r only in shiftPaintQ. Force s₁ = s₂ = R.
    have hs₁_R : s₁ = .R := by
      cases s₁ with
      | R => rfl
      | L => exfalso; exact shiftPaintP_ne_r τ hγ i j₁ (by simpa [paintBySide] using h₁)
    have hs₂_R : s₂ = .R := by
      cases s₂ with
      | R => rfl
      | L => exfalso; exact shiftPaintP_ne_r τ hγ i j₂ (by simpa [paintBySide] using h₂)
    subst hs₁_R; subst hs₂_R
    refine ⟨rfl, ?_⟩
    simp [paintBySide] at h₁ h₂
    match j₁, j₂ with
    | 0, 0 => rfl
    | 0, j₂' + 1 =>
      exfalso
      simp only [shiftPaintQ_zero] at h₁
      simp only [shiftPaintQ_succ] at h₂
      have hPs : τ.P.paint i 0 = .s := DRCSymbol.translateM_eq_r_iff.mp h₁
      have hmemQ_j2 : (i, j₂' + 1) ∈ τ.Q.shape := by
        by_contra habs; rw [τ.Q.paint_outside i (j₂' + 1) habs] at h₂
        exact DRCSymbol.noConfusion h₂
      have hmemQ_0 : (i, 0) ∈ τ.Q.shape :=
        τ.Q.shape.isLowerSet (show (i, 0) ≤ (i, j₂' + 1) from
          Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hmemQ_j2
      have hQ_ne_dot : τ.Q.paint i 0 ≠ .dot := by
        intro habs
        have := (τ.dot_match i 0).mpr ⟨hmemQ_0, habs⟩
        rw [hPs] at this; exact DRCSymbol.noConfusion this.2
      have hsymQ := hγ ▸ τ.sym_Q i 0 hmemQ_0
      simp [DRCSymbol.allowed] at hsymQ
      rcases hsymQ with hQdot | hQr | hQd
      · exact hQ_ne_dot hQdot
      · have := (τ.row_r i .R .R 0 (j₂' + 1)
          (by simp [paintBySide]; exact hQr)
          (by simp [paintBySide]; exact h₂)).2
        omega
      · have := τ.mono_Q i 0 i (j₂' + 1) le_rfl (by omega) hmemQ_j2
        rw [hQd, h₂] at this
        simp [DRCSymbol.layerOrd] at this
    | j₁' + 1, 0 =>
      exfalso
      simp only [shiftPaintQ_zero] at h₂
      simp only [shiftPaintQ_succ] at h₁
      have hPs : τ.P.paint i 0 = .s := DRCSymbol.translateM_eq_r_iff.mp h₂
      have hmemQ_j1 : (i, j₁' + 1) ∈ τ.Q.shape := by
        by_contra habs; rw [τ.Q.paint_outside i (j₁' + 1) habs] at h₁
        exact DRCSymbol.noConfusion h₁
      have hmemQ_0 : (i, 0) ∈ τ.Q.shape :=
        τ.Q.shape.isLowerSet (show (i, 0) ≤ (i, j₁' + 1) from
          Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hmemQ_j1
      have hQ_ne_dot : τ.Q.paint i 0 ≠ .dot := by
        intro habs
        have := (τ.dot_match i 0).mpr ⟨hmemQ_0, habs⟩
        rw [hPs] at this; exact DRCSymbol.noConfusion this.2
      have hsymQ := hγ ▸ τ.sym_Q i 0 hmemQ_0
      simp [DRCSymbol.allowed] at hsymQ
      rcases hsymQ with hQdot | hQr | hQd
      · exact hQ_ne_dot hQdot
      · have := (τ.row_r i .R .R 0 (j₁' + 1)
          (by simp [paintBySide]; exact hQr)
          (by simp [paintBySide]; exact h₁)).2
        omega
      · have := τ.mono_Q i 0 i (j₁' + 1) le_rfl (by omega) hmemQ_j1
        rw [hQd, h₁] at this
        simp [DRCSymbol.layerOrd] at this
    | j₁' + 1, j₂' + 1 =>
      simp only [shiftPaintQ_succ] at h₁ h₂
      exact (τ.row_r i .R .R (j₁' + 1) (j₂' + 1)
        (by simp [paintBySide]; exact h₁)
        (by simp [paintBySide]; exact h₂)).2
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      -- col 0: shiftPaintP(i,0) = c ↔ Q(i,0) = d. Use col_d_Q.
      simp only [shiftPaintP_zero] at h₁ h₂
      have hQ₁ : τ.Q.paint i₁ 0 = .d := DRCSymbol.translateM_eq_c_iff.mp h₁
      have hQ₂ : τ.Q.paint i₂ 0 = .d := DRCSymbol.translateM_eq_c_iff.mp h₂
      exact τ.col_d_Q 0 i₁ i₂ hQ₁ hQ₂
    | succ j' =>
      simp only [shiftPaintP_succ] at h₁ h₂
      exact τ.col_c_P (j' + 1) i₁ i₂ h₁ h₂
  col_c_Q := by
    -- shiftPaintQ never = c (Q values ⊆ {•,r,d}).
    intro j i₁ i₂ h₁ _
    exact absurd h₁ (shiftPaintQ_ne_c τ hγ i₁ j)
  col_d_P := by
    -- shiftPaintP never = d (P values ⊆ {•,s,c}).
    intro j i₁ i₂ h₁ _
    exact absurd h₁ (shiftPaintP_ne_d τ hγ i₁ j)
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      simp only [shiftPaintQ_zero] at h₁ h₂
      have hP₁ : τ.P.paint i₁ 0 = .c := DRCSymbol.translateM_eq_d_iff.mp h₁
      have hP₂ : τ.P.paint i₂ 0 = .c := DRCSymbol.translateM_eq_d_iff.mp h₂
      exact τ.col_c_P 0 i₁ i₂ hP₁ hP₂
    | succ j' =>
      simp only [shiftPaintQ_succ] at h₁ h₂
      exact τ.col_d_Q (j' + 1) i₁ i₂ h₁ h₂

/-! ## Involution: shapeShiftM ∘ shapeShiftM = id -/

/-- Applying shapeShiftM twice returns the original PBP.
    Follows from translateM ∘ translateM = id. -/
theorem shapeShiftM_involution (τ : PBP) (hγ : τ.γ = .M)
    (μP' μQ' : YoungDiagram)
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ τ.Q.shape)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ τ.P.shape)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ τ.P.shape)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ τ.Q.shape) :
    shapeShiftM (shapeShiftM τ hγ μP' μQ' hP'0 hP'S hQ'0 hQ'S) rfl
      τ.P.shape τ.Q.shape
      (fun i => by simp [shapeShiftM]; exact (hQ'0 i).symm)
      (fun i j => by simp [shapeShiftM]; exact (hP'S i j).symm)
      (fun i => by simp [shapeShiftM]; exact (hP'0 i).symm)
      (fun i j => by simp [shapeShiftM]; exact (hQ'S i j).symm) = τ := by
  apply PBP.ext''
  · -- γ = M, and τ.γ = M by hγ
    simp [shapeShiftM]; exact hγ.symm
  · -- P: shape = τ.P.shape (by construction), paint = shiftPaintP(shifted) = τ.P.paint
    apply PaintedYoungDiagram.ext'
    · rfl
    · ext i j
      simp [shapeShiftM]
      cases j with
      | zero => simp [shiftPaintP, shiftPaintQ]
      | succ j' => simp [shiftPaintP]
  · -- Q: symmetric
    apply PaintedYoungDiagram.ext'
    · rfl
    · ext i j
      simp [shapeShiftM]
      cases j with
      | zero => simp [shiftPaintP, shiftPaintQ]
      | succ j' => simp [shiftPaintQ]

/-! ## Proposition 10.2: card equality -/

/-- Shape shifting as a map on PBPSet. -/
noncomputable def shapeShiftM_PBPSet {μP μQ μP' μQ' : YoungDiagram}
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ μQ)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ μP)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ μP)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ μQ)
    (τ : PBPSet .M μP μQ) : PBPSet .M μP' μQ' :=
  ⟨shapeShiftM τ.val τ.prop.1 μP' μQ'
    (by intro i; rw [hP'0, τ.prop.2.2])
    (by intro i j; rw [hP'S, τ.prop.2.1])
    (by intro i; rw [hQ'0, τ.prop.2.1])
    (by intro i j; rw [hQ'S, τ.prop.2.2]),
    ⟨rfl, rfl, rfl⟩⟩

/-- **Proposition 10.2 for M type**: card is independent of ℘.

    Shape shifting gives a bijection PBPSet .M μP μQ ≃ PBPSet .M μP' μQ'
    when the target shapes swap col 0 lengths. Hence cards are equal.

    Reference: [BMSZb] Prop 10.2 / Lemma 10.3. -/
theorem card_PBPSet_M_shapeShift {μP μQ μP' μQ' : YoungDiagram}
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ μQ)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ μP)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ μP)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ μQ) :
    Fintype.card (PBPSet .M μP μQ) = Fintype.card (PBPSet .M μP' μQ') := by
  apply Fintype.card_congr
  refine {
    toFun := shapeShiftM_PBPSet hP'0 hP'S hQ'0 hQ'S
    invFun := shapeShiftM_PBPSet
      (fun i => (hQ'0 i).symm)
      (fun i j => (hP'S i j).symm)
      (fun i => (hP'0 i).symm)
      (fun i j => (hQ'S i j).symm)
    left_inv := fun τ => ?_
    right_inv := fun τ => ?_
  }
  · -- left_inv: shift ∘ shift back = id (at PBPSet level)
    apply Subtype.ext
    simp only [shapeShiftM_PBPSet]
    apply PBP.ext''
    · simp [shapeShiftM]; exact τ.prop.1.symm
    · apply PaintedYoungDiagram.ext'
      · simp [shapeShiftM]; exact τ.prop.2.1.symm
      · ext i j
        simp [shapeShiftM]
        cases j with
        | zero => simp [shiftPaintP, shiftPaintQ]
        | succ j' => simp [shiftPaintP]
    · apply PaintedYoungDiagram.ext'
      · simp [shapeShiftM]; exact τ.prop.2.2.symm
      · ext i j
        simp [shapeShiftM]
        cases j with
        | zero => simp [shiftPaintP, shiftPaintQ]
        | succ j' => simp [shiftPaintQ]
  · -- right_inv: shift back ∘ shift = id (symmetric)
    apply Subtype.ext
    simp only [shapeShiftM_PBPSet]
    apply PBP.ext''
    · simp [shapeShiftM]; exact τ.prop.1.symm
    · apply PaintedYoungDiagram.ext'
      · simp [shapeShiftM]; exact τ.prop.2.1.symm
      · ext i j
        simp [shapeShiftM]
        cases j with
        | zero => simp [shiftPaintP, shiftPaintQ]
        | succ j' => simp [shiftPaintP]
    · apply PaintedYoungDiagram.ext'
      · simp [shapeShiftM]; exact τ.prop.2.2.symm
      · ext i j
        simp [shapeShiftM]
        cases j with
        | zero => simp [shiftPaintP, shiftPaintQ]
        | succ j' => simp [shiftPaintQ]
