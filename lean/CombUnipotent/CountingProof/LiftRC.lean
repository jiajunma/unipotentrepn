/-
# Lift construction for R/C tail cases

This file provides `liftPBP_RC_D`, a lift function that constructs a PBP in the
balanced case where σ's tail bottom at (b, 0) is either `.r` or `.c` (i.e.,
σ is in `R_sub` or `C_sub`). Complements `liftPBP_D` (DD case) in `Lift.lean`.

The condition structure `LiftCondition_RC σ` is weaker than the existing
`LiftCondition`; in exchange the col0 `v` must satisfy a compatibility predicate
`compat_with_RC σ v`.
-/
import CombUnipotent.CountingProof.Swap

open Classical

/-! ## LiftCondition_RC -/

/-- The conditions on σ used by `liftPBP_RC_D`.
    Weaker than `LiftCondition` — in particular, `σ.val.P.paint b 0` is allowed
    to be `.r` or `.c`, not only `.d`. Compatibility with col0 is enforced separately. -/
structure LiftCondition_RC {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) : Prop where
  /-- Strictly above row `b`: σ is entirely `.dot` (outside shape). -/
  tail_dot : ∀ i, μQ.colLen 0 < i → ∀ j, σ.val.P.paint i j = .dot
  /-- Row `b` at columns ≥ 1: σ has layer ≥ 3 (i.e., `.c` or `.d`), for cells inside shape. -/
  row_b_heavy : ∀ j, 1 ≤ j → (μQ.colLen 0, j) ∈ σ.val.P.shape →
    (σ.val.P.paint (μQ.colLen 0) j).layerOrd ≥ 3
  /-- `σ.val.P.paint b 0` is `.r` or `.c`. -/
  tail_symbol : σ.val.P.paint (μQ.colLen 0) 0 = .r ∨
                 σ.val.P.paint (μQ.colLen 0) 0 = .c

/-- Helper: `σ.val.P.paint b 0.layerOrd ≤ 3` when `LiftCondition_RC` holds. -/
lemma LiftCondition_RC.tail_symbol_layer_le_three {μP μQ : YoungDiagram}
    {σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    (h : LiftCondition_RC σ) :
    (σ.val.P.paint (μQ.colLen 0) 0).layerOrd ≤ 3 := by
  rcases h.tail_symbol with heq | heq
  · rw [heq]; decide
  · rw [heq]; decide

/-- Compatibility predicate between col0 and σ at row b.
    Captures the row_r constraint (no duplicate `.r` in row b) and the
    mono_P bound at `(b, 0) ≤ (b, 1)`. -/
def ValidCol0.compat_with_RC {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (v : ValidCol0 μP μQ) : Prop :=
  (v.paint (μQ.colLen 0)).layerOrd ≤ (σ.val.P.paint (μQ.colLen 0) 0).layerOrd ∧
  (σ.val.P.paint (μQ.colLen 0) 0 = .r → v.paint (μQ.colLen 0) ≠ .r)

/-! ## Building `LiftCondition_RC` from tail class -/

/-- Shared structural fact: for σ with `σ.P.paint b 0 ∈ {.r, .c}` and the balanced
    assumption, row b at cols ≥ 1 inside σ.P.shape has layer ≥ 3. -/
lemma row_b_j_ge_1_layer_ge_three {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_rc : σ.val.P.paint (μQ.colLen 0) 0 = .r ∨
            σ.val.P.paint (μQ.colLen 0) 0 = .c)
    (j : ℕ) (hj : 1 ≤ j) (hmem : (μQ.colLen 0, j) ∈ σ.val.P.shape) :
    (σ.val.P.paint (μQ.colLen 0) j).layerOrd ≥ 3 := by
  set b := μQ.colLen 0
  -- Q shape has colLen ≤ b, so (b, j) ∉ σ.Q.shape
  have hnotmem_Q : (b, j) ∉ σ.val.Q.shape := by
    intro h
    rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.colLen_shiftLeft] at h
    have h1 : μQ.colLen (j + 1) ≤ μQ.colLen 0 :=
      μQ.colLen_anti 0 (j + 1) (Nat.zero_le _)
    omega
  -- dot_match contrapositive: (b, j) ∈ P.shape, ∉ Q.shape → paint ≠ .dot
  have hne_dot : σ.val.P.paint b j ≠ .dot := by
    intro hdot
    have ⟨hqm, _⟩ := (σ.val.dot_match b j).mp ⟨hmem, hdot⟩
    exact hnotmem_Q hqm
  -- By r/c_bottom_row_b_ge_j_in_cd, paint ∈ {.c, .d, .dot}
  rcases h_rc with h_r | h_c
  · have := r_bottom_row_b_ge_j_in_cd σ h_bal h_r j hj
    rcases this with hc | hd | hdot
    · rw [hc]; decide
    · rw [hd]; decide
    · exact absurd hdot hne_dot
  · have := c_bottom_row_b_ge_j_in_cd σ h_bal h_c j hj
    rcases this with hc | hd | hdot
    · rw [hc]; decide
    · rw [hd]; decide
    · exact absurd hdot hne_dot

/-- Shared structural fact: rows strictly above `b` are outside σ's shape. -/
lemma row_gt_b_outside {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    {i : ℕ} (hi : μQ.colLen 0 < i) (j : ℕ) :
    σ.val.P.paint i j = .dot := by
  apply σ.val.P.paint_outside
  rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
  have hbal' : μP.colLen 1 = μQ.colLen 0 + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have h1 : μP.colLen (j + 1) ≤ μP.colLen 1 :=
    μP.colLen_anti 1 (j + 1) (by omega)
  omega

/-- `R_sub` elements satisfy `LiftCondition_RC`. -/
lemma liftCondition_RC_of_R_sub {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r) :
    LiftCondition_RC σ where
  tail_dot := fun i hi j => row_gt_b_outside σ h_bal hi j
  row_b_heavy := fun j hj hmem =>
    row_b_j_ge_1_layer_ge_three σ h_bal (Or.inl h_r) j hj hmem
  tail_symbol := Or.inl h_r

/-- `C_sub` elements satisfy `LiftCondition_RC`. -/
lemma liftCondition_RC_of_C_sub {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = .c) :
    LiftCondition_RC σ where
  tail_dot := fun i hi j => row_gt_b_outside σ h_bal hi j
  row_b_heavy := fun j hj hmem =>
    row_b_j_ge_1_layer_ge_three σ h_bal (Or.inr h_c) j hj hmem
  tail_symbol := Or.inr h_c

/-! ## The lift function `liftPBP_RC_D` -/

/-- The RC-case lift: given σ with `LiftCondition_RC` and a col0 compatible with σ at
    row b, produce a D-type PBP. -/
noncomputable def liftPBP_RC_D {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (v : ValidCol0 μP μQ)
    (h_cond : LiftCondition_RC σ)
    (h_compat : v.compat_with_RC σ)
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    PBPSet .D μP μQ := by
  set b := μQ.colLen 0 with hb_def
  have hbal' : μP.colLen 1 = b + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have h_tail_dot := h_cond.tail_dot
  have h_row_b_heavy := h_cond.row_b_heavy
  have h_b0_layer_le3 : (σ.val.P.paint b 0).layerOrd ≤ 3 :=
    h_cond.tail_symbol_layer_le_three
  have h_compat_layer : (v.paint b).layerOrd ≤ (σ.val.P.paint b 0).layerOrd :=
    h_compat.1
  have h_compat_ne_r : σ.val.P.paint b 0 = .r → v.paint b ≠ .r := h_compat.2
  -- paint_outside helper
  have hpo : ∀ i j, (i, j) ∉ μP → liftPaint_D σ.val v.paint i j = .dot := by
    intro i j hmem; cases j with
    | zero => exact v.dot_above i (by rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
    | succ j => exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  refine ⟨⟨.D,
    ⟨μP, liftPaint_D σ.val v.paint, hpo⟩,
    ⟨μQ, fun _ _ => .dot, fun _ _ _ => rfl⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P => intro _ _ _; trivial
  case sym_Q => intro _ _ _; simp [DRCSymbol.allowed]
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        simp only [liftPaint_D] at hpaint
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by
          by_contra h; push_neg at h
          exact v.nondot_tail i h (YoungDiagram.mem_iff_lt_colLen.mp hmem) hpaint), rfl⟩
      | succ j =>
        simp only [liftPaint_D] at hpaint
        have hmemσ : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hq, _⟩ := (σ.val.dot_match i j).mp ⟨hmemσ, hpaint⟩
        rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft] at hq; exact ⟨hq, rfl⟩
    · intro ⟨hmem, _⟩
      cases j with
      | zero =>
        have hq := YoungDiagram.mem_iff_lt_colLen.mp hmem
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hq hQP), by
          simp only [liftPaint_D]; exact v.dot_below i hq⟩
      | succ j =>
        have hq : (i, j) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hp, hpaint⟩ := (σ.val.dot_match i j).mpr
          ⟨hq, PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hq⟩
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft] at hp
        exact ⟨hp, by simp only [liftPaint_D]; exact hpaint⟩
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero => exact v.mono i₁ i₂ hi (YoungDiagram.mem_iff_lt_colLen.mp hmem)
      | succ j₂ =>
        by_cases h : i₁ < b
        · simp only [liftPaint_D]; rw [v.dot_below i₁ h]; simp [DRCSymbol.layerOrd]
        · push_neg at h
          -- i₁ ≥ b. From (i₂, j₂+1) ∈ μP: i₂ < μP.colLen(j₂+1) ≤ μP.colLen 1 = b+1
          have hi₂_le_b : i₂ ≤ b := by
            have h1 : i₂ < μP.colLen (j₂ + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem
            have h2 : μP.colLen (j₂ + 1) ≤ μP.colLen 1 :=
              μP.colLen_anti 1 (j₂ + 1) (by omega)
            omega
          have hi₁_eq_b : i₁ = b := by omega
          have hi₂_eq_b : i₂ = b := by omega
          subst hi₁_eq_b; subst hi₂_eq_b
          -- Goal: layerOrd v.paint b ≤ layerOrd σ.val.P.paint b j₂
          simp only [liftPaint_D]
          -- Case on j₂: 0 or ≥ 1
          cases j₂ with
          | zero => exact h_compat_layer
          | succ j₂' =>
            have hmem_σ : (b, j₂' + 1) ∈ σ.val.P.shape := by
              rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
            have hheavy := h_row_b_heavy (j₂' + 1) (by omega) hmem_σ
            have hv_le_3 : (v.paint b).layerOrd ≤ 3 :=
              le_trans h_compat_layer h_b0_layer_le3
            exact le_trans hv_le_3 hheavy
    | succ j₁ =>
      cases j₂ with
      | zero => exact absurd hj (by omega)
      | succ j₂ =>
        simp only [liftPaint_D]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi (by omega) (by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
  case mono_Q => intro _ _ _ _ _ _ _; simp [DRCSymbol.layerOrd]
  case row_s =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    -- Helper: τ.P.paint i j = .s forces a specific structure
    -- newS ≠ .s for row b cells at j ≥ 1 (heavy), or j = 0 σ.P.paint b 0 ∈ {.r, .c}
    have row_b_no_s : ∀ j, σ.val.P.paint b j ≠ .s := by
      intro j
      by_cases hj : j = 0
      · subst hj
        rcases h_cond.tail_symbol with heq | heq <;> rw [heq] <;> decide
      · -- j ≥ 1
        by_cases hmem : (b, j) ∈ σ.val.P.shape
        · have hheavy := h_row_b_heavy j (by omega) hmem
          intro heq; rw [heq, DRCSymbol.layerOrd] at hheavy; omega
        · rw [σ.val.P.paint_outside b j hmem]; decide
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          -- h₁: v.paint i = .s; h₂: σ.val.P.paint i j₂ = .s
          have hi : b ≤ i := by
            by_contra hh; push_neg at hh; rw [v.dot_below i hh] at h₁
            exact absurd h₁ (by decide)
          by_cases hi_b : i = b
          · subst hi_b; exact absurd h₂ (row_b_no_s j₂)
          · have hi_gt : b < i := lt_of_le_of_ne hi (Ne.symm hi_b)
            rw [h_tail_dot i hi_gt j₂] at h₂; exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : b ≤ i := by
            by_contra hh; push_neg at hh; rw [v.dot_below i hh] at h₂
            exact absurd h₂ (by decide)
          by_cases hi_b : i = b
          · subst hi_b; exact absurd h₁ (row_b_no_s j₁)
          · have hi_gt : b < i := lt_of_le_of_ne hi (Ne.symm hi_b)
            rw [h_tail_dot i hi_gt j₁] at h₁; exact absurd h₁ (by decide)
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have := σ.val.row_s i .L .L j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .L i j₁ = .s by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .L i j₂ = .s by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  case row_r =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    -- Helper: for j ≥ 1 at row b, σ.val.P.paint b j ≠ .r
    have row_b_j_ge_1_ne_r : ∀ j, 1 ≤ j → σ.val.P.paint b j ≠ .r := by
      intro j hj
      by_cases hmem : (b, j) ∈ σ.val.P.shape
      · have hheavy := h_row_b_heavy j hj hmem
        intro heq; rw [heq, DRCSymbol.layerOrd] at hheavy; omega
      · rw [σ.val.P.paint_outside b j hmem]; decide
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- L-L
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          -- h₁: v.paint i = .r; h₂: σ.val.P.paint i j₂ = .r
          have hi : b ≤ i := by
            by_contra hh; push_neg at hh; rw [v.dot_below i hh] at h₁
            exact absurd h₁ (by decide)
          by_cases hi_b : i = b
          · subst hi_b
            -- v.paint b = .r. By compat, σ.val.P.paint b 0 ≠ .r (else contradiction).
            -- Case analysis on j₂.
            cases j₂ with
            | zero =>
              -- h₂ : σ.val.P.paint b 0 = .r
              exact absurd h₁ (h_compat_ne_r h₂)
            | succ j₂' =>
              exact absurd h₂ (row_b_j_ge_1_ne_r (j₂' + 1) (by omega))
          · have hi_gt : b < i := lt_of_le_of_ne hi (Ne.symm hi_b)
            rw [h_tail_dot i hi_gt j₂] at h₂; exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : b ≤ i := by
            by_contra hh; push_neg at hh; rw [v.dot_below i hh] at h₂
            exact absurd h₂ (by decide)
          by_cases hi_b : i = b
          · subst hi_b
            -- Symmetric: h₂ : v.paint b = .r, h₁ : σ.val.P.paint b j₁ = .r
            cases j₁ with
            | zero => exact absurd h₂ (h_compat_ne_r h₁)
            | succ j₁' =>
              exact absurd h₁ (row_b_j_ge_1_ne_r (j₁' + 1) (by omega))
          · have hi_gt : b < i := lt_of_le_of_ne hi (Ne.symm hi_b)
            rw [h_tail_dot i hi_gt j₁] at h₁; exact absurd h₁ (by decide)
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have := σ.val.row_r i .L .L j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .L i j₁ = .r by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .L i j₂ = .r by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    simp only [liftPaint_D] at h₁ h₂
    cases j with
    | zero => exact v.col_c_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    simp only [liftPaint_D] at h₁ h₂
    cases j with
    | zero => exact v.col_d_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h

/-! ## Round-trip and injectivity for `liftPBP_RC_D` -/

@[simp] lemma liftPBP_RC_D_paint_eq {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (v : ValidCol0 μP μQ)
    (h_cond : LiftCondition_RC σ)
    (h_compat : v.compat_with_RC σ)
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    (liftPBP_RC_D σ v h_cond h_compat h_bal hQP).val.P.paint =
      liftPaint_D σ.val v.paint := rfl

/-- Round-trip: ∇²(liftPBP_RC_D σ v ...) = σ. -/
theorem liftPBP_RC_D_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (v : ValidCol0 μP μQ)
    (h_cond : LiftCondition_RC σ)
    (h_compat : v.compat_with_RC σ)
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    doubleDescent_D_map (liftPBP_RC_D σ v h_cond h_compat h_bal hQP) = σ := by
  -- The proof is structurally the same as liftPBP_D_round_trip:
  -- it depends only on τ.P.paint = liftPaint_D σ.val v.paint and τ.Q = all-dots-μQ.
  apply Subtype.ext
  show doubleDescent_D_PBP (liftPBP_RC_D σ v h_cond h_compat h_bal hQP).val
    (liftPBP_RC_D σ v h_cond h_compat h_bal hQP).prop.1 = σ.val
  apply PBP.ext''
  · rw [σ.prop.1]; rfl
  · apply PaintedYoungDiagram.ext'
    · rw [σ.prop.2.1]; rfl
    · funext i j
      set τ := liftPBP_RC_D σ v h_cond h_compat h_bal hQP
      show PBP.doubleDescent_D_paintL τ.val i j = σ.val.P.paint i j
      have hQshape : τ.val.Q.shape = μQ := rfl
      have hPshape : τ.val.P.shape = μP := rfl
      have hPpaint : ∀ k m, τ.val.P.paint k m = liftPaint_D σ.val v.paint k m :=
        fun _ _ => rfl
      have hQ_eq : μQ.colLen (j + 1) = σ.val.Q.shape.colLen j := by
        rw [σ.prop.2.2, YoungDiagram.colLen_shiftLeft]
      have hP_eq : μP.colLen (j + 1) = σ.val.P.shape.colLen j := by
        rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]
      simp only [PBP.doubleDescent_D_paintL, hQshape]
      by_cases hA : i < μQ.colLen (j + 1)
      · rw [if_pos hA]
        rw [hQ_eq] at hA
        have hmemQ : (i, j) ∈ σ.val.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr hA
        have hQdot : σ.val.Q.paint i j = .dot :=
          PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hmemQ
        have ⟨_, hPdot⟩ := (σ.val.dot_match i j).mpr ⟨hmemQ, hQdot⟩
        exact hPdot.symm
      · rw [if_neg hA]
        rw [hQ_eq] at hA
        have hnotQ : (i, j) ∉ σ.val.Q.shape := fun hmem =>
          hA (YoungDiagram.mem_iff_lt_colLen.mp hmem)
        by_cases hB : i < PBP.dotScolLen τ.val.P (j + 1)
        · rw [if_pos hB]
          have hlift_mono : τ.val.P.layerMonotone := τ.val.mono_P
          have hdscol_le : PBP.dotScolLen τ.val.P (j + 1) ≤
              τ.val.P.shape.colLen (j + 1) :=
            PBP.dotScolLen_le_colLen τ.val.P hlift_mono (j + 1)
          have hi_lt_shape : i < τ.val.P.shape.colLen (j + 1) :=
            lt_of_lt_of_le hB hdscol_le
          have hlo_lift : (τ.val.P.paint i (j + 1)).layerOrd ≤ 1 := by
            have hds_eq : PBP.dotScolLen τ.val.P (j + 1) =
                (PBP.dotSdiag τ.val.P hlift_mono).colLen (j + 1) :=
              PBP.dotScolLen_eq_dotSdiag_colLen _ hlift_mono _
            rw [hds_eq] at hB
            exact PBP.layerOrd_le_one_of_lt_dotSdiag_colLen _ hlift_mono hB
          rw [hPpaint] at hlo_lift
          simp only [liftPaint_D] at hlo_lift
          have hmemP : (i, j) ∈ σ.val.P.shape := by
            rw [hPshape] at hi_lt_shape
            rw [YoungDiagram.mem_iff_lt_colLen, ← hP_eq]; exact hi_lt_shape
          have hne_dot : σ.val.P.paint i j ≠ .dot := by
            intro hpd
            have ⟨hqm, _⟩ := (σ.val.dot_match i j).mp ⟨hmemP, hpd⟩
            exact hnotQ hqm
          revert hlo_lift hne_dot
          cases σ.val.P.paint i j <;> simp [DRCSymbol.layerOrd]
        · rw [if_neg hB]
          rw [hPpaint]; rfl
  · apply PaintedYoungDiagram.ext'
    · rw [σ.prop.2.2]; rfl
    · funext i j
      show DRCSymbol.dot = σ.val.Q.paint i j
      by_cases hmem : (i, j) ∈ σ.val.Q.shape
      · exact (PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hmem).symm
      · exact (σ.val.Q.paint_outside i j hmem).symm

/-- Injectivity for `liftPBP_RC_D` in both arguments. -/
theorem liftPBP_RC_D_injective {μP μQ : YoungDiagram}
    {σ₁ σ₂ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    {v₁ v₂ : ValidCol0 μP μQ}
    {h_cond₁ : LiftCondition_RC σ₁} {h_cond₂ : LiftCondition_RC σ₂}
    {h_compat₁ : v₁.compat_with_RC σ₁} {h_compat₂ : v₂.compat_with_RC σ₂}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (h : liftPBP_RC_D σ₁ v₁ h_cond₁ h_compat₁ h_bal hQP =
         liftPBP_RC_D σ₂ v₂ h_cond₂ h_compat₂ h_bal hQP) :
    σ₁ = σ₂ ∧ v₁ = v₂ := by
  have hval := congrArg Subtype.val h
  have hP : (liftPBP_RC_D σ₁ v₁ h_cond₁ h_compat₁ h_bal hQP).val.P.paint =
            (liftPBP_RC_D σ₂ v₂ h_cond₂ h_compat₂ h_bal hQP).val.P.paint :=
    congr_arg (fun τ => τ.P.paint) hval
  have hv : v₁.paint = v₂.paint := by
    ext i; have := congr_fun (congr_fun hP i) 0
    simp [liftPaint_D] at this; exact this
  have hv_eq : v₁ = v₂ := by
    cases v₁; cases v₂; simp only [ValidCol0.mk.injEq]; exact hv
  have hσP : σ₁.val.P.paint = σ₂.val.P.paint := by
    ext i j; have := congr_fun (congr_fun hP i) (j + 1)
    simp [liftPaint_D] at this; exact this
  have hσQ : σ₁.val.Q = σ₂.val.Q := by
    apply PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.2, σ₂.prop.2.2])
    ext i j
    have hQshape_eq : σ₁.val.Q.shape = σ₂.val.Q.shape := by
      rw [σ₁.prop.2.2, σ₂.prop.2.2]
    by_cases hmem : (i, j) ∈ σ₁.val.Q.shape
    · rw [PBP.Q_all_dot_of_D σ₁.val σ₁.prop.1 i j hmem,
          PBP.Q_all_dot_of_D σ₂.val σ₂.prop.1 i j (hQshape_eq ▸ hmem)]
    · rw [σ₁.val.Q.paint_outside i j hmem,
          σ₂.val.Q.paint_outside i j (hQshape_eq ▸ hmem)]
  have hσ_eq : σ₁.val = σ₂.val := PBP.ext'' (by rw [σ₁.prop.1, σ₂.prop.1])
    (PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.1, σ₂.prop.2.1]) hσP) hσQ
  exact ⟨Subtype.ext hσ_eq, hv_eq⟩


/-! ## TSeq peel-first equivalence

`{w : TSeq (k + 1) | w.val 0 = .s} ≃ TSeq k` by dropping the `.s` at position 0. -/

/-- Peel the first element `.s` from a TSeq(k+1). -/
noncomputable def TSeq_peel_first_s (k : ℕ) :
    {w : TSeq (k + 1) // w.val ⟨0, Nat.succ_pos k⟩ = DRCSymbol.s} ≃ TSeq k where
  toFun := fun ⟨w, _⟩ => ⟨
    fun i => w.val ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩,
    fun i => w.property.1 ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩,
    fun i j hij => w.property.2.1
      ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      (by show i.val + 1 ≤ j.val + 1; omega),
    fun i j hi hj => Fin.ext (by
      have hh := w.property.2.2.1
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ hi hj
      have : i.val + 1 = j.val + 1 := Fin.mk.inj_iff.mp hh
      omega),
    fun i j hi hj => Fin.ext (by
      have hh := w.property.2.2.2
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ hi hj
      have : i.val + 1 = j.val + 1 := Fin.mk.inj_iff.mp hh
      omega)⟩
  invFun := fun w' => ⟨⟨
    fun i => if h : i.val = 0 then DRCSymbol.s else w'.val ⟨i.val - 1, by omega⟩,
    by
      intro i
      by_cases hi : i.val = 0
      · dsimp only; rw [dif_pos hi]
        exact Or.inl rfl
      · dsimp only; rw [dif_neg hi]
        exact w'.property.1 ⟨i.val - 1, by omega⟩,
    by
      intro i j hij
      dsimp only
      by_cases hi : i.val = 0
      · rw [dif_pos hi]
        by_cases hj : j.val = 0
        · rw [dif_pos hj]
        · rw [dif_neg hj]
          have := w'.property.1 ⟨j.val - 1, by omega⟩
          rcases this with h | h | h | h <;> rw [h] <;> decide
      · have hj : j.val ≠ 0 := by omega
        rw [dif_neg hi, dif_neg hj]
        exact w'.property.2.1 ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
          (by show i.val - 1 ≤ j.val - 1; omega),
    by
      intro i j hi hj
      dsimp only at hi hj
      by_cases hi0 : i.val = 0
      · rw [dif_pos hi0] at hi
        exact absurd hi (by decide)
      · by_cases hj0 : j.val = 0
        · rw [dif_pos hj0] at hj
          exact absurd hj (by decide)
        · rw [dif_neg hi0] at hi
          rw [dif_neg hj0] at hj
          have hh := w'.property.2.2.1 ⟨i.val - 1, by omega⟩
            ⟨j.val - 1, by omega⟩ hi hj
          have : i.val - 1 = j.val - 1 := Fin.mk.inj_iff.mp hh
          exact Fin.ext (by omega),
    by
      intro i j hi hj
      dsimp only at hi hj
      by_cases hi0 : i.val = 0
      · rw [dif_pos hi0] at hi
        exact absurd hi (by decide)
      · by_cases hj0 : j.val = 0
        · rw [dif_pos hj0] at hj
          exact absurd hj (by decide)
        · rw [dif_neg hi0] at hi
          rw [dif_neg hj0] at hj
          have hh := w'.property.2.2.2 ⟨i.val - 1, by omega⟩
            ⟨j.val - 1, by omega⟩ hi hj
          have : i.val - 1 = j.val - 1 := Fin.mk.inj_iff.mp hh
          exact Fin.ext (by omega)⟩,
    by
      dsimp only
      rw [dif_pos (show (0 : ℕ) = 0 from rfl)]⟩
  left_inv := fun ⟨w, hw⟩ => by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    dsimp only
    by_cases hi : i.val = 0
    · rw [dif_pos hi]
      have : i = ⟨0, Nat.succ_pos k⟩ := Fin.ext hi
      rw [this]; exact hw.symm
    · rw [dif_neg hi]
      have hpos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      have h1 : i.val - 1 + 1 < k + 1 := by
        have := i.isLt; omega
      have h2 : (⟨i.val - 1 + 1, h1⟩ : Fin (k + 1)) = i := Fin.ext (by
        show i.val - 1 + 1 = i.val; omega)
      rw [h2]
  right_inv := fun w' => by
    apply Subtype.ext
    funext i
    dsimp only
    have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (k + 1)).val ≠ 0 := by
      simp
    rw [dif_neg hne]
    have : (⟨i.val + 1 - 1, by omega⟩ : Fin k) = i := Fin.ext (by simp)
    rw [this]

