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


/-! ## Counting R and C subsets of ValidCol0 -/

/-- Direct forward map: from v with v.paint b = .s to a TSeq (k-1) representing the
    tail (rows [b+1, c)). -/
noncomputable def R_col0_toTSeqPred {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0)
    (v : {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s}) :
    TSeq (μP.colLen 0 - μQ.colLen 0 - 1) := by
  refine ⟨fun i => v.val.paint (μQ.colLen 0 + 1 + i.val), ?_, ?_, ?_, ?_⟩
  · intro i
    show v.val.paint _ = .s ∨ v.val.paint _ = .r ∨ v.val.paint _ = .c ∨ v.val.paint _ = .d
    have h1 : μQ.colLen 0 ≤ μQ.colLen 0 + 1 + i.val := by omega
    have h2 : μQ.colLen 0 + 1 + i.val < μP.colLen 0 := by have := i.isLt; omega
    have hne := v.val.nondot_tail _ h1 h2
    generalize hsym : v.val.paint (μQ.colLen 0 + 1 + i.val) = sym at hne ⊢
    cases sym
    · exact absurd rfl hne
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro i j hij
    have h2 : μQ.colLen 0 + 1 + j.val < μP.colLen 0 := by have := j.isLt; omega
    exact v.val.mono _ _ (by omega) h2
  · intro i j hi hj
    have := v.val.col_c_unique _ _ hi hj
    exact Fin.ext (by omega)
  · intro i j hi hj
    have := v.val.col_d_unique _ _ hi hj
    exact Fin.ext (by omega)

/-- Direct inverse: from a TSeq (k-1) build a ValidCol0 with v.paint b = .s. -/
noncomputable def R_col0_ofTSeqPred {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0)
    (w : TSeq (μP.colLen 0 - μQ.colLen 0 - 1)) :
    {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} := by
  -- Use a helper to define the paint function
  let paint : ℕ → DRCSymbol := fun i =>
    if h1 : i < μQ.colLen 0 then DRCSymbol.dot
    else if h2 : i = μQ.colLen 0 then DRCSymbol.s
    else if h3 : i < μP.colLen 0 then
      w.val ⟨i - μQ.colLen 0 - 1, by
        push_neg at h1
        have : i ≠ μQ.colLen 0 := h2
        omega⟩
    else DRCSymbol.dot
  refine ⟨⟨paint, ?dot_below, ?nondot_tail, ?dot_above, ?mono, ?col_c_unique,
    ?col_d_unique⟩, ?b_eq_s⟩
  case dot_below =>
    intro i hi
    show paint i = DRCSymbol.dot
    simp only [paint, dif_pos hi]
  case nondot_tail =>
    intro i h1 h2
    show paint i ≠ DRCSymbol.dot
    have hn1 : ¬ i < μQ.colLen 0 := by omega
    by_cases hi : i = μQ.colLen 0
    · simp only [paint, dif_neg hn1, dif_pos hi]; decide
    · simp only [paint, dif_neg hn1, dif_neg hi, dif_pos h2]
      have hmem := w.property.1 ⟨i - μQ.colLen 0 - 1, by omega⟩
      rcases hmem with h | h | h | h <;> rw [h] <;> decide
  case dot_above =>
    intro i hi
    show paint i = DRCSymbol.dot
    have h1 : ¬ i < μQ.colLen 0 := by omega
    have h2 : i ≠ μQ.colLen 0 := by omega
    have h3 : ¬ i < μP.colLen 0 := by omega
    simp only [paint, dif_neg h1, dif_neg h2, dif_neg h3]
  case mono =>
    intro i₁ i₂ h12 h2
    show (paint i₁).layerOrd ≤ (paint i₂).layerOrd
    by_cases hi1 : i₁ < μQ.colLen 0
    · simp only [paint, dif_pos hi1]; simp [DRCSymbol.layerOrd]
    · by_cases hi1' : i₁ = μQ.colLen 0
      · simp only [paint, dif_neg hi1, dif_pos hi1']
        by_cases hi2 : i₂ < μQ.colLen 0
        · exfalso; omega
        · by_cases hi2' : i₂ = μQ.colLen 0
          · simp only [paint, dif_neg hi2, dif_pos hi2']; exact le_refl _
          · have hi2_lt : i₂ < μP.colLen 0 := h2
            simp only [paint, dif_neg hi2, dif_neg hi2', dif_pos hi2_lt]
            have hmem := w.property.1 ⟨i₂ - μQ.colLen 0 - 1, by omega⟩
            rcases hmem with h | h | h | h <;> rw [h] <;> decide
      · have hi1_lt : i₁ < μP.colLen 0 := by omega
        have hi2_ne : i₂ ≠ μQ.colLen 0 := by omega
        have hi2_not_lt : ¬ i₂ < μQ.colLen 0 := by omega
        simp only [paint, dif_neg hi1, dif_neg hi1', dif_pos hi1_lt]
        simp only [paint, dif_neg hi2_not_lt, dif_neg hi2_ne, dif_pos h2]
        have hb1 : i₁ - μQ.colLen 0 - 1 < μP.colLen 0 - μQ.colLen 0 - 1 := by omega
        have hb2 : i₂ - μQ.colLen 0 - 1 < μP.colLen 0 - μQ.colLen 0 - 1 := by omega
        have hle : i₁ - μQ.colLen 0 - 1 ≤ i₂ - μQ.colLen 0 - 1 := by omega
        exact w.property.2.1 ⟨i₁ - μQ.colLen 0 - 1, hb1⟩
          ⟨i₂ - μQ.colLen 0 - 1, hb2⟩ hle
  case col_c_unique =>
    intro i₁ i₂ hc1 hc2
    show i₁ = i₂
    -- Both must be strictly above b
    have h_not_below : ∀ i, paint i = DRCSymbol.c →
        μQ.colLen 0 < i ∧ i < μP.colLen 0 := by
      intro i hc
      by_cases hi : i < μQ.colLen 0
      · simp only [paint, dif_pos hi] at hc; exact absurd hc (by decide)
      · by_cases hi' : i = μQ.colLen 0
        · simp only [paint, dif_neg hi, dif_pos hi'] at hc; exact absurd hc (by decide)
        · by_cases hi'' : i < μP.colLen 0
          · exact ⟨by omega, hi''⟩
          · simp only [paint, dif_neg hi, dif_neg hi', dif_neg hi''] at hc
            exact absurd hc (by decide)
    obtain ⟨h1a, h1b⟩ := h_not_below i₁ hc1
    obtain ⟨h2a, h2b⟩ := h_not_below i₂ hc2
    have hi1_n1 : ¬ i₁ < μQ.colLen 0 := by omega
    have hi1_ne : i₁ ≠ μQ.colLen 0 := by omega
    have hi2_n1 : ¬ i₂ < μQ.colLen 0 := by omega
    have hi2_ne : i₂ ≠ μQ.colLen 0 := by omega
    simp only [paint, dif_neg hi1_n1, dif_neg hi1_ne, dif_pos h1b] at hc1
    simp only [paint, dif_neg hi2_n1, dif_neg hi2_ne, dif_pos h2b] at hc2
    have hw := w.property.2.2.1 ⟨i₁ - μQ.colLen 0 - 1, by omega⟩
      ⟨i₂ - μQ.colLen 0 - 1, by omega⟩ hc1 hc2
    have hfin : i₁ - μQ.colLen 0 - 1 = i₂ - μQ.colLen 0 - 1 := Fin.mk.inj_iff.mp hw
    omega
  case col_d_unique =>
    intro i₁ i₂ hd1 hd2
    show i₁ = i₂
    have h_not_below : ∀ i, paint i = DRCSymbol.d →
        μQ.colLen 0 < i ∧ i < μP.colLen 0 := by
      intro i hd
      by_cases hi : i < μQ.colLen 0
      · simp only [paint, dif_pos hi] at hd; exact absurd hd (by decide)
      · by_cases hi' : i = μQ.colLen 0
        · simp only [paint, dif_neg hi, dif_pos hi'] at hd; exact absurd hd (by decide)
        · by_cases hi'' : i < μP.colLen 0
          · exact ⟨by omega, hi''⟩
          · simp only [paint, dif_neg hi, dif_neg hi', dif_neg hi''] at hd
            exact absurd hd (by decide)
    obtain ⟨h1a, h1b⟩ := h_not_below i₁ hd1
    obtain ⟨h2a, h2b⟩ := h_not_below i₂ hd2
    have hi1_n1 : ¬ i₁ < μQ.colLen 0 := by omega
    have hi1_ne : i₁ ≠ μQ.colLen 0 := by omega
    have hi2_n1 : ¬ i₂ < μQ.colLen 0 := by omega
    have hi2_ne : i₂ ≠ μQ.colLen 0 := by omega
    simp only [paint, dif_neg hi1_n1, dif_neg hi1_ne, dif_pos h1b] at hd1
    simp only [paint, dif_neg hi2_n1, dif_neg hi2_ne, dif_pos h2b] at hd2
    have hw := w.property.2.2.2 ⟨i₁ - μQ.colLen 0 - 1, by omega⟩
      ⟨i₂ - μQ.colLen 0 - 1, by omega⟩ hd1 hd2
    have hfin : i₁ - μQ.colLen 0 - 1 = i₂ - μQ.colLen 0 - 1 := Fin.mk.inj_iff.mp hw
    omega
  case b_eq_s =>
    show paint (μQ.colLen 0) = DRCSymbol.s
    have h1 : ¬ μQ.colLen 0 < μQ.colLen 0 := Nat.lt_irrefl _
    simp only [paint, dif_neg h1, dif_pos rfl]
    rfl

/-- Direct Equiv: `R_ValidCol0 ≃ TSeq (k - 1)`. -/
noncomputable def R_col0_equiv_TSeqPred {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0) :
    {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} ≃
    TSeq (μP.colLen 0 - μQ.colLen 0 - 1) where
  toFun := R_col0_toTSeqPred hQP hk_pos
  invFun := R_col0_ofTSeqPred hQP hk_pos
  left_inv := fun ⟨v, hv⟩ => by
    apply Subtype.ext
    apply ValidCol0.ext
    funext i
    show (R_col0_ofTSeqPred hQP hk_pos _).val.paint i = v.paint i
    show (if h1 : i < μQ.colLen 0 then _ else
          if h2 : i = μQ.colLen 0 then _ else
          if h3 : i < μP.colLen 0 then _ else _) = _
    by_cases h1 : i < μQ.colLen 0
    · rw [dif_pos h1]; exact (v.dot_below i h1).symm
    · by_cases h2 : i = μQ.colLen 0
      · rw [dif_neg h1, dif_pos h2, h2]; exact hv.symm
      · by_cases h3 : i < μP.colLen 0
        · rw [dif_neg h1, dif_neg h2, dif_pos h3]
          show v.paint (μQ.colLen 0 + 1 + (i - μQ.colLen 0 - 1)) = v.paint i
          congr 1; omega
        · rw [dif_neg h1, dif_neg h2, dif_neg h3]
          exact (v.dot_above i (by omega)).symm
  right_inv := fun w => by
    apply Subtype.ext
    funext i
    show (R_col0_toTSeqPred hQP hk_pos _).val i = w.val i
    show (R_col0_ofTSeqPred hQP hk_pos w).val.paint (μQ.colLen 0 + 1 + i.val) = w.val i
    show (if h1 : _ then _ else if h2 : _ then _ else if h3 : _ then _ else _) = _
    have h1 : ¬ μQ.colLen 0 + 1 + i.val < μQ.colLen 0 := by omega
    have h2 : μQ.colLen 0 + 1 + i.val ≠ μQ.colLen 0 := by omega
    have h3 : μQ.colLen 0 + 1 + i.val < μP.colLen 0 := by have := i.isLt; omega
    rw [dif_neg h1, dif_neg h2, dif_pos h3]
    have hib : μQ.colLen 0 + 1 + i.val - μQ.colLen 0 - 1 <
               μP.colLen 0 - μQ.colLen 0 - 1 := by
      have := i.isLt; omega
    have hfin : (⟨μQ.colLen 0 + 1 + i.val - μQ.colLen 0 - 1, hib⟩ :
           Fin (μP.colLen 0 - μQ.colLen 0 - 1)) = i := Fin.ext (by
      show μQ.colLen 0 + 1 + i.val - μQ.colLen 0 - 1 = i.val
      omega)
    rw [hfin]

/-- Number of valid col0 with `v.paint b = .s`. Equals `|TSeq (k-1)|`. -/
theorem R_ValidCol0_card {μP μQ : YoungDiagram}
    (k : ℕ) (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ k) :
    Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} =
      Fintype.card (TSeq (k - 1)) := by
  have hm_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0 := by omega
  rw [Fintype.card_congr (R_col0_equiv_TSeqPred hQP hm_pos)]
  have hsub : μP.colLen 0 - μQ.colLen 0 - 1 = k - 1 := by omega
  rw [hsub]

/-! ## D_ValidCol0 and C_ValidCol0 counts -/

/-- Number of valid col0 with `v.paint b = .d`. Equals 1 if k=1, else 0. -/
theorem D_ValidCol0_card {μP μQ : YoungDiagram}
    (k : ℕ) (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ k) :
    Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.d} =
      (if k = 1 then 1 else 0) := by
  by_cases hk1 : k = 1
  · -- k = 1: exactly one element
    rw [if_pos hk1]
    rw [Fintype.card_eq_one_iff]
    -- Construct the unique element: v with v.paint b = .d, dot elsewhere
    have hc_eq : μP.colLen 0 = μQ.colLen 0 + 1 := by omega
    let paint_fn : ℕ → DRCSymbol :=
      fun i => if i = μQ.colLen 0 then DRCSymbol.d else DRCSymbol.dot
    refine ⟨⟨⟨paint_fn, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · -- dot_below
      intro i hi
      show paint_fn i = DRCSymbol.dot
      simp only [paint_fn, if_neg (by omega : i ≠ μQ.colLen 0)]
    · -- nondot_tail
      intro i h1 h2
      show paint_fn i ≠ DRCSymbol.dot
      have : i = μQ.colLen 0 := by omega
      simp only [paint_fn, this, if_pos rfl]; decide
    · -- dot_above
      intro i hi
      show paint_fn i = DRCSymbol.dot
      simp only [paint_fn, if_neg (by omega : i ≠ μQ.colLen 0)]
    · -- mono
      intro i₁ i₂ h12 h2
      show (paint_fn i₁).layerOrd ≤ (paint_fn i₂).layerOrd
      by_cases he1 : i₁ = μQ.colLen 0
      · by_cases he2 : i₂ = μQ.colLen 0
        · simp only [paint_fn, if_pos he1, if_pos he2]; exact le_refl _
        · exfalso; omega
      · by_cases he2 : i₂ = μQ.colLen 0
        · simp only [paint_fn, if_neg he1, if_pos he2]; decide
        · simp only [paint_fn, if_neg he1, if_neg he2]; exact le_refl _
    · -- col_c_unique
      intro i₁ i₂ h1 h2
      show i₁ = i₂
      simp only [paint_fn] at h1
      by_cases he : i₁ = μQ.colLen 0
      · rw [if_pos he] at h1; exact absurd h1 (by decide)
      · rw [if_neg he] at h1; exact absurd h1 (by decide)
    · -- col_d_unique
      intro i₁ i₂ h1 h2
      show i₁ = i₂
      simp only [paint_fn] at h1 h2
      by_cases he1 : i₁ = μQ.colLen 0
      · by_cases he2 : i₂ = μQ.colLen 0
        · rw [he1, he2]
        · rw [if_neg he2] at h2; exact absurd h2 (by decide)
      · rw [if_neg he1] at h1; exact absurd h1 (by decide)
    · -- v.paint (μQ.colLen 0) = .d
      show paint_fn (μQ.colLen 0) = _
      simp only [paint_fn, if_pos rfl]
    · -- Uniqueness
      intro ⟨v, hv_eq⟩
      apply Subtype.ext
      apply ValidCol0.ext
      funext i
      show v.paint i = paint_fn i
      by_cases hi : i = μQ.colLen 0
      · simp only [paint_fn, hi, if_pos rfl]; exact hv_eq
      · simp only [paint_fn, if_neg hi]
        by_cases hi_lt : i < μQ.colLen 0
        · exact v.dot_below i hi_lt
        · have : μP.colLen 0 ≤ i := by omega
          exact v.dot_above i this
  · -- k ≥ 2: empty
    rw [if_neg hk1]
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro ⟨v, hv⟩
    -- (μQ.colLen 0 + 1) is also in the tail, mono forces .d there, col_d_unique fails
    have hk2 : k ≥ 2 := by omega
    have h_b_lt : μQ.colLen 0 < μP.colLen 0 := by omega
    have h_b1_lt : μQ.colLen 0 + 1 < μP.colLen 0 := by omega
    have hnd : v.paint (μQ.colLen 0 + 1) ≠ DRCSymbol.dot :=
      v.nondot_tail _ (by omega) h_b1_lt
    have hmono := v.mono (μQ.colLen 0) (μQ.colLen 0 + 1) (by omega) h_b1_lt
    rw [hv] at hmono
    have hd_next : v.paint (μQ.colLen 0 + 1) = DRCSymbol.d := by
      generalize hsym : v.paint (μQ.colLen 0 + 1) = sym at hnd hmono
      cases sym
      · exact absurd rfl hnd
      · rw [DRCSymbol.layerOrd, DRCSymbol.layerOrd] at hmono; omega
      · rw [DRCSymbol.layerOrd, DRCSymbol.layerOrd] at hmono; omega
      · rw [DRCSymbol.layerOrd, DRCSymbol.layerOrd] at hmono; omega
      · rfl
    have := v.col_d_unique (μQ.colLen 0) (μQ.colLen 0 + 1) hv hd_next
    omega

/-- Number of valid col0 with `v.paint b ∈ {.s, .r, .c}` (equivalently, `v.paint b ≠ .d`). -/
theorem C_ValidCol0_card {μP μQ : YoungDiagram}
    (k : ℕ) (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ k) :
    Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) ≠ DRCSymbol.d} =
      4 * k - (if k = 1 then 1 else 0) := by
  -- |C_ValidCol0| = |ValidCol0| - |D_ValidCol0|
  have h_total : Fintype.card (ValidCol0 μP μQ) = 4 * k := by
    have := validCol0_card k hk hQP hk_pos
    rw [this, tailCoeffs_total k hk_pos]
  have h_d : Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.d} =
      (if k = 1 then 1 else 0) := D_ValidCol0_card k hk hQP hk_pos
  -- Use Fintype.card_subtype_or_disjoint or manual splitting
  have hsplit : Fintype.card (ValidCol0 μP μQ) =
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.d} +
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) ≠ DRCSymbol.d} := by
    rw [Fintype.card_subtype_compl]
    have : Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.d} ≤
           Fintype.card (ValidCol0 μP μQ) := Fintype.card_subtype_le _
    omega
  rw [h_total, h_d] at hsplit
  omega

/-! ## Fiber card for R and C cases -/

/-- Helper: for τ ∈ fiber σ with σ.P.paint b 0 = .r, τ.P.paint b 1 = .r. -/
lemma fiber_paint_b1_of_R {μP μQ : YoungDiagram}
    {σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    (τ : doubleDescent_D_fiber σ)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r) :
    τ.val.val.P.paint (μQ.colLen 0) 1 = DRCSymbol.r := by
  -- From ∇²τ = σ, σ.val.P.paint b 0 = PBP.doubleDescent_D_paintL τ.val.val b 0
  have hdd : σ.val = doubleDescent_D_PBP τ.val.val τ.val.prop.1 := by
    have := τ.prop
    unfold doubleDescent_D_map at this
    exact (congr_arg Subtype.val this).symm
  have h_eq : σ.val.P.paint (μQ.colLen 0) 0 =
      PBP.doubleDescent_D_paintL τ.val.val (μQ.colLen 0) 0 := by
    rw [hdd]; rfl
  rw [h_r] at h_eq
  -- Unfold the ∇² formula
  simp only [PBP.doubleDescent_D_paintL] at h_eq
  -- Analyze the if-then-else: branch is the last `else` (else we'd get .dot or .s)
  by_cases hA : μQ.colLen 0 < τ.val.val.Q.shape.colLen (0 + 1)
  · rw [if_pos hA] at h_eq; exact absurd h_eq (by decide)
  · rw [if_neg hA] at h_eq
    by_cases hB : μQ.colLen 0 < PBP.dotScolLen τ.val.val.P (0 + 1)
    · rw [if_pos hB] at h_eq; exact absurd h_eq (by decide)
    · rw [if_neg hB] at h_eq
      exact h_eq.symm

/-- For σ ∈ R_sub, every τ ∈ fiber σ has τ.P.paint b 0 = .s. -/
lemma fiber_col0_of_R_forced_s {μP μQ : YoungDiagram}
    {σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (τ : doubleDescent_D_fiber σ)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r) :
    τ.val.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.s := by
  have h_b1 := fiber_paint_b1_of_R τ h_r
  -- col0(b) = τ.P.paint b 0. From mono_P at (b, 0) ≤ (b, 1) with (b, 1) ∈ shape:
  -- layer col0(b) ≤ layer .r = 2. So col0(b) ∈ {dot, s, r}.
  -- nondot_tail: col0(b) ≠ .dot.
  -- row_r at row b: (b, 1) has .r, can't have another .r at (b, 0). So col0(b) ≠ .r.
  -- → col0(b) = .s.
  have hbal' : μP.colLen 1 = μQ.colLen 0 + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have hμP_gt : μQ.colLen 0 < μP.colLen 0 := by
    have h01 : μP.colLen 1 ≤ μP.colLen 0 := μP.colLen_anti 0 1 (by omega)
    omega
  have hμP_ge_2 : μQ.colLen 0 + 1 < μP.colLen 0 + 1 := by omega
  have hmem_b1 : (μQ.colLen 0, 1) ∈ τ.val.val.P.shape := by
    rw [τ.val.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  have hmono := τ.val.val.mono_P (μQ.colLen 0) 0 (μQ.colLen 0) 1 (le_refl _) (by omega) hmem_b1
  rw [h_b1] at hmono
  simp only [DRCSymbol.layerOrd] at hmono
  -- col0(b).layerOrd ≤ 2
  have hmem_b0 : (μQ.colLen 0, 0) ∈ τ.val.val.P.shape := by
    rw [τ.val.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  have hnotQ : (μQ.colLen 0, 0) ∉ τ.val.val.Q.shape := by
    intro hmem
    rw [τ.val.prop.2.2, YoungDiagram.mem_iff_lt_colLen] at hmem
    omega
  have hne_dot : τ.val.val.P.paint (μQ.colLen 0) 0 ≠ DRCSymbol.dot := by
    intro hd
    exact hnotQ ((τ.val.val.dot_match _ _).mp ⟨hmem_b0, hd⟩).1
  have hne_r : τ.val.val.P.paint (μQ.colLen 0) 0 ≠ DRCSymbol.r := by
    intro hr
    have := τ.val.val.row_r (μQ.colLen 0) .L .L 0 1
      (by simp [paintBySide]; exact hr)
      (by simp [paintBySide]; exact h_b1)
    exact absurd this.2 (by decide)
  -- Case on paint
  cases hp : τ.val.val.P.paint (μQ.colLen 0) 0
  · exact absurd hp hne_dot
  · rfl
  · exact absurd hp hne_r
  · rw [hp] at hmono; simp only [DRCSymbol.layerOrd] at hmono; omega
  · rw [hp] at hmono; simp only [DRCSymbol.layerOrd] at hmono; omega

/-- For σ ∈ R_sub, the fiber over σ has cardinality |TSeq(k-1)|. -/
theorem fiber_card_balanced_R {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ k)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r) :
    Fintype.card (doubleDescent_D_fiber σ) = Fintype.card (TSeq (k - 1)) := by
  rw [← R_ValidCol0_card k hk hQP hk_pos]
  have h_cond := liftCondition_RC_of_R_sub σ h_bal h_r
  -- Upper bound: fiber ↪ R_ValidCol0 via extractCol0_D
  have h_le :
      Fintype.card (doubleDescent_D_fiber σ) ≤
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} := by
    apply Fintype.card_le_of_injective
      (fun τ => ⟨PBP.extractCol0_D τ.val,
        fiber_col0_of_R_forced_s h_bal τ h_r⟩)
    intro τ₁ τ₂ h
    have h_paint : (PBP.extractCol0_D τ₁.val).paint = (PBP.extractCol0_D τ₂.val).paint :=
      congr_arg (·.val.paint) h
    exact extractCol0_D_injective_on_fiber σ h_paint
  -- Lower bound: R_ValidCol0 ↪ fiber via liftPBP_RC_D
  have h_ge :
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} ≤
      Fintype.card (doubleDescent_D_fiber σ) := by
    let f : {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) = DRCSymbol.s} →
            doubleDescent_D_fiber σ :=
      fun v =>
        have h_compat : v.val.compat_with_RC σ := by
          refine ⟨?_, ?_⟩
          · rw [v.prop, h_r]; decide
          · intro _; rw [v.prop]; decide
        ⟨liftPBP_RC_D σ v.val h_cond h_compat h_bal hQP,
         liftPBP_RC_D_round_trip σ v.val h_cond h_compat h_bal hQP⟩
    have hinj : Function.Injective f := by
      intro v₁ v₂ hv
      apply Subtype.ext
      -- Both sides are wrapped in Subtype of fiber; extract the val equality
      have h_val : (f v₁).val = (f v₂).val := by rw [hv]
      simp only [f] at h_val
      -- liftPBP_RC_D v₁ = liftPBP_RC_D v₂; conclude v₁.val = v₂.val
      have := (liftPBP_RC_D_injective h_bal hQP h_val).2
      exact this
    exact Fintype.card_le_of_injective f hinj
  omega

/-- Helper: for τ ∈ fiber σ with σ.P.paint b 0 = .c, τ.P.paint b 1 = .c. -/
lemma fiber_paint_b1_of_C {μP μQ : YoungDiagram}
    {σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    (τ : doubleDescent_D_fiber σ)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c) :
    τ.val.val.P.paint (μQ.colLen 0) 1 = DRCSymbol.c := by
  have hdd : σ.val = doubleDescent_D_PBP τ.val.val τ.val.prop.1 := by
    have := τ.prop
    unfold doubleDescent_D_map at this
    exact (congr_arg Subtype.val this).symm
  have h_eq : σ.val.P.paint (μQ.colLen 0) 0 =
      PBP.doubleDescent_D_paintL τ.val.val (μQ.colLen 0) 0 := by
    rw [hdd]; rfl
  rw [h_c] at h_eq
  simp only [PBP.doubleDescent_D_paintL] at h_eq
  by_cases hA : μQ.colLen 0 < τ.val.val.Q.shape.colLen (0 + 1)
  · rw [if_pos hA] at h_eq; exact absurd h_eq (by decide)
  · rw [if_neg hA] at h_eq
    by_cases hB : μQ.colLen 0 < PBP.dotScolLen τ.val.val.P (0 + 1)
    · rw [if_pos hB] at h_eq; exact absurd h_eq (by decide)
    · rw [if_neg hB] at h_eq
      exact h_eq.symm

/-- For σ ∈ C_sub, every τ ∈ fiber σ has τ.P.paint b 0 ≠ .d. -/
lemma fiber_col0_of_C_ne_d {μP μQ : YoungDiagram}
    {σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (τ : doubleDescent_D_fiber σ)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c) :
    τ.val.val.P.paint (μQ.colLen 0) 0 ≠ DRCSymbol.d := by
  have h_b1 := fiber_paint_b1_of_C τ h_c
  -- mono_P at (b, 0) ≤ (b, 1): layer col0(b) ≤ layer .c = 3. So col0(b) ∈ {dot, s, r, c}, not .d.
  have hbal' : μP.colLen 1 = μQ.colLen 0 + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have h01 : μP.colLen 1 ≤ μP.colLen 0 := μP.colLen_anti 0 1 (by omega)
  have hmem_b1 : (μQ.colLen 0, 1) ∈ τ.val.val.P.shape := by
    rw [τ.val.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  have hmono := τ.val.val.mono_P (μQ.colLen 0) 0 (μQ.colLen 0) 1 (le_refl _) (by omega) hmem_b1
  rw [h_b1] at hmono
  intro hd
  rw [hd] at hmono
  simp only [DRCSymbol.layerOrd] at hmono
  omega

/-- For σ ∈ C_sub, the fiber over σ has cardinality |C_ValidCol0|. -/
theorem fiber_card_balanced_C {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ k)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c) :
    Fintype.card (doubleDescent_D_fiber σ) = 4 * k - (if k = 1 then 1 else 0) := by
  rw [← C_ValidCol0_card k hk hQP hk_pos]
  have h_cond := liftCondition_RC_of_C_sub σ h_bal h_c
  -- Upper bound: fiber ↪ C_ValidCol0 via extractCol0_D
  have h_le :
      Fintype.card (doubleDescent_D_fiber σ) ≤
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) ≠ DRCSymbol.d} := by
    apply Fintype.card_le_of_injective
      (fun τ => ⟨PBP.extractCol0_D τ.val,
        fiber_col0_of_C_ne_d h_bal τ h_c⟩)
    intro τ₁ τ₂ h
    have h_paint : (PBP.extractCol0_D τ₁.val).paint = (PBP.extractCol0_D τ₂.val).paint :=
      congr_arg (·.val.paint) h
    exact extractCol0_D_injective_on_fiber σ h_paint
  -- Lower bound: C_ValidCol0 ↪ fiber via liftPBP_RC_D
  have h_ge :
      Fintype.card {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) ≠ DRCSymbol.d} ≤
      Fintype.card (doubleDescent_D_fiber σ) := by
    let f : {v : ValidCol0 μP μQ // v.paint (μQ.colLen 0) ≠ DRCSymbol.d} →
            doubleDescent_D_fiber σ :=
      fun v =>
        have h_compat : v.val.compat_with_RC σ := by
          refine ⟨?_, ?_⟩
          · -- v.paint b.layerOrd ≤ .c.layerOrd = 3
            rw [h_c]
            -- v.val.paint b ∈ {.s, .r, .c} (nondot + not .d)
            -- Need layer ≤ 3
            have h_nd : v.val.paint (μQ.colLen 0) ≠ DRCSymbol.d := v.prop
            -- Also v.val.paint b ≠ .dot since nondot_tail
            have hqp_lt : μQ.colLen 0 < μP.colLen 0 := by omega
            have h_dot : v.val.paint (μQ.colLen 0) ≠ DRCSymbol.dot :=
              v.val.nondot_tail _ (le_refl _) hqp_lt
            cases hp : v.val.paint (μQ.colLen 0)
            · exact absurd hp h_dot
            · decide
            · decide
            · decide
            · exact absurd hp h_nd
          · intro hr; rw [h_c] at hr; exact absurd hr (by decide)
        ⟨liftPBP_RC_D σ v.val h_cond h_compat h_bal hQP,
         liftPBP_RC_D_round_trip σ v.val h_cond h_compat h_bal hQP⟩
    have hinj : Function.Injective f := by
      intro v₁ v₂ hv
      apply Subtype.ext
      have h_val : (f v₁).val = (f v₂).val := by rw [hv]
      simp only [f] at h_val
      exact (liftPBP_RC_D_injective h_bal hQP h_val).2
    exact Fintype.card_le_of_injective f hinj
  omega

/-! ## Lemma 3: X_r + X_c = 2 · scTotal -/

/-- `|TSeq (k-1)| + (4k - [k=1]) = 2 · ((scDD + scRC + scSS) of tailCoeffs k)`. -/
theorem X_r_plus_X_c_eq_two_scTotal (k : ℕ) (hk_pos : 1 ≤ k) :
    Fintype.card (TSeq (k - 1)) + (4 * k - (if k = 1 then 1 else 0)) =
      2 * ((tailCoeffs k).2.1 + (tailCoeffs k).2.2.1 + (tailCoeffs k).2.2.2) := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- k = 1
    have : k = 1 := by omega
    subst this
    -- |TSeq 0| = 1
    have h0 : Fintype.card (TSeq 0) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨fun i => i.elim0, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro v; apply Subtype.ext; funext i; exact i.elim0
    rw [h0]
    simp [tailCoeffs, nu]
  · -- k ≥ 2
    have h0 : Fintype.card (TSeq (k - 1)) = 4 * (k - 1) := by
      rw [TSeq_card]; omega
    have hk1 : k ≠ 1 := by omega
    rw [h0, if_neg hk1]
    simp [tailCoeffs, nu]
    split_ifs with h
    · omega
    · omega

/-! ## Combining: fiber_card_balanced_RC_aggregate -/

/-- Helper: tailClass_D σ.val = .RC ↔ σ.val.P.paint b 0 ∈ {.r, .c}. -/
lemma tailClass_RC_iff_paint_rc {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1) :
    tailClass_D σ.val = .RC ↔
    (σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r ∨
     σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c) := by
  have hσP_colLen : σ.val.P.shape.colLen 0 = μQ.colLen 0 + 1 := by
    rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have hσQ_le : σ.val.Q.shape.colLen 0 ≤ μQ.colLen 0 := by
    rw [σ.prop.2.2, YoungDiagram.colLen_shiftLeft]
    exact μQ.colLen_anti 0 1 (by omega)
  have htailLen_pos : PBP.tailLen_D σ.val > 0 := by
    simp only [PBP.tailLen_D, hσP_colLen]; omega
  have htailSym_eq : PBP.tailSymbol_D σ.val = σ.val.P.paint (μQ.colLen 0) 0 := by
    simp only [PBP.tailSymbol_D, hσP_colLen, Nat.add_sub_cancel]
  simp only [tailClass_D]
  rw [if_neg (by omega : ¬ PBP.tailLen_D σ.val = 0)]
  rw [htailSym_eq]
  cases σ.val.P.paint (μQ.colLen 0) 0 <;> simp

/-- **Balanced RC aggregate**: `Σ_{σ ∈ RC_sub} |fiber σ| = |RC_sub| · scTotal`. -/
theorem fiber_card_balanced_RC_aggregate {μP μQ : YoungDiagram}
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hk_pos : 1 ≤ k) :
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      tailClass_D σ.val = .RC)).sum (fun σ =>
        Fintype.card (doubleDescent_D_fiber σ)) =
      let (_, (scDD, scRC, scSS)) := tailCoeffs k
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card * (scDD + scRC + scSS) := by
  show (Finset.univ.filter _).sum _ = (Finset.univ.filter _).card *
    ((tailCoeffs k).2.1 + (tailCoeffs k).2.2.1 + (tailCoeffs k).2.2.2)
  have hQP : μQ.colLen 0 ≤ μP.colLen 0 := by omega
  -- Step 1: Rewrite the tailClass_D filter as a paint filter
  have hfilter_eq : Finset.univ.filter
      (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC) =
      Finset.univ.filter (fun σ =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r ∨
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c) := by
    apply Finset.filter_congr
    intros σ _
    exact tailClass_RC_iff_paint_rc σ h_bal
  -- Step 2: Split the filter into R ⊔ C using Finset.filter_or on both sides of hfilter_eq
  have hfilter_or :
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r ∨
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r)) ∪
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)) := Finset.filter_or _ _ _
  rw [hfilter_eq, hfilter_or]
  -- Disjointness of R and C filters
  have hdisj : Disjoint
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r))
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)) := by
    rw [Finset.disjoint_filter]
    intros σ _ hr hc
    rw [hr] at hc
    exact absurd hc (by decide)
  rw [Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj]
  -- Step 3: Evaluate each sum as |R_sub| * X_r and |C_sub| * X_c
  have h_R_sum : (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                                        (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r)).sum
      (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r)).card * Fintype.card (TSeq (k - 1)) := by
    rw [Finset.sum_congr rfl (fun σ hσ => ?_)]
    · rw [Finset.sum_const]; rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact fiber_card_balanced_R σ k h_bal hk hQP hk_pos hσ
  have h_C_sum : (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                                        (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)).sum
      (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)).card *
      (4 * k - (if k = 1 then 1 else 0)) := by
    rw [Finset.sum_congr rfl (fun σ hσ => ?_)]
    · rw [Finset.sum_const]; rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact fiber_card_balanced_C σ k h_bal hk hQP hk_pos hσ
  rw [h_R_sum, h_C_sum]
  -- Step 4: Use |R_sub| = |C_sub|
  set n := (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                                  (YoungDiagram.shiftLeft μQ) =>
    σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.r)).card with hn_def
  have h_eq_n : (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                                  (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = DRCSymbol.c)).card = n :=
    (r_sub_card_eq_c_sub_card h_bal).symm
  rw [h_eq_n]
  -- Step 5: Apply Lemma 3
  have h_lemma3 := X_r_plus_X_c_eq_two_scTotal k hk_pos
  have h_factor : n * Fintype.card (TSeq (k - 1)) + n * (4 * k - (if k = 1 then 1 else 0)) =
    n * (Fintype.card (TSeq (k - 1)) + (4 * k - (if k = 1 then 1 else 0))) :=
    (Nat.mul_add n _ _).symm
  rw [h_factor, h_lemma3, ← Nat.mul_assoc, ← Nat.two_mul, Nat.mul_comm 2 n]
