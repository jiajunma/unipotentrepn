/-
# Counting Proof: Phase 1 — |R_sub| = |C_sub| bijection via swap_b0_cell

Extracted from the monolithic `CountingProof.lean`.
-/
import CombUnipotent.CountingProof.Fiber

open Classical

/-! ### Phase 1: Bijection |R_sub| = |C_sub|

Core observation: in the balanced case, PBPs with tail-bottom .r at (b, 0)
are in bijection with PBPs having tail-bottom .c at (b, 0), via a single-cell
swap. This is the key symmetry that validates the aggregate formula.
-/

/-- Structural fact about r-bottom PBPs at the sub level: no .c anywhere in col 0.
    This follows because σ.mono_P forces any (i, 0) above (b, 0) to have layer ≤ 2,
    and any (i, 0) below is outside σ's shape. -/
theorem r_bottom_no_c_in_col0 {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r) :
    ∀ i, σ.val.P.paint i 0 ≠ .c := by
  intro i hc
  set b := μQ.colLen 0
  -- σ.P.shape.colLen 0 = b + 1 (from h_bal)
  have hσP_colLen : σ.val.P.shape.colLen 0 = b + 1 := by
    rw [σ.prop.2.1]; exact h_bal
  -- (i, 0) ∈ σ.P.shape (since σ.P.paint i 0 = .c ≠ .dot by paint_outside contrapositive)
  have himem : (i, 0) ∈ σ.val.P.shape := by
    by_contra hout
    have := σ.val.P.paint_outside i 0 hout
    rw [hc] at this; exact DRCSymbol.noConfusion this
  -- From himem and hσP_colLen: i < b + 1, i.e., i ≤ b
  have hi_le : i ≤ b := by
    have : i < b + 1 := by
      rw [← hσP_colLen]; exact YoungDiagram.mem_iff_lt_colLen.mp himem
    omega
  -- Case i = b: σ.P.paint b 0 = .r ≠ .c
  by_cases hi_eq : i = b
  · rw [hi_eq, h_r] at hc; exact DRCSymbol.noConfusion hc
  -- Case i < b: use σ.mono_P to get layer (i, 0) ≤ layer (b, 0) = 2 < 3 = layer .c
  have hi_lt : i < b := by omega
  have hmem_b : (b, 0) ∈ σ.val.P.shape :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by rw [hσP_colLen]; omega)
  have hmono := σ.val.mono_P i 0 b 0 (le_of_lt hi_lt) (le_refl _) hmem_b
  rw [hc, h_r] at hmono
  simp [DRCSymbol.layerOrd] at hmono

/-- Structural fact about r-bottom PBPs: no .r at row b other than at (b, 0).
    Follows from σ.row_r with the .r already at (b, 0). -/
theorem r_bottom_no_other_r_in_row_b {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r) :
    ∀ j, j ≠ 0 → σ.val.P.paint (μQ.colLen 0) j ≠ .r := by
  intro j hj hrj
  -- σ.row_r: at most one r per row (across both P and Q, on the SAME side)
  have := σ.val.row_r (μQ.colLen 0) .L .L 0 j
    (by simp [paintBySide]; exact h_r)
    (by simp [paintBySide]; exact hrj)
  exact hj this.2.symm

/-- Structural fact about r-bottom PBPs: σ.P.paint b j ∈ {.c, .d, .dot} for j ≥ 1.
    Combined with σ.mono_P + row_r. -/
theorem r_bottom_row_b_ge_j_in_cd {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r)
    (j : ℕ) (hj : 1 ≤ j) :
    σ.val.P.paint (μQ.colLen 0) j = .c ∨ σ.val.P.paint (μQ.colLen 0) j = .d ∨
    σ.val.P.paint (μQ.colLen 0) j = .dot := by
  set b := μQ.colLen 0
  -- Case 1: (b, j) ∉ σ.P.shape → paint = .dot
  by_cases hmem : (b, j) ∈ σ.val.P.shape
  · -- Case 2: (b, j) ∈ σ.P.shape → use mono + row_r
    -- mono_P σ at (b, 0) ≤ (b, j): layer σ.P.paint b j ≥ layer σ.P.paint b 0 = layer .r = 2
    have hb0_mem : (b, 0) ∈ σ.val.P.shape := by
      rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen] at hmem ⊢
      rw [YoungDiagram.colLen_shiftLeft] at h_bal
      have hμP_le : μP.colLen (j + 1) ≤ μP.colLen 1 :=
        μP.colLen_anti 1 (j + 1) (by omega)
      rw [YoungDiagram.colLen_shiftLeft]
      omega
    have hmono := σ.val.mono_P b 0 b j (le_refl _) (by omega) hmem
    rw [h_r, DRCSymbol.layerOrd] at hmono
    -- σ.P.paint b j.layerOrd ≥ 2 → ∈ {.r, .c, .d}
    -- row_r rules out .r (only one r in row b, at (b, 0))
    have hne_r : σ.val.P.paint b j ≠ .r :=
      r_bottom_no_other_r_in_row_b σ h_r j (by omega)
    -- Case analysis on σ.P.paint b j
    cases h : σ.val.P.paint b j with
    | dot => right; right; rfl
    | s => rw [h, DRCSymbol.layerOrd] at hmono; omega
    | r => rw [h] at hne_r; exact absurd rfl hne_r
    | c => left; rfl
    | d => right; left; rfl
  · -- Outside shape: paint = .dot
    right; right
    exact σ.val.P.paint_outside _ _ hmem

/-- Symmetric facts for c-bottom PBPs: σ.P.paint b j ∈ {.c, .d, .dot} for j ≥ 1.

    Actually, in the c-bottom case, we get a stronger conclusion: σ.P.paint b j
    has layerOrd ≥ 3, so ∈ {.c, .d, .dot(outside shape)}. And by col_c_unique,
    at most one .c in col j for j ≥ 1, but we can still have multiple .d's. -/
theorem c_bottom_row_b_ge_j_in_cd {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = .c)
    (j : ℕ) (hj : 1 ≤ j) :
    σ.val.P.paint (μQ.colLen 0) j = .c ∨ σ.val.P.paint (μQ.colLen 0) j = .d ∨
    σ.val.P.paint (μQ.colLen 0) j = .dot := by
  set b := μQ.colLen 0
  by_cases hmem : (b, j) ∈ σ.val.P.shape
  · -- mono_P σ at (b, 0) ≤ (b, j): layer σ.P.paint b j ≥ layer .c = 3
    have hmono := σ.val.mono_P b 0 b j (le_refl _) (by omega) hmem
    rw [h_c, DRCSymbol.layerOrd] at hmono
    -- σ.P.paint b j.layerOrd ≥ 3 → ∈ {.c, .d}
    cases h : σ.val.P.paint b j with
    | dot => right; right; rfl
    | s => rw [h, DRCSymbol.layerOrd] at hmono; omega
    | r => rw [h, DRCSymbol.layerOrd] at hmono; omega
    | c => left; rfl
    | d => right; left; rfl
  · right; right
    exact σ.val.P.paint_outside _ _ hmem

theorem c_bottom_unique_c_in_col0 {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = .c) :
    ∀ i, σ.val.P.paint i 0 = .c → i = μQ.colLen 0 := by
  intro i hi
  exact σ.val.col_c_P 0 i (μQ.colLen 0) hi h_c

/-- The swapped paint function: replaces (b, 0) with newS, leaves everything else.
    Uses nested if for cleaner case analysis. -/
def swappedPaint (b : ℕ) (newS : DRCSymbol) (paint : ℕ → ℕ → DRCSymbol) :
    ℕ → ℕ → DRCSymbol :=
  fun i j => if j = 0 then (if i = b then newS else paint i j) else paint i j

lemma swappedPaint_at_b0 (b : ℕ) (newS : DRCSymbol) (paint : ℕ → ℕ → DRCSymbol) :
    swappedPaint b newS paint b 0 = newS := by
  simp [swappedPaint]

lemma swappedPaint_off_col0 (b : ℕ) (newS : DRCSymbol) (paint : ℕ → ℕ → DRCSymbol)
    (i j : ℕ) (hj : j ≠ 0) :
    swappedPaint b newS paint i j = paint i j := by
  simp [swappedPaint, hj]

lemma swappedPaint_col0_ne_b (b : ℕ) (newS : DRCSymbol) (paint : ℕ → ℕ → DRCSymbol)
    (i : ℕ) (hi : i ≠ b) :
    swappedPaint b newS paint i 0 = paint i 0 := by
  simp [swappedPaint, hi]

/-- Helper: the new P with swapped cell at (b, 0), as a separate PaintedYoungDiagram. -/
noncomputable def swappedP_PYD {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (newS : DRCSymbol) : PaintedYoungDiagram where
  shape := σ.val.P.shape
  paint := swappedPaint (μQ.colLen 0) newS σ.val.P.paint
  paint_outside := by
    intro i j hmem
    -- Shape facts
    have hbal' : μP.colLen 1 = μQ.colLen 0 + 1 := by
      have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
    have hσP_colLen : σ.val.P.shape.colLen 0 = μQ.colLen 0 + 1 := by
      rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]; exact hbal'
    by_cases hj : j = 0
    · subst hj
      by_cases hi : i = μQ.colLen 0
      · -- (b, 0) ∈ σ.val.P.shape, contradiction with hmem
        exfalso; apply hmem
        rw [hi, YoungDiagram.mem_iff_lt_colLen, hσP_colLen]; omega
      · rw [swappedPaint_col0_ne_b _ _ _ _ hi]
        exact σ.val.P.paint_outside i 0 hmem
    · rw [swappedPaint_off_col0 _ _ _ _ _ hj]
      exact σ.val.P.paint_outside i j hmem

lemma swappedP_PYD_shape {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (newS : DRCSymbol) :
    (swappedP_PYD h_bal σ newS).shape = σ.val.P.shape := rfl

lemma swappedP_PYD_paint {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (newS : DRCSymbol) :
    (swappedP_PYD h_bal σ newS).paint =
      swappedPaint (μQ.colLen 0) newS σ.val.P.paint := rfl

/-- Construct a new PBP by swapping (b, 0) from oldS to newS, where {oldS, newS} = {.r, .c}. -/
noncomputable def swap_b0_cell {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (oldS newS : DRCSymbol)
    (h_symbols : (oldS = .r ∧ newS = .c) ∨ (oldS = .c ∧ newS = .r))
    (h_old : σ.val.P.paint (μQ.colLen 0) 0 = oldS) :
    PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ) := by
  set b := μQ.colLen 0 with hb_def
  -- Pre-extract facts for use in proofs
  have hnew_ne_dot : newS ≠ .dot := by
    rcases h_symbols with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hnew_ne_s : newS ≠ .s := by
    rcases h_symbols with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hnew_ne_d : newS ≠ .d := by
    rcases h_symbols with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hbal' : μP.colLen 1 = b + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have hσP_colLen : σ.val.P.shape.colLen 0 = b + 1 := by
    rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]; exact hbal'
  have hmem_b0 : (b, 0) ∈ σ.val.P.shape := by
    rw [YoungDiagram.mem_iff_lt_colLen, hσP_colLen]; omega
  have hnotmem_Q_b0 : (b, 0) ∉ σ.val.Q.shape := by
    intro hmem
    rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.colLen_shiftLeft] at hmem
    have h1 : μQ.colLen (0 + 1) ≤ μQ.colLen 0 := μQ.colLen_anti 0 (0 + 1) (by omega)
    omega
  -- The new PBP
  refine ⟨{
    γ := .D
    P := swappedP_PYD h_bal σ newS
    Q := σ.val.Q
    sym_P := fun _ _ _ => by trivial
    sym_Q := by
      intro i j hmem
      have := σ.val.sym_Q i j hmem
      rw [σ.prop.1] at this
      exact this
    dot_match := ?dot_match
    mono_P := ?mono_P
    mono_Q := σ.val.mono_Q
    row_s := ?row_s
    row_r := ?row_r
    col_c_P := ?col_c_P
    col_c_Q := σ.val.col_c_Q
    col_d_P := ?col_d_P
    col_d_Q := σ.val.col_d_Q
  }, rfl, σ.prop.2.1, σ.prop.2.2⟩
  case dot_match =>
    intro i j
    show ((i, j) ∈ σ.val.P.shape ∧ swappedPaint b newS σ.val.P.paint i j = .dot) ↔
         ((i, j) ∈ σ.val.Q.shape ∧ σ.val.Q.paint i j = .dot)
    by_cases hj : j = 0
    · subst hj
      by_cases hi : i = b
      · subst hi
        rw [swappedPaint_at_b0]
        constructor
        · intro ⟨_, hdot⟩; exact absurd hdot hnew_ne_dot
        · intro ⟨hmemQ, _⟩; exact absurd hmemQ hnotmem_Q_b0
      · rw [swappedPaint_col0_ne_b _ _ _ _ hi]
        exact σ.val.dot_match i 0
    · rw [swappedPaint_off_col0 _ _ _ _ _ hj]
      exact σ.val.dot_match i j
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem
    show (swappedPaint b newS σ.val.P.paint i₁ j₁).layerOrd ≤
         (swappedPaint b newS σ.val.P.paint i₂ j₂).layerOrd
    -- Case split on whether endpoints are (b, 0).
    by_cases hp1 : (i₁, j₁) = (b, 0)
    · by_cases hp2 : (i₂, j₂) = (b, 0)
      · -- (d) both at (b, 0): identical values
        injection hp1 with hi1 hj1
        injection hp2 with hi2 hj2
        subst hi1; subst hj1; subst hi2; subst hj2
        exact le_refl _
      · -- (b) (i₁, j₁) = (b, 0), (i₂, j₂) ≠ (b, 0)
        injection hp1 with hi1 hj1
        subst hi1; subst hj1
        rw [swappedPaint_at_b0]
        -- i₂ ≥ b (from hi), j₂ ≥ 0 (trivial)
        -- (i₂, j₂) ∈ σ.val.P.shape
        -- Sub-case i₂ > b: impossible
        -- Sub-case i₂ = b, j₂ ≥ 1
        have hi₂_le : i₂ ≤ b := by
          have h1 : i₂ < σ.val.P.shape.colLen j₂ :=
            YoungDiagram.mem_iff_lt_colLen.mp hmem
          have h2 : σ.val.P.shape.colLen j₂ ≤ σ.val.P.shape.colLen 0 :=
            YoungDiagram.colLen_anti _ 0 j₂ (Nat.zero_le _)
          rw [hσP_colLen] at h2
          omega
        have hi₂_eq : i₂ = b := le_antisymm hi₂_le hi
        subst hi₂_eq
        have hj₂_pos : j₂ ≥ 1 := by
          rcases Nat.eq_zero_or_pos j₂ with hj0 | hj0
          · exact absurd (by subst hj0; rfl : (b, j₂) = (b, 0)) hp2
          · exact hj0
        rw [swappedPaint_off_col0 _ _ _ _ _ (by omega : j₂ ≠ 0)]
        -- σ.val.P.paint b j₂ ∈ {.c, .d, .dot}; but (b, j₂) ∈ shape → not .dot
        rcases h_symbols with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- oldS = .r, newS = .c
          have := r_bottom_row_b_ge_j_in_cd σ h_bal h_old j₂ hj₂_pos
          rcases this with hc | hd | hdot
          · rw [hc]
          · rw [hd]; decide
          · -- (b, j₂) ∈ σ.P.shape but paint = .dot → (b, j₂) ∈ σ.Q.shape, but σ.Q.colLen j₂ ≤ b
            exfalso
            have ⟨hQ, _⟩ := (σ.val.dot_match b j₂).mp ⟨hmem, hdot⟩
            rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen,
                YoungDiagram.colLen_shiftLeft] at hQ
            have h1 : μQ.colLen (j₂ + 1) ≤ μQ.colLen 0 :=
              μQ.colLen_anti 0 (j₂ + 1) (Nat.zero_le _)
            omega
        · -- oldS = .c, newS = .r
          have := c_bottom_row_b_ge_j_in_cd σ h_bal h_old j₂ hj₂_pos
          rcases this with hc | hd | hdot
          · rw [hc]; decide
          · rw [hd]; decide
          · exfalso
            have ⟨hQ, _⟩ := (σ.val.dot_match b j₂).mp ⟨hmem, hdot⟩
            rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen,
                YoungDiagram.colLen_shiftLeft] at hQ
            have h1 : μQ.colLen (j₂ + 1) ≤ μQ.colLen 0 :=
              μQ.colLen_anti 0 (j₂ + 1) (Nat.zero_le _)
            omega
    · by_cases hp2 : (i₂, j₂) = (b, 0)
      · -- (c) (i₁, j₁) ≠ (b, 0), (i₂, j₂) = (b, 0)
        injection hp2 with hi2 hj2
        subst hi2; subst hj2
        -- We have j₁ ≤ 0 so j₁ = 0; i₁ ≤ b, (i₁, 0) ≠ (b, 0) → i₁ < b
        have hj₁0 : j₁ = 0 := Nat.le_zero.mp hj
        subst hj₁0
        have hi₁b : i₁ ≠ b := fun h => hp1 (by rw [h])
        rw [swappedPaint_at_b0, swappedPaint_col0_ne_b _ _ _ _ hi₁b]
        have hi₁lt : i₁ < b := lt_of_le_of_ne hi hi₁b
        -- σ.mono_P at (i₁, 0) ≤ (b, 0)
        have hmono := σ.val.mono_P i₁ 0 b 0 (le_of_lt hi₁lt) (le_refl _) hmem_b0
        rw [h_old] at hmono
        -- Case on (oldS, newS)
        rcases h_symbols with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- oldS = .r (layer 2), newS = .c (layer 3); need (i₁,0) layer ≤ 3, have ≤ 2
          simp [DRCSymbol.layerOrd] at hmono ⊢; omega
        · -- oldS = .c, newS = .r; need (i₁,0) layer ≤ 2, have ≤ 3
          -- Must exclude .c (c_bottom_unique_c_in_col0) and .d (layer 4 > 3)
          have hne_c : σ.val.P.paint i₁ 0 ≠ .c := fun hc =>
            absurd (c_bottom_unique_c_in_col0 σ h_old i₁ hc) (by omega)
          rcases hp : σ.val.P.paint i₁ 0 with _ | _ | _ | _ | _
          · simp [hp, DRCSymbol.layerOrd]
          · simp [hp, DRCSymbol.layerOrd]
          · simp [hp, DRCSymbol.layerOrd]
          · exact absurd hp hne_c
          · exfalso; rw [hp] at hmono; simp [DRCSymbol.layerOrd] at hmono
      · -- (a) neither at (b, 0): use σ.mono_P directly
        have hne₁ : ¬(i₁ = b ∧ j₁ = 0) := fun h => hp1 (by rw [h.1, h.2])
        have hne₂ : ¬(i₂ = b ∧ j₂ = 0) := fun h => hp2 (by rw [h.1, h.2])
        -- Rewrite both to σ values
        have eq₁ : swappedPaint b newS σ.val.P.paint i₁ j₁ = σ.val.P.paint i₁ j₁ := by
          by_cases hj1 : j₁ = 0
          · subst hj1
            have : i₁ ≠ b := fun h => hne₁ ⟨h, rfl⟩
            exact swappedPaint_col0_ne_b _ _ _ _ this
          · exact swappedPaint_off_col0 _ _ _ _ _ hj1
        have eq₂ : swappedPaint b newS σ.val.P.paint i₂ j₂ = σ.val.P.paint i₂ j₂ := by
          by_cases hj2 : j₂ = 0
          · subst hj2
            have : i₂ ≠ b := fun h => hne₂ ⟨h, rfl⟩
            exact swappedPaint_col0_ne_b _ _ _ _ this
          · exact swappedPaint_off_col0 _ _ _ _ _ hj2
        rw [eq₁, eq₂]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi hj hmem
  case row_s =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- newS ≠ .s, so at (b, 0) the swapped paint is not .s, so any .s in σ' is at σ.
    -- Helper: translate any .s in swappedPaint to σ.
    have h_trans : ∀ j,
        swappedPaint b newS σ.val.P.paint i j = .s → σ.val.P.paint i j = .s := by
      intro j hs
      by_cases hj : j = 0
      · subst hj
        by_cases hi : i = b
        · subst hi; rw [swappedPaint_at_b0] at hs; exact absurd hs hnew_ne_s
        · rwa [swappedPaint_col0_ne_b _ _ _ _ hi] at hs
      · rwa [swappedPaint_off_col0 _ _ _ _ _ hj] at hs
    cases s₁ <;> cases s₂ <;> simp only [paintBySide] at h₁ h₂
    · exact σ.val.row_s i .L .L j₁ j₂
        (show paintBySide σ.val.P σ.val.Q .L i j₁ = .s by
          simp [paintBySide]; exact h_trans j₁ h₁)
        (show paintBySide σ.val.P σ.val.Q .L i j₂ = .s by
          simp [paintBySide]; exact h_trans j₁ h₁ ▸ h_trans j₂ h₂)
    · -- L, R: h₂ is σ.val.Q.paint i j₂ = .s; use σ.row_s L R
      exact σ.val.row_s i .L .R j₁ j₂
        (show paintBySide σ.val.P σ.val.Q .L i j₁ = .s by
          simp [paintBySide]; exact h_trans j₁ h₁)
        (show paintBySide σ.val.P σ.val.Q .R i j₂ = .s by
          simp [paintBySide]; exact h₂)
    · exact σ.val.row_s i .R .L j₁ j₂
        (show paintBySide σ.val.P σ.val.Q .R i j₁ = .s by
          simp [paintBySide]; exact h₁)
        (show paintBySide σ.val.P σ.val.Q .L i j₂ = .s by
          simp [paintBySide]; exact h_trans j₂ h₂)
    · exact σ.val.row_s i .R .R j₁ j₂
        (show paintBySide σ.val.P σ.val.Q .R i j₁ = .s by
          simp [paintBySide]; exact h₁)
        (show paintBySide σ.val.P σ.val.Q .R i j₂ = .s by
          simp [paintBySide]; exact h₂)
  case row_r =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- Q is all dots for D type, so .r can only come from P side.
    have hQ_dot : ∀ k, σ.val.Q.paint i k ≠ .r := by
      intro k hr
      by_cases hmem : (i, k) ∈ σ.val.Q.shape
      · rw [PBP.Q_all_dot_of_D σ.val σ.prop.1 i k hmem] at hr
        exact DRCSymbol.noConfusion hr
      · rw [σ.val.Q.paint_outside i k hmem] at hr
        exact DRCSymbol.noConfusion hr
    -- Reduce R-side cases to contradictions
    cases s₁ <;> cases s₂ <;> simp only [paintBySide] at h₁ h₂
    · -- L-L: both in σ'.P. Analyze per (oldS, newS) case.
      rcases h_symbols with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- oldS = .r, newS = .c. newS ≠ .r, so both h₁, h₂ give σ.P.paint i j_k = .r.
        have h_trans : ∀ j,
            swappedPaint b .c σ.val.P.paint i j = .r → σ.val.P.paint i j = .r := by
          intro j hr
          by_cases hj : j = 0
          · subst hj
            by_cases hi : i = b
            · subst hi; rw [swappedPaint_at_b0] at hr; exact absurd hr (by decide)
            · rwa [swappedPaint_col0_ne_b _ _ _ _ hi] at hr
          · rwa [swappedPaint_off_col0 _ _ _ _ _ hj] at hr
        exact σ.val.row_r i .L .L j₁ j₂
          (show paintBySide σ.val.P σ.val.Q .L i j₁ = .r by
            simp [paintBySide]; exact h_trans j₁ h₁)
          (show paintBySide σ.val.P σ.val.Q .L i j₂ = .r by
            simp [paintBySide]; exact h_trans j₂ h₂)
      · -- oldS = .c, newS = .r. A new .r appears at (b, 0); σ had none in row b.
        -- Split on i = b.
        by_cases hi_b : i = b
        · subst hi_b
          -- σ.P.paint b 0 = .c; row b j ∈ {c, d, dot} for j ≥ 1.
          -- So σ.P has no .r in row b.
          -- Any h_k : swappedPaint ... b j_k = .r forces j_k = 0.
          have hj_force : ∀ j, swappedPaint b .r σ.val.P.paint b j = .r → j = 0 := by
            intro j hr
            by_cases hj : j = 0
            · exact hj
            · rw [swappedPaint_off_col0 _ _ _ _ _ hj] at hr
              rcases c_bottom_row_b_ge_j_in_cd σ h_bal h_old j (by omega) with hc|hd|hdot
              · rw [hc] at hr; exact absurd hr (by decide)
              · rw [hd] at hr; exact absurd hr (by decide)
              · rw [hdot] at hr; exact absurd hr (by decide)
          exact ⟨rfl, (hj_force j₁ h₁).trans (hj_force j₂ h₂).symm⟩
        · -- i ≠ b: swap doesn't affect row i
          have h_trans : ∀ j,
              swappedPaint b .r σ.val.P.paint i j = .r → σ.val.P.paint i j = .r := by
            intro j hr
            by_cases hj : j = 0
            · subst hj
              rwa [swappedPaint_col0_ne_b _ _ _ _ hi_b] at hr
            · rwa [swappedPaint_off_col0 _ _ _ _ _ hj] at hr
          exact σ.val.row_r i .L .L j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .L i j₁ = .r by
              simp [paintBySide]; exact h_trans j₁ h₁)
            (show paintBySide σ.val.P σ.val.Q .L i j₂ = .r by
              simp [paintBySide]; exact h_trans j₂ h₂)
    · exact absurd h₂ (hQ_dot j₂)
    · exact absurd h₁ (hQ_dot j₁)
    · exact absurd h₁ (hQ_dot j₁)
  case col_c_P =>
    intro j i₁ i₂
    show swappedPaint b newS σ.val.P.paint i₁ j = .c →
         swappedPaint b newS σ.val.P.paint i₂ j = .c → i₁ = i₂
    intro h₁ h₂
    rcases h_symbols with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- oldS = .r, newS = .c. .c added at (b, 0); σ had no .c in col 0.
      by_cases hj : j = 0
      · subst hj
        -- If i_k ≠ b, swappedPaint = σ.paint i_k 0, which is not .c (by r_bottom_no_c_in_col0)
        have hib : ∀ i, swappedPaint b .c σ.val.P.paint i 0 = .c → i = b := by
          intro i hc
          by_contra hne
          rw [swappedPaint_col0_ne_b _ _ _ _ hne] at hc
          exact r_bottom_no_c_in_col0 σ h_bal h_old i hc
        rw [hib i₁ h₁, hib i₂ h₂]
      · rw [swappedPaint_off_col0 _ _ _ _ _ hj] at h₁ h₂
        exact σ.val.col_c_P j i₁ i₂ h₁ h₂
    · -- oldS = .c, newS = .r. .c removed at (b, 0); any .c in σ' is at σ (not (b,0)).
      have h_trans : ∀ i j',
          swappedPaint b .r σ.val.P.paint i j' = .c → σ.val.P.paint i j' = .c := by
        intro i j' hc
        by_cases hj' : j' = 0
        · subst hj'
          by_cases hib : i = b
          · subst hib; rw [swappedPaint_at_b0] at hc; exact absurd hc (by decide)
          · rwa [swappedPaint_col0_ne_b _ _ _ _ hib] at hc
        · rwa [swappedPaint_off_col0 _ _ _ _ _ hj'] at hc
      exact σ.val.col_c_P j i₁ i₂ (h_trans i₁ j h₁) (h_trans i₂ j h₂)
  case col_d_P =>
    intro j i₁ i₂
    show swappedPaint b newS σ.val.P.paint i₁ j = .d →
         swappedPaint b newS σ.val.P.paint i₂ j = .d → i₁ = i₂
    intro h₁ h₂
    -- newS ≠ .d, so any .d in σ' came from σ.
    have h_trans : ∀ i j',
        swappedPaint b newS σ.val.P.paint i j' = .d → σ.val.P.paint i j' = .d := by
      intro i j' hd
      by_cases hj' : j' = 0
      · subst hj'
        by_cases hib : i = b
        · subst hib; rw [swappedPaint_at_b0] at hd; exact absurd hd hnew_ne_d
        · rwa [swappedPaint_col0_ne_b _ _ _ _ hib] at hd
      · rwa [swappedPaint_off_col0 _ _ _ _ _ hj'] at hd
    exact σ.val.col_d_P j i₁ i₂ (h_trans i₁ j h₁) (h_trans i₂ j h₂)

/-- The swap preserves the (b, 0) cell becoming newS. -/
theorem swap_b0_cell_paint {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (oldS newS : DRCSymbol)
    (h_symbols : (oldS = .r ∧ newS = .c) ∨ (oldS = .c ∧ newS = .r))
    (h_old : σ.val.P.paint (μQ.colLen 0) 0 = oldS) :
    (swap_b0_cell h_bal σ oldS newS h_symbols h_old).val.P.paint (μQ.colLen 0) 0 = newS := by
  show (swappedP_PYD h_bal σ newS).paint (μQ.colLen 0) 0 = newS
  exact swappedPaint_at_b0 _ _ _

/-- The swap is an involution: swapping twice returns the original.
    General form — works for both (r,c) and (c,r) initial directions. -/
theorem swap_b0_cell_involutive {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (oldS newS : DRCSymbol)
    (h_symbols : (oldS = .r ∧ newS = .c) ∨ (oldS = .c ∧ newS = .r))
    (h_old : σ.val.P.paint (μQ.colLen 0) 0 = oldS) :
    swap_b0_cell h_bal
      (swap_b0_cell h_bal σ oldS newS h_symbols h_old)
      newS oldS (by
        rcases h_symbols with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩)
      (swap_b0_cell_paint h_bal σ oldS newS h_symbols h_old) = σ := by
  set b := μQ.colLen 0 with hb_def
  apply Subtype.ext
  apply PBP.ext''
  · exact σ.prop.1.symm
  · apply PaintedYoungDiagram.ext'
    · rfl
    · funext i j
      show swappedPaint b oldS (swappedPaint b newS σ.val.P.paint) i j = σ.val.P.paint i j
      by_cases hj : j = 0
      · subst hj
        by_cases hi : i = b
        · subst hi
          rw [swappedPaint_at_b0]
          exact h_old.symm
        · rw [swappedPaint_col0_ne_b _ _ _ _ hi,
              swappedPaint_col0_ne_b _ _ _ _ hi]
      · rw [swappedPaint_off_col0 _ _ _ _ _ hj,
            swappedPaint_off_col0 _ _ _ _ _ hj]
  · rfl

/-- |R_sub| = |C_sub| via the bijection Ψ = swap_b0_cell (r → c). -/
theorem r_sub_card_eq_c_sub_card {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1) :
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = .r)).card =
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = .c)).card := by
  set b := μQ.colLen 0 with hb_def
  refine Finset.card_bij'
    (fun σ hσ => swap_b0_cell h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hσ).2))
    (fun τ hτ => swap_b0_cell h_bal τ .c .r (Or.inr ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hτ).2))
    ?hi ?hj ?left_inv ?right_inv
  case hi =>
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact swap_b0_cell_paint h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hσ).2)
  case hj =>
    intro τ hτ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact swap_b0_cell_paint h_bal τ .c .r (Or.inr ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hτ).2)
  case left_inv =>
    intro σ hσ
    exact swap_b0_cell_involutive h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hσ).2)
  case right_inv =>
    intro τ hτ
    exact swap_b0_cell_involutive h_bal τ .c .r (Or.inr ⟨rfl, rfl⟩)
      ((Finset.mem_filter.mp hτ).2)

