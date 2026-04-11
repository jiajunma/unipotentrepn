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

@[simp] lemma swappedPaint_at_b0 (b : ℕ) (newS : DRCSymbol) (paint : ℕ → ℕ → DRCSymbol) :
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

@[simp] lemma swappedP_PYD_shape {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (newS : DRCSymbol) :
    (swappedP_PYD h_bal σ newS).shape = σ.val.P.shape := rfl

@[simp] lemma swappedP_PYD_paint {μP μQ : YoungDiagram}
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
    sorry  -- Full mono_P case analysis: see docs/swap_b0_cell_detailed.md
  case row_s =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    sorry
  case row_r =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    sorry
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    sorry
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    sorry

/-- The swap preserves the (b, 0) cell becoming newS. -/
theorem swap_b0_cell_paint {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (oldS newS : DRCSymbol)
    (h_symbols : (oldS = .r ∧ newS = .c) ∨ (oldS = .c ∧ newS = .r))
    (h_old : σ.val.P.paint (μQ.colLen 0) 0 = oldS) :
    (swap_b0_cell h_bal σ oldS newS h_symbols h_old).val.P.paint (μQ.colLen 0) 0 = newS := by
  sorry  -- Phase 1, step 7

/-- The swap is an involution: swapping twice returns the original. -/
theorem swap_b0_cell_involutive {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r) :
    swap_b0_cell h_bal
      (swap_b0_cell h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩) h_r)
      .c .r (Or.inr ⟨rfl, rfl⟩)
      (swap_b0_cell_paint h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩) h_r) = σ := by
  sorry  -- Phase 1, step 8

/-- |R_sub| = |C_sub| via the bijection Ψ = swap_b0_cell (r → c). -/
theorem r_sub_card_eq_c_sub_card {μP μQ : YoungDiagram}
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1) :
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = .r)).card =
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      σ.val.P.paint (μQ.colLen 0) 0 = .c)).card := by
  sorry  -- Phase 1, step 9: assemble via swap_b0_cell + Finset.card_bij

