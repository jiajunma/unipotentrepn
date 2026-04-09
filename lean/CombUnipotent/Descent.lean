/-
# Descent of Painted Bipartitions

Reference: [BMSZ] Section 3.3, Lemma 3.7, Definition 3.14.

The naive descent ∇ maps a PBP τ of type γ to a PBP τ' of type γ':
- D → C: remove P's column 0, redistribute dot/s via _fill_ds_C
- C → D: remove Q's column 0, redistribute dot/s via _fill_ds_D
- B⁺/B⁻ → M: remove Q's column 0, redistribute dot/s via _fill_ds_M
- M → B⁺/B⁻: remove P's column 0, redistribute dot/s via _fill_ds_B

In each case, the r/c/d symbols are preserved (shifted by one column
on the removed side). The dot and s symbols are redistributed so that
the new PBP has the correct symbol constraints for the target type.
-/
import CombUnipotent.PBP

namespace PBP

/-! ## Shape lemmas for descent -/

theorem Q_s_rightmost_of_C (τ : PBP) (hγ : τ.γ = .C)
    {i k : ℕ} (hs : τ.Q.paint i k = .s) : (i, k + 1) ∉ τ.Q.shape := by
  intro hmem
  have hmono := τ.mono_Q i k i (k + 1) le_rfl (Nat.le_succ k) hmem
  rw [hs, DRCSymbol.layerOrd] at hmono
  have hk1 := τ.Q_nonDot_eq_s_of_C hγ i (k + 1) hmem (by
    intro heq; rw [heq, DRCSymbol.layerOrd] at hmono; omega)
  have := τ.row_s i .R .R k (k + 1)
    (by simp [paintBySide]; exact hs) (by simp [paintBySide]; exact hk1)
  omega

theorem Q_dot_left_of_C (τ : PBP) (hγ : τ.γ = .C)
    {i k : ℕ} (hmem : (i, k + 1) ∈ τ.Q.shape) : τ.Q.paint i k = .dot := by
  have hmem_k := τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ k⟩) hmem
  by_contra hne
  exact τ.Q_s_rightmost_of_C hγ (τ.Q_nonDot_eq_s_of_C hγ i k hmem_k hne) hmem

theorem dotDiag_colLen_ge_Q_colLen_succ_of_C (τ : PBP) (hγ : τ.γ = .C) (k : ℕ) :
    (dotDiag τ.Q τ.mono_Q).colLen k ≥ τ.Q.shape.colLen (k + 1) := by
  by_contra h; push_neg at h
  set d := (dotDiag τ.Q τ.mono_Q).colLen k
  have hd_mem : (d, k + 1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr h
  have hdk_mem := τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ k⟩) hd_mem
  have hdk_dot := τ.Q_dot_left_of_C hγ hd_mem
  have : (d, k) ∈ (dotDiag τ.Q τ.mono_Q) := by
    simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hdk_mem, hdk_dot⟩
  exact absurd this (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

theorem dotDiag_le (D : PaintedYoungDiagram) (hm : D.layerMonotone) :
    dotDiag D hm ≤ D.shape := by
  intro ⟨i, j⟩ hmem
  simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem.1

/-! ## Dot+s layer count

For a PaintedYoungDiagram with layer monotonicity, the cells with
layerOrd ≤ 1 (dot or s) form a contiguous prefix in each column.
The count of these cells is the boundary between the dot/s block
and the r/c/d block. -/

/-- The dot+s sub-diagram: cells with layerOrd ≤ 1. Forms a YoungDiagram
    by the same argument as dotDiag (monotonicity). -/
def dotSdiag (D : PaintedYoungDiagram) (hm : D.layerMonotone) : YoungDiagram where
  cells := D.shape.cells.filter fun c => (D.paint c.1 c.2).layerOrd ≤ 1
  isLowerSet := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hle hmem
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hmem ⊢
    refine ⟨D.shape.isLowerSet hle hmem.1, ?_⟩
    have hle' := Prod.mk_le_mk.mp hle
    exact le_trans (hm i₂ j₂ i₁ j₁ hle'.1 hle'.2 hmem.1) hmem.2

/-- i < dotSdiag.colLen(j) → paint(i, j).layerOrd ≤ 1. -/
theorem layerOrd_le_one_of_lt_dotSdiag_colLen (D : PaintedYoungDiagram)
    (hm : D.layerMonotone) {i j : ℕ} (h : i < (dotSdiag D hm).colLen j) :
    (D.paint i j).layerOrd ≤ 1 := by
  have hmem : (i, j) ∈ dotSdiag D hm := YoungDiagram.mem_iff_lt_colLen.mpr h
  simp only [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem.2

/-- Count of dot+s cells in column j.
    Equals dotSdiag.colLen j, but defined independently via Finset.card. -/
noncomputable def dotScolLen (D : PaintedYoungDiagram) (j : ℕ) : ℕ :=
  (D.shape.cells.filter (fun c => c.2 = j ∧ (D.paint c.1 c.2).layerOrd ≤ 1)).card

/-- dotScolLen = dotSdiag.colLen (bridge between the two definitions). -/
theorem dotScolLen_eq_dotSdiag_colLen (D : PaintedYoungDiagram) (hm : D.layerMonotone) (j : ℕ) :
    dotScolLen D j = (dotSdiag D hm).colLen j := by
  -- dotScolLen = card of {c ∈ cells | c.2 = j ∧ layerOrd ≤ 1}
  -- dotSdiag.colLen j = card of dotSdiag.col j = card of {c ∈ dotSdiag | c.2 = j}
  -- dotSdiag.cells = {c ∈ D.cells | layerOrd ≤ 1}
  -- So dotSdiag.col j = {c ∈ D.cells | layerOrd ≤ 1 ∧ c.2 = j}
  -- = {c ∈ D.cells | c.2 = j ∧ layerOrd ≤ 1} (same set, different order)
  simp only [dotScolLen, YoungDiagram.colLen_eq_card, YoungDiagram.col,
    dotSdiag, YoungDiagram.mem_mk]
  congr 1
  ext ⟨i, k⟩
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  tauto

/-! ## Naive descent paint functions

For each of the four descent directions, we define the paint functions
of the descended PBP. The key invariant: r/c/d symbols are preserved
(possibly shifted by one column), while dot/s are redistributed.

Convention: cL and cR denote the dot+s counts used in redistribution.
-/

/-- **D → C** left paint: P shifts left, top filled with dots.
    cL(j) = dotScolLen(P, j+1), P'(i,j) = dot if i < cL else P(i, j+1). -/
noncomputable def descentPaintL_DC (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j => if i < dotScolLen τ.P (j + 1) then .dot else τ.P.paint i (j + 1)

/-- **D → C** right paint: Q keeps shape, top with dots, middle with s.
    cL(j) = dotScolLen(P, j+1), cR(j) = Q.colLen(j).
    Q'(i,j) = dot if i < cL, s if cL ≤ i < cR, dot if i ≥ cR. -/
noncomputable def descentPaintR_DC (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.P (j + 1) then .dot
    else if i < τ.Q.shape.colLen j then .s
    else .dot

/-- **C → D** left paint: P keeps shape, top refilled.
    cL(j) = dotScolLen(P, j), cR(j) = Q.colLen(j+1).
    P'(i,j) = dot if i < cR, s if cR ≤ i < cL, P(i,j) if i ≥ cL. -/
noncomputable def descentPaintL_CD (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < τ.Q.shape.colLen (j + 1) then .dot
    else if i < dotScolLen τ.P j then .s
    else τ.P.paint i j

/-- **C → D** right paint: Q shifts left, all dots.
    cR(j) = Q.colLen(j+1). Q'(i,j) = dot if i < cR, dot otherwise. -/
noncomputable def descentPaintR_CD (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j => .dot  -- D-type right is always dot

/-- **B → M** left paint: P keeps shape, top refilled.
    cL(j) = dotScolLen(P, j), cR(j) = dotScolLen(Q, j+1).
    P'(i,j) = dot if i < cR, s if cR ≤ i < cL, P(i,j) if i ≥ cL. -/
noncomputable def descentPaintL_BM (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.Q (j + 1) then .dot
    else if i < dotScolLen τ.P j then .s
    else τ.P.paint i j

/-- **B → M** right paint: Q shifts left, top with dots, rest preserved.
    cR(j) = dotScolLen(Q, j+1).
    Q'(i,j) = dot if i < cR, Q(i, j+1) if i ≥ cR. -/
noncomputable def descentPaintR_BM (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.Q (j + 1) then .dot
    else τ.Q.paint i (j + 1)

/-- **M → B** left paint: P shifts left, top with dots, rest preserved.
    cL(j) = dotScolLen(P, j+1).
    P'(i,j) = dot if i < cL, P(i, j+1) if i ≥ cL. -/
noncomputable def descentPaintL_MB (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.P (j + 1) then .dot
    else τ.P.paint i (j + 1)

/-- **M → B** right paint: Q keeps shape, top refilled.
    cL(j) = dotScolLen(P, j+1), cR(j) = dotScolLen(Q, j).
    Q'(i,j) = dot if i < cL, s if cL ≤ i < cR, Q(i,j) if i ≥ cR. -/
noncomputable def descentPaintR_MB (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.P (j + 1) then .dot
    else if i < dotScolLen τ.Q j then .s
    else τ.Q.paint i j

/-! ## Descent type -/

/-- Target type under descent. For M → B, defaults to B⁺;
    corrected to B⁻ when c appears in P's first column. -/
def descentType (γ : RootType) : RootType :=
  match γ with
  | .C => .D | .D => .C | .Bplus | .Bminus => .M | .M => .Bplus

/-- For M type: the actual B⁺/B⁻ determined by P's first column. -/
def descentType_M (τ : PBP) (hγ : τ.γ = .M) : RootType :=
  if (τ.P.shape.cells.filter (fun c => c.2 = 0 ∧ τ.P.paint c.1 c.2 = .c)).Nonempty
  then .Bminus else .Bplus

/-! ## Recovery lemma for D type

Same descent paint → same P painting on columns ≥ 1. -/

-- dotScolLen_eq_of_descent_eq: not needed (recovery uses case analysis instead)

/-- Recovery: same descent paint + same shapes → same P on cols ≥ 1.

    Proof: for each cell (i, j) with j ≥ 1, the descent paint at (i, j-1)
    gives `if i < cL then dot else P(i, j)`. We case split:

    - If (i, j) ∈ Q.shape: for D type, dot_match gives P.paint = dot.
      Same Q.shape → both paint dot.

    - If (i, j) ∉ Q.shape and (i, j) ∉ P.shape: both paint dot (outside).

    - If (i, j) ∉ Q.shape and (i, j) ∈ P.shape: P.paint ≠ dot
      (otherwise dot_match would give (i,j) ∈ Q.shape).
      Non-dot means layerOrd ≥ 1. The descent at (i, j-1):
      If i < cL: impossible (cL counts cells with layerOrd ≤ 1 in shape,
        and (i,j) ∈ shape with layerOrd ≥ 1 means i could be in the s region
        or the r/c/d region).
      Actually, we need a subtler argument here.

    Simpler approach: use hdesc directly without dotScolLen. -/
theorem descent_eq_implies_cols_ge1_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdesc : ∀ i j, descentPaintL_DC τ₁ i j = descentPaintL_DC τ₂ i j) :
    ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j := by
  intro i j hj
  -- Three cases based on Q.shape and P.shape membership
  by_cases hq : (i, j) ∈ τ₁.Q.shape
  · -- Case 1: (i,j) ∈ Q.shape → both paint dot (D type: dot_match)
    rw [((τ₁.dot_match i j).mpr ⟨hq, Q_all_dot_of_D τ₁ hγ₁ i j hq⟩).2,
        ((τ₂.dot_match i j).mpr ⟨hshapeQ ▸ hq, Q_all_dot_of_D τ₂ hγ₂ i j (hshapeQ ▸ hq)⟩).2]
  · by_cases hp : (i, j) ∈ τ₁.P.shape
    · -- Case 2: (i,j) ∉ Q.shape, (i,j) ∈ P.shape
      -- P.paint(i,j) ≠ dot (otherwise dot_match gives ∈ Q.shape)
      have hne₁ : τ₁.P.paint i j ≠ .dot := fun h =>
        hq ((τ₁.dot_match i j).mp ⟨hp, h⟩).1
      have hne₂ : τ₂.P.paint i j ≠ .dot := fun h =>
        (hshapeQ ▸ hq : (i, j) ∉ τ₂.Q.shape)
          ((τ₂.dot_match i j).mp ⟨hshapeP ▸ hp, h⟩).1
      -- P.paint has layerOrd ≥ 1 (non-dot). The non-dot symbols are {s,r,c,d}.
      -- In the descent: descentPaintL_DC τ i (j-1) =
      --   if i < dotScolLen(P, j) then dot else P.paint(i, j)
      -- Since P.paint(i,j) ≠ dot, and if the 'then' branch fires for one
      -- but not the other, the descent paints would differ (dot vs non-dot).
      -- So either both fire 'then' (both ≠ dot but descent = dot, then we need
      -- more work), or both fire 'else' (direct).
      have key := hdesc i (j - 1)
      simp only [descentPaintL_DC, Nat.sub_add_cancel hj] at key
      -- key : (if i < cL₁ then dot else P₁(i,j)) = (if i < cL₂ then dot else P₂(i,j))
      by_cases h1 : i < dotScolLen τ₁.P j
      · -- Both in then-branch (if one is in then, other must be too):
        -- If τ₂ is in else-branch: key gives dot = P₂(i,j), so P₂ = dot.
        -- But we showed P₂ ≠ dot. Contradiction. So τ₂ must also be in then.
        by_cases h2 : i < dotScolLen τ₂.P j
        · -- Both in then-branch. Both paint ≠ dot. Show both = s.
          -- layerOrd ≤ 1 (dot or s) + ≠ dot → = s.
          -- Need: i < dotScolLen → layerOrd ≤ 1.
          -- This follows from dotScolLen definition + layer monotonicity:
          -- dotScolLen counts cells with layerOrd ≤ 1 in column j.
          -- By monotonicity these are contiguous from the top.
          -- So if i < count, then (i,j) has layerOrd ≤ 1.
          -- Both have layerOrd ≤ 1 and ≠ dot → both = s.
          have paint_s : ∀ (τ : PBP), τ.P.paint i j ≠ .dot →
              i < dotScolLen τ.P j → τ.P.paint i j = .s := by
            intro τ hne hlt
            -- Step 1: i < dotScolLen → layerOrd ≤ 1
            rw [dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hlt
            have hlo := layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P hlt
            -- Step 2: layerOrd ≤ 1 ∧ ≠ dot → = s
            revert hlo hne
            cases τ.P.paint i j <;> simp [DRCSymbol.layerOrd]
          rw [paint_s τ₁ hne₁ h1, paint_s τ₂ hne₂ h2]
        · -- τ₁ in then, τ₂ in else: key gives dot = P₂(i,j). But P₂ ≠ dot.
          rw [if_pos h1, if_neg h2] at key
          exact absurd key.symm hne₂
      · -- τ₁ in else-branch
        by_cases h2 : i < dotScolLen τ₂.P j
        · -- τ₁ else, τ₂ then: key gives P₁(i,j) = dot. But P₁ ≠ dot.
          rw [if_neg h1, if_pos h2] at key
          exact absurd key hne₁
        · -- Both in else: key gives P₁(i,j) = P₂(i,j) directly.
          rw [if_neg h1, if_neg h2] at key
          exact key
    · -- Case 3: (i,j) ∉ P.shape → both outside shape → both paint dot
      rw [τ₁.P.paint_outside i j hp,
          τ₂.P.paint_outside i j (hshapeP ▸ hp)]

end PBP
