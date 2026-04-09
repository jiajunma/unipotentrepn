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

/-- Count of dot+s cells in column j: cells with layerOrd ≤ 1.
    By layer monotonicity, these are contiguous from the top. -/
noncomputable def dotScolLen (D : PaintedYoungDiagram) (j : ℕ) : ℕ :=
  (D.shape.cells.filter (fun c => c.2 = j ∧ (D.paint c.1 c.2).layerOrd ≤ 1)).card

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

theorem descent_eq_implies_cols_ge1_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdesc : ∀ i j, descentPaintL_DC τ₁ i j = descentPaintL_DC τ₂ i j) :
    ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j := by
  intro i j hj
  -- descentPaintL_DC τ i (j-1) involves P.paint i j
  have key := hdesc i (j - 1)
  simp only [descentPaintL_DC] at key
  -- If i < cL₁ and i < cL₂: both are dot in the descent, but we need original P
  -- If i ≥ cL₁ and i ≥ cL₂: key gives P₁(i, j) = P₂(i, j) directly
  -- If i < cL₁ but i ≥ cL₂ (or vice versa): need to show cL₁ = cL₂
  -- cL₁ = dotScolLen τ₁.P j, cL₂ = dotScolLen τ₂.P j
  -- These are the dot+s counts in P col j, which depend on the painting.
  -- But we can show they're equal by counting leading dots in the descent.
  sorry

end PBP
