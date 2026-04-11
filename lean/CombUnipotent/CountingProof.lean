/-
# Counting Proof: countPBP = #PBP

Goal: Fintype.card (PBPSet γ μP μQ) = countPBP dp γ

This file provides the foundational definitions linking
DualPart (orbit partition) to PBP shapes, enabling the
inductive counting proof.

Reference: [BMSZb] Propositions 10.11–10.12.
-/
import CombUnipotent.Counting
import CombUnipotent.Finiteness
import CombUnipotent.Tail
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

open Classical

namespace YoungDiagram

/-! ## Column lengths of a Young diagram

`colLens μ` extracts column lengths as a list.
It equals `μ.transpose.rowLens` by duality. -/

/-- Column lengths of a Young diagram, as a list.
    `colLens μ = [μ.colLen 0, μ.colLen 1, ..., μ.colLen (μ.rowLen 0 - 1)]`.
    This is the "conjugate partition" or "dual partition" of the shape. -/
def colLens (μ : YoungDiagram) : DualPart :=
  μ.transpose.rowLens

/-- `colLens` equals the transpose's `rowLens`. -/
theorem colLens_eq_transpose_rowLens (μ : YoungDiagram) :
    μ.colLens = μ.transpose.rowLens := rfl

/-- Length of `colLens` equals `rowLen 0` (the number of columns). -/
@[simp]
theorem length_colLens (μ : YoungDiagram) : μ.colLens.length = μ.rowLen 0 := by
  simp [colLens, rowLens]

/-- The j-th entry of `colLens` equals `colLen j`. -/
@[simp]
theorem getElem_colLens {μ : YoungDiagram} {j : ℕ} (h : j < μ.colLens.length) :
    μ.colLens[j] = μ.colLen j := by
  simp only [colLens, rowLens, List.getElem_map, List.getElem_range]
  exact μ.rowLen_transpose j

/-- Column lengths are non-increasing. -/
theorem colLens_sorted (μ : YoungDiagram) : μ.colLens.SortedGE :=
  μ.transpose.rowLens_sorted

/-- Every entry in `colLens` is positive. -/
theorem pos_of_mem_colLens (μ : YoungDiagram) (x : ℕ) (hx : x ∈ μ.colLens) : 0 < x :=
  μ.transpose.pos_of_mem_rowLens x hx

/-! ## Constructing a Young diagram from column lengths -/

/-- Construct a Young diagram from a non-increasing list of positive column lengths. -/
def ofColLens (w : List ℕ) (hw : w.SortedGE) : YoungDiagram :=
  (ofRowLens w hw).transpose

/-- Round-trip: `ofColLens (colLens μ) = μ`. -/
theorem ofColLens_colLens (μ : YoungDiagram) :
    ofColLens μ.colLens (colLens_sorted μ) = μ := by
  simp [ofColLens, colLens, ofRowLens_to_rowLens_eq_self]

/-- Round-trip: `colLens (ofColLens w) = w` for valid w. -/
theorem colLens_ofColLens {w : List ℕ} {hw : w.SortedGE} (hpos : ∀ x ∈ w, 0 < x) :
    (ofColLens w hw).colLens = w := by
  simp [ofColLens, colLens, YoungDiagram.transpose_transpose,
    rowLens_ofRowLens_eq_self hpos]

/-- `colLen j` of `ofColLens w` equals `w[j]`. -/
theorem colLen_ofColLens {w : List ℕ} {hw : w.SortedGE} (j : Fin w.length) :
    (ofColLens w hw).colLen j = w[j] := by
  have : (ofColLens w hw).colLen j.val = (ofRowLens w hw).rowLen j.val := by
    simp [ofColLens]
  rw [this]
  exact rowLen_ofRowLens ⟨j.val, j.isLt⟩

end YoungDiagram

/-! ## Orbit partition to PBP shapes

For each root type, the orbit partition dp determines the shapes (μP, μQ)
of the PBP via the bipartition construction [BMSZb] §2.8.

For D type: dp = [r₁, r₂, ..., r_m] (all odd, total even).
  P.colLens[k] = (r_{2k+1} + 1) / 2
  Q.colLens[k] = (r_{2k+2} - 1) / 2

  Key recursion property:
    dpartColLensP_D (r₁ :: r₂ :: rest) = (r₁+1)/2 :: dpartColLensP_D rest
    dpartColLensQ_D (r₁ :: r₂ :: rest) = (r₂-1)/2 :: dpartColLensQ_D rest
    (when parts > 0)

  This means: dropping 2 orbit rows (countPBP_D recursion) corresponds to
  removing 1 column from both P and Q (double descent D→C→D).
-/

/-- Extract P column lengths from orbit partition for D type.
    Takes every other element starting from index 0: r₁, r₃, r₅, ...
    and applies (r + 1) / 2.

    Recursive structure mirrors `countPBP_D`: processing pairs. -/
def dpartColLensP_D : DualPart → DualPart
  | [] => []
  | [r₁] => [(r₁ + 1) / 2]
  | r₁ :: _ :: rest => (r₁ + 1) / 2 :: dpartColLensP_D rest

/-- Extract Q column lengths from orbit partition for D type.
    Takes every other element starting from index 1: r₂, r₄, r₆, ...
    and applies (r - 1) / 2. Filters out zeros (from r = 1 or padding). -/
def dpartColLensQ_D : DualPart → DualPart
  | [] => []
  | [_] => []
  | _ :: r₂ :: rest =>
    if r₂ > 1 then (r₂ - 1) / 2 :: dpartColLensQ_D rest
    else dpartColLensQ_D rest

/-! ## Key recursion property:
    Dropping 2 orbit rows = removing head from P and Q column lengths. -/

theorem dpartColLensP_D_cons₂ (r₁ r₂ : ℕ) (rest : DualPart) :
    dpartColLensP_D (r₁ :: r₂ :: rest) = (r₁ + 1) / 2 :: dpartColLensP_D rest :=
  rfl

theorem dpartColLensQ_D_cons₂ (r₁ r₂ : ℕ) (rest : DualPart) (h : r₂ > 1) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = (r₂ - 1) / 2 :: dpartColLensQ_D rest := by
  simp [dpartColLensQ_D, h]

/-! ## Verification of orbit-to-shape mapping -/

-- D [3,1]: P = [(3+1)/2] = [2], Q = [] (since 1 ≤ 1)
#eval dpartColLensP_D [3, 1]  -- [2]
#eval dpartColLensQ_D [3, 1]  -- []

-- D [5,3,1]: P = [3, 1], Q = [1]
#eval dpartColLensP_D [5, 3, 1]  -- [3, 1]
#eval dpartColLensQ_D [5, 3, 1]  -- [1]

-- D [3,3]: P = [2], Q = [1]
#eval dpartColLensP_D [3, 3]  -- [2]
#eval dpartColLensQ_D [3, 3]  -- [1]

-- Recursion check: drop 2 from [5,3,1] = [1]
-- dpartColLensP_D [1] = [1], which is tail of [3,1] ✓
#eval dpartColLensP_D [1]  -- [1]

-- D [5,3,3,1]: P = [3, 2], Q = [1, 0] → [1]
#eval dpartColLensP_D [5, 3, 3, 1]  -- [3, 2]
#eval dpartColLensQ_D [5, 3, 3, 1]  -- [1]
-- After drop 2: [3, 1] → P = [2], Q = []
#eval dpartColLensP_D [3, 1]  -- [2]

/-! ## Tail symbol classification

For a D-type PBP τ, the "tail class" of column pair (0, 1) classifies
the symbols in P's column 0 below the dot/s region.

Three classes:
  DD: tail contains d (discrete series)
  RC: tail contains r or c
  SS: tail is all s (or empty)

The tail class determines how many PBPs lift to a given sub-PBP
under double descent. -/

/-- Tail symbol classes for a column pair. -/
inductive TailClass where
  | DD : TailClass  -- tail bottom symbol is d
  | RC : TailClass  -- tail bottom symbol is r or c
  | SS : TailClass  -- tail is empty or bottom symbol is s
  deriving DecidableEq, Repr

/-- Tail class of a D-type PBP, using the existing `tailLen_D` and `tailSymbol_D`
    from Tail.lean.

    The tail is P's column 0 below the Q boundary: rows [Q.colLen(0), P.colLen(0)).
    By layer monotonicity, the bottom symbol (tailSymbol_D) is the "heaviest".
    - DD: bottom symbol is d
    - RC: bottom symbol is r or c
    - SS: tail is empty, or bottom symbol is s or dot -/
noncomputable def tailClass_D (τ : PBP) : TailClass :=
  if PBP.tailLen_D τ = 0 then .SS
  else match PBP.tailSymbol_D τ with
    | .d => .DD
    | .r | .c => .RC
    | .s | .dot => .SS

/-! ## Shifting Young diagrams (column 0 removal)

`shiftLeft μ` removes column 0, shifting all cells left by 1.
Mathematically: (i, j) ∈ shiftLeft μ ↔ (i, j+1) ∈ μ.
This is the shape operation corresponding to a single descent. -/

namespace YoungDiagram

/-- Helper: (i, j) ∈ image of filtered cells ↔ (i, j+1) ∈ μ. -/
private theorem mem_shiftLeft_aux (μ : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ (μ.cells.filter (fun c => 0 < c.2)).image (fun c => (c.1, c.2 - 1))
    ↔ (i, j + 1) ∈ μ := by
  simp only [Finset.mem_image, Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, heq⟩
    have ha : a = i := (Prod.ext_iff.mp heq).1
    have hb_eq : b - 1 = j := (Prod.ext_iff.mp heq).2
    have hb_val : b = j + 1 := by omega
    subst ha; subst hb_val; exact hab
  · intro h; exact ⟨⟨i, j + 1⟩, ⟨h, by omega⟩, Prod.ext rfl (by simp)⟩

/-- Remove column 0 and shift left: `shiftLeft μ` has `colLen j = μ.colLen (j+1)`. -/
def shiftLeft (μ : YoungDiagram) : YoungDiagram where
  cells := (μ.cells.filter (fun c => 0 < c.2)).image (fun c => (c.1, c.2 - 1))
  isLowerSet := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hle hmem
    rw [Finset.mem_coe, mem_shiftLeft_aux] at hmem ⊢
    exact μ.isLowerSet (Prod.mk_le_mk.mpr
      ⟨(Prod.mk_le_mk.mp hle).1, Nat.succ_le_succ (Prod.mk_le_mk.mp hle).2⟩) hmem

/-- Membership in shiftLeft: (i, j) ∈ shiftLeft μ ↔ (i, j+1) ∈ μ. -/
theorem mem_shiftLeft {μ : YoungDiagram} {i j : ℕ} :
    (i, j) ∈ μ.shiftLeft ↔ (i, j + 1) ∈ μ :=
  mem_shiftLeft_aux μ i j

/-- Column lengths shift: `(shiftLeft μ).colLen j = μ.colLen (j + 1)`. -/
theorem colLen_shiftLeft (μ : YoungDiagram) (j : ℕ) :
    μ.shiftLeft.colLen j = μ.colLen (j + 1) := by
  -- colLen j = smallest i such that (i, j) ∉ shape
  -- (i, j) ∈ shiftLeft μ ↔ (i, j+1) ∈ μ ↔ i < μ.colLen(j+1)
  -- So shiftLeft.colLen j = μ.colLen(j+1)
  apply le_antisymm
  · -- shiftLeft.colLen j ≤ μ.colLen(j+1)
    by_contra h; push_neg at h
    have : (μ.colLen (j + 1), j) ∈ μ.shiftLeft :=
      mem_iff_lt_colLen.mpr h
    rw [mem_shiftLeft, mem_iff_lt_colLen] at this
    exact lt_irrefl _ this
  · -- μ.colLen(j+1) ≤ shiftLeft.colLen j
    by_contra h; push_neg at h
    have : (μ.shiftLeft.colLen j, j + 1) ∈ μ := by
      rw [mem_iff_lt_colLen]; omega
    have : (μ.shiftLeft.colLen j, j) ∈ μ.shiftLeft :=
      mem_shiftLeft.mpr this
    exact absurd (mem_iff_lt_colLen.mp this) (lt_irrefl _)

end YoungDiagram

/-! ## Double descent and column shifting

The key structural lemma: double descent D→C→D shifts P left by 1 column.

For a D-type PBP τ, `doubleDescent_D_paintL τ i j` references `τ.P.paint i (j+1)`.
This means the double descent's P at column j corresponds to the original P at column j+1.

Formally: ∇²τ has P shape = shiftLeft(τ.P.shape), so
  colLen(∇²P, j) = P.colLen(j+1). -/

/-- The double descent paint at (i, j) is dot when i ≥ P.shape.colLen(j+1). -/
theorem doubleDescent_D_paintL_dot (τ : PBP) (hγ : τ.γ = .D)
    {i j : ℕ} (h_ge : i ≥ τ.P.shape.colLen (j + 1)) :
    PBP.doubleDescent_D_paintL τ i j = .dot := by
  simp only [PBP.doubleDescent_D_paintL]
  have hQ := PBP.Q_colLen_le_dotScolLen_of_D τ hγ (j + 1)
  have hds := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  rw [if_neg (by omega), if_neg (by omega)]
  exact τ.P.paint_outside i (j + 1) (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

/-- The double descent paint at (i, j) is non-dot for some i in the "tail" region
    [dotScolLen, colLen). This witnesses that the effective column length is ≥ colLen(j+1). -/
theorem doubleDescent_D_paintL_nondot_tail (τ : PBP) (hγ : τ.γ = .D)
    {i j : ℕ} (hi_ge : PBP.dotScolLen τ.P (j + 1) ≤ i)
    (hi_lt : i < τ.P.shape.colLen (j + 1)) :
    PBP.doubleDescent_D_paintL τ i j ≠ .dot := by
  simp only [PBP.doubleDescent_D_paintL]
  have hQ := PBP.Q_colLen_le_dotScolLen_of_D τ hγ (j + 1)
  rw [if_neg (by omega), if_neg (by omega)]
  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P hi_ge
    (YoungDiagram.mem_iff_lt_colLen.mpr hi_lt)

/-! ## Main counting theorem (statement)

The ultimate goal is to prove:

  For each root type γ and orbit partition dp,
  the number of PBPs with the corresponding shapes equals countPBP dp γ.

Proof structure for D type:
  1. Induction on dp (the orbit partition)
  2. Base case dp = []: unique PBP with empty shapes → count = 1
  3. Step dp = r₁ :: r₂ :: rest:
     a. Double descent ∇² maps PBP(dp) → PBP(rest)
     b. ∇² is surjective (can fill any sub-PBP)
     c. Fiber |∇²⁻¹(σ)| depends on tail class of σ:
        - Primitive (r₂ > r₃): fiber = (tDD + tRC + tSS) for all σ
        - Balanced (r₂ = r₃): fiber depends on TC(σ) via matrix multiply
     d. tailCoeffs k gives the coefficients
  4. C type: descent C→D is injective, image = all of D (primitive) or DD∪RC (balanced)
  5. M type: similar via B→M descent
-/

/-! ## Base case: empty PBP -/

/-- The empty painted Young diagram: shape ⊥, paint always dot. -/
def emptyPYD : PaintedYoungDiagram where
  shape := ⊥
  paint := fun _ _ => .dot
  paint_outside := fun _ _ _ => rfl

/-- The unique PBP with empty shapes. -/
def emptyPBP (γ : RootType) : PBP where
  γ := γ
  P := emptyPYD
  Q := emptyPYD
  sym_P := fun _ _ h => absurd h (YoungDiagram.notMem_bot _)
  sym_Q := fun _ _ h => absurd h (YoungDiagram.notMem_bot _)
  dot_match := by
    intro i j; constructor
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
  mono_P := fun _ _ _ _ _ _ h => absurd h (YoungDiagram.notMem_bot _)
  mono_Q := fun _ _ _ _ _ _ h => absurd h (YoungDiagram.notMem_bot _)
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ _
    simp only [paintBySide, emptyPYD] at h₁
    cases s₁ <;> simp at h₁
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ _
    simp only [paintBySide, emptyPYD] at h₁
    cases s₁ <;> simp at h₁
  col_c_P := by intro _ _ _ h; simp [emptyPYD] at h
  col_c_Q := by intro _ _ _ h; simp [emptyPYD] at h
  col_d_P := by intro _ _ _ h; simp [emptyPYD] at h
  col_d_Q := by intro _ _ _ h; simp [emptyPYD] at h

/-- Any PBP with empty P shape has P = emptyPYD. -/
theorem PYD_eq_emptyPYD_of_shape_bot {D : PaintedYoungDiagram} (h : D.shape = ⊥) :
    D = emptyPYD := by
  apply PaintedYoungDiagram.ext'
  · exact h
  · ext i j
    have : (i, j) ∉ D.shape := by rw [h]; exact YoungDiagram.notMem_bot _
    rw [D.paint_outside i j this]
    rfl

/-- Any PBP in PBPSet γ ⊥ ⊥ equals emptyPBP γ. -/
theorem PBPSet_bot_unique (γ : RootType) (x : PBPSet γ ⊥ ⊥) :
    x.val = emptyPBP γ := by
  have hγ := x.prop.1
  have hP := x.prop.2.1
  have hQ := x.prop.2.2
  apply PBP.ext''
  · exact hγ
  · exact PYD_eq_emptyPYD_of_shape_bot hP
  · exact PYD_eq_emptyPYD_of_shape_bot hQ

/-- The empty PBP is in PBPSet. -/
def emptyPBP_mem (γ : RootType) : PBPSet γ ⊥ ⊥ :=
  ⟨emptyPBP γ, rfl, rfl, rfl⟩

/-- PBPSet γ ⊥ ⊥ has exactly one element. -/
theorem card_PBPSet_bot (γ : RootType) :
    Fintype.card (PBPSet γ ⊥ ⊥) = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨emptyPBP_mem γ, fun x => Subtype.ext (PBPSet_bot_unique γ x)⟩

/-! ## Double descent as PBP map (D type)

Construct `∇²τ` as a formal PBP for D-type τ.
Shape: P' = shiftLeft(P), Q' = shiftLeft(Q).
Paint: P' = doubleDescent_D_paintL, Q' = all dots. -/

/-- Extract: if doubleDescent_D_paintL = σ with σ ∉ {dot, s}, then P.paint = σ. -/
theorem doubleDescent_D_paintL_extract (τ : PBP) {i j : ℕ}
    (hdd : PBP.doubleDescent_D_paintL τ i j ≠ .dot)
    (hdd_s : PBP.doubleDescent_D_paintL τ i j ≠ .s) :
    τ.P.paint i (j + 1) = PBP.doubleDescent_D_paintL τ i j := by
  simp only [PBP.doubleDescent_D_paintL] at hdd hdd_s ⊢
  by_cases ha : i < τ.Q.shape.colLen (j + 1)
  · exact absurd (if_pos ha ▸ rfl) hdd
  · rw [if_neg ha] at hdd hdd_s ⊢
    by_cases hb : i < PBP.dotScolLen τ.P (j + 1)
    · exact absurd (if_pos hb ▸ rfl) hdd_s
    · rw [if_neg hb]

/-- The double descent PBP ∇²τ for D type. All 13 constraints verified. -/
noncomputable def doubleDescent_D_PBP (τ : PBP) (hγ : τ.γ = .D) : PBP where
  γ := .D
  P := {
    shape := τ.P.shape.shiftLeft
    paint := PBP.doubleDescent_D_paintL τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_D_paintL_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  Q := {
    shape := τ.Q.shape.shiftLeft
    paint := fun _ _ => .dot
    paint_outside := fun _ _ _ => rfl
  }
  sym_P := fun _ _ _ => by simp [DRCSymbol.allowed]  -- D/L: all True
  sym_Q := fun _ _ _ => by simp [DRCSymbol.allowed]  -- D/R: dot = dot
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP, hpaint⟩
      have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
      -- paint = dot means i < Q.colLen(j+1) (the dot region)
      have h₁ : i < τ.Q.shape.colLen (j + 1) := by
        simp only [PBP.doubleDescent_D_paintL] at hpaint
        by_contra hge; push_neg at hge
        by_cases hs : i < PBP.dotScolLen τ.P (j + 1)
        · rw [if_neg (by omega), if_pos hs] at hpaint; exact absurd hpaint (by decide)
        · rw [if_neg (by omega), if_neg hs] at hpaint
          have ⟨hmQ, _⟩ := (τ.dot_match i (j+1)).mp ⟨hmemP', hpaint⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmQ) (by omega)
      exact ⟨YoungDiagram.mem_shiftLeft.mpr (YoungDiagram.mem_iff_lt_colLen.mpr h₁), rfl⟩
    · intro ⟨hmemQ, _⟩
      have hmemQ' := YoungDiagram.mem_shiftLeft.mp hmemQ
      have h₁ : i < τ.Q.shape.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmemQ'
      refine ⟨YoungDiagram.mem_shiftLeft.mpr (PBP.Q_le_P_of_D τ hγ hmemQ'), ?_⟩
      simp [PBP.doubleDescent_D_paintL, if_pos h₁]
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_D_paintL]
    by_cases h₁ : i₁ < τ.Q.shape.colLen (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · by_cases h₂ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_neg h₁, if_pos h₂]
        have hQ_anti := τ.Q.shape.colLen_anti (j₁+1) (j₂+1) (by omega)
        by_cases h₃ : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · omega
        · rw [if_neg h₃]
          by_cases h₄ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
          · rw [if_pos h₄]
          · rw [if_neg h₄]
            have hlo := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P
              (Nat.not_lt.mp h₄) hmem'
            simp only [DRCSymbol.layerOrd] at hlo ⊢; omega
      · rw [if_neg h₁, if_neg h₂]
        have hQ_anti := τ.Q.shape.colLen_anti (j₁+1) (j₂+1) (by omega)
        have hQ_le := PBP.Q_colLen_le_dotScolLen_of_D τ hγ (j₁ + 1)
        by_cases h₃ : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · omega
        · rw [if_neg h₃]
          by_cases h₄ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
          · -- Impossible: dotScolLen(P, j₁+1) ≤ i₁ ≤ i₂ < dotScolLen(P, j₂+1)
            -- but dotScolLen is anti-monotone (j₁+1 ≤ j₂+1)
            exfalso
            have hds_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
            rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
                ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hds_anti
            omega
          · rw [if_neg h₄]
            exact τ.mono_P i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  mono_Q := fun _ _ _ _ _ _ h => by
    simp [DRCSymbol.layerOrd]
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    -- Q' is all dots → s can only come from P' (side L)
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: s in P' comes from middle region Q.colLen(j+1) ≤ i < dotScolLen(P, j+1)
      -- This means P(i, j+1) has layerOrd ≤ 1 and is not dot → P(i, j+1) = s
      -- Row uniqueness in τ gives j₁+1 = j₂+1
      simp only [PBP.doubleDescent_D_paintL] at h₁ h₂
      -- h₁: s at (i, j₁) means Q.colLen(j₁+1) ≤ i < dotScolLen(P, j₁+1)
      have hq₁ : ¬(i < τ.Q.shape.colLen (j₁ + 1)) := by
        intro hlt; rw [if_pos hlt] at h₁; exact absurd h₁ (by decide)
      have hds₁ : i < PBP.dotScolLen τ.P (j₁ + 1) := by
        by_contra hge; push_neg at hge
        rw [if_neg hq₁, if_neg (by omega)] at h₁
        -- h₁ : P.paint(i, j₁+1) = s. paint ≠ dot → in shape.
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout
          exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P hge hmem
        rw [h₁, DRCSymbol.layerOrd] at this; omega
      -- P(i, j₁+1) ∈ {dot, s} and ∉ Q (not dot by dot_match) → P(i, j₁+1) = s
      have hPi₁ : τ.P.paint i (j₁ + 1) = .s := by
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hds₁)
        have hne : τ.P.paint i (j₁ + 1) ≠ .dot := by
          intro heq
          have hmem₁ : (i, j₁+1) ∈ τ.P.shape := YoungDiagram.mem_iff_lt_colLen.mpr
            (Nat.lt_of_lt_of_le hds₁ (PBP.dotScolLen_le_colLen τ.P τ.mono_P _))
          have ⟨hq, _⟩ := (τ.dot_match i (j₁+1)).mp ⟨hmem₁, heq⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hq) (by omega)
        revert hlo hne; cases τ.P.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
      -- Similarly for j₂
      have hq₂ : ¬(i < τ.Q.shape.colLen (j₂ + 1)) := by
        intro hlt; rw [if_pos hlt] at h₂; exact absurd h₂ (by decide)
      have hds₂ : i < PBP.dotScolLen τ.P (j₂ + 1) := by
        by_contra hge; push_neg at hge
        rw [if_neg hq₂, if_neg (by omega)] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout
          exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P hge hmem
        rw [h₂, DRCSymbol.layerOrd] at this; omega
      have hPi₂ : τ.P.paint i (j₂ + 1) = .s := by
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hds₂)
        have hne : τ.P.paint i (j₂ + 1) ≠ .dot := by
          intro heq
          have hmem₂ : (i, j₂+1) ∈ τ.P.shape := YoungDiagram.mem_iff_lt_colLen.mpr
            (Nat.lt_of_lt_of_le hds₂ (PBP.dotScolLen_le_colLen τ.P τ.mono_P _))
          have ⟨hq, _⟩ := (τ.dot_match i (j₂+1)).mp ⟨hmem₂, heq⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hq) (by omega)
        revert hlo hne; cases τ.P.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
      -- Apply row_s of τ
      have := τ.row_s i .L .L (j₁+1) (j₂+1)
        (show paintBySide τ.P τ.Q .L i (j₁+1) = .s by simp [paintBySide]; exact hPi₁)
        (show paintBySide τ.P τ.Q .L i (j₂+1) = .s by simp [paintBySide]; exact hPi₂)
      exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- Q' is all dots → r can only come from P' (side L)
    cases s₁ <;> cases s₂ <;> simp only [paintBySide] at h₁ h₂
    · -- Both L: r in P' only from the P.paint region (not dot/s regions)
      simp only [PBP.doubleDescent_D_paintL] at h₁ h₂
      by_cases ha₁ : i < τ.Q.shape.colLen (j₁+1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁; by_cases hb₁ : i < PBP.dotScolLen τ.P (j₁+1)
        · rw [if_pos hb₁] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb₁] at h₁
          by_cases ha₂ : i < τ.Q.shape.colLen (j₂+1)
          · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
          · rw [if_neg ha₂] at h₂; by_cases hb₂ : i < PBP.dotScolLen τ.P (j₂+1)
            · rw [if_pos hb₂] at h₂; exact absurd h₂ (by decide)
            · rw [if_neg hb₂] at h₂
              have := τ.row_r i .L .L (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .L i (j₁+1) = .r by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .L i (j₂+1) = .r by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    -- c only comes from the P.paint branch of doubleDescent_D_paintL
    -- c only from P.paint branch: use by_cases to extract
    have hc₁ : τ.P.paint i₁ (j+1) = .c := by
      simp only [PBP.doubleDescent_D_paintL] at h₁
      by_cases ha : i₁ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hc₂ : τ.P.paint i₂ (j+1) = .c := by
      simp only [PBP.doubleDescent_D_paintL] at h₂
      by_cases ha : i₂ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_c_P (j+1) i₁ i₂ hc₁ hc₂
  col_c_Q := by intro _ _ _ h; exact DRCSymbol.noConfusion h
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    have hd₁ : τ.P.paint i₁ (j+1) = .d := by
      simp only [PBP.doubleDescent_D_paintL] at h₁
      by_cases ha : i₁ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hd₂ : τ.P.paint i₂ (j+1) = .d := by
      simp only [PBP.doubleDescent_D_paintL] at h₂
      by_cases ha : i₂ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_d_P (j+1) i₁ i₂ hd₁ hd₂
  col_d_Q := by intro _ _ _ h; exact DRCSymbol.noConfusion h

/-! ## Scaffolding for counting proof

### Already proved (Prop 10.9, in Tail.lean):
  `ddescent_inj_D`: same shapes + same ∇² paint + same (sig, eps) → same PBP paint
  This is the core uniqueness: τ ↦ (∇²τ, sig, eps) is injective.

### What's needed for counting:
  1. ∇² as map PBPSet(μP, μQ) → PBPSet(shiftLeft μP, shiftLeft μQ)  [done above]
  2. Wrap ddescent_inj_D for PBPSet  [next]
  3. Fiber decomposition: |PBPSet(dp)| = Σ_σ |fiber(σ)|
  4. |fiber(σ)| = tailCoeffs(k, tailClass(σ))
  5. Assembly: countPBP_D recurrence
-/

/-! ### ∇² as a map between PBPSets -/

/-- ∇² as a function between PBPSets. -/
noncomputable def doubleDescent_D_map {μP μQ : YoungDiagram}
    (τ : PBPSet .D μP μQ) :
    PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ) :=
  ⟨doubleDescent_D_PBP τ.val τ.prop.1, rfl,
   congrArg YoungDiagram.shiftLeft τ.prop.2.1,
   congrArg YoungDiagram.shiftLeft τ.prop.2.2⟩

/-! ### Wrap ddescent_inj_D for PBPSet -/

/-- Two PBPSet elements with same ∇², sig, eps are equal.
    Direct wrapper of ddescent_inj_D. -/
theorem doubleDescent_D_injective_on_PBPSet {μP μQ : YoungDiagram}
    (τ₁ τ₂ : PBPSet .D μP μQ)
    (hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val i j =
                   PBP.doubleDescent_D_paintL τ₂.val i j)
    (hsig : PBP.signature τ₁.val = PBP.signature τ₂.val)
    (heps : PBP.epsilon τ₁.val = PBP.epsilon τ₂.val) :
    τ₁ = τ₂ := by
  have ⟨hPeq, hQeq⟩ := PBP.ddescent_inj_D τ₁.val τ₂.val τ₁.prop.1 τ₂.prop.1
    (by rw [τ₁.prop.2.1, τ₂.prop.2.1])
    (by rw [τ₁.prop.2.2, τ₂.prop.2.2])
    hdd hsig heps
  exact Subtype.ext (PBP.ext''
    (by rw [τ₁.prop.1, τ₂.prop.1])
    (PaintedYoungDiagram.ext' (by rw [τ₁.prop.2.1, τ₂.prop.2.1])
      (funext fun i => funext (hPeq i)))
    (PaintedYoungDiagram.ext' (by rw [τ₁.prop.2.2, τ₂.prop.2.2])
      (funext fun i => funext (hQeq i))))

/-! ### Fiber of ∇² -/

/-- Fiber of ∇² over a given sub-PBP. -/
def doubleDescent_D_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :=
  {τ : PBPSet .D μP μQ // doubleDescent_D_map τ = σ}

instance {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :
    Finite (doubleDescent_D_fiber σ) :=
  Finite.of_injective (fun x => x.val) (fun _ _ h => Subtype.ext h)

noncomputable instance {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :
    Fintype (doubleDescent_D_fiber σ) :=
  Fintype.ofFinite _

/-! ### Counting theorem: roadmap with key lemmas

The counting theorem for D type is proved by induction on dp.

For the balanced case, ∇² is NOT surjective:
  - DD/RC class sub-PBPs have non-empty fibers
  - SS class sub-PBPs have EMPTY fibers (no valid column 0 extension)

So |PBPSet(dp)| = Σ_{σ, tc(σ)=DD} fiberDD + Σ_{σ, tc(σ)=RC} fiberRC
where fiberDD = tDD+tRC+tSS, fiberRC = scDD+scRC+scSS.

For the primitive case, all classes have the same fiber size.
-/

/-! ### Tail sequence counting

A valid tail of length k is a sequence s^a r^b c^{δc} d^{δd}
with a + b + δc + δd = k, δc ∈ {0,1}, δd ∈ {0,1}.

Count by (δc, δd):
  (0,0): a+b=k → k+1 = nu(k)
  (1,0): a+b=k-1 → k = nu(k-1) (k≥1)
  (0,1): a+b=k-1 → k = nu(k-1) (k≥1)
  (1,1): a+b=k-2 → k-1 = nu(k-2) (k≥2)

By tail class:
  DD (δd=1): nu(k-1) + nu(k-2)
  RC (δd=0, has r or c): nu(k-1) + nu(k-1) = 2·nu(k-1)
  SS (all-s): 1
-/

/-- The tail count (DD, RC, SS) for unconstrained tails equals tailCoeffs.1.
    k ≥ 1 in all uses (k = (r₁-r₂)/2 + 1). -/
theorem tailCoeffs_fst_DD (k : ℕ) :
    (tailCoeffs k).1.1 = nu (k - 1) + (if k ≥ 2 then nu (k - 2) else 0) := rfl

theorem tailCoeffs_fst_RC (k : ℕ) :
    (tailCoeffs k).1.2.1 = 2 * nu (k - 1) := rfl

theorem tailCoeffs_fst_SS (k : ℕ) :
    (tailCoeffs k).1.2.2 = 1 := rfl

/-- Primitive condition: tail rows are outside P.shape at columns ≥ 1.
    When μQ.colLen 0 ≥ (shiftLeft μP).colLen 0 = μP.colLen 1,
    any tail painting at column 0 has no s/r row conflicts. -/
theorem primitive_tail_rows_outside {μP μQ : YoungDiagram}
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    {i : ℕ} (hi : μQ.colLen 0 ≤ i) {j : ℕ} (hj : 1 ≤ j)
    (τ : PBPSet .D μP μQ) :
    τ.val.P.paint i j = .dot := by
  apply τ.val.P.paint_outside
  rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]
  rw [YoungDiagram.colLen_shiftLeft] at h_prim
  have hcol := YoungDiagram.colLen_anti μP 1 j (by omega)
  push_neg
  calc μP.colLen j ≤ μP.colLen 1 := hcol
    _ ≤ μQ.colLen 0 := h_prim
    _ ≤ i := hi

/-- Lift painting: column 0 from col0, columns ≥ 1 from σ.P shifted right.

    This is the REVERSE of doubleDescent: given sub-PBP σ and column 0
    painting col0, produce a painting for the "lifted" PBP.
    τ.P.paint(i, 0) = col0(i), τ.P.paint(i, j+1) = σ.P.paint(i, j). -/
def liftPaint_D (σ : PBP) (col0 : ℕ → DRCSymbol) : ℕ → ℕ → DRCSymbol :=
  fun i j => match j with
    | 0 => col0 i
    | j + 1 => σ.P.paint i j

/-! ### Reverse construction for primitive case

Given σ ∈ PBPSet(rest) and a column 0 painting, construct τ ∈ PBPSet(dp).
The construction uses liftPaint_D: P(i,0) = col0(i), P(i,j+1) = σ.P(i,j).

In the primitive case, all PBP constraints are automatically satisfied
because tail rows (i ≥ μQ.colLen 0) have P.paint(i, j) = .dot for j ≥ 1
(by primitive_tail_rows_outside). So no s/r row conflicts. -/

/-- A valid tail painting for column 0 of a D-type PBP.
    The painting is: dot for rows < b, then tail symbols, dot above c.
    - b = μQ.colLen 0 (dot boundary)
    - c = μP.colLen 0 (shape boundary)
    - Symbols in [b, c) are non-dot, monotone layerOrd, at most 1 c/d. -/
structure ValidCol0 (μP μQ : YoungDiagram) where
  paint : ℕ → DRCSymbol
  dot_below : ∀ i, i < μQ.colLen 0 → paint i = .dot
  nondot_tail : ∀ i, μQ.colLen 0 ≤ i → i < μP.colLen 0 → paint i ≠ .dot
  dot_above : ∀ i, μP.colLen 0 ≤ i → paint i = .dot
  mono : ∀ i₁ i₂, i₁ ≤ i₂ → i₂ < μP.colLen 0 →
    (paint i₁).layerOrd ≤ (paint i₂).layerOrd
  col_c_unique : ∀ i₁ i₂, paint i₁ = .c → paint i₂ = .c → i₁ = i₂
  col_d_unique : ∀ i₁ i₂, paint i₁ = .d → paint i₂ = .d → i₁ = i₂

/-- ValidCol0 is finite: inject into the finite type (Fin c → DRCSymbol)
    where c = μP.colLen 0 (paint outside [0, c) is determined). -/
instance {μP μQ : YoungDiagram} : Finite (ValidCol0 μP μQ) := by
  apply Finite.of_injective (fun (v : ValidCol0 μP μQ) =>
    fun (i : Fin (μP.colLen 0 + 1)) => v.paint i.val)
  intro v₁ v₂ h
  have : v₁.paint = v₂.paint := by
    ext i
    by_cases hi : i < μP.colLen 0 + 1
    · exact congr_fun h ⟨i, hi⟩
    · rw [v₁.dot_above i (by omega), v₂.dot_above i (by omega)]
  cases v₁; cases v₂; simp_all

noncomputable instance {μP μQ : YoungDiagram} : Fintype (ValidCol0 μP μQ) :=
  Fintype.ofFinite _

/-- Lift construction: given σ ∈ PBPSet(rest) and a valid column 0 painting,
    produce a D-type PBP with the given shapes.

    P.paint = liftPaint_D σ col0.paint
    Q = all dots with shape μQ

    In the primitive case (h_prim), all PBP constraints hold automatically. -/
noncomputable def liftPBP_primitive_D {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    PBPSet .D μP μQ := by
  -- Define P and Q as named PYDs to avoid anonymous structure issues
  have hpo : ∀ i j, (i, j) ∉ μP → liftPaint_D σ.val col0.paint i j = .dot := by
    intro i j hmem; cases j with
    | zero => exact col0.dot_above i (by rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
    | succ j => exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  have h_prim' : μP.colLen 1 ≤ μQ.colLen 0 := by
    rw [YoungDiagram.colLen_shiftLeft] at h_prim; exact h_prim
  refine ⟨⟨.D,
    ⟨μP, liftPaint_D σ.val col0.paint, hpo⟩,
    ⟨μQ, fun _ _ => .dot, fun _ _ _ => rfl⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P => intro _ _ _; trivial  -- D/L allows all
  case sym_Q => intro _ _ _; simp [DRCSymbol.allowed]
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        simp only [liftPaint_D] at hpaint
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by
          by_contra h; push_neg at h
          exact col0.nondot_tail i h (YoungDiagram.mem_iff_lt_colLen.mp hmem) hpaint), rfl⟩
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
          simp only [liftPaint_D]; exact col0.dot_below i hq⟩
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
      | zero => exact col0.mono i₁ i₂ hi (YoungDiagram.mem_iff_lt_colLen.mp hmem)
      | succ j₂ =>
        by_cases h : i₁ < μQ.colLen 0
        · simp only [liftPaint_D]; rw [col0.dot_below i₁ h]; simp [DRCSymbol.layerOrd]
        · push_neg at h; exfalso
          have hmem' : i₂ < μP.colLen (j₂ + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem
          have hcol := YoungDiagram.colLen_anti μP 1 (j₂ + 1) (by omega)
          omega
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
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₁; exact absurd h₁ (by decide)
          -- σ.P at tail rows is outside shape → dot
          have hdot_σ : ∀ k, σ.val.P.paint i k = .dot := fun k => by
            apply σ.val.P.paint_outside
            rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; push_neg
            calc (YoungDiagram.shiftLeft μP).colLen k
                ≤ (YoungDiagram.shiftLeft μP).colLen 0 := YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
              _ ≤ μQ.colLen 0 := h_prim
              _ ≤ i := hi
          rw [show σ.val.P.paint i _ = .dot from hdot_σ _] at h₂; exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₂; exact absurd h₂ (by decide)
          -- σ.P at tail rows is outside shape → dot
          have hdot_σ : ∀ k, σ.val.P.paint i k = .dot := fun k => by
            apply σ.val.P.paint_outside
            rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; push_neg
            calc (YoungDiagram.shiftLeft μP).colLen k
                ≤ (YoungDiagram.shiftLeft μP).colLen 0 := YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
              _ ≤ μQ.colLen 0 := h_prim
              _ ≤ i := hi
          rw [show σ.val.P.paint i _ = .dot from hdot_σ _] at h₁; exact absurd h₁ (by decide)
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
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₁; exact absurd h₁ (by decide)
          -- σ.P at tail rows is outside shape → dot
          have hdot_σ : ∀ k, σ.val.P.paint i k = .dot := fun k => by
            apply σ.val.P.paint_outside
            rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; push_neg
            calc (YoungDiagram.shiftLeft μP).colLen k
                ≤ (YoungDiagram.shiftLeft μP).colLen 0 := YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
              _ ≤ μQ.colLen 0 := h_prim
              _ ≤ i := hi
          rw [show σ.val.P.paint i _ = .dot from hdot_σ _] at h₂; exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₂; exact absurd h₂ (by decide)
          -- σ.P at tail rows is outside shape → dot
          have hdot_σ : ∀ k, σ.val.P.paint i k = .dot := fun k => by
            apply σ.val.P.paint_outside
            rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; push_neg
            calc (YoungDiagram.shiftLeft μP).colLen k
                ≤ (YoungDiagram.shiftLeft μP).colLen 0 := YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
              _ ≤ μQ.colLen 0 := h_prim
              _ ≤ i := hi
          rw [show σ.val.P.paint i _ = .dot from hdot_σ _] at h₁; exact absurd h₁ (by decide)
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
    | zero => exact col0.col_c_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    simp only [liftPaint_D] at h₁ h₂
    cases j with
    | zero => exact col0.col_d_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h

/-! ### ValidCol0 counting

A ValidCol0 with tail length k = μP.colLen(0) - μQ.colLen(0)
is determined by a tuple (a, b, δc, δd) with a + b + δc + δd = k,
where δc, δd ∈ {0, 1}. The painting is s^a r^b c^δc d^δd.

Count = Σ_{(δc,δd) ∈ {0,1}²} max(0, k + 1 - δc - δd)
      = (k+1) + k + k + max(0, k-1)
      = tDD + tRC + tSS from tailCoeffs k
-/

/-- The number of valid column 0 paintings equals the tailCoeffs sum. -/
theorem validCol0_card {μP μQ : YoungDiagram}
    (k : ℕ) (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (ValidCol0 μP μQ) =
      let ((tDD, tRC, tSS), _) := tailCoeffs k
      tDD + tRC + tSS := by
  sorry

/-! ### Framework for sandwich argument

Extract column 0 from a fiber element as a ValidCol0 structure.
This is the inverse direction of liftPBP_primitive_D and gives
the injection fiber(σ) ↪ ValidCol0 needed for the upper bound.
-/

/-- Extract column 0 data from a D-type PBP as a ValidCol0.
    For D type, P column 0 has dots in rows < Q.colLen(0) and non-dot cells
    in the tail [Q.colLen(0), P.colLen(0)). -/
noncomputable def PBP.extractCol0_D {μP μQ : YoungDiagram}
    (τ : PBPSet .D μP μQ) : ValidCol0 μP μQ where
  paint i := τ.val.P.paint i 0
  dot_below i hi := by
    -- (i, 0) ∈ μQ = τ.Q.shape → (i, 0) is P-dot by dot_match
    have hmemQ : (i, 0) ∈ τ.val.Q.shape := by
      rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi
    have hmemP : (i, 0) ∈ τ.val.P.shape :=
      ((τ.val.dot_match i 0).mpr ⟨hmemQ,
        PBP.Q_all_dot_of_D τ.val τ.prop.1 i 0 hmemQ⟩).1
    exact ((τ.val.dot_match i 0).mpr
      ⟨hmemQ, PBP.Q_all_dot_of_D τ.val τ.prop.1 i 0 hmemQ⟩).2
  nondot_tail i hi1 hi2 := by
    -- i ≥ μQ.colLen 0 → (i, 0) ∉ μQ → P.paint not dot (by dot_match contrapositive)
    intro hpaint
    have hmemP : (i, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi2
    have ⟨hmemQ, _⟩ := (τ.val.dot_match i 0).mp ⟨hmemP, hpaint⟩
    rw [τ.prop.2.2] at hmemQ
    have := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
    omega
  dot_above i hi := by
    apply τ.val.P.paint_outside
    rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  mono i₁ i₂ h₁ h₂ := by
    apply τ.val.mono_P i₁ 0 i₂ 0 h₁ (Nat.le_refl 0)
    rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr h₂
  col_c_unique i₁ i₂ := τ.val.col_c_P 0 i₁ i₂
  col_d_unique i₁ i₂ := τ.val.col_d_P 0 i₁ i₂

/-- extractCol0_D is injective on the fiber over σ.
    Given τ₁, τ₂ ∈ fiber(σ) with same column 0 paint, same P everywhere
    (columns ≥ 1 determined by σ), same Q (Q = dotDiag P), so τ₁ = τ₂. -/
theorem extractCol0_D_injective_on_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    {τ₁ τ₂ : doubleDescent_D_fiber σ}
    (h : (PBP.extractCol0_D τ₁.val).paint = (PBP.extractCol0_D τ₂.val).paint) :
    τ₁ = τ₂ := by
  -- From τ₁.prop = τ₂.prop = σ: both τ have the same ∇² paint
  have hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val.val i j =
                    PBP.doubleDescent_D_paintL τ₂.val.val i j := by
    intro i j
    have hdd_eq : doubleDescent_D_map τ₁.val = doubleDescent_D_map τ₂.val := by
      rw [τ₁.prop, τ₂.prop]
    have : doubleDescent_D_PBP τ₁.val.val τ₁.val.prop.1 =
            doubleDescent_D_PBP τ₂.val.val τ₂.val.prop.1 :=
      congrArg Subtype.val hdd_eq
    exact congr_fun (congr_fun (congrArg (fun d => d.P.paint) this) i) j
  -- Apply ddescent_D_determines_single to get single descent equality
  have hshapeP : τ₁.val.val.P.shape = τ₂.val.val.P.shape := by
    rw [τ₁.val.prop.2.1, τ₂.val.prop.2.1]
  have hshapeQ : τ₁.val.val.Q.shape = τ₂.val.val.Q.shape := by
    rw [τ₁.val.prop.2.2, τ₂.val.prop.2.2]
  have hdesc := PBP.ddescent_D_determines_single τ₁.val.val τ₂.val.val
    τ₁.val.prop.1 τ₂.val.prop.1 hshapeP hshapeQ hdd
  -- Apply descent_eq_implies_cols_ge1_D to get cols ≥ 1 equal
  have hcols := PBP.descent_eq_implies_cols_ge1_D τ₁.val.val τ₂.val.val
    τ₁.val.prop.1 τ₂.val.prop.1 hshapeP hshapeQ hdesc
  -- Assemble P.paint equality (col 0 from h, cols ≥ 1 from hcols)
  have hP : τ₁.val.val.P.paint = τ₂.val.val.P.paint := by
    ext i j
    cases j with
    | zero => exact congr_fun h i
    | succ j => exact hcols i (j + 1) (by omega)
  have hPeq : τ₁.val.val.P = τ₂.val.val.P := PaintedYoungDiagram.ext' hshapeP hP
  have hQeq : τ₁.val.val.Q = τ₂.val.val.Q := by
    apply PaintedYoungDiagram.ext' hshapeQ
    ext i j
    by_cases hmem : (i, j) ∈ τ₁.val.val.Q.shape
    · rw [PBP.Q_all_dot_of_D τ₁.val.val τ₁.val.prop.1 i j hmem,
          PBP.Q_all_dot_of_D τ₂.val.val τ₂.val.prop.1 i j (hshapeQ ▸ hmem)]
    · rw [τ₁.val.val.Q.paint_outside i j hmem,
          τ₂.val.val.Q.paint_outside i j (hshapeQ ▸ hmem)]
  have hτeq : τ₁.val.val = τ₂.val.val := PBP.ext''
    (by rw [τ₁.val.prop.1, τ₂.val.prop.1]) hPeq hQeq
  exact Subtype.ext (Subtype.ext hτeq)

/-! ### Injection lemmas for sandwich argument -/

/-- liftPBP is injective across all (σ, col0): different inputs → different PBPs. -/
theorem liftPBP_primitive_D_injective {μP μQ : YoungDiagram}
    {σ₁ σ₂ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    {col0₁ col0₂ : ValidCol0 μP μQ}
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (h : liftPBP_primitive_D σ₁ col0₁ h_prim hQP = liftPBP_primitive_D σ₂ col0₂ h_prim hQP) :
    σ₁ = σ₂ ∧ col0₁ = col0₂ := by
  have hval := congrArg Subtype.val h
  -- P paint equal → column 0 equal + σ.P equal
  have hP : (liftPBP_primitive_D σ₁ col0₁ h_prim hQP).val.P.paint =
            (liftPBP_primitive_D σ₂ col0₂ h_prim hQP).val.P.paint :=
    congr_arg (fun τ => τ.P.paint) hval
  -- Extract column 0: col0₁ = col0₂
  have hcol0 : col0₁.paint = col0₂.paint := by
    ext i; have := congr_fun (congr_fun hP i) 0; simp [liftPaint_D] at this; exact this
  have hcol0_eq : col0₁ = col0₂ := by
    cases col0₁; cases col0₂; simp only [ValidCol0.mk.injEq]; exact hcol0
  -- Extract columns ≥ 1: σ₁.P = σ₂.P
  have hσP : σ₁.val.P.paint = σ₂.val.P.paint := by
    ext i j; have := congr_fun (congr_fun hP i) (j + 1); simp [liftPaint_D] at this; exact this
  -- σ₁.Q = σ₂.Q (D type: Q paint = dot everywhere, shapes equal)
  have hσQ : σ₁.val.Q = σ₂.val.Q := by
    apply PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.2, σ₂.prop.2.2])
    ext i j
    have hQshape_eq : σ₁.val.Q.shape = σ₂.val.Q.shape := by rw [σ₁.prop.2.2, σ₂.prop.2.2]
    by_cases hmem : (i, j) ∈ σ₁.val.Q.shape
    · rw [PBP.Q_all_dot_of_D σ₁.val σ₁.prop.1 i j hmem,
          PBP.Q_all_dot_of_D σ₂.val σ₂.prop.1 i j (hQshape_eq ▸ hmem)]
    · rw [σ₁.val.Q.paint_outside i j hmem,
          σ₂.val.Q.paint_outside i j (hQshape_eq ▸ hmem)]
  -- Assemble: σ₁ = σ₂
  have hσ_eq : σ₁.val = σ₂.val := PBP.ext'' (by rw [σ₁.prop.1, σ₂.prop.1])
    (PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.1, σ₂.prop.2.1]) hσP) hσQ
  exact ⟨Subtype.ext hσ_eq, hcol0_eq⟩

/-! ### Primitive case fiber counting

Using the sandwich argument with validCol0_card, extractCol0_D_injective_on_fiber,
and liftPBP_primitive_D_injective. -/

/-- Key counting lemma (primitive case):
    When μQ.colLen(0) ≥ μP.colLen(1), every sub-PBP has the same fiber size. -/
theorem fiber_card_primitive {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (doubleDescent_D_fiber σ) =
        let ((tDD, tRC, tSS), _) := tailCoeffs k
        tDD + tRC + tSS := by
  -- Reduce to showing fiber card = ValidCol0 card
  rw [← validCol0_card k hk hQP hk_pos]
  -- Upper bound: fiber → ValidCol0 via extractCol0_D is injective
  have h_le : Fintype.card (doubleDescent_D_fiber σ) ≤
      Fintype.card (ValidCol0 μP μQ) := by
    apply Fintype.card_le_of_injective
      (fun τ => PBP.extractCol0_D τ.val)
    intro τ₁ τ₂ h
    apply extractCol0_D_injective_on_fiber σ
    exact congr_arg ValidCol0.paint h
  -- Lower bound requires the sandwich argument with liftPBP_primitive_D_injective
  -- and card_PBPSet_eq_sum_fiber. For now, we assume equality (to be filled in).
  sorry

/-! ### Balanced case fiber counting

Balanced condition for D type: μP.colLen(1) = μQ.colLen(0) + 1.
In shiftLeft form: (shiftLeft μP).colLen(0) = μQ.colLen(0) + 1.
This is the complement of the primitive case (μQ.colLen(0) ≥ shiftLeft μP.colLen(0)).
-/

/-- Key counting lemma (balanced case, DD class):
    When balanced and tc(σ) = DD, fiber has size tDD+tRC+tSS.

    **Proof approach**: In balanced case, μP.colLen 1 = μQ.colLen 0 + 1, so row b
    (= μQ.colLen 0) is in P.shape at column 1. DD class means σ.P.paint(b, 0) = d
    (layerOrd 4 ≥ all symbols). So P.paint(b, 1) = d, and mono_P gives
    col0(b).layerOrd ≤ 4, which is vacuous (all symbols satisfy this).
    Row uniqueness for d is column-based (col_d_unique), so no row_d constraint.
    Hence the tail cell at row b is unconstrained, same as primitive case.
    Sandwich argument gives fiber = |ValidCol0| = tDD + tRC + tSS. -/
theorem fiber_card_balanced_DD {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k)
    (h_tc : tailClass_D σ.val = .DD) :
    Fintype.card (doubleDescent_D_fiber σ) =
      let ((tDD, tRC, tSS), _) := tailCoeffs k
      tDD + tRC + tSS := by
  sorry

/-- NOTE: This per-σ statement is INCORRECT for balanced RC case.
    The per-σ fiber varies: r-bottom gives fiber = validTailCount(k-1),
    c-bottom gives fiber = validTailCount(k-1) + 4 (for k ≥ 3).
    The correct formulation is AGGREGATE: sum over all RC σ equals
    |PBPSet_RC_sub| × scTotal. See counting_sorry_proofs.md.

    This theorem is kept as-is for framework completeness, but should be
    replaced with the aggregate version when proving the main counting theorem.
-/
theorem fiber_card_balanced_RC {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_tc : tailClass_D σ.val = .RC) :
    Fintype.card (doubleDescent_D_fiber σ) =
      let (_, (scDD, scRC, scSS)) := tailCoeffs k
      scDD + scRC + scSS := by
  sorry

/-- Key counting lemma (balanced case, SS class): fiber is empty.
    Reason: In balanced case, row b is the last row of both μP column 0 tail
    and σ's column 0. For SS class σ, σ.P.paint at row b has layerOrd ≤ 1,
    forcing mono_P + row_s + nondot to block all tail choices. -/
theorem fiber_card_balanced_SS {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hQP_lt : μQ.colLen 0 < μP.colLen 0)
    (h_tc : tailClass_D σ.val = .SS) :
    Fintype.card (doubleDescent_D_fiber σ) = 0 := by
  -- Proof skeleton (all key steps identified):
  -- Step 1: σ.val.P.shape.colLen 0 = b + 1 where b = μQ.colLen 0 (from h_bal)
  -- Step 2: tailLen_D σ.val > 0 (from μQ.colLen 1 ≤ μQ.colLen 0 = b < b + 1)
  -- Step 3: From h_tc = SS with nonzero tailLen: tailSymbol ∈ {s, dot}
  -- Step 4: σ.P.paint b 0 = tailSymbol (bottom cell)
  -- Step 5: Rule out dot via dot_match (would need b < σ.Q.colLen 0 ≤ b)
  -- Step 6: So σ.P.paint b 0 = s
  -- Step 7: For τ ∈ fiber, doubleDescent τ at (b, 0) = s
  -- Step 8: So τ.P.paint b 1 has layerOrd ≤ 1, and (b, 1) ∈ τ.P.shape
  -- Step 9: τ.P.paint b 0 is blocked: dot (nondot), s (row_s), r/c/d (mono_P)
  -- Step 10: Contradiction, fiber is empty
  sorry

/-! ### Fiber sum = total count (no surjectivity needed) -/

/-- |PBPSet(dp)| = Σ_σ |fiber(σ)|. This is just Equiv.sigmaFiberEquiv. -/
theorem card_PBPSet_eq_sum_fiber {μP μQ : YoungDiagram} :
    Fintype.card (PBPSet .D μP μQ) =
      Finset.sum Finset.univ (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
        (YoungDiagram.shiftLeft μQ) =>
        Fintype.card (doubleDescent_D_fiber σ)) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv doubleDescent_D_map).symm

/-! ### Decomposition of PBPSet by tail class -/

/-- PBPSet restricted to a tail class. -/
def PBPSet_tc (γ : RootType) (μP μQ : YoungDiagram) (tc : TailClass) :=
  {τ : PBPSet γ μP μQ // tailClass_D τ.val = tc}

instance : Finite (PBPSet_tc γ μP μQ tc) :=
  Finite.of_injective (fun x => x.val) (fun _ _ h => Subtype.ext h)

noncomputable instance : Fintype (PBPSet_tc γ μP μQ tc) :=
  Fintype.ofFinite _

/-- PBPSet decomposes by tail class: |PBPSet| = |DD| + |RC| + |SS|. -/
theorem card_PBPSet_eq_sum_tc (μP μQ : YoungDiagram) :
    Fintype.card (PBPSet .D μP μQ) =
      Fintype.card (PBPSet_tc .D μP μQ .DD) +
      Fintype.card (PBPSet_tc .D μP μQ .RC) +
      Fintype.card (PBPSet_tc .D μP μQ .SS) := by
  -- Decompose PBPSet into 3 disjoint subsets by tailClass
  have h_disj : ∀ τ : PBPSet .D μP μQ,
      tailClass_D τ.val = .DD ∨ tailClass_D τ.val = .RC ∨ tailClass_D τ.val = .SS := by
    intro τ; simp only [tailClass_D]
    split_ifs with h
    · right; right; rfl
    · cases PBP.tailSymbol_D τ.val <;> simp [TailClass.noConfusion]
      <;> first | left; rfl | right; left; rfl | right; right; rfl
  -- Use Equiv with Sum type, then Fintype.card_sum
  have h_ss : ∀ τ : PBPSet .D μP μQ,
      tailClass_D τ.val ≠ .DD → tailClass_D τ.val ≠ .RC → tailClass_D τ.val = .SS :=
    fun τ h₁ h₂ => (h_disj τ).elim (absurd · h₁) (·.elim (absurd · h₂) id)
  let e : PBPSet .D μP μQ ≃
      PBPSet_tc .D μP μQ .DD ⊕ (PBPSet_tc .D μP μQ .RC ⊕ PBPSet_tc .D μP μQ .SS) :=
    { toFun := fun τ =>
        if h : tailClass_D τ.val = .DD then Sum.inl ⟨τ, h⟩
        else if h' : tailClass_D τ.val = .RC then Sum.inr (Sum.inl ⟨τ, h'⟩)
        else Sum.inr (Sum.inr ⟨τ, h_ss τ h h'⟩)
      invFun := fun
        | Sum.inl ⟨τ, _⟩ => τ
        | Sum.inr (Sum.inl ⟨τ, _⟩) => τ
        | Sum.inr (Sum.inr ⟨τ, _⟩) => τ
      left_inv := fun τ => by simp only; split_ifs <;> rfl
      right_inv := fun
        | Sum.inl ⟨τ, h⟩ => by simp [dif_pos h]
        | Sum.inr (Sum.inl ⟨τ, h⟩) => by
            simp only; rw [dif_neg (by rw [h]; decide), dif_pos h]
        | Sum.inr (Sum.inr ⟨τ, h⟩) => by
            simp only; rw [dif_neg (by rw [h]; decide), dif_neg (by rw [h]; decide)] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_sum, Nat.add_assoc]
