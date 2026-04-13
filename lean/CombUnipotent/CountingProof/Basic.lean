/-
# Counting Proof: Basic definitions (column lengths, dual-part → shape, shiftLeft)

Extracted from the monolithic `CountingProof.lean`.

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

/-! ## C-type column lengths

For C-type dp = [r₁, r₂, ...rest]:
  P cols = dpartColLensP_D (r₂ :: rest)  (same as D-type of tail)
  Q cols = [(r₁-1)/2] ++ dpartColLensQ_D (r₂ :: rest)  (prepend one Q column)

The C→D descent preserves P shape and shifts Q: shiftLeft(C-Q) = D-Q. -/

def dpartColLensP_C : DualPart → DualPart
  | [] => []
  | [_] => []
  | _ :: r₂ :: rest => dpartColLensP_D (r₂ :: rest)

def dpartColLensQ_C : DualPart → DualPart
  | [] => []
  | [r₁] => if r₁ > 1 then [(r₁ - 1) / 2] else []
  | r₁ :: r₂ :: rest =>
    if r₁ > 1 then (r₁ - 1) / 2 :: dpartColLensQ_D (r₂ :: rest)
    else dpartColLensQ_D (r₂ :: rest)

-- C [3,1]: P = dpartColLensP_D [1] = [1], Q = [(3-1)/2] = [1]
#eval dpartColLensP_C [3, 1]  -- [1]
#eval dpartColLensQ_C [3, 1]  -- [1]

-- C [5,3]: P = dpartColLensP_D [3] = [2], Q = [(5-1)/2] = [2]
#eval dpartColLensP_C [5, 3]  -- [2]
#eval dpartColLensQ_C [5, 3]  -- [2]

-- C [3,3]: P = [2], Q = [1]
#eval dpartColLensP_C [3, 3]  -- [2]
#eval dpartColLensQ_C [3, 3]  -- [1]

-- C [5,3,3]: P = dpartColLensP_D [3,3] = [2], Q = [2] ++ dpartColLensQ_D [3,3] = [2,1]
#eval dpartColLensP_C [5, 3, 3]  -- [2]
#eval dpartColLensQ_C [5, 3, 3]  -- [2, 1]

-- C [3,3,3]: P = [2], Q = [1,1]
#eval dpartColLensP_C [3, 3, 3]  -- [2]
#eval dpartColLensQ_C [3, 3, 3]  -- [1, 1]

-- C [1]: P = [], Q = [] (r₁=1, (1-1)/2=0, skip)
#eval dpartColLensP_C [1]  -- []
#eval dpartColLensQ_C [1]  -- []

-- C [3]: P = [], Q = [1]
#eval dpartColLensP_C [3]  -- []
#eval dpartColLensQ_C [3]  -- [1]

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
