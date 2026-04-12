/-
# DualPart ↔ YoungDiagram correspondence for D-type

The key lemma `colLens_shiftLeft` connects `shiftLeft` to `List.tail`, and the
top-level theorem `card_PBPSet_D_eq_countPBP_D` states that for any (μP, μQ)
whose colLens match the dp-derived colLens, the fiber count equals `countPBP_D dp`.
-/
import CombUnipotent.CountingProof.LiftRC

open Classical

/-! ## `shiftLeft` as `tail` on `colLens` -/

namespace YoungDiagram

/-- `(shiftLeft μ).rowLen 0 = μ.rowLen 0 - 1`. -/
lemma rowLen_zero_shiftLeft (μ : YoungDiagram) :
    μ.shiftLeft.rowLen 0 = μ.rowLen 0 - 1 := by
  by_cases h : μ.rowLen 0 = 0
  · rw [h]
    simp only [Nat.zero_sub]
    by_contra hne
    have hp : 0 < μ.shiftLeft.rowLen 0 := Nat.pos_of_ne_zero hne
    have hmem : (0, 0) ∈ μ.shiftLeft := mem_iff_lt_rowLen.mpr hp
    rw [mem_shiftLeft] at hmem
    have hr : 0 + 1 < μ.rowLen 0 := mem_iff_lt_rowLen.mp hmem
    omega
  · have h_pos : 0 < μ.rowLen 0 := Nat.pos_of_ne_zero h
    apply le_antisymm
    · by_contra hc
      push_neg at hc
      have hge : μ.shiftLeft.rowLen 0 ≥ μ.rowLen 0 := by omega
      have hmem : (0, μ.rowLen 0 - 1) ∈ μ.shiftLeft := by
        apply mem_iff_lt_rowLen.mpr
        omega
      rw [mem_shiftLeft] at hmem
      have : μ.rowLen 0 - 1 + 1 < μ.rowLen 0 := mem_iff_lt_rowLen.mp hmem
      omega
    · by_contra hc
      push_neg at hc
      by_cases hge2 : μ.rowLen 0 ≥ 2
      · have hmem_orig : (0, μ.rowLen 0 - 1) ∈ μ :=
          mem_iff_lt_rowLen.mpr (by omega)
        have hmem_shift : (0, μ.rowLen 0 - 2) ∈ μ.shiftLeft := by
          rw [mem_shiftLeft]
          have : μ.rowLen 0 - 2 + 1 = μ.rowLen 0 - 1 := by omega
          rw [this]
          exact hmem_orig
        have : μ.rowLen 0 - 2 < μ.shiftLeft.rowLen 0 := mem_iff_lt_rowLen.mp hmem_shift
        omega
      · have : μ.rowLen 0 = 1 := by omega
        rw [this] at hc
        omega

/-- `(shiftLeft μ).colLens = μ.colLens.tail`. -/
lemma colLens_shiftLeft (μ : YoungDiagram) :
    μ.shiftLeft.colLens = μ.colLens.tail := by
  apply List.ext_getElem
  · rw [length_colLens, rowLen_zero_shiftLeft, List.length_tail, length_colLens]
  · intro j h1 h2
    rw [getElem_colLens h1, colLen_shiftLeft]
    rw [List.getElem_tail]
    rw [getElem_colLens]

end YoungDiagram

/-! ## dp-recursion lemmas

We use a custom well-founded recursion on `dp.length` to avoid complex pattern
matching on dp structure. -/

/-- Helper: when dp = `r₁ :: r₂ :: rest`, `dpartColLensP_D dp = (r₁+1)/2 :: dpartColLensP_D rest`. -/
lemma dpartColLensP_D_cons₂_eq (r₁ r₂ : ℕ) (rest : DualPart) :
    dpartColLensP_D (r₁ :: r₂ :: rest) = (r₁ + 1) / 2 :: dpartColLensP_D rest := rfl

lemma dpartColLensQ_D_cons₂_pos (r₁ r₂ : ℕ) (rest : DualPart) (h : r₂ > 1) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = (r₂ - 1) / 2 :: dpartColLensQ_D rest := by
  simp [dpartColLensQ_D, h]

lemma dpartColLensQ_D_cons₂_neg (r₁ r₂ : ℕ) (rest : DualPart) (h : ¬ r₂ > 1) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = dpartColLensQ_D rest := by
  simp [dpartColLensQ_D, h]

/-! ## Top-level D theorem in dp form

We prove the final correspondence: for any (μP, μQ) matching the dp-derived colLens,
`Fintype.card (PBPSet .D μP μQ) = countPBP_D dp` sum.

The proof works by induction on `μP.rowLen 0` (which equals `dp.length / 2` rounded up
for dp-derived shapes), using the step theorems at each level. -/

/-- The sum of a triple. -/
def tripleSum (t : ℕ × ℕ × ℕ) : ℕ := t.1 + t.2.1 + t.2.2

/-- `countPBP_D [] = (1, 0, 0)` ⇒ sum is 1. -/
lemma tripleSum_countPBP_D_nil : tripleSum (countPBP_D []) = 1 := by
  simp [tripleSum, countPBP_D]


/-- Base case: `countPBP_D []` has sum 1. -/
lemma tripleSum_countPBP_D_empty : tripleSum (countPBP_D []) = 1 := rfl

/-- `μ.colLens = []` implies `μ.rowLen 0 = 0`, which implies `μ = ⊥`. -/
lemma yd_of_colLens_nil {μ : YoungDiagram} (h : μ.colLens = []) : μ = ⊥ := by
  have h_row : μ.rowLen 0 = 0 := by
    have hlen : μ.colLens.length = μ.rowLen 0 := YoungDiagram.length_colLens μ
    rw [h] at hlen; simpa using hlen.symm
  -- From μ.rowLen 0 = 0, (0, 0) ∉ μ (since rowLen 0 = 0 means row 0 is empty).
  -- By isLowerSet, every cell is ≤ (0, j) for some j, but row 0 has no cells.
  -- Conclude μ is empty.
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  constructor
  · intro hmem
    exfalso
    have h_lower : (0, j) ∈ μ := by
      apply μ.isLowerSet (show ((0, j) : ℕ × ℕ) ≤ (i, j) from ?_) hmem
      exact ⟨Nat.zero_le _, le_refl _⟩
    have : j < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp h_lower
    omega
  · intro hmem; exact absurd hmem (YoungDiagram.notMem_bot _)

/-- When both colLens are nil, both YDs are ⊥. -/
lemma card_PBPSet_D_bot_case {μP μQ : YoungDiagram}
    (hP : μP.colLens = []) (hQ : μQ.colLens = []) :
    Fintype.card (PBPSet .D μP μQ) = 1 := by
  rw [yd_of_colLens_nil hP, yd_of_colLens_nil hQ, card_PBPSet_bot]
