/-
# `YoungDiagram.shiftLeft` card decrease

Small lemma: when column 0 is non-empty, `shiftLeft` strictly decreases
the cell count.

Motivation: this lemma is needed as the termination measure for
`exists_descentChain_D` (well-founded recursion on
`τ.P.shape.card + τ.Q.shape.card`).

Reference: `lean/docs/blueprints/Phase_B_axiom_codebase_mapping.md`.
-/
import CombUnipotent.CountingProof.Basic

namespace YoungDiagram

/-- The cells of `shiftLeft μ` are in bijection with the cells of `μ`
    in columns `≥ 1`. Hence `shiftLeft.cells.card = μ.cells.card − μ.colLen 0`. -/
theorem shiftLeft_cells_card (μ : YoungDiagram) :
    μ.shiftLeft.cells.card = μ.cells.card - μ.colLen 0 := by
  have h_image_card : μ.shiftLeft.cells.card =
      (μ.cells.filter (fun c => 0 < c.2)).card := by
    show ((μ.cells.filter (fun c => 0 < c.2)).image
      (fun c => (c.1, c.2 - 1))).card = _
    apply Finset.card_image_of_injOn
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    have hb₁ : 0 < b₁ := (Finset.mem_filter.mp h₁).2
    have hb₂ : 0 < b₂ := (Finset.mem_filter.mp h₂).2
    have hpair := Prod.ext_iff.mp heq
    have ha : a₁ = a₂ := hpair.1
    have hb_sub : b₁ - 1 = b₂ - 1 := hpair.2
    ext
    · exact ha
    · omega
  rw [h_image_card]
  -- Split cells: col > 0 vs col = 0, disjoint union = all cells.
  have h_disj : Disjoint
      (μ.cells.filter (fun c => 0 < c.2))
      (μ.cells.filter (fun c => c.2 = 0)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega
  have h_union : (μ.cells.filter (fun c => 0 < c.2)) ∪
      (μ.cells.filter (fun c => c.2 = 0)) = μ.cells := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hb : b = 0
      · exact Or.inr ⟨h, hb⟩
      · exact Or.inl ⟨h, Nat.pos_of_ne_zero hb⟩
  have h_sum := Finset.card_union_of_disjoint h_disj
  rw [h_union] at h_sum
  -- |filter .2 = 0| = colLen 0
  have h_col0 : (μ.cells.filter (fun c => c.2 = 0)).card = μ.colLen 0 := by
    rw [YoungDiagram.colLen_eq_card]
    -- Both sides are the same finset
    have h_eq : μ.cells.filter (fun c => c.2 = 0) = μ.col 0 := by
      ext ⟨a, b⟩
      simp [YoungDiagram.mem_col_iff]
    rw [h_eq]
  omega

/-- `μ.colLen 0 ≤ μ.cells.card`: the column-0 cells are a subset of all cells. -/
theorem colLen_zero_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.cells.card := by
  rw [YoungDiagram.colLen_eq_card]
  apply Finset.card_le_card
  intro c hc
  exact (YoungDiagram.mem_col_iff.mp hc).1

/-- If column 0 of `μ` is non-empty, `shiftLeft μ` has strictly fewer cells. -/
theorem shiftLeft_card_lt (μ : YoungDiagram) (h : 0 < μ.colLen 0) :
    μ.shiftLeft.cells.card < μ.cells.card := by
  rw [shiftLeft_cells_card]
  have h_ge := colLen_zero_le_card μ
  omega

/-- `shiftLeft.card ≤ card` unconditionally. -/
theorem shiftLeft_card_le (μ : YoungDiagram) :
    μ.shiftLeft.cells.card ≤ μ.cells.card := by
  rw [shiftLeft_cells_card]; omega

/-- `μ.colLen 0 = 0 ↔ μ = ⊥`.

    Forward: if column 0 is empty but cells exist, any cell `(i, j) ∈ μ`
    forces `(0, 0) ∈ μ` (down-set property), contradicting colLen 0 = 0.
    Reverse: ⊥ has no cells. -/
theorem colLen_zero_eq_zero_iff_empty (μ : YoungDiagram) :
    μ.colLen 0 = 0 ↔ μ = ⊥ := by
  constructor
  · intro h
    apply YoungDiagram.ext
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells]
    constructor
    · intro hmem
      -- (i, j) ∈ μ ⟹ (0, 0) ∈ μ ⟹ 0 < colLen 0, contradicting h
      have h₀ : (0, 0) ∈ μ := μ.isLowerSet (by simp : (0, 0) ≤ (i, j)) hmem
      rw [YoungDiagram.mem_iff_lt_colLen] at h₀
      omega
    · intro hbot
      simp at hbot
  · intro h
    subst h
    -- colLen of ⊥ at 0: Nat.find where (0, 0) ∉ ⊥ (vacuously)
    unfold YoungDiagram.colLen
    apply Nat.find_eq_zero _ |>.mpr
    simp

end YoungDiagram
