/-
# Painted Bipartition (PBP)

Reference: [BMSZb] Definition 2.24–2.25; [BMSZ] Definition 3.1.

A painted bipartition (PBP) τ = (ι, P) × (j, Q) × γ consists of:
- Two Young diagrams ι and j (the shapes, forming a bipartition)
- Paintings P : cells(ι) → DRCSymbol and Q : cells(j) → DRCSymbol
- A root type γ ∈ {B⁺, B⁻, C, D, M}

The painting must satisfy five constraints:
1. Symbol sets are type-dependent ([BMSZb] Def 2.25)
2. P and Q paint the same cells with • ([BMSZb] Def 2.3)
3. Layer monotonicity ↔ layer stripping ([BMSZ] Def 3.1 (1))
4. Row uniqueness for s, r ([BMSZ] Def 3.1 (2))
5. Column uniqueness for c, d ([BMSZ] Def 3.1 (3))
-/
import CombUnipotent.Basic

/-! ## Painted Young Diagram -/

/-- A painted Young diagram: a Young diagram μ with a painting function
    assigning a DRC symbol to each cell.

    The painting is extended to all of ℕ × ℕ by setting paint = • outside μ.
    This simplifies cross-diagram comparisons (dot matching, row uniqueness). -/
structure PaintedYoungDiagram where
  /-- The underlying Young diagram (shape). -/
  shape : YoungDiagram
  /-- The painting function: assigns a symbol to each grid position. -/
  paint : ℕ → ℕ → DRCSymbol
  /-- Paint is • (dot) outside the shape. -/
  paint_outside : ∀ i j, (i, j) ∉ shape → paint i j = .dot

namespace PaintedYoungDiagram

/-- Layer monotonicity: within the shape, the layer order of symbols is
    non-decreasing when moving down (increasing row) or right (increasing column).

    This is equivalent to the layer stripping condition in [BMSZ] Definition 3.1 (1):
    for each k ∈ {0,1,2,3}, the set of cells with `layerOrd ≤ k` forms a Young diagram
    (i.e., is a lower set in ℕ × ℕ with the product order).

    **Proof of equivalence**:
    (⇒) If layerOrd is monotone and (i₂,j₂) has layerOrd ≤ k with (i₁,j₁) ≤ (i₂,j₂),
    then layerOrd(i₁,j₁) ≤ layerOrd(i₂,j₂) ≤ k.
    (⇐) Given (i₁,j₁) ≤ (i₂,j₂), let k = layerOrd(i₂,j₂). Then (i₂,j₂) is in the
    k-th sub-diagram. By lower set, so is (i₁,j₁), meaning layerOrd(i₁,j₁) ≤ k. -/
def layerMonotone (D : PaintedYoungDiagram) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ ≤ i₂ → j₁ ≤ j₂ → (i₂, j₂) ∈ D.shape →
    (D.paint i₁ j₁).layerOrd ≤ (D.paint i₂ j₂).layerOrd

/-- In a layer-monotone diagram, cells above-and-left of a shape cell
    are also in the shape (inherited from YoungDiagram.isLowerSet). -/
theorem mem_of_le_of_mem (D : PaintedYoungDiagram) {i₁ j₁ i₂ j₂ : ℕ}
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) (h : (i₂, j₂) ∈ D.shape) :
    (i₁, j₁) ∈ D.shape :=
  D.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) h

end PaintedYoungDiagram

/-! ## Selecting diagrams by side -/

/-- Select the paint function from a pair of painted diagrams by side. -/
def paintBySide (P Q : PaintedYoungDiagram) : Side → ℕ → ℕ → DRCSymbol
  | .L => P.paint
  | .R => Q.paint

/-! ## Painted Bipartition (PBP) -/

/-- A painted bipartition (PBP), also called a DRC diagram.

    Reference: [BMSZb] Definition 2.24–2.25; [BMSZ] Definition 3.1.

    The five constraint groups correspond to the mathematical conditions
    in the paper definitions. All are stated as Props (proof obligations). -/
structure PBP where
  /-- Root system type γ ∈ {B⁺, B⁻, C, D, M}. -/
  γ : RootType
  /-- Left painted diagram P (shape = ι). -/
  P : PaintedYoungDiagram
  /-- Right painted diagram Q (shape = j). -/
  Q : PaintedYoungDiagram

  -- (1) Symbol constraints: [BMSZb] Definition 2.25
  /-- Every cell of P is painted with a symbol allowed for (γ, left). -/
  sym_P : ∀ i j, (i, j) ∈ P.shape → (P.paint i j).allowed γ .L
  /-- Every cell of Q is painted with a symbol allowed for (γ, right). -/
  sym_Q : ∀ i j, (i, j) ∈ Q.shape → (Q.paint i j).allowed γ .R

  -- (2) Dot matching: [BMSZb] Definition 2.3 (1)
  /-- P and Q agree on which cells are painted •.
      Since paint = • outside each shape, this implies that non-• cells
      of one diagram lie within the shape of the other (see lemmas below). -/
  dot_match : ∀ i j, P.paint i j = .dot ↔ Q.paint i j = .dot

  -- (3) Layer monotonicity ↔ layer stripping: [BMSZ] Definition 3.1 (1)
  /-- P satisfies the layer ordering • < s < r < c < d from top-left to bottom-right. -/
  mono_P : P.layerMonotone
  /-- Q satisfies the layer ordering. -/
  mono_Q : Q.layerMonotone

  -- (4) Row uniqueness: [BMSZ] Definition 3.1 (2)
  /-- Each row has at most one cell painted `s`, across both P and Q combined.
      (Outside both shapes, paint = • ≠ s, so this constrains only cells in shapes.) -/
  row_s : ∀ i (s₁ s₂ : Side) (j₁ j₂ : ℕ),
    paintBySide P Q s₁ i j₁ = .s →
    paintBySide P Q s₂ i j₂ = .s →
    s₁ = s₂ ∧ j₁ = j₂
  /-- Each row has at most one cell painted `r`, across both P and Q combined. -/
  row_r : ∀ i (s₁ s₂ : Side) (j₁ j₂ : ℕ),
    paintBySide P Q s₁ i j₁ = .r →
    paintBySide P Q s₂ i j₂ = .r →
    s₁ = s₂ ∧ j₁ = j₂

  -- (5) Column uniqueness: [BMSZ] Definition 3.1 (3)
  /-- Each column of P has at most one `c`. -/
  col_c_P : ∀ j i₁ i₂, P.paint i₁ j = .c → P.paint i₂ j = .c → i₁ = i₂
  /-- Each column of Q has at most one `c`. -/
  col_c_Q : ∀ j i₁ i₂, Q.paint i₁ j = .c → Q.paint i₂ j = .c → i₁ = i₂
  /-- Each column of P has at most one `d`. -/
  col_d_P : ∀ j i₁ i₂, P.paint i₁ j = .d → P.paint i₂ j = .d → i₁ = i₂
  /-- Each column of Q has at most one `d`. -/
  col_d_Q : ∀ j i₁ i₂, Q.paint i₁ j = .d → Q.paint i₂ j = .d → i₁ = i₂

namespace PBP

/-! ## Basic consequences -/

/-- The bipartition (ι, j) = (P.shape, Q.shape). -/
def bipartition (τ : PBP) : YoungDiagram × YoungDiagram :=
  (τ.P.shape, τ.Q.shape)

/-- A cell painted non-• in P must lie within Q's shape.
    Proof: if (i,j) ∉ Q.shape then Q.paint = • (paint_outside),
    so P.paint = • (dot_match.mpr), contradicting the hypothesis. -/
theorem mem_Q_of_P_nonDot (τ : PBP) {i j : ℕ} (h : τ.P.paint i j ≠ .dot) :
    (i, j) ∈ τ.Q.shape := by
  by_contra h_not
  exact h ((τ.dot_match i j).mpr (τ.Q.paint_outside i j h_not))

/-- A cell painted non-• in Q must lie within P's shape. -/
theorem mem_P_of_Q_nonDot (τ : PBP) {i j : ℕ} (h : τ.Q.paint i j ≠ .dot) :
    (i, j) ∈ τ.P.shape := by
  by_contra h_not
  exact h (((τ.dot_match i j).mp (τ.P.paint_outside i j h_not)).symm ▸ rfl)

/-- The non-• cells of P are exactly the non-• cells of Q.
    This is a direct restatement of dot_match in contrapositive form. -/
theorem nonDot_iff (τ : PBP) (i j : ℕ) :
    τ.P.paint i j ≠ .dot ↔ τ.Q.paint i j ≠ .dot := by
  constructor
  · intro h
    exact fun hq => h ((τ.dot_match i j).mpr hq)
  · intro h
    exact fun hp => h ((τ.dot_match i j).mp hp)

end PBP
