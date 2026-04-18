/-
# Painted Bipartition (PBP)

Reference: [BMSZb] Definition 2.24–2.25; [BMSZ] Definition 3.1.

A painted bipartition (PBP) τ = (ι, P) × (j, Q) × γ consists of:
- Two Young diagrams ι and j (the shapes, forming a bipartition)
- Paintings P : cells(ι) → DRCSymbol and Q : cells(j) → DRCSymbol
- A root type γ ∈ {B⁺, B⁻, C, D, M}

The painting must satisfy five constraints:
1. Symbol sets are type-dependent ([BMSZb] Def 2.25)
2. P and Q have the same •-sub-diagram ([BMSZb] Def 2.3)
3. Layer monotonicity ↔ layer stripping ([BMSZ] Def 3.1 (1))
4. Row uniqueness for s, r ([BMSZ] Def 3.1 (2))
5. Column uniqueness for c, d ([BMSZ] Def 3.1 (3))
-/
import CombUnipotent.Basic

/-! ## Painted Young Diagram -/

/-- A painted Young diagram: a Young diagram μ with a painting function
    assigning a DRC symbol to each cell.

    The painting is extended to all of ℕ × ℕ by setting paint = • outside μ.
    This is a convention for cells not in the diagram; the mathematically
    meaningful painting is only on cells within the shape. -/
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

    Equivalent to the layer stripping condition [BMSZ] Def 3.1 (1):
    for each k, the cells with `layerOrd ≤ k` form a Young diagram (lower set). -/
def layerMonotone (D : PaintedYoungDiagram) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ ≤ i₂ → j₁ ≤ j₂ → (i₂, j₂) ∈ D.shape →
    (D.paint i₁ j₁).layerOrd ≤ (D.paint i₂ j₂).layerOrd

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
  /-- P and Q have identical •-sub-diagrams: a cell is a •-cell of P
      (i.e., in P.shape and painted •) iff it is a •-cell of Q.

      This replaces the earlier `∀ i j, P.paint i j = .dot ↔ Q.paint i j = .dot`
      which was too strong: for D type, Q is entirely •, and that formulation
      would force P to also be entirely •. The correct constraint only requires
      the •-cells *within each shape* to agree. -/
  dot_match : ∀ i j, ((i, j) ∈ P.shape ∧ P.paint i j = .dot) ↔
                      ((i, j) ∈ Q.shape ∧ Q.paint i j = .dot)

  -- (3) Layer monotonicity ↔ layer stripping: [BMSZ] Definition 3.1 (1)
  /-- P satisfies the layer ordering • < s < r < c < d. -/
  mono_P : P.layerMonotone
  /-- Q satisfies the layer ordering. -/
  mono_Q : Q.layerMonotone

  -- (4) Row uniqueness: [BMSZ] Definition 3.1 (2)
  /-- Each row has at most one cell painted `s`, across both P and Q combined. -/
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

/-! ## The dot sub-diagram -/

/-- The •-cells of a layer-monotone painted Young diagram form a Young diagram.

    `IsLowerSet` convention: `∀ a b, b ≤ a → a ∈ S → b ∈ S`.
    Here a = ⟨i₁, j₁⟩ ∈ S (a dot cell), b = ⟨i₂, j₂⟩ with b ≤ a.
    By monotonicity, paint(i₂,j₂).layerOrd ≤ paint(i₁,j₁).layerOrd = 0,
    so paint(i₂,j₂) = •. -/
def dotDiag (D : PaintedYoungDiagram) (hm : D.layerMonotone) : YoungDiagram where
  cells := D.shape.cells.filter fun c => D.paint c.1 c.2 = .dot
  isLowerSet := by
    -- IsLowerSet: ∀ a b, b ≤ a → a ∈ S → b ∈ S
    -- a = ⟨i₁, j₁⟩ (in set), b = ⟨i₂, j₂⟩ (to prove in set)
    -- hle : ⟨i₂, j₂⟩ ≤ ⟨i₁, j₁⟩, i.e., i₂ ≤ i₁ and j₂ ≤ j₁
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hle hmem
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hmem ⊢
    obtain ⟨hmem₁, hpaint₁⟩ := hmem
    refine ⟨D.shape.isLowerSet hle hmem₁, ?_⟩
    -- hm : i₂ ≤ i₁ → j₂ ≤ j₁ → (i₁, j₁) ∈ shape → layerOrd(i₂,j₂) ≤ layerOrd(i₁,j₁)
    have hle' := Prod.mk_le_mk.mp hle
    have hmono := hm i₂ j₂ i₁ j₁ hle'.1 hle'.2 hmem₁
    rw [hpaint₁, DRCSymbol.layerOrd] at hmono
    -- paint(i₂,j₂).layerOrd ≤ 0
    match h : D.paint i₂ j₂, hmono with
    | .dot, _ => rfl

/-- The dot sub-diagrams of P and Q are equal (from dot_match). -/
theorem dotDiag_eq (τ : PBP) : dotDiag τ.P τ.mono_P = dotDiag τ.Q τ.mono_Q := by
  ext ⟨i, j⟩
  simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
  exact τ.dot_match i j

/-! ## Shape constraints by type -/

/-- For D type: Q is entirely •, so Q.shape equals the dot sub-diagram. -/
theorem Q_all_dot_of_D (τ : PBP) (hγ : τ.γ = .D) (i j : ℕ) (h : (i, j) ∈ τ.Q.shape) :
    τ.Q.paint i j = .dot := by
  have := τ.sym_Q i j h
  rw [hγ] at this
  -- allowed D R σ ↔ σ = .dot
  simp [DRCSymbol.allowed] at this
  exact this

/-- For D type: Q.shape ≤ P.shape (Q is contained in P as Young diagrams).
    Proof: every cell of Q is • (by Q_all_dot_of_D), so by dot_match
    it is also a •-cell of P, hence in P.shape. -/
theorem Q_le_P_of_D (τ : PBP) (hγ : τ.γ = .D) : τ.Q.shape ≤ τ.P.shape := by
  intro ⟨i, j⟩ hmem
  have hq_dot := τ.Q_all_dot_of_D hγ i j hmem
  exact ((τ.dot_match i j).mpr ⟨hmem, hq_dot⟩).1

/-- For D type: Q.shape equals the dot diagram of P. -/
theorem Q_eq_dotDiag_of_D (τ : PBP) (hγ : τ.γ = .D) :
    τ.Q.shape = (dotDiag τ.P τ.mono_P) := by
  ext ⟨i, j⟩
  simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · intro hmem
    exact (τ.dot_match i j).mpr ⟨hmem, τ.Q_all_dot_of_D hγ i j hmem⟩
  · intro ⟨_, hp_dot⟩
    exact ((τ.dot_match i j).mp ⟨‹_›, hp_dot⟩).1

/-- For B⁺/B⁻ type: P has only {•, c}. Non-• cells in P are all c. -/
theorem P_nonDot_eq_c_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    (i j : ℕ) (h : (i, j) ∈ τ.P.shape) (hne : τ.P.paint i j ≠ .dot) :
    τ.P.paint i j = .c := by
  have hsym := τ.sym_P i j h
  rcases hγ with h₁ | h₁ <;> rw [h₁] at hsym <;> simp [DRCSymbol.allowed] at hsym <;> tauto

/-- For C type: Q has only {•, s}. Non-• cells in Q are all s. -/
theorem Q_nonDot_eq_s_of_C (τ : PBP) (hγ : τ.γ = .C)
    (i j : ℕ) (h : (i, j) ∈ τ.Q.shape) (hne : τ.Q.paint i j ≠ .dot) :
    τ.Q.paint i j = .s := by
  have := τ.sym_Q i j h
  rw [hγ] at this
  simp [DRCSymbol.allowed] at this
  tauto

/-! ## Descent type and direction -/

/-- The Howe dual type under descent.
    Reference: [BMSZ] Section 3.3.
    C ↔ D, B⁺ → M, B⁻ → M, M → B⁺ (default; actual B⁺/B⁻ determined by P). -/
def descentTargetType : RootType → RootType
  | .C => .D
  | .D => .C
  | .Bplus => .M
  | .Bminus => .M
  | .M => .Bplus  -- default; corrected to B⁻ when c ∈ first column of P

/-- Which side's first column is removed in descent.
    C, B⁺, B⁻: remove first column of Q (right).
    D, M: remove first column of P (left).
    Reference: [BMSZ] Section 3.3, Lemma 3.7. -/
def descentSide : RootType → Side
  | .C | .Bplus | .Bminus => .R
  | .D | .M => .L

end PBP
