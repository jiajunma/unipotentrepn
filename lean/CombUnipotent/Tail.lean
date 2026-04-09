/-
# Tail of a Painted Bipartition

Reference: [BMSZb] Section 10.5; [BMSZ] Section 11.2.

For ★ ∈ {B, D}, the **tail** of a PBP τ = (P, Q) consists of cells
in the first column of one diagram that extend beyond the other.

The **tail symbol** x_τ is the painting of the last cell of the tail.

**Proposition 10.9** ([BMSZb]): For ★ ∈ {B, D}, the map
  τ ↦ (∇τ, (p_τ, q_τ), ε_τ)
is injective on PBP_★(Ǒ).
-/
import CombUnipotent.Signature
import CombUnipotent.Descent

namespace PBP

/-! ## Tail for D type

For D type, Q ⊆ P (by `Q_le_P_of_D`).
The tail = cells in P's column 0 that are NOT in Q.
These are exactly the non-• cells in P's column 0
(since Q.shape = dotDiag(P) for D type). -/

/-- Tail cells for D type: non-Q cells in P's first column. -/
def tailCells_D (τ : PBP) : Finset (ℕ × ℕ) :=
  τ.P.shape.cells.filter fun c => c.2 = 0 ∧ c ∉ τ.Q.shape

/-- Tail length for D type. -/
def tailLen_D (τ : PBP) : ℕ :=
  τ.P.shape.colLen 0 - τ.Q.shape.colLen 0

/-- Tail cells are painted non-• in P.
    Proof: (i, 0) ∈ P.shape, (i, 0) ∉ Q.shape.
    If P.paint i 0 = •, then by dot_match (i, 0) ∈ Q.shape. Contradiction. -/
theorem tail_nonDot_D (τ : PBP) (hγ : τ.γ = .D) {c : ℕ × ℕ}
    (h : c ∈ tailCells_D τ) : τ.P.paint c.1 c.2 ≠ .dot := by
  simp only [tailCells_D, Finset.mem_filter, YoungDiagram.mem_cells] at h
  intro heq
  exact h.2.2 ((τ.dot_match c.1 c.2).mp ⟨h.1, heq⟩).1

/-! ## Tail for B type -/

/-- Tail cells for B type: non-P cells in Q's first column. -/
def tailCells_B (τ : PBP) : Finset (ℕ × ℕ) :=
  τ.Q.shape.cells.filter fun c => c.2 = 0 ∧ c ∉ τ.P.shape

/-- Tail length for B type. -/
def tailLen_B (τ : PBP) : ℕ :=
  τ.Q.shape.colLen 0 - τ.P.shape.colLen 0

/-! ## Tail symbol -/

/-- The tail symbol for D type: painting of the last cell of P's first column.
    When the tail is non-empty, this is a non-• symbol. -/
def tailSymbol_D (τ : PBP) : DRCSymbol :=
  τ.P.paint (τ.P.shape.colLen 0 - 1) 0

/-- The tail symbol for B type: painting of the last cell of Q's first column. -/
def tailSymbol_B (τ : PBP) : DRCSymbol :=
  τ.Q.paint (τ.Q.shape.colLen 0 - 1) 0

/-! ## Epsilon and tail symbol relationship

For D type: ε_τ = 0 iff d appears in P's first column.
By layer monotonicity, d is the bottom-most symbol (layerOrd 4).
So d in P's column 0 iff tailSymbol_D = d.

Similarly for B type with Q's column 0. -/

/-- For D type: d in P's column 0 implies the bottom cell is d (by monotonicity).
    If paint(i, 0) = d for some i < colLen, then paint(colLen-1, 0) = d
    because layerOrd is non-decreasing going down. -/
theorem d_at_bottom_of_col0_D (τ : PBP) (hγ : τ.γ = .D)
    {i : ℕ} (hi : i < τ.P.shape.colLen 0) (hd : τ.P.paint i 0 = .d) :
    τ.P.paint (τ.P.shape.colLen 0 - 1) 0 = .d := by
  -- By layer monotonicity: layerOrd(i, 0) ≤ layerOrd(colLen-1, 0)
  have hmono := τ.mono_P i 0 (τ.P.shape.colLen 0 - 1) 0
    (by omega) le_rfl
    (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  rw [hd, DRCSymbol.layerOrd] at hmono
  -- layerOrd(bottom) ≥ 4, so bottom = d
  revert hmono
  match τ.P.paint (τ.P.shape.colLen 0 - 1) 0 with
  | .d => intro _; rfl
  | .dot => simp [DRCSymbol.layerOrd]
  | .s => simp [DRCSymbol.layerOrd]
  | .r => simp [DRCSymbol.layerOrd]
  | .c => simp [DRCSymbol.layerOrd]

/-- For D type: the tail symbol is d iff d appears somewhere in P's column 0. -/
theorem tailSymbol_D_eq_d_iff (τ : PBP) (hγ : τ.γ = .D)
    (hne : 0 < τ.P.shape.colLen 0) :
    τ.tailSymbol_D = .d ↔
    ∃ i, i < τ.P.shape.colLen 0 ∧ τ.P.paint i 0 = .d := by
  constructor
  · intro h
    exact ⟨τ.P.shape.colLen 0 - 1, by omega, h⟩
  · rintro ⟨i, hi, hd⟩
    exact d_at_bottom_of_col0_D τ hγ hi hd

/-- For D type with non-empty column: ε_τ = 0 iff tailSymbol_D = d.
    Reference: [BMSZ] Equation (3.6) combined with [BMSZb] Section 10.5.

    For D type, Q is all dots, so 'd' never appears in Q's first column.
    Therefore ε_τ = 0 iff 'd' appears in P's first column iff tailSymbol_D = d. -/
theorem epsilon_zero_iff_tail_d_D (τ : PBP) (hγ : τ.γ = .D)
    (hne : 0 < τ.P.shape.colLen 0) :
    τ.epsilon = 0 ↔ τ.tailSymbol_D = .d := by
  simp only [PBP.epsilon, PaintedYoungDiagram.hasDInCol0]
  constructor
  · intro h
    -- ε = 0 means hasDInCol0 for P or Q
    -- Q is all dots for D type, so hasDInCol0_Q is false
    -- Therefore hasDInCol0_P is true: some cell (i, 0) ∈ P with paint = d
    sorry -- requires unfolding Finset.Nonempty and Bool logic
  · intro h
    -- tailSymbol = d means P.paint(colLen-1, 0) = d
    -- So hasDInCol0_P is true
    sorry -- requires constructing the witness in the Finset

/-! ## Proposition 10.9 ([BMSZb])

For ★ ∈ {B, D}: the map τ ↦ (∇τ, (p_τ, q_τ), ε_τ) is injective.

Equivalently: if two PBPs of the same type and orbit have the same
descent (painting on columns ≥ 1), same signature, and same epsilon,
they are equal.

The proof relies on showing that column 0 is determined by:
1. The dot part: fixed by the orbit (dot_match + shape).
2. The non-dot part (tail): determined by signature and epsilon.
   - The tail symbols must satisfy layer monotonicity (ordered).
   - Row/column uniqueness constrains them relative to columns ≥ 1 (from descent).
   - Signature determines the total counts of each symbol.
   - Epsilon determines whether d appears.
   Together these uniquely determine the tail painting. -/

/-- **Proposition 10.9** ([BMSZb]): Injectivity of descent + invariants.

    For D type, if two PBPs have:
    - Same shapes (same orbit)
    - Same painting on columns ≥ 1 (same descent)
    - Same signature
    - Same epsilon
    then they have the same painting on column 0 too (hence are equal). -/
theorem prop_10_9_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (hdescent_Q : ∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂)
    : ∀ i, τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  sorry

end PBP
