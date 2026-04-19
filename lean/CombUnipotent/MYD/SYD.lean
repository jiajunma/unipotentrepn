/-
# Signed Young Diagram (SYD)

Reference: [BMSZ] arXiv:1712.05552, Definitions 9.1–9.8.

An SYD represents a nilpotent orbit O for a classical group of root type γ.
The combinatorial data assigns to each row length `i ∈ ℕ⁺` a pair
`(p_i, q_i) ∈ ℕ × ℕ` where `p_i + q_i` equals the number of rows of
length `i` in the underlying partition.

Parity constraints (paper Def 9.1):
- γ ∈ {B, D}: `p_i = q_i` is forced when `i` is even
- γ ∈ {C, C̃}: `p_i = q_i` is forced when `i` is odd

In Lean we use 0-indexed lists: `rows[j] = (p_{j+1}, q_{j+1})`.

Companion blueprint: `lean/docs/blueprints/MYD_type_and_bijection.md`.
-/
import CombUnipotent.Basic

namespace BMSZ

/-- γ-dependent parity condition: for which 1-indexed row lengths is
    `p_i = q_i` forced?

    - γ ∈ {B⁺, B⁻, D}: i even
    - γ ∈ {C, M = C̃}: i odd -/
def SYDParityForced (γ : RootType) (i : ℕ) : Prop :=
  match γ with
  | .Bplus | .Bminus | .D => i % 2 = 0
  | .C | .M => i % 2 = 1

instance (γ : RootType) (i : ℕ) : Decidable (SYDParityForced γ i) := by
  unfold SYDParityForced; cases γ <;> exact inferInstance

/-- A single row entry (p_i, q_i) is γ-valid at 1-indexed position `i`
    iff parity is satisfied: when parity is forced, p_i = q_i. -/
def SYDRowValid (γ : RootType) (i : ℕ) (pq : ℕ × ℕ) : Prop :=
  SYDParityForced γ i → pq.1 = pq.2

instance (γ : RootType) (i : ℕ) (pq : ℕ × ℕ) :
    Decidable (SYDRowValid γ i pq) := by
  unfold SYDRowValid; exact inferInstance

/-- **Signed Young Diagram** (paper Def 9.1) for root type γ.

    `rows[j]` holds the `(p, q)`-pair for row length `j + 1`. The tail of
    the list may contain `(0, 0)` entries (rows of that length absent).

    The validity predicate enforces γ-parity on each row entry. Totality
    of the partition is encoded implicitly via the list length.

    Decidable equality and a `Fintype` instance for bounded SYDs follow
    from the computable predicate. -/
structure SYD (γ : RootType) where
  rows : List (ℕ × ℕ)
  valid : ∀ (j : ℕ), (h : j < rows.length) → SYDRowValid γ (j + 1) rows[j]

namespace SYD

variable {γ : RootType}

/-- Two SYDs agree iff their row lists agree. -/
theorem ext {O₁ O₂ : SYD γ} (h : O₁.rows = O₂.rows) : O₁ = O₂ := by
  cases O₁; cases O₂; congr

/-- Underlying partition sum:
    `size O = Σ_{j = 0}^{length - 1} (j + 1) · (p_{j+1} + q_{j+1})`.
    This is the total number of boxes in the Young diagram. -/
def size (O : SYD γ) : ℕ :=
  (O.rows.zipIdx.foldr (fun ⟨pq, j⟩ s => s + (j + 1) * (pq.1 + pq.2)) 0)

/-- Total "positive" entries: `Σ (j + 1) · p_{j+1}` with the γ-specific
    weighting from paper Eq. (9.10). This is a helper toward `Sign`. -/
def totalP (O : SYD γ) : ℕ :=
  O.rows.zipIdx.foldr (fun ⟨pq, j⟩ s => s + (j + 1) * pq.1) 0

/-- Total "negative" entries: `Σ (j + 1) · q_{j+1}`. -/
def totalQ (O : SYD γ) : ℕ :=
  O.rows.zipIdx.foldr (fun ⟨pq, j⟩ s => s + (j + 1) * pq.2) 0

/-- The empty SYD (no rows) is γ-valid for any γ. -/
def empty (γ : RootType) : SYD γ :=
  ⟨[], fun j h => absurd h (by simp)⟩

theorem empty_rows : (empty γ).rows = [] := rfl
theorem empty_size : (empty γ).size = 0 := by
  unfold size empty; simp

end SYD

end BMSZ
