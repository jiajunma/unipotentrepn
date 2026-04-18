/-
# Basic Types for PBP Combinatorics

Reference:
  [BMSZ]  Barbasch–Ma–Sun–Zhu, "Special unipotent representations: construction and unitarity"
  [BMSZb] Barbasch–Ma–Sun–Zhu, "Special unipotent representations: counting and reduction"
-/
import Mathlib.Combinatorics.Young.YoungDiagram

/-! ## Root system type -/

/-- Root system type γ ∈ {B⁺, B⁻, C, D, M}.
    Reference: [BMSZb] Section 2.1.
    - B⁺, B⁻: real forms of SO(n)
    - C: symplectic Sp(2n)
    - D: even orthogonal SO(2n)
    - M: metaplectic Mp(2n), denoted C̃ in the papers -/
inductive RootType where
  | Bplus
  | Bminus
  | C
  | D
  | M
  deriving DecidableEq, Repr, BEq

/-! ## DRC symbols -/

/-- Symbols used in painted bipartitions.
    Reference: [BMSZb] Definition 2.25.
    - dot (•): shared between the two diagrams
    - s, r: real symbols (at most one each per row across both diagrams)
    - c: compact (at most one per column in each diagram)
    - d: discrete (at most one per column in each diagram) -/
inductive DRCSymbol where
  | dot  -- •
  | s
  | r
  | c
  | d
  deriving DecidableEq, Repr, BEq

instance : Fintype DRCSymbol where
  elems := {.dot, .s, .r, .c, .d}
  complete := fun x => by cases x <;> simp

namespace DRCSymbol

/-- Layer ordering on symbols: • < s < r < c < d.
    This ordering captures the layer structure in [BMSZ] Definition 3.1 (1):
    within each column of a painted Young diagram, symbols must appear
    in this order from top to bottom.

    Equivalently, for each k, the cells whose symbol has layerOrd ≤ k
    form a Young diagram (lower set in ℕ × ℕ). -/
def layerOrd : DRCSymbol → ℕ
  | .dot => 0
  | .s => 1
  | .r => 2
  | .c => 3
  | .d => 4

end DRCSymbol

/-! ## Diagram side -/

/-- Which side of the bipartition: left (P) or right (Q). -/
inductive Side where
  | L  -- left = P diagram
  | R  -- right = Q diagram
  deriving DecidableEq, Repr, BEq

/-! ## Allowed symbol sets

Reference: [BMSZb] Definition 2.25.

| γ       | P (left) symbols | Q (right) symbols |
|---------|------------------|-------------------|
| B⁺/B⁻  | {•, c}           | {•, s, r, d}      |
| C       | {•, r, c, d}     | {•, s}            |
| D       | {•, s, r, c, d}  | {•}               |
| M (=C̃)  | {•, s, c}        | {•, r, d}         |
-/

/-- Predicate: symbol σ is allowed for root type γ on side s.
    Reference: [BMSZb] Definition 2.25. -/
def DRCSymbol.allowed (γ : RootType) (s : Side) (σ : DRCSymbol) : Prop :=
  match γ, s with
  | .Bplus,  .L | .Bminus, .L => σ = .dot ∨ σ = .c
  | .Bplus,  .R | .Bminus, .R => σ = .dot ∨ σ = .s ∨ σ = .r ∨ σ = .d
  | .C,      .L => σ = .dot ∨ σ = .r ∨ σ = .c ∨ σ = .d
  | .C,      .R => σ = .dot ∨ σ = .s
  | .D,      .L => True  -- all five symbols allowed
  | .D,      .R => σ = .dot
  | .M,      .L => σ = .dot ∨ σ = .s ∨ σ = .c
  | .M,      .R => σ = .dot ∨ σ = .r ∨ σ = .d

instance (γ : RootType) (s : Side) (σ : DRCSymbol) :
    Decidable (DRCSymbol.allowed γ s σ) := by
  simp only [DRCSymbol.allowed]
  cases γ <;> cases s <;> exact inferInstance
