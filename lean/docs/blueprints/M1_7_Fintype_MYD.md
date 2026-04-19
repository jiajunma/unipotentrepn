# M1.7: `Fintype (MYD γ O)` + card equality theorems

**Milestone**: M1.7.

**Status**: natural-language draft (2026-04-19).

## Goal

Provide a `Fintype` instance for `MYD γ O` and use it to derive card
equalities:

- B/D: `|PBPSet γ μP μQ × Fin 2| = |MYD γ (dpToSYD γ dp)|`
- C/M: `|PBPSet γ μP μQ| = |MYD γ (dpToSYD γ dp)|`

Both follow from the respective Phi_γ_equiv Equivs via
`Fintype.card_congr`.

## Why MYD γ O is finite

`MYD γ O = { E : ILS // parity ∧ absValues E = O.rows }`.

- `ILS = List (ℤ × ℤ)` is infinite in general.
- But the MYD subtype bounds:
  - `E.length = O.rows.length` (forced by `absValues E = O.rows`,
    combined with `absValues_length`).
  - Each entry `E[j] = (p, q)` has `|p| + |q|` bounded by the row
    count at position `j+1` in O's partition.
    More specifically: `|p| = O.rows[j].1` and `|q| = O.rows[j].2`
    (from the absValues equality).
  - So each entry lies in a 2×2 × (±) space of size 4 (signs
    combinations) unless the entry is `(0, 0)`.

Concretely, for each row `j`, knowing `|p_j| = a` and `|q_j| = b`
(from O.rows[j] = (a, b)), the entry `(p_j, q_j) ∈ ℤ × ℤ` ranges over:
- if `a = 0 ∧ b = 0`: only `(0, 0)` — 1 choice
- if `a > 0 ∧ b = 0`: `(±a, 0)` — 2 choices
- if `a = 0 ∧ b > 0`: `(0, ±b)` — 2 choices
- if `a > 0 ∧ b > 0`: `(±a, ±b)` — 4 choices

Subject to the parity constraint (forcing p = q ≥ 0 at certain
indices, which fixes `(p_j, q_j) = (a, a)` there).

So `|MYD γ O|` is `≤ 4^{O.rows.length}`, finite.

## Strategy

### Approach A: via Equiv (preferred)

We already have `Phi_γ_equiv : PBPSet × Fin 2 ≃ MYD` (for B/D) or
`PBPSet ≃ MYD` (for C/M). PBPSet has a Fintype (existing in Lean
via the finiteness proofs in Section 10). We can then use
`Fintype.ofEquiv` to derive `Fintype (MYD γ O)`.

**Caveat**: this gives us a Fintype, but it's "backwards" — we know
MYD is finite because it's equivalent to a finite type. The
cardinality equality is then by definition (same Equiv).

This is the simplest path. Phase B for the Phi_γ_equiv will prove
the Equiv constructively; meanwhile we get the Fintype for free.

### Approach B: direct enumeration

Enumerate `{E | parity γ E ∧ absValues E = O.rows}` as a `Finset`
of bounded ILSs. More work but gives an explicit computable
enumeration without depending on the Equiv axioms.

**Decision**: Approach A for this milestone. When Phase B proofs
land for the Equivs, Approach A becomes fully grounded.

## Lean

```lean
namespace BMSZ

noncomputable instance {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp) :
    Fintype (MYD .D (dpToSYD .D dp)) :=
  Fintype.ofEquiv _ (Phi_D_equiv dp h_coh)

-- Similarly for Bplus, Bminus, C, M
```

Then card equalities:

```lean
theorem card_PBPSet_D_Fin2_eq_MYD (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp) :
    Fintype.card (PBPSet .D μP μQ × Fin 2) =
    Fintype.card (MYD .D (dpToSYD .D dp)) :=
  Fintype.card_congr (Phi_D_equiv dp h_coh)
```

## Review

### Pass 1: types

- `Fintype.ofEquiv : α → α ≃ β → Fintype β` requires Fintype α. 
  PBPSet × Fin 2 has Fintype (both factors do). ✓
- `Fintype.card_congr` returns `card α = card β` given `α ≃ β`. ✓

### Pass 2: paper

- Paper Prop 11.15 card content: `|PBPSet| × 2 = |MYD|`. Since
  `|Fin 2| = 2`, and `|α × β| = |α| × |β|`, we have
  `|PBPSet × Fin 2| = |PBPSet| × 2 = |MYD|`. ✓
- Paper Prop 11.17: `|PBPSet| = |MYD|`. ✓

### Pass 3: downstream

- This unlocks card-based reasoning for the MYD side, enabling
  future Phase B arguments (e.g., pigeonhole-style proofs of
  surjectivity).
- The Fintype instance is `noncomputable` because it's built on the
  `noncomputable` Phi_γ_equiv. Acceptable for math content.

**Verdict**: proceed.
