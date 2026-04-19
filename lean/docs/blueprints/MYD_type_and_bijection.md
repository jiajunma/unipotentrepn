# MYD_γ(O) type + constructive bijection PBP_γ × Fin 2 ≃ MYD_γ(O)

**Status**: planning (2026-04-19)

**Goal**: Replace the current abstract wrappers
`prop_11_14/15/16/17_PBP_*` (which take an externally-supplied
`e : α ≃ β`) with a **concrete**, computable bijection between specific
Lean types. All algorithms in [BMSZ] / [BMSZb] are computable, so we
aim for `def` (not `noncomputable def`).

## Summary of the paper claim

For each root type γ and a quasi-distinguished nilpotent orbit O (of the
appropriate classical group), the paper asserts:

| γ | Source | Target | Map |
|---|---|---|---|
| D, B⁺, B⁻ | PBP_γ(Ǒ) × Fin 2 | MYD_γ(O) | (τ, ε) ↦ L_τ ⊗ (ε, ε) |
| C, C̃ (= M) | PBP_γ(Ǒ) | MYD_γ(O) | τ ↦ L_τ |

where `L_τ := AC.fold γ (descentChain τ)` unfolds the theta-lift chain
back from the trivial base.

## MYD_γ in the paper (Def. 9.3) vs. in Lean

**Paper**: `MYD_γ(O) := { E : ℕ⁺ → ℤ × ℤ | finiteSupport, parity, Sign(E) = Sign(O) }`

| γ | Parity constraint on E(i) = (p_i, q_i) |
|---|---|
| B, D | p_i = q_i ∈ ℕ for i even |
| C, C̃ | p_i = q_i ∈ ℕ for i odd |

**Lean** (already present): `ILS = List (ℤ × ℤ)` plays the role of a single
MYD, with `E(i+1) ≡ ILS.get i`. The existing formalization works entirely
with `ILS`.

**Lean** (to add): `MYD_γ(O) := { E : ILS // satisfiesMYDConstraints γ O E }`
where `satisfiesMYDConstraints` is a decidable predicate (so `MYD_γ(O)` is
computable and a `Fintype` when the orbit O is finite).

## The map Φ : PBP → ILS is already present

The AC chain computation `AC.fold γ (descentChain τ)` lives in
`MYD.lean:337` and returns `ACResult := List (ℤ × ILS)` (a ℤ-linear
combination of ILS's, not a single ILS).

**Key observation** (to be proved as a lemma):
for every τ ∈ PBP_γ(Ǒ), `AC.fold γ (descentChain τ)` is a **single-term**
list `[(1, E)]` with multiplicity 1. That single `E` is the MYD.

This follows inductively because:
- AC.base outputs a single-term list with multiplicity 1 (by definition)
- AC.step preserves "single-term, multiplicity 1" — theta-lift for special
  unipotent orbits yields exactly one MYD (paper §9.4, the multiplicity-1
  property of unipotent representations)

Call this lemma `AC_fold_singleton`. Once available, we extract
`L_τ : ILS` from `L_τ_combo : ACResult` by projecting out the unique term.

## MYD constraint: orbit-matching

`satisfiesMYDConstraints γ O E` is the conjunction of:
1. **Parity**: paper Def 9.3 (even/odd index parity depending on γ)
2. **Shape**: E's support corresponds to row lengths of O
3. **Signature**: `Sign_MYD(E) = Sign(O)` where Sign_MYD is the signature
   computation from Eq. 9.10

For orbit O of bounded size, `MYD_γ(O)` is a finite subset of a bounded
space of ILS's → computable `Fintype`.

## Constructive bijection proof strategy (per γ)

**Step 1**: Define the single-term projection
```
Phi_γ : PBP_γ(Ǒ) × Fin 2 → ILS
Phi_γ (τ, ε) := extractMYD (AC.fold γ (descentChain τ))
                  |> (if ε = 1 then twistBD (-1) (-1) else id)
```

**Step 2**: Prove `Phi_γ (τ, ε) ∈ MYD_γ(O)` for all (τ, ε). This uses:
- Parity preservation through AC.fold (already partly in MYD.lean)
- Signature preservation (existing sign-row lemmas)
- Shape correspondence (the paper's Sec 11.1 constraints)

**Step 3**: Prove injectivity of Phi_γ. Already done at the AC level
via `prop_11_12` (B/D) and `prop_11_17_injectivity` (C/M). Just port up.

**Step 4**: Counting equality
`|PBP_γ(Ǒ)| × 2 = |MYD_γ(O)|` (for D, B±) or `|PBP_γ(Ǒ)| = |MYD_γ(O)|`
(for C, M). **The PBP side is already formalized** in CountingProof/:
- `card_PBPSet_B/D_eq_countPBP_B/D` gives `|PBP_γ(Ǒ)| = countPBP_γ(Ǒ)`.
- For the MYD side, we'd need `|MYD_γ(O)| = 2 × countPBP_γ(Ǒ)` (or
  equal for C/M). This is new work — prove by constructive enumeration of
  MYDs satisfying the orbit's parity + signature constraints.

**Step 5**: Conclude bijectivity via Mathlib
`Fintype.equivOfInjectiveCardEq : Injective f → card α = card β → α ≃ β`
then convert to `Function.Bijective`. This is the same injective+counting
argument we already use, but now applied to the **concrete** Phi_γ, so
the resulting `Equiv` is an honest Lean term (not an unevaluated abstract
wrapper).

## Scope for first milestone (incremental approach)

- [ ] **M1.1**: Define `MYD_γ` predicate + type for γ ∈ {D, B⁺, B⁻, C, M}
      (start with one type, say D, to validate the design).
- [ ] **M1.2**: Prove `AC_fold_singleton`: `AC.fold γ (descentChain τ)` is
      single-term with multiplicity 1. Hard but self-contained.
- [ ] **M1.3**: Define `extractMYD : ACResult → Option ILS` (computable
      single-term projection), plus `Phi_γ` as a total map.
- [ ] **M1.4**: Prove `Phi_γ (τ, ε) ∈ MYD_γ(O)` (type-safe reformulation).
- [ ] **M1.5**: Prove `|MYD_D(O)| = 2 × countPBP_D(Ǒ)` (orbit-side
      counting — new work; may require a constructive enumeration of
      MYDs via the paper's SYD decomposition).
- [ ] **M1.6**: Concrete bijection `PBP_D(Ǒ) × Fin 2 ≃ MYD_D(O)`.

## Open questions for user

Before coding, need to confirm:

1. **Computability of `descentChain`**: current `descent` code uses
   `Classical` / `noncomputable def` in places. If we want
   `Phi_γ` computable we need to audit and replace where possible.
   If not feasible, accept `noncomputable def` for Phi and just aim for
   the bijection to exist (not evaluable).

2. **Scope of `MYD_γ(O)`**: do we want the **general** orbit version
   (parameterised by O) or a **PBP-indexed** version
   (`MYD_γ_of_PBP τ := { E : ILS | E is a valid MYD matching τ's orbit }`)?
   The latter avoids defining orbits separately and is more tractable as a
   starting point.

3. **Priority ordering**: D first, then B±, then C/M? Or prove a generic
   γ-parametric version? The parametric version is cleaner but more
   upfront abstraction work.
