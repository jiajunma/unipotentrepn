# Recursive Counting Formulas: Propositions 10.11–10.14

Reference: [BMSZb] Section 10.6.

## Notation

For orbit Ǒ with dual partition (r₁, r₂, ...), define:
- `Ǒ[k:]` = orbit with dual partition `(r_{k+1}, r_{k+2}, ...)`
- PP_★(Ǒ) = primitive pairs
- (i, i+1) ∈ PP iff r_i > r_{i+1}

For ★ ∈ {B, D}: PBPs decompose by tail symbol x_τ ∈ {d, c∪r, s}:
- DD = #{τ : x_τ = d}
- RC = #{τ : x_τ ∈ {c, r}}
- SS = #{τ : x_τ = s}
- Total #PBP = DD + RC + SS

## Proposition 10.11: Recursive counting for D and B types

### Setup

Let Ǒ = (r₁, r₂, ...) with good parity for ★ ∈ {D, B}.
Define k = (r₁ - r₂)/2 + 1 (half the "excess" of the first row, plus 1).
Note k ≥ 1 since r₁ ≥ r₂.

### Tail polynomials (evaluated at p=q=1)

Define ν(n) = n + 1 for n ≥ 0, ν(n) = 0 for n < 0.

For type D:
```
TDD(k) = ν(k-1) + ν(k-2) = k + (k-1) = 2k-1     (for k ≥ 2)
TRC(k) = ν(k-1) + ν(k-1) = 2k                      (for k ≥ 1)
TSS(k) = 1
```

For the "scattered" variant (when (2,3) is balanced, i.e., r₂ = r₃):
```
scDD(k) = ν(k-2) + ν(k-2) = 2(k-1)                (for k ≥ 2)
scRC(k) = ν(k-1) + ν(k-2) = k + (k-1) = 2k-1      (for k ≥ 2)
scSS(k) = 1
```

### Statement (D type)

**Case (a)**: (2,3) ∈ PP (i.e., r₂ > r₃, or equivalently r₂ > r₃ ≥ 0):
```
(DD, RC, SS) = total_sub · (TDD, TRC, TSS)
```
where `total_sub = DD' + RC' + SS'` with `(DD', RC', SS') = countPBP_D(Ǒ[2:])`.

**Case (b)**: (2,3) ∉ PP (i.e., r₂ = r₃, "balanced"):
```
DD = DD' · TDD + RC' · scDD
RC = DD' · TRC + RC' · scRC
SS = DD' · TSS + RC' · scSS
```
where `(DD', RC', SS') = countPBP_D(Ǒ[2:])`.

**Base case**: Ǒ = ∅ (empty partition): (DD, RC, SS) = (1, 0, 0).

### Proof sketch (D type)

The descent ∇: PBP_D(Ǒ) → PBP_C(Ǒ[1:]) removes P's first column.
The double descent ∇²: PBP_D(Ǒ) → PBP_D(Ǒ[2:]).

By Prop 10.9 (D type): τ is determined by (∇²τ, p_τ, q_τ, ε_τ).
Equivalently: τ is determined by (∇τ, tail_data), where the C→D descent
is injective and the tail determines (p, q, ε).

The tail of τ has k cells in P's first column beyond Q. These cells
determine x_τ and the signature contribution. The tail polynomials
TDD, TRC, TSS count the number of valid tails with each tail symbol,
evaluated at p=q=1 (counting, not tracking signatures).

In case (a), (2,3) ∈ PP means the "next pair" starts fresh. The
descent reduces to Ǒ[2:], and each PBP at Ǒ[2:] generates
TDD + TRC + TSS tails. But only total_sub of them are valid PBPs.

In case (b), the balanced pair constrains the tail more. The DD'-class
PBPs generate tails with TDD/TRC/TSS counts, while the RC'-class
generates tails with scDD/scRC/scSS counts (the "scattered" variants).

### Statement (B type)

Identical structure to D type, with the same TDD/TRC/TSS formulas
(after evaluating at p=q=1). The base case is:
- Ǒ = single row [2c₁] or empty:
  DD = 2·ν(c₁-1), RC = ν(c₁) + ν(c₁-1), SS = 1

## Proposition 10.12: Counting for C and M types

### Statement (C type)

C → D descent is injective (Prop 10.9, C type). So:
```
#PBP_C(Ǒ) = #{τ' ∈ PBP_D(Ǒ[1:]) : τ' is in the image of ∇}
```

**Case (a)**: (1,2) ∈ PP (r₁ > r₂):
```
#PBP_C(Ǒ) = DD + RC + SS = #PBP_D(Ǒ[1:])
```
Every D-type PBP at Ǒ[1:] has a C-type preimage.

**Case (b)**: (1,2) ∉ PP (r₁ = r₂):
```
#PBP_C(Ǒ) = DD + RC
```
Only the D-type PBPs with x_τ ∈ {d, c, r} have C-type preimages.
Those with x_τ = s do not.

**Base case**: Ǒ = empty → #PBP_C = 0. Ǒ = single row → #PBP_C = 1.

### Proof sketch (C type)

For case (a): (1,2) ∈ PP means (1,2) is a primitive pair. The shape
shifting (Prop 10.8) provides additional PBPs via ℘ = {(1,2)}.
The descent from C to D maps each C-type PBP to a unique D-type PBP
(C→D is injective). Every D-type PBP has a preimage because the
primitive pair allows constructing the inverse.

For case (b): (1,2) ∉ PP means r₁ = r₂. The C-type PBPs with ℘ = ∅
map to D-type PBPs. But not every D-type PBP has a C-type preimage:
those with tail symbol s cannot be lifted back (the reconstruction
would require a negative s count, which is impossible).

### Statement (M type)

Identical structure to C type, with B replacing D:
```
#PBP_M(Ǒ) = DD + RC + SS    if (1,2) ∈ PP
#PBP_M(Ǒ) = DD + RC          if (1,2) ∉ PP
```
where (DD, RC, SS) = countPBP_B(Ǒ[1:]).

**Base case**: Ǒ = empty → #PBP_M = 1.

## Propositions 10.13–10.14 (generating functions)

These extend Props 10.11–10.12 to track the full generating function
f(p, q) = Σ p^{p_τ} q^{q_τ}, not just the count at p=q=1.

The formulas involve polynomial coefficients ν_k(p,q) instead of
ν(k) = k+1. At p=q=1, these reduce to Props 10.11–10.12.

For the initial formalization, we focus on the counting version
(p=q=1) as stated in Props 10.11–10.12.

## Formalization Plan

### In Lean

1. Define `DualPartition` as a decreasing list of positive naturals.
2. Define `goodParity(dpart, rtype)` predicate.
3. Define `primitivePair(dpart, i)` predicate.
4. Define `countPBP_D(dpart) : ℕ × ℕ × ℕ` (DD, RC, SS triple).
5. Define `countPBP_B(dpart) : ℕ × ℕ × ℕ`.
6. Define `countPBP_C(dpart) : ℕ`.
7. Define `countPBP_M(dpart) : ℕ`.
8. State Props 10.11–10.12 as: `countPBP_★(Ǒ) = #PBP_★(Ǒ, ∅)`.
9. Prove Props 10.11–10.12 using the descent injectivity theorems.

### Key dependencies

- Props 10.11–10.12 depend on Prop 10.9 (descent injectivity).
- Prop 10.9 depends on the recovery lemmas (descent_eq_implies_cols_ge1).
- The counting formulas also need the bijection between PBP sets
  (Prop 10.2: #PBP independent of ℘).

### What to prove vs what to define

The recursive formulas ARE the definitions (they define countPBP).
The theorem is that these match the actual count of PBPs.

Since we don't yet have a computable enumeration of PBPs in Lean
(that would require `dpart2drc`), we can:
- Define the recursive formulas.
- State the correctness theorem (formula = actual count).
- Prove the recursive STRUCTURE (showing how the count at Ǒ relates
  to the count at Ǒ[2:] via descent), using the descent theorems.
