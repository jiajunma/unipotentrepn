# MYD Computation from PBP via Descent Chain

Reference: [BMSZ] arXiv:1712.05552v6, Sections 9.3-9.5, 11.1-11.5.

## Overview

Given a painted bipartition τ ∈ PBP_★(Ǒ), the associated cycle L_τ ∈ Z[MYD_★(O)]
is computed by:
1. Computing the descent chain τ → τ' → τ'' → ... → τ_base
2. Starting from the base case L_{τ_base}
3. Lifting back up the chain using the theta lift ϑ̂

The BV dual orbit O = d^★_BV(Ǒ) is identified with a Young diagram in Nil(g_s).

## Marked Young Diagram (Definition 9.3)

A marked Young diagram of type ★ is a map E : N⁺ → Z × Z with finite support
(p_i = q_i = 0 for all but finitely many i) satisfying:

| ★ | Condition |
|---|----------|
| B, D | p_i = q_i ∈ N when i is even |
| C, C̃ | p_i = q_i ∈ N when i is odd |

The map V : Z × Z → N × N, (a,b) ↦ (|a|, |b|) sends MYD_★ to SYD_★.

## Signature of an MYD (9.10)

```
Sign(E) = (p, q) where
  (p, q) = Σ_{k≥1} (k·|p_{2k}| + k·|q_{2k}|, k·|p_{2k}| + k·|q_{2k}|)
          + Σ_{k≥1} (k·|p_{2k-1}| + (k-1)·|q_{2k-1}|, (k-1)·|p_{2k-1}| + k·|q_{2k-1}|)
```

This must equal the group signature (p_τ, q_τ) of the PBP τ.

## Four Operations on MYD (Section 9.4)

### (i) Sign Twist (9.15)

For ★ ∈ {B, D} and (ε⁺, ε⁻) ∈ Z/2Z × Z/2Z:
```
(E ⊗ (ε⁺, ε⁻))(i) =
  ┌ ((-1)^{(i+1)/2·ε⁺ + (i-1)/2·ε⁻} · p_i,
  │  (-1)^{(i-1)/2·ε⁺ + (i+1)/2·ε⁻} · q_i),    if i is odd;
  └ (p_i, q_i),                                    if i is even.
```

### (ii) Involution T (9.16)

For ★ ∈ {C, C̃}:
```
(TE)(i) = ┌ -E(i),     if i ≡ 2 (mod 4);
           └  E(i),     otherwise.
```
T is an involution: T² = identity.

### (iii) Augmentation (9.18)

For (p₀, q₀) ∈ N × N (or half-integers for C*, D*):
```
(E' ⊗ (p₀, q₀))(i) = ┌ (p₀, q₀),    if i = 1;
                        └ E'(i-1),      if i > 1.
```
Shifts all entries up by 1 and inserts (p₀, q₀) at level 1.

### (iv) Truncation Λ (9.19-9.20)

For E ∈ MYD_★ with E(1) = (p₁, q₁):

E ⊇ (p₀, q₀) requires:
```
  (p₁ ≥ p₀ ≥ 0  or  p₁ ≤ p₀ ≤ 0)  AND
  (q₁ ≥ q₀ ≥ 0  or  q₁ ≤ q₀ ≤ 0)
```

When E ⊇ (p₀, q₀):
```
(Λ_{(p₀,q₀)} E)(i) = ┌ E(1) - (p₀, q₀),   if i = 1;
                       └ E(i),                if i > 1.
```

## Signed Young Diagram of an Orbit (9.1-9.8)

For O ∈ Nil(p_s) with row lengths (r₁ ≥ r₂ ≥ ...) and real form O(p,q):

The SYD O assigns to each row length i a pair (p_{O,i}, q_{O,i}) where:
- p_{O,i} + q_{O,i} = number of rows of length i
- ★ ∈ {B, D}: p_i = q_i when i is even (forced equal)
- ★ ∈ {C, C̃}: p_i = q_i when i is odd (forced equal)

The free levels (odd for B/D, even for C/M) must be chosen so that
Sign(O) = (p, q) matches the group signature.

## ˡSign Computation (page 55)

For O' ∈ Nil(p_{s'}) with SYD entries O'(j) = (p'_j, q'_j):
```
ˡSign(O') = Σ_{i∈N⁺} (p'_{2i}, q'_{2i}) + Σ_{i∈N⁺} (q'_{2i-1}, p'_{2i-1})
```
Note the swap of (p, q) for odd indices.

### Computing O' via Lemma 9.2

Given O ∈ Nil(g_s), its descent O' = ∇^s_{s'}(O) is:
```
(p₀, q₀) = (p', q') - Sign(∇_naive(O))     ... (9.12)

O'(1) = O(2) + (p₀, q₀)
O'(i) = O(i+1)     for i ≥ 2
```
where ∇_naive(O)(i) = O(i+1) is the index-shifted SYD.

## Theta Lift Formulas

### Case ★ ∈ {B, D} — formula (9.29)

Given E' ∈ MYD_{★'}(O'), compute:
```
δ = c₁(O) - c₂(O)           ... from Lemma 4.4
(p₀, q₀) = (p, q) - (p', q') - ˡSign(O') + (δ/2, δ/2)

γ_T = ┌ (p_τt - q_τt)/2 + 1,    if ★ = B     ... (p_τt, q_τt) = tail signature
      └ (p_τt - q_τt)/2,         if ★ = D
```
But in practice, use the formula from (11.10):
```
γ_τ = ┌ (p_τt - q_τt)/2 + 1,   if ★ = B
      └ (p_τt - q_τt)/2,        if ★ = D
```
where (p_τt, q_τt) is the tail signature from Lemma 11.3.

Result:
```
ϑ̂(E') = (T^{γ_τ}(Λ_{(δ/2, δ/2)}(E'))) ⊗ (p₀, q₀)
```

### Case ★ ∈ {C, C̃} — formula (9.30)

Given E' ∈ MYD_{★'}(O'), compute:
```
δ = c₁(O) - c₂(O)
n₀ = δ/2 = (c₁(O) - c₂(O))/2

γ_T = ┌ (p' - q')/2,       if ★ = C
      └ (p' - q' - 1)/2,   if ★ = C̃
```

Result:
```
ϑ̂(E') = T^{γ_T}( Σ_{j=0}^{δ} Λ_{(j, δ-j)}(E') ⊗ (n₀, n₀) )
```

## Induction Formula (11.2)

For τ = (τ, ℘) ∈ PBP^ext_★(Ǒ), with ℘ = ∅ (special shape):

### Base case (|Ǒ| = 0)
```
L_τ = ┌ (1, 0)_★    if γ = B⁺
      │ (0, -1)_★   if γ = B⁻
      └ (0, 0)_★    otherwise  (empty MYD)
```

### Inductive case (|Ǒ| > 0)

Let τ' = ∇(τ), s_τ = (★, p_τ, q_τ), ε_τ from (3.6).

```
L_τ = ┌ ϑ̂(L_{τ'}) ⊗ (0, ε_τ),          if ★ ∈ {B, D}
      └ ϑ̂(L_{τ'} ⊗ (ε_℘, ε_℘)),        if ★ ∈ {C, C̃}
```

Since ℘ = ∅, we have ε_℘ = 0, so for C/C̃: L_τ = ϑ̂(L_{τ'}).

### Sign twist at the end

For ★ ∈ {B, D}: the ⊗ (0, ε_τ) is a sign twist applied AFTER the theta lift.
This only affects odd-level entries.

## Multiplicity and Splitting (Proposition 11.7)

- If r₂(Ǒ) > r₃(Ǒ) (quasi-distinguished at top): L_τ is a SINGLE MYD
  (the sum in (9.30) collapses to one term because truncation fails for others).

- If r₂(Ǒ) = r₃(Ǒ): L_τ = L_{τ,+} + L_{τ,-} (sum of two MYDs).
  Both are computed via (11.13) and (11.14).

## Delta Computation (Lemma 4.4)

For O ∈ Nil(g_s) with BV dual O = d^★_BV(Ǒ):
```
δ = |s'| - |∇_naive(O)| = c₁(O) - c₂(O)
```

Alternatively, from the orbit Ǒ directly:
- For ★ ∈ {B, D}: δ = r₁(Ǒ) - r₂(Ǒ) (when (1,2) is primitive) or
                    δ = 0 (when (1,2) is balanced, i.e. r₁ = r₂)
  More precisely: δ equals the difference of the first two column lengths of the
  BV dual orbit O.

## Implementation Notes

- The descent chain can be computed once and cached.
- For each step in the chain, we need: (drc, rtype, (p,q), ε, dpart).
- The theta lift operates on Z[MYD], but for quasi-distinguished orbits, each
  step produces at most 1 MYD term (the truncation sum has only 1 valid term).
- For the balanced case (r₂ = r₃), the splitting produces 2 terms.
- Python's `functools.lru_cache` can cache the descent chain and BV duals.
- The lift tree visualization shows the full descent chain with MYD at each level.
