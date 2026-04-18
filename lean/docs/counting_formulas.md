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

## Detailed Proofs

### Proof of Proposition 10.11 (D type)

**Claim**: For D-type orbit Ǒ = (r₁, r₂, ...) with good parity (all odd, total even):
```
(DD, RC, SS) = countPBP_D(Ǒ)
```
where DD = #{τ ∈ PBP_D(Ǒ,∅) : x_τ = d}, etc.

**Proof by strong induction on |Ǒ| (total size)**:

**Base case**: Ǒ = ∅. The only PBP is the empty one (trivial group SO(0)).
Its tail symbol is d by convention. So DD=1, RC=0, SS=0. ✓

**Inductive step**: Ǒ = (r₁, r₂, ...) with r₁ ≥ r₂ ≥ ...

By Prop 10.9 (D type, proved): the map τ ↦ (∇²τ, p_τ, q_τ, ε_τ)
is injective on PBP_D(Ǒ).

Here ∇² = ∇_C ∘ ∇_D is the double descent (D → C → D), landing at
PBP_D(Ǒ[2:]) where Ǒ[2:] = (r₃, r₄, ...).

**Step 1: Fiber counting.**

For each τ' ∈ PBP_D(Ǒ[2:]), count the number of τ ∈ PBP_D(Ǒ)
with ∇²τ = τ' (up to (p, q, ε) invariants).

The single descent ∇_D: PBP_D(Ǒ) → PBP_C(Ǒ[1:]) is characterized by
removing P's column 0 and redistributing. The fiber over a C-type PBP
is determined by the tail (column 0 data).

The double descent ∇_C ∘ ∇_D further descends from C to D.
Since C→D is injective (proved: descent_inj_CD), the fiber of ∇²
over τ' ∈ PBP_D(Ǒ[2:]) is the same as the fiber of ∇_D over the
unique C-type preimage of τ'.

**Step 2: Tail analysis.**

The tail of τ has k = (r₁ - r₂)/2 + 1 cells in P's column 0
beyond Q's column 0. The tail contains:
- Dots at the top (matching Q's dot diagram)
- Then non-dot symbols: s, r, c, d (in layerOrd order by monotonicity)

The tail symbol x_τ = paint of the LAST cell of the tail.

The tail painting determines (p_τ, q_τ, ε_τ) via:
- Signature: each symbol contributes to (p, q) with known weights
- Epsilon: ε = 0 iff d is in the tail (iff x_τ = d, since d is last by monotonicity)

**Step 3: Counting valid tails.**

Given ∇²τ = τ', the tail data (column 0 painting) must satisfy:
1. Layer monotonicity (symbols in order • < s < r < c < d)
2. Row uniqueness (at most one s/r per row, constrained by ∇τ)
3. Column uniqueness (at most one c, one d in column 0)

The number of valid tails with each tail symbol, evaluated at p=q=1:
- Tails with x_τ = d: count = TDD(k) = ν(k-1) + ν(k-2)
- Tails with x_τ ∈ {c, r}: count = TRC(k) = 2·ν(k-1)
- Tails with x_τ = s: count = TSS(k) = 1

These come from enumerating all valid layerOrd sequences of length k
with given last element, subject to column uniqueness.

**Step 4: Case split on (2,3) ∈ PP.**

**Case (a)**: r₂ > r₃ (primitive pair): every τ' ∈ PBP_D(Ǒ[2:]) contributes
equally. Total per τ' = TDD + TRC + TSS = (2k-1) + 2k + 1 = 4k.
But wait, the count depends on x_{τ'} (the tail symbol of τ').

Actually, for case (a), the C-type PBP at Ǒ[1:] is uniquely determined
by τ' (C→D injective, and every D-type PBP has a C-type preimage
when (1,2) is primitive). So the fiber of ∇² over τ' has exactly
TDD + TRC + TSS elements. And these are distributed as:
```
DD(τ') = TDD = ν(k-1) + ν(k-2)
RC(τ') = TRC = 2·ν(k-1)
SS(τ') = TSS = 1
```

Summing over all τ':
```
DD = (DD' + RC' + SS') · TDD
RC = (DD' + RC' + SS') · TRC
SS = (DD' + RC' + SS') · TSS
```
where (DD', RC', SS') = countPBP_D(Ǒ[2:]). ✓

**Case (b)**: r₂ = r₃ (balanced): the tail structure depends on x_{τ'}.
When x_{τ'} = d (DD' class): standard tail coefficients apply.
When x_{τ'} ∈ {c, r} (RC' class): "scattered" tail coefficients apply
(the tail interacts with τ' through the correction).
When x_{τ'} = s (SS' class): this doesn't contribute (the C-type
preimage doesn't exist when (1,2) is not primitive).

Wait, for case (b), (2,3) is balanced (r₂ = r₃). The C→D descent
from Ǒ[1:] to Ǒ[2:]: (1,2) for C type at Ǒ[1:] corresponds to
rows r₂, r₃. Since r₂ = r₃, (1,2) is NOT primitive. By Prop 10.12(b):
```
#PBP_C(Ǒ[1:]) = DD_D(Ǒ[2:]) + RC_D(Ǒ[2:])    (no SS contribution)
```

So the SS' class of PBP_D(Ǒ[2:]) does NOT lift to PBP_C(Ǒ[1:]).
Only DD' and RC' classes contribute.

For the DD' class: the correction at Ǒ[2:] level has x_{τ'} = d.
The tail coefficients are TDD, TRC, TSS as before.

For the RC' class: x_{τ'} ∈ {c, r}. The tail coefficients change
because the correction at the D level interacts with the tail.
The "scattered" coefficients are scDD, scRC, scSS.

```
DD = DD' · TDD + RC' · scDD
RC = DD' · TRC + RC' · scRC
SS = DD' · TSS + RC' · scSS
```

This gives the matrix multiplication formula. ✓

### Proof of Proposition 10.12 (C type)

**Claim**: For C-type orbit Ǒ:
```
#PBP_C(Ǒ) = DD + RC + SS    if (1,2) ∈ PP (r₁ > r₂)
#PBP_C(Ǒ) = DD + RC          if (1,2) ∉ PP (r₁ = r₂)
```
where (DD, RC, SS) = countPBP_D(Ǒ[1:]).

**Proof**:

By C→D descent injectivity (proved: descent_inj_CD):
∇_C : PBP_C(Ǒ) → PBP_D(Ǒ[1:]) is injective.

So #PBP_C(Ǒ) = #{τ' ∈ PBP_D(Ǒ[1:]) : τ' is in the image of ∇_C}.

**Case (a)**: (1,2) ∈ PP (r₁ > r₂).

Claim: every τ' ∈ PBP_D(Ǒ[1:]) has a preimage under ∇_C.

Proof: given τ' = (P', Q') of D type at Ǒ[1:], construct τ = (P, Q)
of C type at Ǒ with ∇_C(τ) = τ'.

Construction:
- Q column 0: length = (r₁ - 1)/2 + 1 (from orbit formula for C type).
  Top δ.colLen(0) rows are dots. Remaining rows (up to (r₁-1)/2) are s.
  Since (1,2) ∈ PP (r₁ > r₂), the number of s rows is positive.
- Q columns ≥ 1: from Q' (shifted back).
- P: determined by Q + Q' + redistribution formula.

The existence of this preimage for all τ' ∈ PBP_D(Ǒ[1:]) gives:
#PBP_C(Ǒ) = #PBP_D(Ǒ[1:]) = DD + RC + SS. ✓

**Case (b)**: (1,2) ∉ PP (r₁ = r₂).

Claim: τ' ∈ PBP_D(Ǒ[1:]) has a preimage iff x_{τ'} ≠ s.

Proof of "⟹": if τ has a preimage τ, then τ is C-type. The C→D
descent removes Q col 0. Q col 0 has (r₁-1)/2 dots + 0 s cells
(since r₁ = r₂, the excess is 0). So Q col 0 is all dots.

When Q col 0 is all dots, the redistribution _fill_ds_D produces:
P'(i, j) = P(i, j) for non-dot cells (no new s cells added).
This means the tail of τ' (= P' col 0) comes directly from P col 0,
which has no s (C type P has {•, r, c, d}). So x_{τ'} ≠ s. ✓

Proof of "⟸": if x_{τ'} ≠ s (x_{τ'} ∈ {c, d, r}), construct the
preimage. Since r₁ = r₂, Q col 0 has (r₁-1)/2 dots and 0 s cells.
The inverse redistribution works because no negative counts arise. ✓

So #PBP_C(Ǒ) = DD + RC (excluding SS). ✓

### Proof of Proposition 10.12 (M type)

Exactly symmetric to C type, with B replacing D:
- M→B descent is not fully injective (B type Q col 0 has non-trivial symbols).
  BUT: for counting purposes, the fiber structure is the same.
- (1,2) ∈ PP: every B-type PBP at Ǒ[1:] has an M-type preimage.
- (1,2) ∉ PP: only DD + RC classes contribute (SS excluded).

### Proof of Proposition 10.11 (B type)

Exactly symmetric to D type, with the M↔B pair replacing C↔D.
The tail is in Q (not P) since Q.colLen(0) ≥ P.colLen(0) for B type.

**Base case**: Ǒ = single row [r₁] or empty.
For empty: DD=0, RC=1, SS=1 (conventions for the trivial B-type PBP).
For [r₁]: c₁ = r₁/2. DD = 2·ν(c₁-1), RC = ν(c₁) + ν(c₁-1), SS = 1.

The total count for B type includes BOTH B⁺ and B⁻. The actual
#PBP_{B⁺}(Ǒ) = (DD + RC + SS) / 2 (they have equal count).

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
