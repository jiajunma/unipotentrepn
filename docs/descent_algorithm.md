# Descent Algorithm for Painted Bipartitions

Reference: [BMSZ] arXiv:1712.05552v6, Section 3.3 (Definitions 3.8, 3.14; Lemmas 3.7, 3.10, 3.12).

## Setup

A painted bipartition is a triple τ = (ι, P) × (j, Q) × γ, where:
- (ι, P) and (j, Q) are painted Young diagrams
- γ ∈ {B⁺, B⁻, C, D, C̃} is the type label

Notation:
- ★_τ := B if γ ∈ {B⁺, B⁻}; otherwise ★_τ := γ
- c_i(ι) = i-th column length of ι (so c₁ is the longest column)
- r_i(Ǒ) = i-th row length of the orbit Ǒ
- P(i,j) = symbol at row i, column j of painting P (1-indexed)

In standalone.py: γ is the `rtype` parameter with values `'B+'`, `'B-'`, `'C'`, `'D'`, `'M'`.

## ε_τ (Equation 3.6)

```
ε_τ = 0  ⟺  symbol d occurs in the first column of (ι, P) or (j, Q)
```

In code terms: check if `'d'` appears in `drcL[0]` or `drcR[0]`.
If yes → ε_τ = 0; if no → ε_τ = 1.

## Step 1: Determine γ' (Equation 3.11)

The descended type γ' depends on γ:

```
γ' = ┌ B⁺,  if γ = C̃  and  c does NOT occur in first column of P
     │ B⁻,  if γ = C̃  and  c occurs in first column of P
     └ ★',  if γ ≠ C̃
```

where ★' is the Howe dual of ★:

| ★ (from) | ★' (to) | In code |
|----------|---------|---------|
| B (B⁺ or B⁻) | C̃ | `'M'` |
| C | D | `'D'` |
| D | C | `'C'` |
| C̃ (= M) | B | `'B+'` or `'B-'` |

**Key**: Only descent from M (= C̃) produces B⁺ vs B⁻. The distinction is:
- **B⁺** if `'c'` is NOT in P's first column (`drcL[0]`)
- **B⁻** if `'c'` IS in P's first column (`drcL[0]`)

Descent from B⁺ or B⁻ always goes to M.

## Step 2: Naive Descent (Lemma 3.7)

### Case (a): ★ ∈ {B, C} — remove first column of j (right diagram)

Applies when γ ∈ {B⁺, B⁻, C}.

Young diagram shapes:
```
(ι', j') = (ι, ∇_naive(j))
```
i.e., ι stays the same, j loses its first column.

Painting rules:
```
For (i,j) ∈ Box(ι'):
  P'(i,j) = ┌ • or s,   if P(i,j) ∈ {•, s}
             └ P(i,j),   if P(i,j) ∉ {•, s}       (r, c, d preserved)

For (i,j) ∈ Box(j'):
  Q'(i,j) = ┌ • or s,   if Q(i, j+1) ∈ {•, s}     (note: column shift by +1)
             └ Q(i, j+1), if Q(i, j+1) ∉ {•, s}    (r, c, d preserved from j+1)
```

In code: remove `drcR[0]`, shift Q columns left; r/c/d symbols are kept, •/s are
refilled to satisfy painting constraints (Definition 3.1).

### Case (b): ★ ∈ {C̃, D} — remove first column of ι (left diagram)

Applies when γ ∈ {M, D}.

Young diagram shapes:
```
(ι', j') = (∇_naive(ι), j)
```
i.e., ι loses its first column, j stays the same.

Painting rules:
```
For (i,j) ∈ Box(ι'):
  P'(i,j) = ┌ • or s,    if P(i, j+1) ∈ {•, s}    (note: column shift by +1)
             └ P(i, j+1),  if P(i, j+1) ∉ {•, s}   (r, c, d preserved from j+1)

For (i,j) ∈ Box(j'):
  Q'(i,j) = ┌ • or s,    if Q(i,j) ∈ {•, s}
             └ Q(i,j),    if Q(i,j) ∉ {•, s}        (r, c, d preserved)
```

In code: remove `drcL[0]`, shift P columns left; r/c/d symbols are kept, •/s are
refilled to satisfy painting constraints.

### "• or s" filling rule

After removing a column, the non-{•,s} symbols (r, c, d) are pinned. The •/s
positions are uniquely determined by the painting constraints (Definition 3.1):
1. Removing {d}, {c,d}, {r,c,d}, {s,r,c,d} must each leave a valid Young diagram
2. Each row has at most one s and at most one r
3. Each column has at most one c and at most one d

In practice, • and s fill the remaining cells so that the column lengths decrease
at each layer-stripping step. This is implemented by `_fill_ds_*` functions.

## Step 3: Corrections (Lemma 3.10 and 3.12)

### Lemma 3.10 — correction for γ = B⁺ only

Conditions (ALL must hold):
1. γ = B⁺
2. r₂(Ǒ) > 0  (orbit has at least 2 rows)
3. Q(c₁(ι), 1) ∈ {r, d}  (bottom cell of Q's first column is r or d)

Correction:
```
P'(c₁(ι'), 1) = s
```
i.e., set the bottom cell of P's first column in the descended diagram to `s`,
overriding whatever the naive descent produced.

All other cells use the naive descent values.

**This correction does NOT apply to B⁻.**

### Lemma 3.12 — correction for γ = D only

Conditions (ALL must hold):
1. γ = D
2. r₂(Ǒ) = r₃(Ǒ) > 0  (orbit rows 2 and 3 are equal and positive)
3. (P(c₂(ι), 1), P(c₂(ι), 2)) = (r, c)  (specific symbols at bottom of cols 1,2 of P)
4. P(c₁(ι), 1) ∈ {r, d}  (bottom cell of P's first column is r or d)

Correction:
```
P'(c₁(ι'), 1) = r
```
i.e., set the bottom cell of P's first column in the descended diagram to `r`,
overriding whatever the naive descent produced.

All other cells use the naive descent values.

## Step 4: Complete Descent (Definition 3.14)

```
∇(τ) = ┌ τ',       if conditions of Lemma 3.10 or 3.12 hold
        └ τ'_naive,  otherwise
```

where τ' is the corrected version from Lemma 3.10 or 3.12.

## Summary Table

| γ (from) | ★ | Which column removed | γ' (to) | Correction |
|----------|---|---------------------|---------|------------|
| B⁺ | B | j (right) | M | Lemma 3.10 (may apply) |
| B⁻ | B | j (right) | M | none |
| C | C | j (right) | D | none |
| D | D | ι (left) | C | Lemma 3.12 (may apply) |
| M (= C̃) | C̃ | ι (left) | B⁺ or B⁻ | none |

## Injectivity (Proposition 3.15)

- For ★ ∈ {C, C̃}: the map ∇ : PBP_★(Ǒ) → PBP_{★'}(Ǒ') is injective.
- For ★ ∈ {B, D}: the map τ ↦ (∇(τ), p_τ, q_τ, ε_τ) is injective.

This means:
- C and M descents are uniquely recoverable from the descended PBP alone.
- B and D descents require the additional data (p_τ, q_τ, ε_τ) to recover τ.

## Orbit Descent

The orbit also descends:
```
Ǒ' = ∇(Ǒ) = ┌ □ (single box),  if ★ ∈ {D} and |Ǒ| = 0
              └ ∇_naive(Ǒ),     otherwise (remove first row of Ǒ)
```

## PP Descent (Equation 3.15)

The primitive pairs descend as:
```
℘' = ∇̂(℘) = { (i, i+1) : i ∈ ℕ⁺, (i+1, i+2) ∈ ℘ } ⊆ PP_{★'}(Ǒ')
```
i.e., shift all indices down by 1, discard the pair (0,1) if it would appear.

## Examples from the Paper

### Example 3.9 (C̃ → B⁻)
Ǒ = (8, 6, 6, 6, 4, 4, 2), γ = C̃

```
τ = [•••c]  ×  [•••]  × C̃
    [•sc ]     [•rd]
    [sc  ]     [dd ]
    [c   ]
```

c occurs in first column of P (at rows 1,2,3,4) → γ' = B⁻

```
∇_naive(τ) = [••c]  ×  [•••]  × B⁻
             [•c ]     [•rd]
             [c  ]     [dd ]
```

(Naive descent = final descent, no Lemma 3.10 correction since γ' = B⁻.)

### Example 3.11 (B⁺ with Lemma 3.10 correction)
Ǒ = (4, 4, 2), γ = B⁺

```
τ = [•c]  ×  [•r]  × B⁺
    [c ]     [rd]
```

- r₂(Ǒ) = 4 > 0 ✓
- Q(c₁(ι), 1) = Q(2, 1) = r ∈ {r, d} ✓
- Lemma 3.10 applies!

```
τ'_naive = [sc]  ×  [r]  × C̃     ← naive: P'(2,1) would be c
           [c ]     [d]

τ' =       [sc]  ×  [r]  × C̃     ← corrected: P'(c₁(ι'), 1) = P'(2, 1) = s
           [s ]     [d]
```

### Example 3.13 (D with Lemma 3.12 correction)
Ǒ = (7, 7, 7, 3), γ = D

```
τ = [••]  ×  [••]  × D
    [•s]     [• ]
    [•s]     [• ]
    [rc]
```

- r₂(Ǒ) = r₃(Ǒ) = 7 > 0 ✓
- (P(c₂(ι), 1), P(c₂(ι), 2)) = (r, c) at the boundary row ✓
- P(c₁(ι), 1) ∈ {r, d} ✓
- Lemma 3.12 applies:
```
τ'_naive = [•]  ×  [•s]  × C     ← naive: P'(4,1) = c
           [•]     [• ]
           [•]     [• ]
           [c]

τ' =       [•]  ×  [•s]  × C     ← corrected: P'(c₁(ι'),1) = P'(4, 1) = r
           [•]     [• ]
           [•]     [• ]
           [r]
```
