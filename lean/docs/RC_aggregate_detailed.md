# Detailed informal proof: `fiber_card_balanced_RC_aggregate`

Every step must be trivial equality substitution. This document is the formalization-ready
reference for all remaining RC-aggregate proofs.

## Setup

- `μP, μQ : YoungDiagram` with `k := μP.colLen 0 - μQ.colLen 0 ≥ 1`
- `b := μQ.colLen 0`, `c := μP.colLen 0`
- Balanced hypothesis `h_bal : (shiftLeft μP).colLen 0 = b + 1`
  — equivalently, `μP.colLen 1 = b + 1`.
- Sub PBP set: `PBPSet_sub := PBPSet .D (shiftLeft μP) (shiftLeft μQ)`.
- For `σ : PBPSet_sub`, its P-shape has `colLen 0 = b + 1`.
- `σ.val.Q.shape.colLen j ≤ σ.val.Q.shape.colLen 0 ≤ b`, so any `(b, j) ∉ σ.val.Q.shape`.
- Hence by `dot_match`, `(b, j) ∈ σ.val.P.shape` forces `σ.val.P.paint b j ≠ .dot`.

### Sub-classes

- `R_sub := {σ : σ.val.P.paint b 0 = .r}`
- `C_sub := {σ : σ.val.P.paint b 0 = .c}`
- `RC_sub := R_sub ⊔ C_sub` (disjoint by value at (b, 0))

### Goal

```
Σ_{σ ∈ RC_sub} |fiber σ| = |RC_sub| · scTotal
```

where `scTotal := scDD + scRC + scSS` = the second triple of `tailCoeffs k`,
and `fiber σ := {τ ∈ PBPSet .D μP μQ | ∇²τ = σ}`.

Numerical table:

| k   | scDD    | scRC   | scSS | scTotal |
|-----|---------|--------|------|---------|
| 1   | 0       | 1      | 1    | 2       |
| 2   | 2       | 3      | 1    | 6       |
| ≥3  | 2(k−1)  | 2k−1   | 1    | 4k−2    |

## Structural facts we already have

(From `Swap.lean`.)

1. **`r_bottom_row_b_ge_j_in_cd`**: if `σ.val.P.paint b 0 = .r`, then for all
   `j ≥ 1`, `σ.val.P.paint b j ∈ {.c, .d, .dot}`.

2. **`c_bottom_row_b_ge_j_in_cd`**: if `σ.val.P.paint b 0 = .c`, then for all
   `j ≥ 1`, `σ.val.P.paint b j ∈ {.c, .d, .dot}`.

3. **`r_sub_card_eq_c_sub_card` (Phase 1)**: `|R_sub| = |C_sub|`.

## Lemma 0: row-b exclusion of `.dot` inside σ.P.shape

**Claim.** If `(b, j) ∈ σ.val.P.shape`, then `σ.val.P.paint b j ≠ .dot`.

**Proof.** Suppose `σ.val.P.paint b j = .dot`. By `dot_match`,
`(b, j) ∈ σ.val.Q.shape`, i.e., `b < σ.val.Q.shape.colLen j`. But
`σ.val.Q.shape.colLen j ≤ σ.val.Q.shape.colLen 0 ≤ b`, contradiction. ∎

## Lemma 0': row-b-heavy

**Claim.** For `σ ∈ R_sub ∪ C_sub`, and `j ≥ 1` with `(b, j) ∈ σ.val.P.shape`,
`σ.val.P.paint b j.layerOrd ≥ 3`.

**Proof.** By r/c_bottom_row_b_ge_j_in_cd, `σ.val.P.paint b j ∈ {.c, .d, .dot}`.
By Lemma 0, inside-shape rules out `.dot`. So `∈ {.c, .d}`, layer ∈ {3, 4} ≥ 3. ∎

## Lemma 0'': tail-dot

**Claim.** For any σ (in particular for σ ∈ RC_sub), and any `i > b`,
`σ.val.P.paint i j = .dot` for all j.

**Proof.** `σ.val.P.shape.colLen j ≤ σ.val.P.shape.colLen 0 = b + 1`, so for
`i > b`, `(i, j) ∉ σ.val.P.shape`, and `paint_outside` gives `.dot`. ∎

---

## Lemma R (aka Lemma 1): fiber size for σ ∈ R_sub

### Statement

Define `X_r(k)`:
- `k = 1`: `X_r = 1`
- `k ≥ 2`: `X_r = 4(k-1)`

**Claim.** For σ ∈ R_sub, `|fiber σ| = X_r(k)`.

### Characterization of the fiber

**Claim R.1.** For any `τ ∈ fiber σ`, the col-0 column `col0 := λ i. τ.P.paint i 0`
satisfies:

(a) `col0` is a valid `ValidCol0 μP μQ` (from the definition of `extractCol0_D`).

(b) `col0(b) = .s` (forced).

**Proof of (b).** Since `∇²τ = σ`, by the ∇² formula:
`σ.val.P.paint b 0 = PBP.doubleDescent_D_paintL τ.val b 0`.

Unfolding `doubleDescent_D_paintL` at `(b, 0)`:
- The "dot zone" check: `b < τ.Q.shape.colLen (0+1) = μQ.colLen 1 ≤ μQ.colLen 0 = b`. False.
- The "s zone" check: `b < dotScolLen τ.P 1`. If true, the function returns `.s`, not `.r`.
  So it must be false.
- Else branch: returns `τ.P.paint b 1`. So `τ.P.paint b 1 = .r`.

Now examine `col0(b) = τ.P.paint b 0`:

1. **Layer bound from `mono_P`**: `(b, 0) ≤ (b, 1)`, `(b, 1) ∈ τ.P.shape`
   (since `b < μP.colLen 1 = b+1`). So
   `layerOrd col0(b) ≤ layerOrd τ.P.paint b 1 = layerOrd .r = 2`.
   Hence `col0(b) ∈ {.dot, .s, .r}`.

2. **Non-dot from `ValidCol0.nondot_tail`**: `μQ.colLen 0 ≤ b < μP.colLen 0`,
   so `col0(b) ≠ .dot`.

3. **Exclude `.r` via `row_r`**: τ has `.r` at `(b, 1)` (derived above). If
   `col0(b) = .r`, then τ has two `.r` in row b (at columns 0 and 1), violating
   `row_r`. So `col0(b) ≠ .r`.

Combining: `col0(b) = .s`. ∎

### Claim R.2 (reverse): every valid col0 with col0(b) = .s extends

For any `v : ValidCol0 μP μQ` with `v.paint b = .s`, there exists a unique
`τ ∈ fiber σ` with `extractCol0_D τ = v`.

**Construction.** Define
```
τ.P.paint := liftPaint_D σ.val v.paint
-- i.e., τ.P.paint i 0 = v.paint i
--       τ.P.paint i (j+1) = σ.val.P.paint i j
τ.Q := { shape := μQ, paint := fun _ _ => .dot }
τ.P.shape := μP
τ.γ := .D
```

The 13 constraints are verified below (see "Lift validity for R/C").

**Uniqueness.** If `τ' ∈ fiber σ` has `extractCol0_D τ' = v`, then `τ'.P.paint i 0 = v.paint i`
and `τ'.P.paint i (j+1) = (∇²τ').P.paint i j = σ.val.P.paint i j`, so `τ'.P.paint = τ.P.paint`.
Combined with `τ'.P.shape = μP` and `τ'.Q = τ.Q = all-dots`, `τ' = τ`. ∎

### Lift validity for σ ∈ R_sub, v with v.paint b = .s

Using the structural facts (Lemmas 0, 0', 0'' above).

1. **`sym_P`**: D/L allows all symbols. Trivial. ✓
2. **`sym_Q`**: Q-paint is all .dot, which is allowed. ✓
3. **`dot_match`** at `(i, j)`:
   - **`j = 0`**: LHS `(i, 0) ∈ μP ∧ v.paint i = .dot`; RHS `(i, 0) ∈ μQ ∧ .dot = .dot`.
     - → direction: `v.paint i = .dot` means `i < μQ.colLen 0 = b` (from nondot_tail contrapositive),
       so `(i, 0) ∈ μQ`.
     - ← direction: `(i, 0) ∈ μQ`, i.e., `i < μQ.colLen 0 = b`, so `v.paint i = .dot` (dot_below).
   - **`j ≥ 1`**: LHS reduces to `(i, j) ∈ μP ∧ σ.val.P.paint i (j-1) = .dot`.
     `(i, j) ∈ μP ⟺ (i, j-1) ∈ shiftLeft μP = σ.val.P.shape`. Similarly RHS.
     Apply `σ.val.dot_match i (j-1)`. ✓
4. **`mono_P`**: split by `j₁`:
   - **`j₁ = 0, j₂ = 0`**: `v.mono i₁ i₂ hi hmem`. ✓
   - **`j₁ = 0, j₂ = j₂' + 1 ≥ 1`**:
     - If `i₁ < b`: `v.paint i₁ = .dot`, layer 0 ≤ anything. ✓
     - If `i₁ ≥ b`: from `(i₂, j₂'+1) ∈ μP`, `i₂ < μP.colLen (j₂'+1) ≤ μP.colLen 1 = b+1`,
       so `i₂ ≤ b`. With `i₁ ≤ i₂ ≤ b` and `i₁ ≥ b`, `i₁ = i₂ = b`.
       Need: `layerOrd v.paint b ≤ layerOrd σ.val.P.paint b j₂'`.
       - `v.paint b = .s`, layer 1.
       - If `j₂' = 0`: `σ.val.P.paint b 0 = .r`, layer 2. `1 ≤ 2`. ✓
       - If `j₂' ≥ 1`: Lemma 0' gives layer ≥ 3 (with `(b, j₂') ∈ σ.val.P.shape` from
         `(b, j₂'+1) ∈ μP ⟺ (b, j₂') ∈ shiftLeft μP = σ.P.shape`). `1 ≤ 3`. ✓
   - **`j₁ ≥ 1, j₂ ≥ 1`**: `σ.val.mono_P` with shifted indices. ✓
   - **`j₁ ≥ 1, j₂ = 0`**: contradicts `j₁ ≤ j₂`. Vacuous.
5. **`mono_Q`**: Q is all dots, trivially monotone. ✓
6. **`row_s`** at row `i`:
   - Cases by sides `(s₁, s₂) ∈ {(L,L), (L,R), (R,L), (R,R)}`.
   - R side has `.s` ⟹ Q-paint `.s`, impossible (Q all dots). Contradiction via `h₂`.
   - L-L case: `τ.P.paint i j_k = .s` for k=1,2.
     - **`j₁ = 0`**: `h₁ : v.paint i = .s`. Then `i ∉ [0, b)` (else .dot ≠ .s), so `i ≥ b`.
       - **`j₂ = 0`**: trivial, `j₁ = j₂ = 0`, done.
       - **`j₂ = j₂' + 1`**: `h₂ : σ.val.P.paint i j₂' = .s`.
         - `i > b`: Lemma 0'' gives `σ.val.P.paint i j₂' = .dot ≠ .s`. Contradiction.
         - `i = b`:
           - `j₂' = 0`: `σ.val.P.paint b 0 = .r ≠ .s`. Contradiction.
           - `j₂' ≥ 1`: `σ.val.P.paint b j₂'.layerOrd ≥ 3` (Lemma 0' if in shape; otherwise .dot).
             If in shape, `.s` has layer 1, but paint has layer ≥ 3, contradiction.
             If outside shape, `.dot ≠ .s`, contradiction.
     - **`j₁ = j₁' + 1`**: symmetric.
     - **`j₁ ≥ 1, j₂ ≥ 1`**: `σ.val.row_s i L L j₁' j₂'` gives `j₁' = j₂'`, so `j₁ = j₂`. ✓
7. **`row_r`** at row `i`:
   - R side: same as row_s, Q is all dots, no .r. Contradiction via Q-paint.
   - L-L: similar to row_s with `.r` instead of `.s`.
     - **`j₁ = 0`**: `h₁ : v.paint i = .r`. Then `i ≥ b`.
       - **`i = b`**: `v.paint b = .s ≠ .r`. Contradiction with `h₁`.
       - **`i > b`**: `v.paint i` could potentially be `.r` (any TSeq entry).
         - **`j₂ = 0`**: `h₂ : v.paint i' = .r` for `i' = i` in other interpretation?
           Wait, row_r is same row `i`, just different columns. So `j₁ = 0, j₂ = 0` gives `j₁ = j₂`, trivial.
         - **`j₂ = j₂' + 1 ≥ 1`**: `h₂ : σ.val.P.paint i j₂' = .r`.
           - `i > b`: Lemma 0'' gives `.dot ≠ .r`. Contradiction.
     - **`j₁ = j₁' + 1 ≥ 1`**: symmetric.
     - **`j₁ ≥ 1, j₂ ≥ 1`**: `σ.val.row_r`. ✓
8. **`col_c_P`** at column `j`:
   - `j = 0`: `h_k : v.paint i_k = .c`. Then `v.col_c_unique` gives `i₁ = i₂`. ✓
   - `j ≥ 1`: `h_k : σ.val.P.paint i_k (j-1) = .c`. `σ.val.col_c_P (j-1)` gives `i₁ = i₂`. ✓
9. **`col_c_Q`**: Q all dots, no .c. Contradiction via `h`.
10. **`col_d_P`**: similar to col_c_P.
11. **`col_d_Q`**: similar.

All 13 constraints verified. ∎

### Counting R_col0

Define `R_col0 := {v ∈ ValidCol0 μP μQ | v.paint b = .s}`.

**Claim R.3.** `|R_col0| = X_r(k)`.

**Proof.** A valid col0 with `v.paint b = .s` is determined by:
- `v.paint i = .dot` for `i < b` (dot_below + mono).
- `v.paint b = .s` (fixed).
- `v.paint i` for `i ∈ [b+1, c)` (the tail).

The tail segment is a sequence of length `k - 1` (since `c - (b+1) = c - b - 1 = k - 1`)
with values in `{.s, .r, .c, .d}`, monotone layer (≥ `.s`'s layer 1 = always), with
`col_c_unique` globally (so at most 1 `.c` in the tail, since `v.paint b = .s` has no `.c` yet),
and `col_d_unique` globally (at most 1 `.d` in the tail).

These are exactly `TSeq (k - 1)` sequences.

- `k = 1`: `TSeq 0` has cardinality 1 (empty sequence). `X_r(1) = 1`. ✓
- `k ≥ 2`: `TSeq (k-1)` has cardinality `4(k-1)` (by `TSeq_card`). `X_r(k) = 4(k-1)`. ✓

Combining R.1, R.2, R.3:

`|fiber σ| = |R_col0| = X_r(k)`. ∎

---

## Lemma C (aka Lemma 2): fiber size for σ ∈ C_sub

### Statement

Define `X_c(k)`:
- `k = 1`: `X_c = 3`
- `k ≥ 2`: `X_c = 4k`

**Claim.** For σ ∈ C_sub, `|fiber σ| = X_c(k)`.

### Characterization of the fiber

**Claim C.1.** For any `τ ∈ fiber σ`, `col0 := λ i. τ.P.paint i 0` satisfies:

(a) `col0 ∈ ValidCol0 μP μQ`.

(b) `col0(b) ∈ {.s, .r, .c}` (i.e., layer ≤ 3).

**Proof of (b).** Same as R.1:
- `τ.P.paint b 1 = σ.val.P.paint b 0 = .c`.
- `mono_P`: `layerOrd col0(b) ≤ layerOrd .c = 3`.
- `nondot_tail`: `col0(b) ≠ .dot`.
- No `row_c` constraint in PBP (unlike row_r, row_s).

Hence `col0(b) ∈ {.s, .r, .c}`. ∎

Note: `col0(b) = .d` is excluded because layer 4 > 3.

### Claim C.2 (reverse): every valid col0 with col0(b) ∈ {.s, .r, .c} extends

Analogous to R.2. The lift `liftPaint_D σ v.paint` gives a valid τ. The key
differences from R case:

- **row_r at row b**: If `v.paint b = .r`, the only `.r` in τ's row b. Specifically,
  `τ.P.paint b 0 = .r`, `τ.P.paint b 1 = σ.val.P.paint b 0 = .c ≠ .r`, and for `j ≥ 2`,
  `τ.P.paint b j = σ.val.P.paint b (j-1) ∈ {.c, .d, .dot}` (Lemma 0' + tail_dot), all ≠ .r.
  So exactly 1 `.r` in row b. ✓

- **col_c_P** at column 0: if `v.paint b = .c`, then the only `.c` in col 0 is at `(b, 0)`
  (since `v.col_c_unique`).

- **col_c_P** at column 1: `τ.P.paint i 1 = σ.val.P.paint i 0`. The `.c`'s in column 1
  are exactly the `.c`'s in column 0 of σ. By `σ.val.col_c_P`, at most one. ✓

- **mono_P** at (b, 0) → (b, j≥1): same as R case; `v.paint b.layerOrd ≤ 3` and 
  `σ.val.P.paint b j.layerOrd ≥ 3` (Lemma 0'), or at `j = 0`, `σ.val.P.paint b 0 = .c`, layer 3.
  Compatibility: `v.paint b.layerOrd ≤ 3`. ✓

- **row_s at row b with v.paint b = .s**: `τ` row b has `.s` only at `(b, 0)`. For
  j ≥ 1, paint is `.c`, `.d`, or `.dot`. ≠ .s. ✓

All other constraints are identical to R case or handled by σ. ∎

### Counting C_col0

Define `C_col0 := {v ∈ ValidCol0 μP μQ | (v.paint b).layerOrd ≤ 3}`
     `= {v : v.paint b ∈ {.s, .r, .c}}` (also excluding `.dot` by nondot_tail
     since `v` is in `ValidCol0` with non-empty tail).
     `= ValidCol0 \ {v : v.paint b = .d}` (complement of `.d`).

**Claim C.3.** `|C_col0| = X_c(k)`.

**Proof.**
`|C_col0| = |ValidCol0| - |{v : v.paint b = .d}|`.

`|ValidCol0| = 4k` (existing theorem `validCol0_card`).

`|{v : v.paint b = .d}| = D_col0(k)`:
- `k = 1`: `v = (.d)`, one element, `D_col0(1) = 1`.
- `k ≥ 2`: `v.paint b = .d` means `v[0] = .d`. By `col_d_unique`, no other `.d`. And mono
  with `v[0] = .d` (layer 4) forces `v[j] ∈ {.d}` for `j ≥ 1` (all subsequent layers ≥ 4).
  But no more `.d` allowed. So tail must be empty, contradicting length `k - 1 ≥ 1`.
  `D_col0(k) = 0` for `k ≥ 2`.

Thus:
- `k = 1`: `|C_col0| = 4 - 1 = 3 = X_c(1)`. ✓
- `k ≥ 2`: `|C_col0| = 4k - 0 = 4k = X_c(k)`. ✓

∎

Combining C.1, C.2, C.3:

`|fiber σ| = |C_col0| = X_c(k)`. ∎

---

## Lemma 3: `X_r(k) + X_c(k) = 2 · scTotal(k)`

Case analysis on k.

**k = 1:**
- `X_r + X_c = 1 + 3 = 4`.
- `scTotal = scDD + scRC + scSS = 0 + 1 + 1 = 2`.
- `2 · 2 = 4`. ✓

**k = 2:**
- `X_r + X_c = 4(k-1) + 4k = 4 + 8 = 12`.
- `scTotal = 2 + 3 + 1 = 6`.
- `2 · 6 = 12`. ✓

**k ≥ 3:**
- `X_r + X_c = 4(k-1) + 4k = 8k - 4`.
- `scTotal = 2(k-1) + (2k - 1) + 1 = 4k - 2`.
- `2 · (4k - 2) = 8k - 4`. ✓

∎

---

## Lemma 5 (= aggregate combine)

```
Σ_{σ ∈ RC_sub} |fiber σ|
  = Σ_{σ ∈ R_sub} |fiber σ| + Σ_{σ ∈ C_sub} |fiber σ|     [1: disjoint split]
  = Σ_{σ ∈ R_sub} X_r + Σ_{σ ∈ C_sub} X_c                  [2: Lemmas R, C]
  = |R_sub| · X_r + |C_sub| · X_c                          [3: sum_const]
  = |R_sub| · X_r + |R_sub| · X_c                          [4: |R_sub| = |C_sub|, Phase 1]
  = |R_sub| · (X_r + X_c)                                  [5: distrib]
  = |R_sub| · 2 · scTotal                                  [6: Lemma 3]
  = (|R_sub| + |R_sub|) · scTotal                          [7: 2x = x + x]
  = (|R_sub| + |C_sub|) · scTotal                          [8: Phase 1 again]
  = |RC_sub| · scTotal                                     [9: disjoint union card]
```

### Step details

**[1]**: `RC_sub = R_sub ⊔ C_sub` as a disjoint union of Finsets (disjoint because
`σ.val.P.paint b 0` is either `.r` or `.c`, not both). Apply `Finset.sum_union`.

**[2]**: Apply `Lemma R` to each σ in R_sub, `Lemma C` to each σ in C_sub.
Use `Finset.sum_congr`.

**[3]**: `Finset.sum_const` gives `Σ_{σ ∈ S} c = |S| · c`.

**[4]**: Use `r_sub_card_eq_c_sub_card`.

**[5]**: `a · x + a · y = a · (x + y)`, ring arithmetic.

**[6]**: Substitute `X_r + X_c = 2 · scTotal` from Lemma 3.

**[7]**: `2 · x = x + x`, ring.

**[8]**: Symmetric use of Phase 1.

**[9]**: `|A ⊔ B| = |A| + |B|` for disjoint finsets.

## Dependencies summary

- Phase 1 (already proved): `r_sub_card_eq_c_sub_card`.
- Lemma R (to prove): fiber size for R_sub. Requires new lift infrastructure.
- Lemma C (to prove): fiber size for C_sub. Requires new lift infrastructure.
- Lemma 3 (to prove): arithmetic.
- Combine (to prove): sum manipulation + [1]-[9] above.
