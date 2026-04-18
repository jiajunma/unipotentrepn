# `card_PBPSet_D_balanced_step` — Detailed Informal Proof

## Context

This is the balanced-case recursive step for Prop 10.11 D-type in its
*total-count form*. Together with the already-proved
`card_PBPSet_D_primitive_step`, it will give the full recursive formula
for `|PBPSet .D μP μQ|` matching `countPBP .D` from Counting.lean, with
the single remaining sorry being `fiber_card_balanced_RC_aggregate`
(which is a purely combinatorial symmetry fact about the RC class).

## Notation

- `b := μQ.colLen 0`, `c := μP.colLen 0`, `k := c - b`
- **balanced condition:** `(shiftLeft μP).colLen 0 = b + 1`, i.e., `μP.colLen 1 = b + 1`
- `sub := shiftLeft μP × shiftLeft μQ`
- `PBPSet_sub := PBPSet .D (shiftLeft μP) (shiftLeft μQ)`
- For `σ ∈ PBPSet_sub`, `fiber σ := {τ ∈ PBPSet .D μP μQ | ∇²τ = σ}`
- `tailCoeffs k = ((tDD, tRC, tSS), (scDD, scRC, scSS))` with
  - `tDD + tRC + tSS = 4k` (total for unconstrained tail)
  - `scDD + scRC + scSS = 4k - 2` (total for "scattered" balanced-RC case)

## Statement

```
|PBPSet .D μP μQ| = #DD_sub · 4k + #RC_sub · (4k - 2)
```

where `#DD_sub := |{σ ∈ PBPSet_sub | tailClass_D σ = .DD}|` and similarly
for RC_sub. Note that `#SS_sub`'s contribution is zero (balanced SS has
empty fiber), so it doesn't appear in the formula.

## Proof strategy

Use `card_PBPSet_eq_sum_fiber` to rewrite `|PBPSet .D μP μQ|` as
`Σ_σ |fiber σ|`. Split the sum over σ by σ's tailClass into three parts:

```
Σ_σ |fiber σ| = Σ_{σ ∈ DD_filter} |fiber σ|
              + Σ_{σ ∈ RC_filter} |fiber σ|
              + Σ_{σ ∈ SS_filter} |fiber σ|
```

Compute each part separately.

## The three parts

### Part 1: DD contribution

**Claim:** `Σ_{σ ∈ DD_filter} |fiber σ| = #DD_sub · 4k`

**Proof:** For each `σ ∈ DD_sub`, `fiber_card_balanced_DD` gives
`|fiber σ| = tDD + tRC + tSS = 4k`, a constant. So the sum is
`#DD_sub · 4k`. Use `Finset.sum_const` after rewriting each summand
via `Finset.sum_congr`.

**Dependencies:**
- `fiber_card_balanced_DD` ✓ (proved)
- `tailCoeffs_total` ✓ (proved)

### Part 2: RC contribution

**Claim:** `Σ_{σ ∈ RC_filter} |fiber σ| = #RC_sub · (scDD + scRC + scSS)`

**Proof:** Direct application of `fiber_card_balanced_RC_aggregate`.

**Dependencies:**
- `fiber_card_balanced_RC_aggregate` ⚠️ **sorry** (leaf)

### Part 3: SS contribution

**Claim:** `Σ_{σ ∈ SS_filter} |fiber σ| = 0`

**Proof:** For each `σ ∈ SS_sub`, `fiber_card_balanced_SS` gives
`|fiber σ| = 0`. Sum of zeros is zero.

**Dependencies:**
- `fiber_card_balanced_SS` ✓ (proved)

Note: `fiber_card_balanced_SS` requires `μQ.colLen 0 < μP.colLen 0`
(i.e., `hQP_lt`), which is equivalent to `k ≥ 1`. This follows from
`hk_pos : 1 ≤ k` and `hk : k = c - b`.

## Combining

```
|PBPSet .D μP μQ|
  = Σ_σ |fiber σ|                                          [sigma fiber]
  = Σ_{DD} |fiber σ| + Σ_{RC} |fiber σ| + Σ_{SS} |fiber σ|  [trichotomy split]
  = #DD_sub · 4k + #RC_sub · scTotal + 0                   [Parts 1, 2, 3]
  = #DD_sub · (tDD+tRC+tSS) + #RC_sub · (scDD+scRC+scSS)
```

## Trichotomy split — the mechanical core

The step "split Σ_σ into DD + RC + SS" is the bookkeeping-heavy part.
We need to show:

```
Σ_{σ ∈ univ} f σ
  = Σ_{σ ∈ univ.filter (tc=DD)} f σ
  + Σ_{σ ∈ univ.filter (tc=RC)} f σ
  + Σ_{σ ∈ univ.filter (tc=SS)} f σ
```

This follows from the disjoint union `univ = DD ∪ RC ∪ SS` (since every
σ has exactly one tailClass). Specifically:

1. `univ \ DD_filter = RC_filter ∪ SS_filter` (by trichotomy)
2. `Finset.sum_filter_add_sum_filter_not f (tc=DD)`:
   `Σ_σ f σ = (DD_filter).sum f + ((univ \ DD_filter)).sum f`
3. Further split `(univ \ DD_filter).sum f`:
   - `= (RC_filter).sum f + (SS_filter).sum f`
   - Using `sum_filter_add_sum_filter_not` again with `tc=RC` applied
     to the restricted universe.

Alternatively, use `Finset.sum_partition` (if it exists) with the
classifier `tailClass_D`.

**Simpler approach (recommended):** use the existing
`card_PBPSet_eq_sum_tc` to split `|PBPSet|` first, then relate each
`|PBPSet_tc|` to a sum over the corresponding filter. But
`|PBPSet_tc .D sub X|` is the count of σ's in X-class, not the sum of
their fiber sizes. So this approach gives `|PBPSet_tc| = #X_filter`
but not the sum directly.

**Concrete approach using filters:**

```lean
have hDD_sum : Finset.univ.sum (fun σ => Fintype.card (fiber σ)) =
    (univ.filter (·∈DD)).sum (fiber_card) +
    (univ.filter (¬(·∈DD))).sum (fiber_card) := 
  (Finset.sum_filter_add_sum_filter_not _ _).symm

have hRC_sum : (univ.filter (¬(·∈DD))).sum (fiber_card) =
    (univ.filter (¬(·∈DD) ∧ (·∈RC))).sum (fiber_card) +
    (univ.filter (¬(·∈DD) ∧ ¬(·∈RC))).sum (fiber_card) :=
  (Finset.sum_filter_add_sum_filter_not _ _).symm

-- Show: (¬DD ∧ RC) ↔ RC, and (¬DD ∧ ¬RC) ↔ SS
-- via trichotomy of tailClass
```

## Corner case check: `hQP_lt`

`fiber_card_balanced_SS` requires `hQP_lt : μQ.colLen 0 < μP.colLen 0`.

Derivation from our hypotheses:
- `hk : k = μP.colLen 0 - μQ.colLen 0`
- `hk_pos : 1 ≤ k`
- `hQP : μQ.colLen 0 ≤ μP.colLen 0`

Therefore `μP.colLen 0 - μQ.colLen 0 ≥ 1`, so `μP.colLen 0 > μQ.colLen 0`.
This gives `hQP_lt` by `omega`.

## Summary of dependencies

```
card_PBPSet_D_balanced_step
├── card_PBPSet_eq_sum_fiber ✓
├── fiber_card_balanced_DD ✓
├── fiber_card_balanced_RC_aggregate ⚠️ sorry (unchanged)
├── fiber_card_balanced_SS ✓
├── tailCoeffs_total ✓ (for 4k simplification)
└── Finset.sum manipulation lemmas (Mathlib)
```

No new sorries introduced.
