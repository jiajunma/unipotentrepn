# `fiber_card_balanced_RC_aggregate` — Complete Informal Proof

## Statement

In the balanced D-type case:
- `h_bal : (shiftLeft μP).colLen 0 = μQ.colLen 0 + 1`
- `hk : k = μP.colLen 0 - μQ.colLen 0` with `k ≥ 1`

We claim:
```
Σ_{σ ∈ PBPSet_sub_RC} |fiber σ| = |PBPSet_sub_RC| · scTotal
```

where:
- `PBPSet_sub := PBPSet .D (shiftLeft μP) (shiftLeft μQ)`
- `PBPSet_sub_RC := {σ ∈ PBPSet_sub : tailClass_D σ.val = .RC}`
- `scTotal := scDD + scRC + scSS` (the second triple of `tailCoeffs k`)
- `fiber σ := {τ ∈ PBPSet .D μP μQ : ∇²τ = σ}`

## Setup notation

- `b := μQ.colLen 0` (= the row at which σ's tail bottom sits)
- `c := μP.colLen 0` (= τ's col-0 length at current level)
- At sub level, σ.P.shape.colLen 0 = (shiftLeft μP).colLen 0 = `μP.colLen 1` = `b + 1` (by `h_bal`).
  So **σ's tail bottom row is at `b`** (the row `(σ.P.shape.colLen 0) - 1 = b`).
- `tailSymbol_D σ.val := σ.val.P.paint b 0`
- `tailClass_D σ.val = .RC ↔ σ.val.P.paint b 0 ∈ {.r, .c}`

## Decomposition

Define:
- `R_sub := {σ ∈ PBPSet_sub : σ.val.P.paint b 0 = .r}`
- `C_sub := {σ ∈ PBPSet_sub : σ.val.P.paint b 0 = .c}`

Then `PBPSet_sub_RC = R_sub ⊔ C_sub` (disjoint union).

So:
```
Σ_{σ ∈ RC_sub} |fiber σ| = Σ_{σ ∈ R_sub} |fiber σ| + Σ_{σ ∈ C_sub} |fiber σ|
```

## Four key lemmas

### Lemma 1: Per-σ fiber size for `R_sub` (constant)

For σ ∈ R_sub, `|fiber σ| = X_r` where:
- `k = 1`: `X_r = 1`
- `k ≥ 2`: `X_r = 4(k-1)`

**Proof outline:**

Every τ ∈ fiber σ has `∇²τ = σ`, so `∇²τ.P.paint b 0 = σ.P.paint b 0 = .r`.
Unfolding `doubleDescent_D_paintL` at `(b, 0)`:
- **Not in dot zone**: `b < τ.Q.shape.colLen 1 = μQ.colLen 1 ≤ μQ.colLen 0 = b` is false.
- **Not in s zone**: if it were, value = .s ≠ .r.
- So we're in the **else** branch: `τ.P.paint b 1 = σ.P.paint b 0 = .r`.

Now examine `col0 := τ.P.paint(·, 0)` (τ's col 0):
- At `i = b` (top of tail): `col0(b) = τ.P.paint b 0`.
  - `mono_P τ` at `(b, 0) ≤ (b, 1)` with `(b, 1) ∈ τ.P.shape` (since `b < μP.colLen 1 = b+1`):
    `layerOrd col0(b) ≤ layerOrd τ.P.paint b 1 = 2`. So `col0(b) ∈ {dot, s, r}`.
  - `nondot_tail`: `col0(b) ≠ dot`.
  - `row_r` at row `b`: τ has `.r` at `(b, 1)`. If `col0(b) = .r`, two r's at row b → violation. So `col0(b) ≠ .r`.
  - Therefore `col0(b) = .s` (forced).

- `col0[b+1, c)` (rest of tail): unconstrained TSeq(k-1) sequence.
  - Each element is in `{s, r, c, d}` (non-dot tail), mono, ≤1 c, ≤1 d.
  - Count: `|TSeq(k-1)| = 4(k-1)` for `k ≥ 2`, or `|TSeq(0)| = 1` for `k = 1`.

**Lift construction (existence of fiber elements):** For any such col0, there's a τ in PBPSet .D μP μQ with `τ.P.paint i 0 = col0(i)` and `τ.P.paint i (j+1) = σ.P.paint i j`. Validity requires a `LiftCondition_R σ`:
- `no_sr_above`: for `i > b`, σ.P.paint i k has no .s or .r (these rows are outside σ's shape).
- `row_b_structure`: σ.P.paint b 0 = .r and σ.P.paint b j ∈ {.c, .d} for `j ≥ 1` (with `(b, j) ∈ shape`).
- `mono_for_cr`: at mono-conflicting positions, σ.P.paint i₂ j has layerOrd ≥ 2.

These all follow from σ's own validity + DD-free structure at row b.

### Lemma 2: Per-σ fiber size for `C_sub` (constant)

For σ ∈ C_sub, `|fiber σ| = X_c` where:
- `k = 1`: `X_c = 3`
- `k = 2`: `X_c = 8`
- `k ≥ 3`: `X_c = 4k`

**Proof outline:**

Analogous to Lemma 1 but with `σ.P.paint b 0 = .c` ⇒ `τ.P.paint b 1 = .c`.

Now `col0(b)`:
- `mono_P τ` at `(b, 0) ≤ (b, 1)`: `layerOrd col0(b) ≤ 3`. So `col0(b) ∈ {dot, s, r, c}`.
- `nondot_tail`: `col0(b) ∈ {s, r, c}`.
- No `row_c` constraint (there isn't one).
- `col_c_P` uniqueness: if `col0(b) = .c`, no other c in col 0 of τ.

**Three sub-cases** based on `col0(b)`:

**(a) col0(b) = .s:**
- `col0[b+1, c) ∈ TSeq(k-1)` (any).
- Contribution: `4(k-1)` for `k ≥ 2`, `1` for `k = 1`.

**(b) col0(b) = .r:**
- `col0[b+1, c)` ∈ mono sequences in `{r, c, d}` with ≤1 c, ≤1 d, length `k-1`.
- Equivalent to `{v ∈ TSeq(k-1) : v.last.layerOrd ≥ 2}` (no s). Actually it's
  mono sequences starting at layer ≥ 2 — call this `GSeq'(k-1)`.
- Count:
  - `k = 1`: length 0, `1` option.
  - `k = 2`: length 1, 3 options `(r), (c), (d)`.
  - `k ≥ 3`: length `k-1`, by (β, δc, δd) with β + δc + δd = k-1:
    - `(k-1, 0, 0)`: 1, `(k-2, 1, 0)`: 1, `(k-2, 0, 1)`: 1, `(k-3, 1, 1)`: 1. Total `4` (for k ≥ 3).

**(c) col0(b) = .c:**
- `col0[b+1, c)` must have no c (col_c_unique consumed) and mono ≥ c, so in `{d}` with ≤1 d.
- Count:
  - `k = 1`: length 0, `1` option (just `(c,)`).
  - `k = 2`: length 1, `1` option `(c, d)`.
  - `k ≥ 3`: length ≥ 2, mono all `.d`, but ≤1 d forbids more than 1. `0` options.

**Totals for c-bottom:**
- `k = 1`: `1 + 1 + 1 = 3` ✓
- `k = 2`: `4 + 3 + 1 = 8` ✓
- `k ≥ 3`: `4(k-1) + 4 + 0 = 4k` ✓

### Lemma 3: `X_r + X_c = 2 · scTotal`

**Verification by cases (mechanical arithmetic):**

Recall `tailCoeffs k` second triple:
- `k = 1`: `scDD = 0, scRC = 1, scSS = 1`, `scTotal = 2`.
- `k = 2`: `scDD = 2, scRC = 3, scSS = 1`, `scTotal = 6`.
- `k ≥ 3`: `scDD = 2(k-1), scRC = 2k-1, scSS = 1`, `scTotal = 4k-2`.

Then:
- `k = 1`: `X_r + X_c = 1 + 3 = 4 = 2 · 2`. ✓
- `k = 2`: `X_r + X_c = 4 + 8 = 12 = 2 · 6`. ✓
- `k ≥ 3`: `X_r + X_c = 4(k-1) + 4k = 8k - 4 = 2 · (4k-2)`. ✓

### Lemma 4: `|R_sub| = |C_sub|` — **explicit bijection**

Define `Ψ : R_sub → C_sub` by "swap (b, 0) cell from .r to .c":
```
Ψ(σ).P.paint i j := if (i, j) = (b, 0) then .c else σ.P.paint i j
Ψ(σ).Q := σ.Q
Ψ(σ).γ := .D
Ψ(σ).P.shape := σ.P.shape
```

**Claim:** Ψ(σ) is a valid PBP and `Ψ(σ).P.paint b 0 = .c` (so Ψ(σ) ∈ C_sub).

**Verification:** All PBP constraints are preserved:

**col_c_P (col 0 has ≤1 c):** Before the swap, σ had no `.c` in col 0. Why? Because:
- σ's tail bottom at `(b, 0)` is `.r` (layerOrd 2).
- For any cell `(i, 0)` with `i < b`, σ.mono_P gives layer `(i, 0) ≤ layer (b, 0) = 2`. So `(i, 0) ≠ .c` (layer 3).
- For `(i, 0)` with `i ≥ b + 1 = σ.P.shape.colLen 0`: outside shape, paint = .dot.
- So σ's col 0 has no `.c` cells.
- After swap, Ψ(σ) has exactly 1 c at `(b, 0)`. ✓

**mono_P at (i, 0) ≤ (b, 0)** with `i < b`: unchanged cells except `(b, 0)`.
- layer `σ.P.paint i 0 ≤ 2` (from σ.mono_P).
- New layer `Ψ(σ).P.paint b 0 = 3`. `2 ≤ 3` ✓.

**mono_P at (b, 0) ≤ (b, j)** with `j ≥ 1`, `(b, j) ∈ shape`:
- In σ: layer `σ.P.paint b j ≥ 2` (from σ.mono_P at `(b,0) ≤ (b,j)`, σ.P.paint b 0 = .r).
- σ.row_r at row b: σ has `.r` at `(b, 0)`, at most 1 r per row, so `σ.P.paint b j ≠ .r`.
- So `σ.P.paint b j ∈ {.c, .d}`, layer ∈ {3, 4}.
- After swap, `Ψ(σ).P.paint b 0 = .c` (layer 3). Need layer `(b, j) ≥ 3`. ✓

**mono_P at other positions:** Unchanged. ✓

**row_r at row b:**
- σ had 1 r at `(b, 0)`, no others in row b.
- After swap, Ψ(σ) has 0 r's at `(b, 0)`, no others. Total 0. ≤ 1 ✓.

**row_s:** `.r → .c` doesn't involve `.s`, so row_s is unaffected. ✓

**col_d_P, col_c_Q, col_d_Q, sym_P, sym_Q, dot_match, row_r at other rows:** Unchanged by the single-cell swap (verification is mechanical).

**Inverse `Ψ⁻¹ : C_sub → R_sub`:** Define by swapping `.c → .r` at `(b, 0)`.

**Verification of Ψ⁻¹:**
- For σ' ∈ C_sub: σ'.P.paint b 0 = .c (layer 3). col_c_unique gives at most 1 c in col 0 of σ'; this one must be at (b, 0) (since it's the tail bottom, and by mono, any other c would have to be below b, but b is the bottom). So σ' has exactly 1 c at (b, 0), no others.
- σ'.mono_P at `(b, 0) ≤ (b, j)`: `σ'.P.paint b j` has layer ≥ 3, so `∈ {.c, .d}`. col_c_unique in col j (for j ≥ 1) allows at most 1 c per col, but here we're looking at row b specifically. Actually σ'.P.paint b j ≠ .r (layer 3 vs required ≥ 3), so no row_r concern.
- After swap, σ.P.paint b 0 = .r. `row_r` at row b: σ has 1 r at (b, 0), need no other r in row b. Other cells in row b of σ' had layer ≥ 3, so no r. After swap, unchanged. ✓
- `col_c_unique` in col 0 of σ: 0 c's. ✓
- `mono_P at (b, 0) ≤ (b, j)`: σ.P.paint b 0 = .r (layer 2), σ.P.paint b j ∈ {.c, .d} (layer ≥ 3). 2 ≤ 3 ✓.
- Other constraints: unchanged.

**Ψ and Ψ⁻¹ are inverses:** Double swap is identity. ∎

Therefore `|R_sub| = |C_sub|`.

## Combining

Let `n := |R_sub| = |C_sub|`, so `|RC_sub| = 2n`.

```
Σ_{σ ∈ RC_sub} |fiber σ|
  = Σ_{σ ∈ R_sub} |fiber σ| + Σ_{σ ∈ C_sub} |fiber σ|
  = n · X_r + n · X_c                          [Lemmas 1, 2]
  = n · (X_r + X_c)
  = n · (2 · scTotal)                           [Lemma 3]
  = 2n · scTotal
  = |RC_sub| · scTotal                          [since |RC_sub| = 2n]
```
∎

## Dependencies

```
fiber_card_balanced_RC_aggregate
├── Lemma 4: |R_sub| = |C_sub|  
│     (clean bijection, ~100 LoC)
├── Lemma 1: X_r per-σ fiber count 
│     ├── LiftCondition_R (new structure + proof, ~100 LoC)
│     ├── liftPBP_R / round_trip_R / injectivity (~80 LoC) 
│     └── TSeq(k-1) count (use existing HSeq/GSeq/TSeq machinery, ~30 LoC)
├── Lemma 2: X_c per-σ fiber count 
│     ├── LiftCondition_C (new structure + proof, ~120 LoC)
│     ├── liftPBP_C / round_trip_C / injectivity (~80 LoC) 
│     └── Three sub-case enumeration (~150 LoC)
├── Lemma 3: X_r + X_c = 2 · scTotal 
│     (arithmetic by cases, ~30 LoC)
└── Combining (~40 LoC)
```

**Total estimate: ~730 LoC** of new code.

## Assessment

- **Lemma 4 is the cleanest and shortest** (clean bijection, no new lift infrastructure).
- **Lemmas 1, 2 are the biggest chunks**, needing new `LiftCondition_R` and `LiftCondition_C` structures + corresponding `liftPBP_R` / `liftPBP_C` constructions + round-trip + injectivity proofs.
- **Lemma 3 is purely arithmetic.**

## Simplification option: avoid Lemmas 1 and 2

**Key observation:** We don't need X_r and X_c individually — we only need their sum `X_r + X_c = 2 · scTotal`.

**Alternative approach:** Prove the aggregate directly via a "swap the full fiber" bijection.

Define a map on pairs:
```
Φ : (σ, τ) ↦ (σ', τ')
```
where σ ∈ R_sub, τ ∈ fiber σ, σ' = Ψ(σ) ∈ C_sub, and τ' ∈ fiber σ' is obtained by swapping `τ.P.paint b 1` from .r to .c (analogous swap at current level).

If this map is well-defined and a bijection between `(σ ∈ R_sub, τ ∈ fiber σ)` and `(σ' ∈ C_sub, τ' ∈ fiber σ')`, then:
```
Σ_{σ ∈ R_sub} |fiber σ| = Σ_{σ' ∈ C_sub} |fiber σ'|
```

But this is already true (both equal `n · X_r` or `n · X_c`). It only says the sums are EQUAL, not that they equal `n · scTotal`.

**So this alternative doesn't avoid computing X_r or X_c.**

**Another alternative:** Compute the TOTAL aggregate `Σ |fiber σ|` directly as `|{τ ∈ PBPSet_current : τ.P.paint b 1 ∈ {.r, .c}}|` (from the ∇² case analysis). Then this equals:

```
|{τ : τ.P.paint b 1 = .r}| + |{τ : τ.P.paint b 1 = .c}|
```

These two counts can be analyzed via col0(b) constraints, but they're at the current level, not the sub level. They don't directly simplify to `|RC_sub| · scTotal`.

**Conclusion:** Lemmas 1 and 2 are essential. No shortcut.

## Decision

Given the ~700 LoC scope, formalization of this lemma is a significant undertaking (comparable in size to the entire validCol0_card recursive framework we built earlier).

**Recommended phased approach:**
1. **Phase 1**: Prove Lemma 4 (bijection, ~100 LoC, zero dependencies). This is standalone valuable.
2. **Phase 2**: Prove Lemma 3 (arithmetic, ~30 LoC, zero dependencies).
3. **Phase 3**: Build `LiftCondition_R` + Lemma 1 (~200 LoC).
4. **Phase 4**: Build `LiftCondition_C` + Lemma 2 (~300 LoC).
5. **Phase 5**: Combine everything in the main theorem (~40 LoC).

Each phase can commit independently. If we run out of time, Phases 1-3 alone already give significant progress (Lemma 4 with its clean bijection is mathematically interesting on its own).
