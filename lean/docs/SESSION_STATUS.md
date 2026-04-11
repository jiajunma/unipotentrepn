# Session Status — Prop 10.11 D-type Counting Formalization

**Last updated:** Session ending 2026-04-11

## Big picture

**Goal:** Formalize Prop 10.11 D of [BMSZb] — the recursive counting formula for
painted bipartitions of D-type. The main theorem:

```
|PBPSet .D μP μQ| = countPBP_D (dual partition derived from (μP, μQ))
```

assembled from a primitive recursive step and a balanced recursive step.

## Proven theorems (no sorry)

### Supporting infrastructure
- `HSeq_card k = k + 1` — monotone {s,r}-sequences
- `GSeq_card k = 2k + 1` — with at most one c
- `TSeq_card k = 4k` (k ≥ 1) — with at most one c and one d
- `ValidCol0.equivTSeq` — bijection between valid col-0 paintings and TSeq
- `validCol0_card = 4k` — count of valid col-0 paintings

### Fiber counts
- `fiber_card_primitive` — in primitive case, every σ has fiber = 4k
- `fiber_card_balanced_DD` — balanced DD class σ also has fiber = 4k
- `fiber_card_balanced_SS` — balanced SS class σ has empty fiber

### Lift constructions
- `LiftCondition` structure + `liftPBP_D` (general)
- `liftPBP_primitive_D`, `liftPBP_balanced_DD_D` (thin wrappers)
- `liftPBP_D_round_trip`, `liftPBP_D_injective` (general proofs)

### Top-level recursive steps
- `card_PBPSet_D_primitive_step` — `|PBPSet .D μP μQ| = |sub| · 4k`
- `card_PBPSet_D_balanced_step` —
  `|PBPSet .D μP μQ| = |DD_sub| · 4k + |RC_sub| · scTotal`
  (depends on `fiber_card_balanced_RC_aggregate`, the only remaining sorry)

### Phase 1 structural lemmas (5/5)
- `r_bottom_no_c_in_col0` — no .c in col 0 of r-bottom σ
- `r_bottom_no_other_r_in_row_b` — row_r consequence
- `r_bottom_row_b_ge_j_in_cd` — σ.P.paint b j ∈ {.c, .d, .dot} for j ≥ 1
- `c_bottom_row_b_ge_j_in_cd` — analogous for c-bottom
- `c_bottom_unique_c_in_col0` — col_c_unique consequence

### Swap helpers
- `swappedPaint` — single-cell swap function
- `swappedPaint_at_b0`, `swappedPaint_col0_ne_b`, `swappedPaint_off_col0` — reduction lemmas
- `swappedP_PYD` — new PaintedYoungDiagram after swap (with paint_outside proof)

### Partial `swap_b0_cell` constraints
Within the `swap_b0_cell` construction, these constraints are proved:
- `sym_P` (D/L trivial)
- `sym_Q` (unchanged + γ rewrite)
- `dot_match` (3-branch case analysis, fully proved)
- `mono_Q` (unchanged)
- `col_c_Q`, `col_d_Q` (unchanged)

## Remaining sorries (9 positions)

### 1. `swap_b0_cell` internal constraints (5 sorries)

#### 1a. `mono_P` — 4-case analysis

**Detailed plan:** see `docs/swap_b0_cell_detailed.md#constraint-4-mono_p`

Case structure:
- (a) Neither endpoint is (b, 0) → use σ.val.mono_P directly
- (b) (i₁, j₁) = (b, 0), (i₂, j₂) ≠ (b, 0)
  - Sub (b1) i₂ = b, j₂ ≥ 1 → use r/c_bottom_row_b_ge_j_in_cd
  - Sub (b2) i₂ > b → vacuous (outside shape)
- (c) (i₁, j₁) ≠ (b, 0), (i₂, j₂) = (b, 0)
  - Use σ.val.mono_P + (for c → r) c_bottom_unique_c_in_col0
- (d) Both = (b, 0) → rfl

Estimated: ~100 lines.

**Key technical issue encountered:** In case (c) c → r, the `cases hp : σ.val.P.paint i₁ 0 with | d => ...` branch needs `rw [hp] at hmono_old` followed by `omega`, but omega can't close the goal. Need `simp [DRCSymbol.layerOrd] at hmono_old` or explicit contradiction.

**Also:** In case (b1) r → c, after `rw [hc]` (where hc : σ.val.P.paint b j₂ = .c), the goal has `(.c).layerOrd ≤ (.c).layerOrd` which should close via `le_refl`, but `simp [DRCSymbol.layerOrd]` says "No goals to be solved" suggesting it already closed. Use `Nat.le_refl` or specific decide.

#### 1b. `row_s` — L/R branches

**Detailed plan:** see `docs/swap_b0_cell_detailed.md#constraint-6-row_s`

Key: **newS ≠ .s**, so any .s in σ' came from σ (unchanged cell).

Case L-L: each h gives σ'.P.paint i j = .s. By case on (i, j) = (b, 0): if yes, .s = newS, contradiction. Else σ.P.paint i j = .s. Apply σ.val.row_s L-L.

Cases L-R, R-L, R-R: similar, Q side unchanged.

Estimated: ~50 lines.

#### 1c. `row_r` — more complex due to swap creating/removing .r

**Detailed plan:** see `docs/swap_b0_cell_detailed.md#constraint-7-row_r`

**Sub-case r → c** (removes .r at (b, 0)): all .r in σ' correspond to .r in σ at same position. Straightforward.

**Sub-case c → r** (adds .r at (b, 0)): more subtle.
- L-L, i = b: σ had .c at (b, 0) and by c_bottom_row_b_ge_j_in_cd, σ.P.paint b j ∈ {.c,.d,.dot} for j ≥ 1. So σ' has .r at row b ONLY at (b, 0). Hence both h₁ and h₂ force j₁ = j₂ = 0.
- L-L, i ≠ b: swap doesn't affect row i, use σ.val.row_r.
- L-R, R-L, R-R: Q side is all-dots for D type, so .r at Q-side is impossible.

Estimated: ~80 lines.

#### 1d. `col_c_P` — 2 sub-cases (r → c adds, c → r removes)

**Detailed plan:** see `docs/swap_b0_cell_detailed.md#constraint-8-col_c_p`

**Sub-case r → c:** σ had no .c in col 0 (`r_bottom_no_c_in_col0`). New .c is at (b, 0) only. If j = 0: both i₁, i₂ must be b. If j ≠ 0: unchanged.

**Sub-case c → r:** σ' has no new .c. Any .c in σ' corresponds to σ at same position (not (b, 0)).

Estimated: ~30 lines.

#### 1e. `col_d_P` — newS ≠ .d

Straightforward: any .d in σ' corresponds to σ.val.P.paint = .d at same position (since swap doesn't introduce or remove .d).

Estimated: ~15 lines.

### 2. `swap_b0_cell_paint` — 1 sorry

Once `swap_b0_cell` is built, this is literally `rfl` (by construction of `swappedP_PYD`).

Estimated: 5 lines.

### 3. `swap_b0_cell_involutive` — 1 sorry

Double-swap gives the same PBP. Uses `swap_b0_cell_paint` (which gives the intermediate
state after first swap) and then unfolds to show the second swap restores.

Requires PBPSet Subtype.ext + PBP.ext'' + PaintedYoungDiagram.ext' for the paint function.
The key equation: `swappedPaint b .r (swappedPaint b .c σ.P.paint) = σ.P.paint`.

Estimated: 30 lines.

### 4. `r_sub_card_eq_c_sub_card` — 1 sorry

Apply `Finset.card_bij` with:
- `i σ hσ := swap_b0_cell h_bal σ .r .c (Or.inl ⟨rfl, rfl⟩) (from hσ)`
- Maps-to: via `swap_b0_cell_paint`
- Injectivity: if `swap σ₁ = swap σ₂`, apply involution to both sides, σ₁ = σ₂
- Surjectivity: given τ ∈ C_sub, preimage is `swap τ .c .r`; involution shows this works

Estimated: 60 lines.

### 5. `fiber_card_balanced_RC_aggregate` — the goal (1 sorry)

Once all above are done, this follows from:
- Lemma 1 (X_r per-σ count) — requires new `LiftCondition_R` (~200 lines, not yet started)
- Lemma 2 (X_c per-σ count) — requires new `LiftCondition_C` (~300 lines, not yet started)
- Lemma 3 (X_r + X_c = 2·scTotal) — arithmetic (~30 lines)
- Lemma 4 (|R_sub| = |C_sub|) — the bijection chain above

Estimated: ~600 lines total for Lemmas 1-4 + the final combine.

## Task list for next session

### Priority 1: finish `swap_b0_cell` (Phase 1)
1. Fill `mono_P` — largest case (~100 lines)
2. Fill `row_s` — medium (~50 lines)
3. Fill `row_r` — medium with c → r subtlety (~80 lines)
4. Fill `col_c_P` — small (~30 lines)
5. Fill `col_d_P` — small (~15 lines)

**Verify:** `swap_b0_cell` has no internal sorries.

### Priority 2: finish Phase 1 bijection
6. `swap_b0_cell_paint` (trivial once 1 is done)
7. `swap_b0_cell_involutive` — 30 lines
8. `r_sub_card_eq_c_sub_card` — 60 lines

**Verify:** `|R_sub| = |C_sub|` is proved.

### Priority 3: Phase 2 (Lemma 3 arithmetic)
9. Prove `X_r + X_c = 2 · scTotal` by cases on k

### Priority 4: Phases 3, 4 (Lemmas 1, 2 — the big ones)
10. `LiftCondition_R` structure + proof of its existence for r-bottom σ
11. `liftPBP_R_D` construction (based on `liftPBP_D` pattern)
12. Prove `X_r` per-σ fiber size using the TSeq(k-1) bijection
13. Same for C: `LiftCondition_C`, `liftPBP_C_D`, `X_c`

### Priority 5: Phase 5 (Combine)
14. `fiber_card_balanced_RC_aggregate`:
    - Split sum R_sub ⊔ C_sub
    - Apply Lemma 1 per R-σ, Lemma 2 per C-σ
    - Sum with |R_sub| = |C_sub|
    - Simplify via Lemma 3

## Key technical notes for next session

### Issue: anonymous structure projection + `rw`

When building a PBP via `refine ⟨⟨..., swappedPaint b newS σ.val.P.paint, ...⟩, ...⟩`,
the goals in constraint proofs reference the anonymous structure:
`{shape, paint := swappedPaint ..., paint_outside}.paint b 0`

This should definitionally reduce to `swappedPaint b newS σ.val.P.paint b 0`,
but `rw [swappedPaint_at_b0]` fails to match because `rw` wants syntactic equality.

**Workaround 1:** Use `show` to rewrite the goal with the explicit `swappedPaint` form.
```
case dot_match =>
  intro i j
  show ((i, j) ∈ σ.val.P.shape ∧ swappedPaint b newS σ.val.P.paint i j = .dot) ↔ ...
  -- Now `rw [swappedPaint_at_b0]` etc. works
```

**Workaround 2:** Extract `swappedP_PYD` as a separate definition (already done).
This hides the anonymous structure behind a name, so `swappedP_PYD.paint` has a
clean reducible form.

### Issue: `0 + 1` vs `1` in `YoungDiagram.colLen_shiftLeft`

`(shiftLeft μP).colLen j = μP.colLen (j + 1)`

After rewriting, the term is `μP.colLen (0 + 1)` not `μP.colLen 1`. `omega` can't
bridge these automatically. Solution: introduce `have h1 : μP.colLen (0 + 1) ≤ μP.colLen 0 := ...`
and let omega use the explicit form.

### Issue: `cases hp : expr` and goal rewriting

`cases hp : σ.val.P.paint i₁ 0 with | d => ...` binds hp but does NOT substitute the
expression in the goal (only in the match tree). To derive contradiction in the `| d =>`
branch:
```
| d =>
  exfalso
  rw [hp] at hmono_old
  simp [DRCSymbol.layerOrd] at hmono_old
```
or use `omega` with explicit hypotheses.

### Good patterns
- `σ.prop.1 : σ.val.γ = .D` for γ rewrites
- `σ.prop.2.1 : σ.val.P.shape = shiftLeft μP`
- `σ.prop.2.2 : σ.val.Q.shape = shiftLeft μQ`
- `YoungDiagram.mem_iff_lt_colLen` for shape membership
- `YoungDiagram.colLen_anti` for shape column monotonicity

## Documentation

- `docs/fiber_card_balanced_RC_aggregate_proof.md` — high-level plan (Lemmas 1-4)
- `docs/swap_b0_cell_detailed.md` — 13-constraint step-by-step proof
- `docs/card_PBPSet_D_balanced_step_proof.md` — balanced step proof (already implemented)
- This file (`SESSION_STATUS.md`) — current state + next-session roadmap

## Git log (recent)

```
8741cb7 Phase 1: partial swap_b0_cell — 6/13 constraints proved
911dddc Add detailed informal proof for swap_b0_cell construction
5a206cc Phase 1: simplify swap_b0_cell body to sorry after validating approach
31ba8a0 Phase 1 partial: structural lemmas for RC aggregate bijection
526e323 Prove card_PBPSet_D_balanced_step (Option X, total form)
3793932 Replace incorrect RC per-σ with aggregate; add primitive recursive step
2ba2575 Prove round_trip, balanced SS, balanced DD; refactor lift to use LiftCondition
48871a1 Rewrite validCol0_card via HSeq/GSeq/TSeq recursive Equivs
```

Tag `validcol0-card-complete` marks the point where `validCol0_card` was first proved
via the TSeq recursive framework.
