# `swap_b0_cell` — Formalization-Ready Detailed Natural Language Proof

This document provides a step-by-step informal proof for the 13 PBP
constraint verifications needed to define `swap_b0_cell`. Each step is
written so that the corresponding Lean proof is mechanical.

## Setup

Given:
- `μP μQ : YoungDiagram`
- `h_bal : (shiftLeft μP).colLen 0 = μQ.colLen 0 + 1` (so `μP.colLen 1 = b + 1` with `b := μQ.colLen 0`)
- `σ : PBPSet .D (shiftLeft μP) (shiftLeft μQ)`
- `(oldS, newS) ∈ {(.r, .c), (.c, .r)}`
- `h_old : σ.val.P.paint b 0 = oldS`

Goal: construct `σ' ∈ PBPSet .D (shiftLeft μP) (shiftLeft μQ)` with:
- `σ'.P.shape = σ.val.P.shape`
- `σ'.Q = σ.val.Q`
- `σ'.γ = .D`
- `σ'.P.paint = swappedPaint b newS σ.val.P.paint`
  (= σ.val.P.paint except at (b, 0) where it's newS)

## Shape facts (used throughout)

**Fact S1:** `σ.val.P.shape.colLen 0 = b + 1`
  Proof: `σ.val.P.shape = shiftLeft μP`, and `(shiftLeft μP).colLen 0 = μP.colLen 1 = b + 1`.

**Fact S2:** `(b, 0) ∈ σ.val.P.shape`
  Proof: by S1, `b < b + 1 = σ.val.P.shape.colLen 0`, so `(b, 0) ∈ σ.val.P.shape` by `YoungDiagram.mem_iff_lt_colLen`.

**Fact S3:** `(b, 0) ∉ σ.val.Q.shape`
  Proof: `σ.val.Q.shape.colLen 0 = (shiftLeft μQ).colLen 0 = μQ.colLen 1 ≤ μQ.colLen 0 = b`.
  So `σ.val.Q.shape.colLen 0 ≤ b`, hence `b ∉ [0, σ.val.Q.shape.colLen 0)`, so `(b, 0) ∉ σ.val.Q.shape`.

## Constraint 1: `sym_P`

**Goal:** `∀ i j, (i, j) ∈ σ'.P.shape → σ'.P.paint i j .allowed .D .L`.

For D type on the left (L) side, all symbols are allowed
(`DRCSymbol.allowed .D .L = True`). So the constraint is vacuous.

**Proof:** `intro _ _ _; trivial`.

## Constraint 2: `sym_Q`

**Goal:** `∀ i j, (i, j) ∈ σ'.Q.shape → σ'.Q.paint i j .allowed .D .R`.

Since `σ'.Q = σ.val.Q` and `σ'.γ = .D = σ.val.γ`, this is exactly `σ.val.sym_Q` (after
using `σ.prop.1 : σ.val.γ = .D` to rewrite).

**Proof:** `exact σ.val.sym_Q` (with potential γ rewrite if Lean requires it explicitly).

## Constraint 3: `dot_match`

**Goal:** `∀ i j, ((i, j) ∈ σ'.P.shape ∧ σ'.P.paint i j = .dot) ↔ ((i, j) ∈ σ'.Q.shape ∧ σ'.Q.paint i j = .dot)`.

σ'.P.shape = σ.val.P.shape, σ'.Q = σ.val.Q. Only σ'.P.paint differs from σ.val.P.paint, specifically at (b, 0).

**Case (i, j) ≠ (b, 0):**
σ'.P.paint i j = σ.val.P.paint i j (by `swappedPaint_col0_ne_b` or `swappedPaint_off_col0`).
So the iff reduces to `σ.val.dot_match i j`, which holds by assumption.

**Case (i, j) = (b, 0):**
σ'.P.paint b 0 = newS ∈ {.r, .c}.
- LHS: `((b, 0) ∈ σ.val.P.shape ∧ newS = .dot)`. Since newS ≠ .dot, this is False.
- RHS: `((b, 0) ∈ σ.val.Q.shape ∧ σ.val.Q.paint b 0 = .dot)`. Since (b, 0) ∉ σ.val.Q.shape (Fact S3), this is False.
- False ↔ False ✓.

## Constraint 4: `mono_P`

**Goal:** `∀ i₁ j₁ i₂ j₂, i₁ ≤ i₂ → j₁ ≤ j₂ → (i₂, j₂) ∈ σ'.P.shape → layerOrd σ'.P.paint i₁ j₁ ≤ layerOrd σ'.P.paint i₂ j₂`.

4 sub-cases based on whether endpoints are at (b, 0):

**Case (a): Neither (i₁, j₁) nor (i₂, j₂) is (b, 0).**
Both paint values are unchanged. Use σ.val.mono_P directly.

**Case (b): (i₁, j₁) = (b, 0), (i₂, j₂) ≠ (b, 0).**
σ'.P.paint b 0 = newS.
σ'.P.paint i₂ j₂ = σ.val.P.paint i₂ j₂ (unchanged).
Need: `layerOrd newS ≤ layerOrd σ.val.P.paint i₂ j₂`.

From constraints: i₁ = b ≤ i₂ and j₁ = 0 ≤ j₂.

**Sub-case b1: i₂ = b.** Then j₂ ≥ 1 (since (i₂, j₂) ≠ (b, 0)).
- We need `layerOrd newS ≤ layerOrd σ.val.P.paint b j₂`.
- From Lemma `r_bottom_row_b_ge_j_in_cd` (if oldS = .r): σ.val.P.paint b j₂ ∈ {.c, .d, .dot}.
  - σ.val.P.paint b j₂ = .c: layerOrd = 3. layerOrd newS (= .c) = 3. `3 ≤ 3` ✓.
  - σ.val.P.paint b j₂ = .d: layerOrd = 4. layerOrd newS = 3. `3 ≤ 4` ✓.
  - σ.val.P.paint b j₂ = .dot: need to rule out since `(b, j₂) ∈ σ.val.P.shape`.
    If `.dot` and `(b, j₂) ∈ P.shape`, by dot_match, `(b, j₂) ∈ σ.val.Q.shape`, so
    `b < σ.val.Q.shape.colLen j₂ ≤ σ.val.Q.shape.colLen 0 ≤ b`, contradiction.
- From Lemma `c_bottom_row_b_ge_j_in_cd` (if oldS = .c): σ.val.P.paint b j₂ ∈ {.c, .d, .dot}.
  - .c → layer 3. newS = .r (layer 2). `2 ≤ 3` ✓.
  - .d → layer 4. `2 ≤ 4` ✓.
  - .dot: same contradiction as above.

**Sub-case b2: i₂ > b.** Then `(i₂, j₂) ∈ σ.val.P.shape = shiftLeft μP` means
`i₂ < (shiftLeft μP).colLen j₂ = μP.colLen (j₂ + 1) ≤ μP.colLen 1 = b + 1`.
So `i₂ ≤ b`, contradicting `i₂ > b`. Vacuous.

**Case (c): (i₁, j₁) ≠ (b, 0), (i₂, j₂) = (b, 0).**
σ'.P.paint i₁ j₁ = σ.val.P.paint i₁ j₁.
σ'.P.paint b 0 = newS.
Need: `layerOrd σ.val.P.paint i₁ j₁ ≤ layerOrd newS`.

From `j₁ ≤ 0`, `j₁ = 0`. From `i₁ ≤ b` and `(i₁, 0) ≠ (b, 0)`, `i₁ < b`.

σ.val.mono_P at (i₁, 0) ≤ (b, 0) gives: `layerOrd σ.val.P.paint i₁ 0 ≤ layerOrd σ.val.P.paint b 0 = layerOrd oldS`.

**If oldS = .r (newS = .c):** layerOrd ≤ 2 → need ≤ 3. ✓ (2 ≤ 3).

**If oldS = .c (newS = .r):** layerOrd ≤ 3 → need ≤ 2.
Need to show σ.val.P.paint i₁ 0 is NOT .c and NOT .d.
- Not .c: by `c_bottom_unique_c_in_col0`, the unique .c in col 0 is at (b, 0). Since i₁ < b, σ.val.P.paint i₁ 0 ≠ .c.
- Not .d: layerOrd σ.val.P.paint i₁ 0 ≤ 3 (from σ.mono), so can't be .d (layer 4).
So σ.val.P.paint i₁ 0 ∈ {.dot, .s, .r}, all with layer ≤ 2. ✓

**Case (d): Both (i₁, j₁) = (i₂, j₂) = (b, 0).**
Same cell, same value, `≤` is reflexive. ✓

## Constraint 5: `mono_Q`

σ'.Q = σ.val.Q unchanged. Use σ.val.mono_Q directly.

## Constraint 6: `row_s`

**Goal:** `∀ i s₁ s₂ j₁ j₂, paintBySide σ'.P σ'.Q s₁ i j₁ = .s → paintBySide σ'.P σ'.Q s₂ i j₂ = .s → s₁ = s₂ ∧ j₁ = j₂`.

Key fact: **newS ≠ .s**. So if any cell has paint = .s in σ', the swap didn't affect it.

**Case s₁ = L, s₂ = L (both P side):**
- h₁: σ'.P.paint i j₁ = .s.
  - If (i, j₁) = (b, 0): σ'.P.paint b 0 = newS ≠ .s. Contradiction.
  - If (i, j₁) ≠ (b, 0): σ'.P.paint i j₁ = σ.val.P.paint i j₁ = .s.
- Similarly h₂: σ.val.P.paint i j₂ = .s.
- Apply σ.val.row_s at row i, sides L-L, j₁, j₂. Conclude `s₁ = s₂ ∧ j₁ = j₂`.

**Case s₁ = L, s₂ = R:** Extract h₁' : σ.val.P.paint i j₁ = .s (as above). h₂ is about σ.val.Q (unchanged). Apply σ.val.row_s L-R.

**Case s₁ = R, s₂ = L:** Symmetric.

**Case s₁ = R, s₂ = R:** Both on Q side, unchanged. Apply σ.val.row_s R-R.

## Constraint 7: `row_r`

**Goal:** `∀ i s₁ s₂ j₁ j₂, paintBySide σ'.P σ'.Q s₁ i j₁ = .r → paintBySide σ'.P σ'.Q s₂ i j₂ = .r → s₁ = s₂ ∧ j₁ = j₂`.

**Sub-case R → C swap (oldS = .r, newS = .c):**
After swap, the .r at (b, 0) is replaced by .c. So σ'.P has one fewer .r than σ.

**Case L-L:**
- h₁: σ'.P.paint i j₁ = .r.
  - If (i, j₁) = (b, 0): σ'.P.paint b 0 = .c ≠ .r. Contradiction.
  - Else: σ'.P.paint = σ.val.P.paint, so σ.val.P.paint i j₁ = .r.
- Similarly for h₂.
- Apply σ.val.row_r L-L.

**Case L-R:** Similar (h₂ is Q side, unchanged).
**Case R-L:** Symmetric.
**Case R-R:** Both Q side, unchanged.

**Sub-case C → R swap (oldS = .c, newS = .r):**
After swap, σ' has a new .r at (b, 0) that σ didn't have. But σ had .c at (b, 0), and by
`c_bottom_row_b_ge_j_in_cd`, σ.val.P.paint b j ∈ {.c, .d, .dot} for j ≥ 1. So σ had no .r in row b at all.

**Case L-L:**
- Sub-sub-case **i = b**: σ'.P has .r only at (b, 0) in row b (the new one). So any h_k : σ'.P.paint b j_k = .r forces (b, j_k) = (b, 0), i.e., j_k = 0.
  - More precisely: if j_k ≠ 0, σ'.P.paint b j_k = σ.val.P.paint b j_k ∈ {.c, .d, .dot} ≠ .r. Contradiction.
  - So j₁ = j₂ = 0, both at (b, 0). Conclude `s₁ = s₂ = L, j₁ = j₂ = 0`. ✓
- Sub-sub-case **i ≠ b**: swap doesn't affect row i. σ'.P.paint i j_k = σ.val.P.paint i j_k = .r. Apply σ.val.row_r L-L.

**Case L-R:**
- Sub-sub-case **i = b**: h₂: σ.val.Q.paint b j₂ = .r. But σ.val.Q is all-dots for D type, so σ.val.Q.paint b j₂ ∈ {.dot, outside shape ⇒ .dot}. Contradiction.
- Sub-sub-case **i ≠ b**: swap doesn't affect row i. Apply σ.val.row_r L-R.

**Case R-L:** Symmetric.

**Case R-R:** Q side, unchanged.

## Constraint 8: `col_c_P`

**Goal:** `∀ j i₁ i₂, σ'.P.paint i₁ j = .c → σ'.P.paint i₂ j = .c → i₁ = i₂`.

**Sub-case R → C swap (adds .c at (b, 0)):**
σ had no .c in col 0 (Lemma `r_bottom_no_c_in_col0`). The swap creates a new .c at (b, 0).

**Case j = 0:**
- If (i_k, 0) ≠ (b, 0) for some k, then σ'.P.paint i_k 0 = σ.val.P.paint i_k 0. But σ has no .c in col 0, so σ.val.P.paint i_k 0 ≠ .c. Contradiction with h_k.
- So both (i₁, 0) and (i₂, 0) must be (b, 0). Therefore i₁ = i₂ = b. ✓

**Case j ≠ 0:** Swap doesn't affect col j. Apply σ.val.col_c_P.

**Sub-case C → R swap (removes .c at (b, 0)):**
σ'.P has no new .c. Any .c in σ'.P at (i, j) corresponds to σ.val.P.paint i j = .c with (i, j) ≠ (b, 0) (since σ' at (b, 0) = .r now).

- h_k gives σ'.P.paint i_k j = .c.
  - If (i_k, j) = (b, 0): σ'.P.paint b 0 = .r ≠ .c. Contradiction.
  - Else: σ.val.P.paint i_k j = .c.
- Apply σ.val.col_c_P.

## Constraint 9: `col_c_Q`

σ'.Q = σ.val.Q. Use σ.val.col_c_Q.

## Constraint 10: `col_d_P`

**Goal:** `∀ j i₁ i₂, σ'.P.paint i₁ j = .d → σ'.P.paint i₂ j = .d → i₁ = i₂`.

Key fact: **newS ≠ .d**. So the swap neither creates nor removes .d at (b, 0).
(σ also didn't have .d at (b, 0) since σ.val.P.paint b 0 = oldS ∈ {.r, .c} ≠ .d.)

Any .d in σ' at some (i_k, j) corresponds to σ.val.P.paint i_k j = .d with (i_k, j) ≠ (b, 0).

- If (i_k, j) = (b, 0): σ'.P.paint b 0 = newS ≠ .d. Contradiction.
- Else: σ.val.P.paint i_k j = .d.
- Apply σ.val.col_d_P.

## Constraint 11: `col_d_Q`

σ'.Q = σ.val.Q. Use σ.val.col_d_Q.

## `paint_outside` for σ'.P

**Goal:** `∀ i j, (i, j) ∉ σ'.P.shape → σ'.P.paint i j = .dot`.

σ'.P.shape = σ.val.P.shape.

- If (i, j) = (b, 0): then (b, 0) ∉ σ.val.P.shape, but by Fact S2, (b, 0) ∈ σ.val.P.shape. Contradiction.
- Else: σ'.P.paint i j = σ.val.P.paint i j, and σ.val.P.paint_outside gives the result.

## Key technical Lean remark

The challenge in Lean is that when we write `refine ⟨⟨.D, ⟨σ.val.P.shape, swappedPaint b newS σ.val.P.paint, hpo_new⟩, σ.val.Q, ...⟩, ...⟩`, the goals in the constraint proofs reference the anonymous structure via projections (e.g., `{shape, paint, paint_outside}.paint b 0`), which should definitionally reduce to `swappedPaint b newS σ.val.P.paint b 0`, but `rw` tactics fail to match the pattern because they want syntactic equality.

**Fix:** Use `show` or `change` at the start of each constraint proof to rewrite the goal into the form with `swappedPaint` appearing explicitly. Then `rw` with `swappedPaint_at_b0` / `swappedPaint_col0_ne_b` / `swappedPaint_off_col0` works.

Alternatively: use `simp only [show (⟨shape, paint, po⟩ : PaintedYoungDiagram).paint = paint from rfl]` to fold the projection.

Alternatively: abstract the new PaintedYoungDiagram as a `let` before the `refine`, so the proofs operate on a single named entity.

## Line-count estimate

Each constraint is ~10-40 lines of Lean code. Total for all 13: ~250 lines.
With proper refactoring using helper lemmas (e.g., case_at_b0, case_away_b0), this can be reduced to ~150-200 lines.
