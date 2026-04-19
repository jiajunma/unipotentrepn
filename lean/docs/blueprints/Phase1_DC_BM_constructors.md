# Phase 1: `descentDC_raw` + `descentBM_raw` constructors

**Scope**: 2 new single-descent PBP constructors to complete the ALT
chain infrastructure.

**Date**: 2026-04-19

## Existing template

`descentCD_raw` in `CountingProof/CorrespondenceC.lean:125-244`
provides the template for C→D direction:

```lean
noncomputable def descentCD_raw (τ : PBP) (hγ : τ.γ = .C)
    (μP μQ : YoungDiagram) (hPsh : τ.P.shape = μP) (hQsh : τ.Q.shape = μQ)
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) : PBP where
  γ := .D
  P := { shape := μP, paint := PBP.descentPaintL_CD τ, … }
  Q := { shape := YoungDiagram.shiftLeft μQ, paint := fun _ _ => .dot, … }
  -- 11 proof obligations (sym_P, sym_Q, dot_match, mono_P, mono_Q,
  --  row_s, row_r, col_c_P, col_c_Q, col_d_P, col_d_Q)
```

~120 lines. Each proof obligation handled separately.

## Target 1: `descentDC_raw` (D → C)

### Shapes (from descentPaint*_DC)

- `descentPaintL_DC τ i j = if i < dotScolLen τ.P (j + 1) then .dot else τ.P.paint i (j + 1)`
  → P' shifts left: `P'.shape = τ.P.shape.shiftLeft`
- `descentPaintR_DC τ i j = if i < dotScolLen τ.P (j + 1) then .dot else if i < τ.Q.shape.colLen j then .s else .dot`
  → Q' keeps shape: `Q'.shape = τ.Q.shape`

### Signature (for τ ∈ PBP .D with shapes from dp)

```lean
noncomputable def descentDC_raw (τ : PBP) (hγ : τ.γ = .D)
    (μP μQ : YoungDiagram) (hPsh : τ.P.shape = μP) (hQsh : τ.Q.shape = μQ)
    -- may need coherence hypothesis on (μP, μQ, paint) for dp structure
    : PBP where
  γ := .C
  P := { shape := YoungDiagram.shiftLeft μP
         paint := PBP.descentPaintL_DC τ
         paint_outside := … }
  Q := { shape := μQ
         paint := PBP.descentPaintR_DC τ
         paint_outside := … }
  -- 11 proof obligations
```

### Proof obligations (11 per paint)

For each PBP constraint, adapt `descentCD_raw`'s pattern:
- **sym_P (C type allows {•, r, c, d})**:
  `descentPaintL_DC τ i j = if i < dotScolLen τ.P (j+1) then .dot else τ.P.paint i (j+1)`.
  - Branch 1: `.dot` is C-allowed. ✓
  - Branch 2: `τ.P.paint i (j+1)` for `i ≥ dotScolLen τ.P (j+1)`. By `layerOrd_gt_one_of_ge_dotScolLen`, paint has layerOrd > 1, i.e., ∈ {r, c, d}. Which IS C-allowed. ✓

  **Key insight**: the `dotScolLen` threshold structure automatically
  excludes `.s` from the "paint-through" branch, so `sym_P` for C holds
  without explicit filtering. This is why paper's descent works cleanly.
- **sym_Q (C type Q allows {•, s})**: descentPaintR_DC returns .dot or .s based on ranges. ✓

- **dot_match**, **row_s**, **row_r**, **col_c_P**, **col_c_Q**, **col_d_P**, **col_d_Q**, **mono_P**, **mono_Q**: adapt `descentCD_raw` patterns.

### Complication

The D→C direction has the "s transformation" issue: D's P allows s, but
C's P doesn't. The paper's D→C descent must handle this via dotScolLen
regions (s appears only BELOW dotScolLen). Under descent, s entries
above the s-line become dots in C-side; s entries below translate…
Hmm, actually descentPaintL_DC just passes τ.P.paint directly for
i ≥ dotScolLen (j+1). So if τ.P.paint i (j+1) = .s for some such i,
it goes through to the C-side, which is **not allowed**.

This suggests descentPaintL_DC is NOT paper's exact D→C descent at the
paint level, OR there's an implicit assumption that such .s don't
occur under some condition.

**Needs paper re-reading**: what does paper §10 say about D→C descent's
paint transformation exactly?

## Target 2: `descentBM_raw` (B → M)

### Shapes (from descentPaint*_BM)

- `descentPaintL_BM`: P keeps shape, paint refilled
- `descentPaintR_BM`: Q shifts left

So B → M: `P.shape` unchanged, `Q.shape = τ.Q.shape.shiftLeft`.

### Signature

```lean
noncomputable def descentBM_raw (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : τ.P.shape = μP) (hQsh : τ.Q.shape = μQ)
    : PBP where
  γ := .M
  P := { shape := μP, paint := PBP.descentPaintL_BM τ, … }
  Q := { shape := YoungDiagram.shiftLeft μQ, paint := PBP.descentPaintR_BM τ, … }
```

### Proof obligations

Similar to descentCD_raw. B-type PBP has:
- P allowed: {•, c}
- Q allowed: {•, s, r, d}

M-type:
- P allowed: {•, s, c}
- Q allowed: {•, r, d}

Transition: B's P ({•, c}) → M's P ({•, s, c}) — allows more; sym_P is easier.
B's Q ({•, s, r, d}) → M's Q ({•, r, d}) — must exclude s. Similar s-transformation issue but reversed: B's Q has s, M's Q doesn't.

Likely similar dotScolLen-based resolution.

## Session scope recommendation

Each constructor is ~120 lines of PBP constraint discharge with
detailed case analysis on paint regions. **ONE CONSTRUCTOR PER SESSION**
is the realistic scope.

Suggested order:
1. `descentDC_raw` (this session if time allows, else next)
2. `descentBM_raw` (next-next session)
3. Define PBPSet-level wrappers (`descentDC_PBP`, `descentBM_PBP`)

Both are pure construction work, high mechanical, but requires
careful paint-region analysis. The real subtlety is the s-symbol
transformation between D/B and C/M types.

## Alternative simpler path

If `descentDC_raw` / `descentBM_raw` prove too complex, consider:

**Express ALT chain via existing double-descent** + intermediate type tracking.
For example, `doubleDescent_D_PBP` = `descentCD (descentDC τ)`. So we
can "unfold" each double step into two single steps conceptually without
needing the single constructors as first-class defs.

Specifically: define a chain predicate that says "there's some alternating
sequence τ_D → τ_C → τ_D → τ_C → ... → base" without constructing each
τ_C explicitly. Use the fact that doubleDescent factors through C-type
PBPs (implicitly) for the sign/shape tracking.

This avoids building `descentDC_raw` / `descentBM_raw` at all. Trade-off:
the chain structure is less concrete.
