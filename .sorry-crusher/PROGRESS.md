# Progress — Prop10_8_M.lean

## Current state (verified by grep)

- Sorries: 2 (prompt said 3, but actual is 2)
- File length: 1164 lines
- `lake build`: PASSES

## Remaining sorries

### Sorry #1 — `descentMB_liftBM_naive_Q_paint` (line 954)

**Location**: Prop10_8_M.lean:954

**Signature**:
```
theorem descentMB_liftBM_naive_Q_paint (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1) :
    ∀ i j, PBP.descentPaintR_MB
      (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc) i j = σ.Q.paint i j
```

**Goal**: For every (i, j), prove descent's Q paint at (i, j) of τ = liftBM_naive σ equals σ.Q.paint(i, j).

Recall:
- `PBP.descentPaintR_MB τ i j = if i < dotScolLen τ.P (j+1) then .dot else if i < dotScolLen τ.Q j then .s else τ.Q.paint i j`
- τ.Q.paint(i,j) = `liftPaintQ_naive σ i j` = `if (i,j) ∈ σ.Q.shape ∧ ¬(σ.Q(i,j).lo ≤ 1) then σ.Q(i,j) else .dot`

**Strategy**:
Case split on whether (i,j) ∈ σ.Q.shape (= μQ).
- **Outside σ.Q.shape**: σ.Q.paint(i, j) = .dot, and we need descent to give .dot.
  - (i,j) ∉ μQ = τ.Q.shape, so descent should also be .dot... but wait, descent doesn't check shape. It's `.dot` if i < dotScolLen τ.P (j+1). Need to show: outside μQ, descent gives .dot.
  - Actually, since we're working with the τ PBP, outside its shape everything is dot via paint_outside. But descentPaintR_MB doesn't directly check shape. Need lemma.
- **Inside σ.Q.shape**: σ.Q.paint ∈ {•, s, r, d} (B-type Q).
  - σ.Q = • or s: σ.Q.lo ≤ 1. Then τ.Q(i,j) = • (by liftPaintQ_naive_mem / dot). Need descent to return σ.Q.
    - Case σ.Q = •: descent should be .dot (if i < dotScolLen τ.P (j+1)) or .s? No — should be •.
    - Case σ.Q = s: descent should be .s.
    - Subtlety: dotScolLen τ.P(j+1) = dotScolLen σ.P(j) ... the boundary aligns with shiftLeft.
  - σ.Q = r or d: σ.Q.lo > 1. Then τ.Q(i,j) = σ.Q(i,j). descent's third branch returns τ.Q.paint = σ.Q. ✓

Key insight: dotScolLen equalities between τ and σ across the shape shift.
- dotScolLen τ.P (j+1) = dotScolLen σ.P j (shiftLeft)
  - But τ.P at col j+1 uses σ.P at col j. When σ.P(i,j) = dot, τ.P(i,j+1) ∈ {dot, s}; if σ.P(i,j) = c, τ.P(i,j+1) = c.
  - Since σ is B-type, σ.P ∈ {dot, c}. So σ.P.lo ∈ {0, 3}. The dotScolLen σ.P j counts cells with lo ≤ 1 = dot count = σ.P.dotDiag.colLen j.
  - Similarly τ.P.lo ≤ 1 at (i, j+1) iff σ.P(i, j) ≠ c iff σ.P(i,j) = dot.
  - Plus (i, j+1) must be in μP for τ.P to be non-dot.

**Informal sketch (from comments in file)**:
```
-- σ.Q = dot/s: τ.Q = dot, need descent to produce dot/s based on dotScolLen regions.
-- σ.Q = r/d: τ.Q = σ.Q, descent returns τ.Q directly.
-- Key dotScolLen equality: dotScolLen τ.Q j = dotScolLen σ.Q j (same {dot/s}-boundary).
```

**Known infrastructure (file-local)**:
- `liftPaintP_naive_succ_c_iff` (line 140)
- `liftPaintP_naive_succ_s_iff` (line 153)
- `liftPaintQ_naive_dot_iff` (line 169)
- Descent helpers in Descent.lean: `ge_dotScolLen_of_nonDot`, `dotScolLen_eq_dotSdiag_colLen`, `layerOrd_gt_one_of_ge_dotScolLen`, `dotScolLen_le_colLen`, `layerOrd_le_one_of_lt_dotSdiag_colLen`, `paint_ne_dot_of_ge_dotScolLen`

**Plan of attack**:

1. Prove helper **`dotScolLen_liftBM_P_succ_eq`**: `dotScolLen τ.P (j+1) = dotScolLen σ.P j + [correction for col 0 bottom if γ = B-]`.
   Actually simpler: show that τ.P(i, j+1).lo ≤ 1 ↔ (i, j+1) ∈ μP ∧ σ.P(i, j) ≠ c.
   But σ.P(i, j) ≠ c means σ.P(i, j) = dot (in overlap) or (i, j) ∉ σ.P.shape.
   Or just iff: `(i, j) ∈ σ.P.shape ∧ σ.P(i, j).lo ≤ 1` ↔ `(i, j+1) ∈ μP ∧ τ.P(i, j+1).lo ≤ 1 ∧ ¬(γ=B- at bottom)`.
   
2. Prove helper **`dotScolLen_liftBM_Q_eq`**: `dotScolLen τ.Q j = dotScolLen σ.Q j`.
   Because τ.Q(i,j).lo ≤ 1 ↔ (by liftPaintQ_naive def) σ.Q(i,j).lo ≤ 1 (when in σ.Q.shape).

3. Main proof: case split on whether (i,j) ∈ μQ and the value σ.Q.paint(i,j).

**Estimated effort**: 60-90 lines total. 3-4 helpers + main proof.

### Sorry #2 — `descent_image_balanced` (line 1148)

**Location**: Prop10_8_M.lean:1148

**Signature**:
```
theorem descent_image_balanced {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0) (h_pos : μP.colLen 0 > 0) :
    Fintype.card (PBPSet .M μP μQ) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card +
      (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card
```

**Strategy**: Build an Equiv analogous to `descent_equiv_primitive` but restricted to the "non-SS" subset on the B⁺/B⁻ side. Or: first show that `PBPSet .M μP μQ` embeds into `Finset.filter` of non-SS σ via descent, and this is a bijection.

**Implementation routes**:

**Route A (explicit Equiv)**: Build Equiv between:
  - LHS: `PBPSet .M μP μQ`
  - RHS: Sum of two subtypes `{σ : PBPSet .Bplus μP.shiftLeft μQ // non-SS σ}` and `{σ : PBPSet .Bminus μP.shiftLeft μQ // non-SS σ}`
  Then apply Fintype.card_sum + Fintype.card_subtype (with filter) to get target.

**Route B (descentMB_sum filter)**: Show that image of `descentMB_sum : PBPSet .M μP μQ → Sum` lies in filter set, and is a bijection onto.

**Route C (factor through primitive case)**: Construct a PBPSet-level map that, for balanced case, is exactly the filter-based map.

Let me think about the cleanest route. The key observation: in balanced case, the descent bijection still works, but only surjects onto non-SS σ's (because σ-bottom must be non-SS for lift to produce a valid M PBP).

Actually, looking at `liftBM_naive_PBPSet` definition, the h_bal_exc constraint is REQUIRED for balanced. So lift only exists for non-SS inputs. Descent is always defined (no filter needed). The equation we want: |M| = |non-SS B⁺| + |non-SS B⁻|.

So proof: build Equiv `PBPSet .M μP μQ ≃ {σ : PBPSet .Bplus _ _ // non-SS σ} ⊕ {σ : PBPSet .Bminus _ _ // non-SS σ}`, then use `Fintype.card_congr`.

**Key observation**: descent(τ) for τ ∈ M is always non-SS in balanced case. Because if τ ∈ M in balanced shape, we need (bottom, 0) ∈ μQ AND τ.Q.paint (bottom, 0) must satisfy τ's constraints. Since descent preserves Q shape and τ is in M, at (bottom, 0) in μQ, descent's Q paint = τ.Q.paint. For the descent σ to be non-SS, we need σ.Q(bottom, 0).lo > 1.

**Question**: Why does τ ∈ M → descent σ has σ.Q(bottom, 0).lo > 1?

From M's definition: τ.Q ∈ {•, r, d}. At (bottom, 0) in μQ: τ.Q(bottom, 0) ∈ {•, r, d}. τ.Q = • would mean both P and Q = • at (bottom, 0) via dot_match, but in balanced + M, bottom of P col 0 is either c or • — it's column 0 after all. Need to check.

**Estimated effort**: 50-100 lines. Similar Equiv structure to primitive case but with Subtype.

## Order of attack

1. **Q_paint first** — more prerequisite work but no new Equiv/Fintype machinery needed.
2. **descent_image_balanced second** — needs the Equiv composition + Subtype cardinality.
