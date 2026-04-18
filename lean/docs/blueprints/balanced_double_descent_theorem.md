# Balanced Double Descent Theorem for B-type

## Lean 形式化
- `prop_10_9_B`, `cor_10_10_B` in `CountingProof/Section10.lean`
- 底层：`PBP.ddescent_inj_B`, `doubleDescent_B_injective_on_PBPSet` in `CombUnipotent/Tail.lean`

## Goal

Build a balanced-case analog of `card_PBPSet_Bplus_primitive_step_top_Q`. Once this is
proven, all 5 remaining sorries in `CorrespondenceB.lean` close.

## Primitive baseline (already proven, line 2040)

```lean
private theorem card_PBPSet_Bplus_primitive_step_top_Q {μP μQ : YoungDiagram}
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hQ_pos : μQ.colLen 0 ≥ 1)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1)
    (sym : DRCSymbol) :
    Fintype.card {τ : PBPSet .Bplus μP μQ //
      τ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym} =
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) *
        Fintype.card {v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) //
          topSym_B (μP.colLen 0) (μQ.colLen 0) v = sym}
```

The primitive bound works because:
- `hprimP`, `hprimQ` guarantee col 0 of the new P, Q extends columns ≥ 1
- `ValidCol0_B` captures all col 0 paintings that lift validly
- Fiber size = 4k for every σ (uniform across σ)

## Balanced case (target)

In balanced (r₂ ≤ r₃), **`hprimQ` fails** because μQ.shiftLeft.colLen 0 = r₃/2 ≥ r₂/2 = μP.colLen 0.

The naive lift construction would violate `mono_Q` across columns: in overlap rows, the new
col 0 symbol must be ≤ σ.Q(i, 0).layerOrd.

### Statement (target)

```lean
theorem card_PBPSet_Bplus_balanced_step_top_Q {μP μQ : YoungDiagram}
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hQ_pos : μQ.colLen 0 ≥ 1)
    (h_bal : μQ.shiftLeft.colLen 0 ≥ μP.colLen 0)   -- key: balanced condition
    (sym : DRCSymbol) :
    Fintype.card {τ : PBPSet .Bplus μP μQ //
      τ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym} =
      ∑ σ ∈ Finset.univ, (ValidCol0_B_bal σ sym).card
```

where the sum is over σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft, and
`ValidCol0_B_bal σ sym` is the balanced admissibility subtype of `ValidCol0_B` with
top symbol = `sym` AND satisfying cross-column `mono_Q` against σ's col 0.

### Uniform reformulation (empirically verified)

Numerical verification shows the **fiber count depends only on σ.Q_bot, not on the full
σ structure**:

```lean
theorem card_ValidCol0_B_bal_uniform
    (σ₁ σ₂ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_eq : σ₁.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 =
            σ₂.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0) :
    Fintype.card (ValidCol0_B_bal σ₁ sym) =
    Fintype.card (ValidCol0_B_bal σ₂ sym)
```

This uniformity is **unexpected** from the naive definition (which sees all of σ.Q col 0),
but empirically true for all 82 tested dp cases. The mathematical reason lies in the
balanced shape constraint + sym_Q + mono_Q interactions: the overlap region's painting
constraints bottom out at σ.Q_bot.

## Closure path for the 5 sorries

Once `ValidCol0_B_bal` and its cardinality formulas are built:

### Sorry 1 (line 3420) — `fiber_card_B_bal_Qd`
When σ.Q_bot = d:
- Admissibility vacuous for all overlap rows (d = layerOrd 4, highest).
- Fiber = |ValidCol0_B| = 4k.

### Sorry 2 (line 3442) — `fiber_card_B_bal_Qr`
When σ.Q_bot = r:
- Admissibility: overlap row top ≤ layerOrd 2.
- Excludes col-0 paintings where top would become c or d at boundary.
- Fiber = 4k - 2.

### Sorry 3 (line 3463) — `fiber_card_B_bal_Qlow`
When σ.Q_bot.layerOrd ≤ 1:
- Heavy admissibility: overlap row top ≤ 1.
- Fiber = 2k - 1.

### Sorry 4 (line 2998) — `card_B_DD_alpha_eq_countB_dd` inductive
Split primitive/balanced:
- Primitive: closed by `card_B_DD_alpha_primitive_step` (already exists).
- Balanced: via refinement of `card_B_bal_grouped_fiber` per new-Q_bot class.

### Sorry 5 (line 3137) — `card_B_SS_alpha_eq_countB_ss` inductive
Similar structure to sorry 4, but for Q_bot.lo ≤ 1 class.

## Implementation outline (~1300 lines)

### Phase A: Define ValidCol0_B_bal (~200 lines)

```lean
private def ValidCol0_B_bal {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (hP hQ : ℕ) : Type :=
  { v : ValidCol0_B hP hQ //
    ∀ i, i < min hP (μQ.shiftLeft.colLen 0) →
      (liftCol0Q_B hP hQ v i).layerOrd ≤ (σ.val.Q.paint i 0).layerOrd }
```

### Phase B: Lift construction for balanced case (~400 lines)

`liftPBP_B_bal σ v` similar to `liftPBP_B` but handles balanced cross-column constraints.
Key: must also respect `row_s`/`row_r` in overlap — if σ.Q(i, 0) = .s then new τ.Q(i, 1)
cannot = .s (row_s would require equal cols).

### Phase C: Round-trip + injectivity (~300 lines)

Mirror of `liftPBP_B_round_trip` and `liftPBP_B_injective` for balanced.

### Phase D: Card formulas for ValidCol0_B_bal (~300 lines)

Three per-Q_bot-class cardinalities:
- `ValidCol0_B_bal_card_Qd σ = 4k` (when σ.Q_bot = d)
- `ValidCol0_B_bal_card_Qr σ = 4k - 2`
- `ValidCol0_B_bal_card_Qlow σ = 2k - 1`

### Phase E: Integrate into the 5 sorries (~100 lines)

Apply the lemmas to close each fiber sorry and the A1/A3 inductive cases.

## Why uniformity holds (proof sketch)

Given two sub-PBPs σ₁, σ₂ with σ₁.Q_bot = σ₂.Q_bot:
- In balanced case, μQ.shiftLeft.colLen 0 = μP.colLen 0 (both = some common c).
- σ.Q col 0 has height c; mono_Q sorts it ascending, so its max is σ.Q(c-1, 0) = σ.Q_bot.
- For any v ∈ ValidCol0_B admissible against σ₁: by monotonicity, v's top ≤ σ₁.Q_bot.
- If σ₂ has the same Q_bot, v is also admissible against σ₂ (since monotonicity bound
  only references the top).

**But** this argument only works if the admissibility bound is solely at the top row.
The mono_Q constraint is **row-by-row**, not just top. So the full story requires:
- All σ.Q col 0 entries ≤ σ.Q_bot (by mono).
- Any admissible v has col 0 entries ≤ σ.Q col 0 entries (by new-τ.mono_Q across cols).
- These chain: v entries ≤ σ.Q_bot.

The tightest bound is at the top row (i = c-1), but other rows may have weaker σ.Q values
(e.g., dots). Those give tighter constraints — but `v` is also monotone ascending, so
`v(0) ≤ v(c-1) ≤ σ.Q_bot`. Under this chain, the count is determined by σ.Q_bot.

More precisely: v is a DSeq (monotone ascending non-dot) painting. For v admissible
against σ, we need v(i) ≤ σ.Q(i, 0) for overlap rows. But σ.Q(i, 0) ≤ σ.Q(c-1, 0) by
mono. And v(i) ≤ v(c-1). So if σ.Q(c-1, 0) = σ.Q_bot gives the bound on v(c-1), and
v(i) ≤ v(c-1) ≤ σ.Q_bot bounds all rows... but this needs v(i) ≤ σ.Q(i, 0) not
just v(i) ≤ σ.Q_bot.

Actually wait: σ.Q(i, 0) may be dot for i < some point. Then v(i) ≤ dot.layerOrd = 0
forces v(i) = dot. But v is non-dot throughout its DSeq tail.

This is where the row_s/row_r constraints + dot_match interact. The full picture is
subtle and needs careful handling.

## Numerical verification status

- 82 dp cases tested in `tools/verify_all_B_lemmas.py` — all pass.
- 11 balanced cases verified in `tools/verify_fiber_by_Qbot.py` — fiber counts
  (4k, 4k-2, 2k-1) match.
- Primitive case verified in `tools/verify_primitive_fiber_class.py`.

## Estimated effort

~1300 lines across 5 phases. Realistic completion: 3-5 focused sessions of
~300 lines each.

## Current session contribution

Documentation + structural alignment. The actual Lean proofs remain to be written.
Target: establish `ValidCol0_B_bal` skeleton + at least one cardinality formula
in next session.
