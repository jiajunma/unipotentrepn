# Progress — Prop10_8_M.lean

## Summary

- Started session 2 with 1 sorry (descent_image_balanced).
- Closed all sorries: 0 remaining.
- Build: PASSES.

## Closed this session (session 2)

### descent_image_balanced (was line 1367, closed)

**Key discovery**: The theorem statement was still incorrect after commit 8b3e618.
Specifically, the B⁺ filter `σ.Q(bottom, 0) ≠ •` was too restrictive.

**Counterexample**: For μP = μQ = single row of length 2 (`ofRowLens [2]`):
- |M| = 9 (manually enumerated + verified in Lean with `tau1` = all-dot M PBP)
- Old filter sum (B⁺ with σ.Q≠•, B⁻ with lo>1) = 6.
- Mismatch of 3.

The issue: all-dot M τ (and τ.P = (•,s), (•,c) variants) descend to B⁺ σ
with σ.Q(bottom, 0) = • (via Zone 1 in descentPaintR_MB). These τ are in
the image but fail the old filter.

**Correct statement**: |M| = |B⁺| + |{σ ∈ B⁻ : σ.Q(bottom, 0).lo > 1}|.
- Verified on [1]: |M|=5 = 3 + 2. ✓
- Verified on [2]: |M|=9 = 7 + 2. ✓

### Refactoring work

Major refactor: `h_bal_exc` signature changed from
```
μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
  (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1
```
to
```
μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 → σ.γ = .Bminus →
  (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1
```

The new `σ.γ = .Bminus` hypothesis allows vacuous satisfaction for σ ∈ B⁺
(since the conclusion isn't needed when σ.γ ≠ Bminus), enabling total lifts
for ALL B⁺ σ (not just those with σ.Q.lo > 1).

Helpers added:
- `h_bal_exc_of_Bplus`: for σ.γ = .Bplus, provides vacuous h_bal_exc.
- `M_descent_Bminus_Q_lo_gt_one`: asymmetric forward theorem.
  For balanced τ ∈ M with descentType_M = .Bminus, proves σ.Q(bottom, 0).lo > 1.
  Proof via Zone analysis:
  - descentType_M = Bminus → ∃ c in τ.P col 0 → by mono_P c is at bottom.
  - dot_match: τ.P(bot, 0) = c → τ.Q(bot, 0) ≠ • → τ.Q ∈ {r, d}, lo > 1.
  - Zone 1 (bottom < dotScolLen τ.P 1): would require τ.P(bot, 1) ∈ {•, s},
    but mono_P j↑ gives τ.P(bot, 0).lo ≤ τ.P(bot, 1).lo, 3 ≤ 1 false. ∴ NOT Zone 1.
  - Zone 2 (bottom < dotScolLen τ.Q 0): would force τ.Q(bot, 0).lo ≤ 1,
    contradicting > 1. ∴ NOT Zone 2.
  - Zone 3: σ.Q(bot, 0) = τ.Q(bot, 0). lo > 1. ✓
- `descentMB_sum_balanced`: forward map M → B⁺ ⊕ non-SS B⁻.
- `descent_equiv_balanced`: full Equiv.

Updated `descent_image_balanced` to new statement + proof via Equiv.

### Cascading signature updates

All these lemmas had h_bal_exc updated to the new signature:
- `liftPaintP_naive_col0_to_succ_mono`
- `liftBM_naive` 
- `descentType_M_liftBM_naive`
- `descentMB_liftBM_naive_P_paint`
- `descentMB_liftBM_naive_Q_paint`
- `descentMB_liftBM_naive`
- `τP_succ_c_not_dotScolLen`, `τP_succ_outside_not_dotScolLen`
- `liftBM_naive_PBPSet`
- `h_bal_exc_of_primitive` (added σ.γ = .Bminus param)
- `liftBM_from_nonSS`

## Closed in session 1

### descentMB_liftBM_naive_Q_paint (line 954, closed with commit 88f7ee4)

Case analysis on σ.Q ∈ {dot, s, r, d}:
- dot: Zone 1 via τ.P(i, j+1).lo ≤ 1.
- s: ¬Zone 1; Zone 2 via τ.Q = dot.
- r/d: ¬Zone 1; τ.Q preserved; ¬Zone 2; Zone 3.
- Outside: Zones collapse to dot.

## Files modified (session 2)

- `/Users/hoxide/mycodes/unipotentrepn/lean/CombUnipotent/CountingProof/Prop10_8_M.lean`
  - Lines added: ~200
  - Helpers added: 4
  - Refactoring touched: 10+ lemmas

## Verification

- `grep -c sorry Prop10_8_M.lean`: 0
- `lake build`: PASSES (full project)
