# Progress — Prop10_8_M.lean

## Summary

- Started session: 2 sorries (descentMB_liftBM_naive_Q_paint, descent_image_balanced).
- Closed: 1 (Q_paint).
- Remaining: 1 (descent_image_balanced — UNPROVABLE as stated).

## Verified State

- `grep -c sorry`: 2 lines contain "sorry" string (1 actual sorry + 1 in comment).
- Actual unresolved sorries: 1.
- `lake build`: PASSES.

## Closed this session

### descentMB_liftBM_naive_Q_paint (line 954, closed with commit 88f7ee4)

Case analysis on σ.Q ∈ {dot, s, r, d}:
- dot: Zone 1 via τ.P(i, j+1).lo ≤ 1 (from σ.P = dot via dot_match).
- s: ¬Zone 1 (σ.P = c or outside shape); Zone 2 via τ.Q = dot.
- r/d: ¬Zone 1; τ.Q preserved; ¬Zone 2 since τ.Q.lo > 1; Zone 3.
- Outside σ.Q.shape: σ.Q = dot by paint_outside; descent via split_ifs.

Helpers added:
- `τP_succ_outside_not_dotScolLen`
- `τP_succ_c_not_dotScolLen`
- `σP_c_of_Q_ne_dot`

~200 lines of proof.

## Remaining (unprovable as stated)

### descent_image_balanced (line 1371)

**The theorem is provably FALSE as currently stated.**

Statement: `card M = card {σ ∈ B+ : σ.Q(bottom).lo > 1} + card {σ ∈ B- : σ.Q(bottom).lo > 1}`.

Counterexample: μP = μQ = single cell [1]:
- card(PBPSet .M μP μQ) = 5.
- Non-SS B+ (Q ∈ {r, d}) = 2, Non-SS B- (Q ∈ {r, d}) = 2.
- 2 + 2 = 4 ≠ 5.

The issue is B+ "correction": in the paper (see `docs/blueprints/B_tail_symbol_correction.md`), a B+ σ with Q(bottom) = s is classified as RC (non-SS), not SS. So the correct filter for B+ is `Q ≠ dot` (not `Q.lo > 1`).

The correct theorem should read:
```
card M = card {σ ∈ B+ : σ.Q(bottom) ≠ dot} + card {σ ∈ B- : σ.Q(bottom).lo > 1}
```

(Or equivalently via corrected tailClass_B.)

### Infrastructure added (commit 550b6b4)

- `liftBM_from_nonSS`: total backward map from non-SS σ (Subtype) to M τ.
  Takes `σp : {σ : PBPSet .Bplus ... // (σ.val.Q.paint ... 0).lo > 1}` and
  passes the proof as h_bal_exc to `liftBM_naive`.

This would serve the backward direction of an Equiv if the forward direction
(M descents to non-SS) were provable. Since it isn't with the current filter,
the sorry remains.

### What would be needed to close

Either:
1. **Restate** the theorem with corrected filter (different for B+ vs B-).
   Then prove forward direction with B+ correction.
2. **Find a different proof route** that bypasses the descent-image argument
   (e.g., using existing `liftMB_raw` or a direct cardinality argument).
3. **Relax the theorem** to an inequality.

These require >100 lines of additional infrastructure and may require changes
to downstream callers if the signature changes.

## Recommendation

Escalate to user: the sorry's intended meaning is incorrect as stated. Either
change the statement, or accept the admitted status.
