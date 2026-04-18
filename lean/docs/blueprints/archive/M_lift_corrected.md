# M Lift: Corrected Construction

## Problem with current lift

Current `liftPaintQ_BM` maps σ.Q(i,j) directly (collapse s→dot), while `liftPaintP_BM` shifts σ.P right. This creates a column misalignment: P(i,j+1) comes from σ.P(i,j) but Q(i,j+1) comes from σ.Q(i,j+1) (NOT shifted). The `dot_match` at (i,j+1) requires σ.P(i,j)=dot ↔ σ.Q(i,j+1) layerOrd ≤ 1, which is a cross-column condition that doesn't hold for all B PBPs.

## Correct approach: use `_fill_ds_M` to transform BOTH P and Q

M→B descent does:
1. Remove P col 0
2. Apply `_fill_ds_B` to (remaining P, Q)

B→M lift should:
1. Apply `_fill_ds_M` to (σ.P, σ.Q) — this transforms BOTH P and Q simultaneously
2. Insert P col 0

`_fill_ds_M` definition (from standalone.py):
```python
for colL, colR in zip_longest(drcL, drcR):
    cL, cR = _count_ds(colL), _count_ds(colR)  
    ndrcL.append('*' * cR + 's' * (cL - cR) + colL[cL:])
    ndrcR.append('*' * cR + colR[cR:])
```

For B type input (P ∈ {dot, c}, Q ∈ {dot, s, r, d}):
- cL = #{dot in P col j} (B P has no s, so dot/s count = dot count)
- cR = #{dot/s in Q col j} (both dot and s count)
- New P col j = cR dots + (cL - cR) s's + P's c cells
- New Q col j = cR dots + Q's non-dot-s cells (r, d only)

This simultaneously:
- Expands P's dot zone to match Q's dot/s zone (adding s's where Q had s)
- Collapses Q's s zone to dots

After `_fill_ds_M`:
- New P ∈ {dot, s, c} (M P symbols ✓)
- New Q ∈ {dot, r, d} (M Q symbols ✓)
- dot_match holds because: new P has dots exactly where new Q has dots
  (both have cR dots at the top of each column)

## Formal definition

```
liftPaint_M_P (σ : B PBP) (i j : ℕ) : DRCSymbol :=
  let cR := dotScolLen σ.Q j  -- #{dot/s in Q col j}
  if i < cR then .dot
  else if i < dotScolLen σ.P j then .s  -- expansion zone
  else σ.P.paint i j  -- non-dot zone (= c)

liftPaint_M_Q (σ : B PBP) (i j : ℕ) : DRCSymbol :=
  let cR := dotScolLen σ.Q j  -- #{dot/s in Q col j}
  if i < cR then .dot
  else σ.Q.paint i j  -- if layerOrd > 1: unchanged. If layerOrd ≤ 1: was already counted in cR.
  -- Actually: i ≥ cR means σ.Q(i,j) has layerOrd > 1 (by definition of dotScolLen)
  -- So σ.Q(i,j) ∈ {r, d} → M Q allowed ✓
```

Then M PBP:
- P(i, 0) = fill (dot/s + maybe c at bottom for B⁻)
- P(i, j+1) = liftPaint_M_P(σ)(i, j)
- Q(i, j) = liftPaint_M_Q(σ)(i, j)  -- NO SHIFT for Q

**Wait**: this doesn't shift P! The descent shifts P LEFT. So the lift should shift P RIGHT:
- M P(i, 0) = new col 0
- M P(i, j+1) = liftPaint_M_P(σ)(i, j)
- M Q(i, j) = liftPaint_M_Q(σ)(i, j)

dot_match at (i, j+1):
- P(i, j+1) = liftPaint_M_P(σ)(i, j) = dot iff i < dotScolLen(σ.Q, j) =: cR
- Q(i, j+1) = liftPaint_M_Q(σ)(i, j+1) = dot iff i < dotScolLen(σ.Q, j+1) =: cR'

These are DIFFERENT cR values (for different columns j vs j+1). So dot_match at (i,j+1) requires: i < cR ↔ i < cR'. This is NOT true in general (cR ≠ cR').

**Problem again!** The column misalignment persists because P is shifted but Q is not.

## Fundamental insight

The issue is structural: M→B descent shifts P LEFT while keeping Q UNSHIFTED. This means the LIFT must shift P RIGHT while keeping Q UNSHIFTED. But dot_match requires same-column alignment.

The way the paper handles this: the shapes (ι, j) have the interleaving property. The descent preserves this: after removing P col 0, the remaining (P', Q') still interleave. And `_fill_ds_B` only redistributes within each column pair (P col j, Q col j).

The lift uses `_fill_ds_M` which also redistributes within each column pair. After redistribution, the new (P_M, Q_M) at column j are:
- P_M(i, j) has cR(j) dots then s then c
- Q_M(i, j) has cR(j) dots then r/d

dot_match at (i, j) holds because both have cR(j) dots at the top.

Then inserting P col 0 and shifting P right: P_shifted(i, j+1) = P_M(i, j). Q stays as Q_M(i, j). dot_match at (i, j+1): P_shifted(i, j+1) = P_M(i, j) = dot iff i < cR(j). Q_M(i, j+1) = dot iff i < cR(j+1).

Hmm, still misaligned. Unless: the shift also shifts the Q_M. But M→B descent keeps Q unshifted.

**WAIT**. Let me re-read the descent more carefully.

descentPaintL_MB(τ)(i, j) = if i < dotScolLen(τ.P, j+1) then dot else τ.P(i, j+1)
descentPaintR_MB(τ)(i, j) = if i < dotScolLen(τ.P, j+1) then dot 
                              elif i < dotScolLen(τ.Q, j) then s 
                              else τ.Q(i, j)

So descent P uses τ.P at j+1 (shifted). Descent Q uses τ.Q at j (NOT shifted). But the dot boundary in Q uses dotScolLen(τ.**P**, j+1) — which is the P boundary at the SHIFTED column!

This is the key: the Q refill uses the P boundary, not the Q boundary. The refill adds dots up to dotScolLen(P, j+1), then s's up to dotScolLen(Q, j).

So the lift should reverse this:
- Given B PBP σ with P' and Q' paints
- Q'(i, j) has dots up to dotScolLen(P, j+1), then s's up to dotScolLen(Q, j), then Q(i, j)
- P'(i, j) has dots up to dotScolLen(P, j+1), then P(i, j+1)

Reverse:
- τ.P(i, j+1) = P'(i, j) (if i ≥ dotScolLen_zone) = σ.P(i, j) for i ≥ cL
- τ.Q(i, j) = Q'(i, j) for i ≥ cR_zone

The column indices align: P'(i, j) → τ.P(i, j+1), Q'(i, j) → τ.Q(i, j). So:
- τ.P(i, j+1) recovers from σ.P(i, j) — **same j in σ and τ**
- τ.Q(i, j) recovers from σ.Q(i, j) — **same j in σ and τ**

dot_match at (i, j) in τ: 
- τ.P(i, j) at j ≥ 1: = P_M(i, j) which is dot/s/c
- τ.Q(i, j): = Q_M(i, j) which is dot/r/d

For j ≥ 1:
- τ.P(i, j) = dot iff ... from liftPaint_M_P at (i, j-1)... 
  NO: τ.P is the FULL M P, not just the lifted version.

Actually τ.P(i, j+1) = reverse_fill(σ.P(i, j), σ.Q(i, j)). And τ.Q(i, j) = reverse_fill_Q(σ.Q(i, j)).

The reverse_fill for column j simultaneously determines τ.P(i, j+1) and τ.Q(i, j) from (σ.P(i, j), σ.Q(i, j)):
- Top cR(j) cells: τ.P(i, j+1) = dot, τ.Q(i, j) = dot (where cR = dotScolLen(σ.Q, j))
- Middle (cL(j) - cR(j)) cells: τ.P(i, j+1) = dot, τ.Q(i, j) = s
  Wait: σ.P has cL dots at the top. The middle zone in σ is s zone (from _fill_ds_B which added s's).
  In reverse (_fill_ds_M): these s's in σ.Q become dots in τ.Q, and the corresponding dots in σ.P become s's in τ.P.
  
  Hmm let me think more carefully.

Actually: the reverse is NOT _fill_ds_M applied to σ. It's the INVERSE of _fill_ds_B.

_fill_ds_B(P, Q) → (P', Q') where:
- P'(i, j) = dot for i < cL(j), then P non-dot/s (= c)
- Q'(i, j) = dot for i < cL(j), then s for cL(j) ≤ i < cR(j), then Q non-dot/s (= r/d)
  where cL = #{dot in P col j}, cR = #{dot/s in Q col j}

Wait: B's _fill_ds_B:
```
cL, cR = _count_ds(colL), _count_ds(colR)
ndrcL = '*' * cL + colL[cL:]      # cL dots, then non-dot/s part of P
ndrcR = '*' * cL + 's' * (cR - cL) + colR[cR:]  # cL dots, (cR-cL) s, then non-dot/s part of Q
```

So after _fill_ds_B: P' = cL dots then c cells. Q' = cL dots then (cR-cL) s then r/d cells.

The INVERSE (going from (P', Q') back to (P, Q)):
- P' has cL' dots = cL (same as original cL because non-dot/s = c cells are preserved)
- Q' has cR' = cL' + (cR-cL) = cR (dots plus s's)
  
  Wait: _count_ds counts dots AND s. Q' has cL dots + (cR-cL) s = cL+cR-cL = cR dot/s cells. So cR' = cR. ✓

  So from (P', Q') we can recover cL = cL' = #{dot in P'} and cR = cR' = #{dot/s in Q'}.
  Then reverse:
  - P(i, j): dot for i < cR, s for cR ≤ i < cL, c for i ≥ cL? 
    NO: P had cL original dots/s. The original P has dot/s/c. But B P only has dot and c (no s).
    So original P dots = cL, then c cells.
    
    After _fill_ds_B: P' = cL dots then c cells. SAME as original. So P = P'. No change!

Wait: _fill_ds_B doesn't change P at all?! Let me re-check.

For B type: P has {dot, c}. _count_ds(P col j) = #{dot/s in P col j} = #{dot in P col j} = cL (no s in B P).
Then: P' col j = cL dots + P[cL:] = cL dots + c cells = original P col j.

So _fill_ds_B **doesn't change P** for B type. It only changes Q!

And _fill_ds_M: for M type, P has {dot, s, c}. _count_ds(P col j) = #{dot/s} = #{dot} + #{s} = cL.
Then: P' col j = cR dots + (cL - cR) s + P[cL:] (c cells).

So _fill_ds_M changes BOTH P and Q.

Going from B to M (lift):
- σ.P is unchanged by descent (B P = original M P shifted, with `_fill_ds_B` not changing P)
  Wait NO: descent first shifts P LEFT, THEN applies _fill_ds_B.
  
  descent: (τ.P, τ.Q) → remove P col 0 → (P_shifted, Q) → _fill_ds_B → (P', Q')
  
  _fill_ds_B doesn't change P (for B output where P ∈ {dot, c}).
  So P' = P_shifted. ✓
  
  Q' = _fill_ds_B(Q) where the refill uses cL from P_shifted.

lift: reverse _fill_ds_B on Q (using P' = σ.P as the unchanged reference), then insert P col 0.

Since _fill_ds_B only changes Q:
- σ.Q = _fill_ds_B result
- τ.Q = original Q = _fill_ds_B⁻¹(σ.Q, σ.P)

_fill_ds_B⁻¹ at column j:
- cL = #{dot in σ.P col j}
- σ.Q col j = cL dots + (cR-cL) s + r/d cells
  where cR was the ORIGINAL #{dot/s in τ.Q col j}
- Recover τ.Q col j = cR dot/s + r/d cells
  But we need to know which of the cR were dot and which were s.
  
  From σ.Q: the first cL positions are dot (= original dots from τ.Q up to cL).
  The next cR-cL positions are s (= original dot/s from τ.Q between cL and cR, mapped to s).
  
  So the original τ.Q at positions < cL was dot/s (and descent turned them to dot in P', s in Q').
  At positions cL ≤ i < cR: original τ.Q was dot/s (and descent added s in Q').
  At positions ≥ cR: original τ.Q was r/d (preserved).

  The original VALUES of dot/s at positions < cR are NOT recoverable from σ alone!
  (We know they were dot or s, but not which.)

This means the lift is NOT unique — multiple M PBPs can descent to the same B PBP.

**But descent is INJECTIVE!** So each B PBP in the image has exactly one M preimage.

The resolution: the M PBP's (τ.P, τ.Q) determine the dot/s values uniquely via M's own constraints (dot_match between τ.P and τ.Q). 

In particular: τ.Q(i, j) = dot iff τ.P(i, j) = dot (M dot_match). And τ.P(i, j) is determined by P col 0 + σ.P (the descent preserves P cols ≥ 1 up to _fill_ds_M redistribution).

This is getting very circular. Let me step back and think about what the actual bijection is.

## Correct lift: same as CorrespondenceC

In CorrespondenceC.lean, the C→D lift works because:
- C P = D P with dot/s collapsed to dot (liftPaintP_CD = collapse s→dot)
- C Q = D Q + new col 0 filled with s

The key: C and D have the SAME P shape. No shift.

For M→B:
- B P = M P shifted LEFT, with _fill_ds_B (identity on P for B)
- B Q = M Q with _fill_ds_B refill

Since _fill_ds_B doesn't change P: **B P = M P shifted left** (just removing col 0).
And B Q = _fill_ds_B(M Q) using P_shifted as reference.

Lift:
- M P(i, j+1) = B P(i, j) = σ.P(i, j)  — direct shift right, no transformation needed!
- M Q(i, j) = _fill_ds_B⁻¹(σ.Q, σ.P)(i, j)
  = "undo the dot/s refill"
  = if i < dotScolLen(σ.P, j) then Q is in the "original dot/s zone" → recover from context
  ...

Hmm, the Q recovery is still the issue.

Actually wait: if _fill_ds_B doesn't change P, and descent only removes P col 0, then:
- M→B: P_B(i,j) = M.P(i, j+1), Q_B(i,j) = _fill_ds_B(M.Q)(i,j)
- lift: M.P(i, j+1) = P_B(i, j), M.Q(i, j) = _fill_ds_B⁻¹(Q_B)(i, j)

M.Q = _fill_ds_B⁻¹(Q_B, P_B).

_fill_ds_B maps M.Q to Q_B:
Q_B(i, j) = dot for i < cL(j), s for cL(j) ≤ i < cR(j), Q_nonDS(i, j) for i ≥ cR(j)
where cL(j) = dotScolLen(M.P, j+1), cR(j) = dotScolLen(M.Q, j)

Inverse: M.Q(i, j) = ? 

We know Q_B has cL dots, (cR-cL) s, then r/d.
cL = dotScolLen(P_B, j) = #{dot in P_B col j} = #{dot in M.P col (j+1)} = dotScolLen(M.P, j+1).
cR = #{dot/s in Q_B col j} = cL + (cR-cL) = cR.

M.Q(i, j) should be: 
- dot for i < cR (the original dot/s zone, but we don't know which were dot vs s)
  
  But M's dot_match tells us: M.Q(i,j) = dot iff M.P(i,j) = dot. 
  M.P(i, j) for j ≥ 1: = from the non-shifted version... 
  
  M.P(i, j) for j ≥ 1 includes col 0. For j ≥ 1: M.P(i, j) = something.
  For j = 0: M.P(i, 0) is the col 0 we're inserting.

Actually I think the key insight is: **we DON'T need to exactly recover M.Q**. We just need to construct SOME M PBP that descents to σ. It doesn't have to be the SAME one. For surjectivity, any preimage suffices.

And the simplest preimage: set M.Q(i, j) = dot everywhere (except where forced to be non-dot by shape + M constraints).

No, M Q has {dot, r, d}. Q needs to contain the r/d from σ.Q.

Hmm. OK let me just use the EXISTING round-trip (already proved!) + existing lift. The round-trip proves that descent ∘ lift = id for inputs satisfying the preconditions. I just need to show the preconditions hold.

The preconditions that fail: h_dot_cross. But maybe I can reformulate the lift to avoid h_dot_cross entirely?

Actually, the current liftPaintQ_BM = collapse s→dot in σ.Q. This is EXACTLY _fill_ds_M on Q (since _fill_ds_M on Q gives: cR dots then Q non-dot/s = cR dots then r/d, where cR = #{dot/s in Q} = #{dot+s in σ.Q}).

And liftPaintP_BM (shifting right + fill col 0) is NOT _fill_ds_M on P. _fill_ds_M on P would give: cR dots then (cL-cR) s then c cells. But liftPaintP_BM uses P(i, j+1) = σ.P(i, j) (direct shift, no _fill_ds_M transformation).

**The fix**: apply _fill_ds_M transformation to both P AND Q, then shift P right. That is:

M P(i, 0) = col 0 fill  
M P(i, j+1) = _fill_ds_M_P(σ.P, σ.Q)(i, j) = cR dots then (cL-cR) s then σ.P non-dot
M Q(i, j) = _fill_ds_M_Q(σ.P, σ.Q)(i, j) = cR dots then σ.Q non-dot/s

With this, dot_match at (i, j+1): 
P(i, j+1) = dot iff i < cR(j). Q(i, j+1) = _fill_ds_M_Q at (i, j+1) = dot iff i < cR(j+1).

Still different cR values! The SHIFT between P and Q column indices persists.

I think the fundamental issue is that there's no way around the column misalignment. The descent maps M.P(i, j+1) → B.P(i, j) but keeps M.Q(i, j) → B.Q(i, j). Any lift must reverse this, creating the misalignment.

**CONCLUSION**: The M→B bijection proof requires a fundamentally different approach than explicit lift. Perhaps use the paper's Prop 10.8 directly (proved via representation theory / counting argument), or use fiber decomposition.
