# M→B and B→M Recovery: Detailed Informal Proofs

## PBP Shape Constraints by Type

Before proving recovery, we need the shape constraints that follow from PBP axioms.

### Symbol sets and shape consequences

| Type | P symbols | Q symbols | P dot+s region | Q dot+s region |
|------|-----------|-----------|----------------|----------------|
| D    | {•,s,r,c,d} | {•}     | dot+s          | all dot         |
| C    | {•,r,c,d}   | {•,s}   | dot only (no s)| dot+s          |
| B⁺/⁻| {•,c}       | {•,s,r,d}| dot only (no s)| dot+s          |
| M    | {•,s,c}     | {•,r,d} | dot+s          | dot only (no s)|

Key observation: **the "no s" side has dotScolLen = dot count only**.

### Symmetry between types

| Pair    | "no s" side | "has s" side | Descent removes |
|---------|-------------|--------------|-----------------|
| D ↔ C   | C.P, D.Q    | D.P, C.Q    | D→C: P col 0, C→D: Q col 0 |
| M ↔ B   | B.P, M.Q    | M.P, B.Q    | M→B: P col 0, B→M: Q col 0 |

So **M→B is structurally analogous to D→C** (both remove P col 0), and
**B→M is analogous to C→D** (both remove Q col 0).

But there's a key difference: for D→C, the "target" Q is the one with "no s" (D.Q = all dots).
For M→B, the "target" Q is the one with "has s" (B.Q = {•,s,r,d}).

This means:
- **D→C**: Q.shape knowledge is simple (Q = dot diagram). Recovery of P is direct.
- **M→B**: Q.shape is complex (Q has non-trivial symbols). Recovery requires more care.

## M→B Recovery: Step-by-Step

### Given

Two M-type PBPs τ₁, τ₂ with:
- Same shapes: P₁.shape = P₂.shape, Q₁.shape = Q₂.shape
- Same descent paint: descentPaintL_MB τ₁ = descentPaintL_MB τ₂ and descentPaintR_MB τ₁ = descentPaintR_MB τ₂

### Descent paint definitions (M→B)

```
P'(i, j) = if i < dotScolLen(P, j+1) then dot else P(i, j+1)
Q'(i, j) = if i < dotScolLen(P, j+1) then dot
           else if i < dotScolLen(Q, j) then s
           else Q(i, j)
```

Note: P' only depends on P. Q' depends on BOTH P and Q.

### Step 0: dotScolLen(P₁, j) = dotScolLen(P₂, j) for all j ≥ 1

From hdescL (P'₁ = P'₂), using the same argument as D→C:

P'(i, k) = if i < cL(k+1) then dot else P(i, k+1)

where cL(j) = dotScolLen(P, j).

**Claim**: cL₁(j) = cL₂(j) for j ≥ 1 (equivalently, for k ≥ 0).

**Proof**: Suppose cL₁(j) < cL₂(j) for some j.
At i = cL₁(j), k = j-1:
- P'₁(cL₁, j-1) = P₁(cL₁, j) (since cL₁ ≥ cL₁, else branch)
- P'₂(cL₁, j-1) = dot (since cL₁ < cL₂, then branch)

So P₁(cL₁, j) = dot.

But cL₁ = dotScolLen(P₁, j) means:
- If cL₁ < P₁.colLen(j): cell (cL₁, j) ∈ P₁.shape and has layerOrd > 1
  (it's past the dot+s boundary). So P₁(cL₁, j) ∈ {c} (for M type, non-dot-s = c).
  P₁(cL₁, j) = c ≠ dot. Contradiction. ✓
- If cL₁ = P₁.colLen(j): all cells in P₁ col j have layerOrd ≤ 1.
  Then cL₂ > cL₁ = P₁.colLen(j) = P₂.colLen(j) (same shape).
  But cL₂ counts cells IN P₂.shape, so cL₂ ≤ P₂.colLen(j). Contradiction. ✓

Symmetric for cL₂ < cL₁. So cL₁ = cL₂. ✓

**Note**: For M type P ({•,s,c}), non-dot with layerOrd > 1 means c (layerOrd 3).
The cell at the dot+s boundary either has c or is outside shape.
Either way, P(cL, j) ≠ dot. Key fact: **layerOrd > 1 for M-type P means c**.

### Step 1: Recover Q on all columns

With cL₁ = cL₂ (Step 0), the first threshold in Q' is the same for both.

Q'(i, j) = if i < cL(j+1) then dot else if i < dotScolLen(Q, j) then s else Q(i, j)

where cL(j+1) = dotScolLen(P, j+1) (same for both by Step 0, for j ≥ 0 → j+1 ≥ 1... 
wait, Step 0 gives cL(j) = cL(j) for j ≥ 1. We need cL(j+1) for j ≥ 0, which means j+1 ≥ 1 i.e. j ≥ 0. ✓)

Now Q' has three regions with the first boundary cL(j+1) identical. The second boundary
dotScolLen(Q, j) depends on Q, which we're trying to recover.

**Key for M type Q**: Q has {•, r, d}, **no s**. So dotScolLen(Q, j) = dot count only.
Non-dot in Q has layerOrd > 1 (r=2, d=4).

**Sub-claim**: If Q₁(i,j) ≠ dot and Q₂(i,j) ≠ dot, then Q'₁(i,j) = Q₁(i,j) and Q'₂(i,j) = Q₂(i,j).

Proof: Q non-dot → layerOrd > 1 → i ≥ dotScolLen(Q, j) (past dot+s = dot boundary).
So i ≥ dotScolLen(Q, j). And i ≥ cL(j+1)? Not necessarily without interlacing!

If i ≥ dotScolLen(Q, j) but i < cL(j+1): Q'(i,j) = dot. But Q(i,j) ≠ dot. 
This means Q'₁(i,j) = dot ≠ Q₁(i,j). But Q' is defined as the descent paint,
which should be consistent...

Wait, this is a **validity issue** with the descent definition. If cL(j+1) > dotScolLen(Q, j),
then there are cells where Q' = dot but Q ≠ dot. This means the redistribution creates
extra dot cells. Is this correct for the actual descent?

Let me re-check the Python code:
```python
def _fill_ds_B(drc):  # used for M→B
    drcL, drcR = drc  # drcL = P[1:], drcR = Q (original)
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = _count_ds(colL), _count_ds(colR)
        ndrcL.append('*' * cL + colL[cL:])
        ndrcR.append('*' * cL + 's' * (cR - cL) + colR[cR:])
```

Here cL = _count_ds(P[1:] col k) = dot+s count in P col k+1.
And cR = _count_ds(Q col k) = dot+s count in Q col k = dot count in M-type Q.

ndrcR[k] = cL dots + (cR - cL) s + Q col k's non-(dot,s) part.

For this to make sense, we need **cR ≥ cL**, i.e., dotScolLen(Q, k) ≥ dotScolLen(P, k+1)!

If cR < cL: we'd get **negative** s count: (cR - cL) < 0. This is invalid!

So the descent IS only well-defined when cR ≥ cL, i.e.,
**dotScolLen(Q, j) ≥ dotScolLen(P, j+1)** (interlacing from Q to P).

This is an **orbit-level constraint**, not derivable from PBP axioms alone!

### Interlacing for M→B

The interlacing condition is:
```
dotScolLen(Q, j) ≥ dotScolLen(P, j+1)   for all j
```

For M type: Q has {•,r,d}, P has {•,s,c}.
- dotScolLen(Q, j) = dot count in Q col j (no s in Q).
- dotScolLen(P, j+1) = dot+s count in P col j+1.

This comes from the orbit structure:
- For M type with orbit Ǒ = (r₁, r₂, ...):
  - P col i has length related to r_{2i-1}/2
  - Q col i has length related to r_{2i}/2
  - The dot diagram column lengths are min(P.colLen, Q.colLen) at each column
  - The interlacing r₁ ≥ r₂ ≥ r₃ ≥ ... ensures the shape constraints

**For the formalization**: we should add the interlacing as a hypothesis to `descent_eq_implies_cols_ge1_MB`.

### With interlacing: Q recovery

With cL(j+1) ≤ cR(j) = dotScolLen(Q, j):

For Q non-dot at (i, j): i ≥ cR(j) ≥ cL(j+1). So Q'(i,j) = Q(i,j). ✓
For Q dot at (i, j): i < cR(j). Either i < cL(j+1) (Q' = dot) or cL ≤ i < cR (Q' = s).

4-way case split on Q₁ dot/non-dot × Q₂ dot/non-dot:
- Both dot: trivial. ✓
- Both non-dot: Q' = Q for both (i ≥ cR ≥ cL). Direct from hdescR. ✓
- Q₁ dot, Q₂ non-dot: Q'₁ ∈ {dot, s}, Q'₂ = Q₂ ∈ {r, d}. {dot,s} ∩ {r,d} = ∅. Contradiction. ✓
- Q₁ non-dot, Q₂ dot: symmetric. ✓

So Q₁ = Q₂ on all cells. ✓

### Step 2: P recovery using Q

With Q known, use dot_match:
P.paint(i,j) = dot ↔ ((i,j) ∈ P.shape ∧ P.paint = dot) ↔ ((i,j) ∈ Q.shape ∧ Q.paint = dot)

Since Q is the same and shapes are the same:
- P.paint = dot for both ↔ Q.paint = dot at (i,j). Same Q → same. ✓
- P.paint = s for both (non-dot with layerOrd ≤ 1, same dot classification). ✓
- P.paint = c for both (layerOrd > 1, P' = P directly from descent). ✓

So P₁ = P₂ on columns ≥ 1. ✓

## B→M Recovery

B→M removes Q col 0, applies _fill_ds_M on (P, Q[1:]):

```
cL = dotScolLen(P, j)     -- dot count in B-type P ({•,c}, no s)
cR = dotScolLen(Q, j+1)   -- dot+s count in Q col j+1
P'(i,j) = if i < cR then dot else if i < cL then s else P(i,j)
Q'(i,j) = if i < cR then dot else Q(i, j+1)
```

**Interlacing**: cL ≥ cR needed (otherwise negative s count in P').
cL = dot count in B-type P, cR = dot+s count in B-type Q col j+1.

This interlacing is also an orbit-level constraint.

### With interlacing: P recovery

Same as C→D. B type P has {•,c}, no s. dotScolLen = dot count.
Non-dot = c (layerOrd 3 > 1).

descent_preserves_nonDot: P non-dot → i ≥ cL ≥ cR → P' = P. ✓
descent_maps_dot: P dot → i < cL → P' ∈ {dot, s}. ✓

4-way case split: identical to C→D. ✓

### Q recovery

Q' shifts Q left: Q'(i,j) = if i < cR then dot else Q(i, j+1).
For i ≥ cR: Q' = Q(i, j+1). Direct recovery for Q cols ≥ 1. ✓
For i < cR: Q has layerOrd ≤ 1 (dot or s). Determined by dot_match + same P. ✓

Q col 0: determined by shapes + dot_match + P. ✓

So τ₁ = τ₂. ✓

## Summary

Both M→B and B→M recovery require an **interlacing hypothesis** from the orbit:
- M→B: dotScolLen(Q, j) ≥ dotScolLen(P, j+1)
- B→M: dotScolLen(P, j) ≥ dotScolLen(Q, j+1)

These ensure the s-count in the redistribution is non-negative.

With interlacing:
- M→B: recover Q from Q' (4-way split), then P from Q + P' (dot_match). ✓
- B→M: recover P from P' (4-way split, like C→D), then Q from P + Q'. ✓
