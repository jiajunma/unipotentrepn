# Natural Language Proofs for Counting Sorry's

## Setup

- D-type PBP τ with P.shape = μP, Q.shape = μQ
- Q = all dots, Q.shape = dotDiag(P)
- b = μQ.colLen(0), c = μP.colLen(0), k = c - b (tail length)
- Double descent: σ = ∇²τ has σ.P.shape = shiftLeft(μP), σ.Q.shape = shiftLeft(μQ)
- doubleDescent_D_paintL τ i j = if i < Q.colLen(j+1) then dot else if i < dotScolLen(P,j+1) then s else P.paint(i, j+1)
- liftPaint_D σ col0 i j = col0(i) for j=0, σ.P.paint(i, j-1) for j≥1

### Key structural fact (primitive)
Primitive condition: b ≥ μP.colLen(1) (= shiftLeft(μP).colLen(0)).
Consequence: tail rows [b, c) are outside P.shape at columns ≥ 1, so P.paint(i, j) = dot for i ≥ b, j ≥ 1.

### Key structural fact (balanced)
Balanced condition: μP.colLen(1) = b + 1.
Consequence: exactly ONE tail row (row b) is in P.shape at column 1. P.paint(b, 1) = σ.P.paint(b, 0), which is the FIRST cell of σ's column 0.

---

## Sorry 1: validCol0_card

**Statement**: For k ≥ 1, |ValidCol0(μP, μQ)| = tDD + tRC + tSS where k = c - b.

**Proof**:
A ValidCol0 is determined by its tail: k symbols at rows [b, c). The tail is a non-decreasing sequence from {s, r, c, d} (layerOrd 1 ≤ 2 ≤ 3 ≤ 4) with at most 1 c and at most 1 d.

Such a sequence has canonical form s^α r^β c^δc d^δd where α + β + δc + δd = k.

Bijection: ValidCol0 ↔ {(α, β, δc, δd) : α,β ≥ 0, δc,δd ∈ {0,1}, α+β+δc+δd = k}.
- Forward: count each symbol in the tail
- Backward: paint s^α r^β c^δc d^δd starting at row b

The backward direction gives a valid ValidCol0 because:
- Non-decreasing: s ≤ r ≤ c ≤ d in layerOrd ✓
- Non-dot in tail ✓
- At most 1 c, 1 d ✓

Count by (δc, δd):
- (0,0): α + β = k → k+1 choices
- (1,0): α + β = k-1 → k choices (k ≥ 1) ✓
- (0,1): α + β = k-1 → k choices
- (1,1): α + β = k-2 → k-1 choices (k ≥ 2, else 0)

By tail class (determined by δd and whether β > 0 or δc = 1):
- DD (δd = 1): k + max(0, k-1) = nu(k-1) + (k≥2 ? nu(k-2) : 0) = tDD
- RC (δd = 0, not all-s): k + k = 2·nu(k-1) = tRC
- SS (all s: α=k): 1 = tSS

Total = tDD + tRC + tSS. ∎

---

## Sorry 2: fiber_card_primitive

**Statement**: For primitive case (b ≥ μP.colLen(1)), |fiber(σ)| = tDD + tRC + tSS for all σ.

**Proof** (sandwich argument):

**Step 1**: extractCol0 : fiber(σ) → ValidCol0 is injective.
Given τ₁, τ₂ ∈ fiber(σ) with same column 0 paint:
- Same ∇² (both = σ) → same P paint at columns ≥ 1 (by double descent formula)
- Same P paint at column 0 (hypothesis)
- Same P everywhere → same Q (Q = dotDiag P) → same PBP
So τ₁ = τ₂. ∎

**Step 2**: liftPBP : PBPSet(rest) × ValidCol0 → PBPSet(dp) is injective.
This is liftPBP_primitive_D_injective (fully proved). ∎

**Step 3**: |PBPSet(dp)| = Σ_σ |fiber(σ)| (card_PBPSet_eq_sum_fiber, proved). ∎

**Step 4**: Sandwich.
- From Step 1: |fiber(σ)| ≤ |ValidCol0| for each σ.
  Sum: Σ|fiber| ≤ |PBPSet(rest)| × |ValidCol0|.
- From Step 2: |PBPSet(dp)| ≥ |PBPSet(rest)| × |ValidCol0|.
- From Step 3: |PBPSet(dp)| = Σ|fiber|.
- So: |PBPSet(rest)| × |ValidCol0| ≤ Σ|fiber| ≤ |PBPSet(rest)| × |ValidCol0|.
- Equality everywhere. Since |ValidCol0| is constant (depends on μP, μQ only),
  each |fiber(σ)| = |ValidCol0|.

**Step 5**: |ValidCol0| = tDD + tRC + tSS (validCol0_card). ∎

---

## Sorry 3: fiber_card_balanced_SS

**Statement**: Balanced case + tailClass(σ) = SS → |fiber(σ)| = 0.

**Proof**:
Balanced means μP.colLen(1) = b + 1. SS class means σ's tail is all s (σ.P.paint(i, 0) = s for i in σ's tail).

Suppose for contradiction τ ∈ fiber(σ). Consider row b (the first tail row) in τ.

P column 1 at row b: P.paint(b, 1) = σ.P.paint(b, 0).

Since σ has SS class, σ's column 0 first cell is s (or is in the s-region from double descent). Specifically:
- σ.P.paint(b, 0) is non-dot (since b < σ.P.colLen(0) = μP.colLen(1) = b + 1)
- σ.P.paint(b, 0) has layerOrd ≤ 1: need to show this.

From the double descent formula: σ.P.paint(b, j) came from τ.P.paint(b, j+1). For j = 0: σ.P.paint(b, 0) = doubleDescent at (b, 0), which involves:
- if b < Q.colLen(1): dot. Q.colLen(1) = μQ.colLen(1). Need to check.
- else if b < dotScolLen(P, 1): s
- else P.paint(b, 1)

For σ's SS class: the tail symbol at the BOTTOM of σ's column 0 is s. Since σ's tail is monotone and tailSymbol = s, the entire tail is s.

Key constraint on row b in the lifted PBP:

**Case A**: P.paint(b, 1) = s (σ.P encodes s at row b).
Then P.paint(b, 0) ≠ s (row_s: at most one s per row).
And P.paint(b, 0).layerOrd ≤ P.paint(b, 1).layerOrd = 1 (mono_P: (b,0) ≤ (b,1) and (b,1) ∈ P.shape since b < μP.colLen(1) = b+1).
So P.paint(b, 0) has layerOrd ≤ 1. Combined with ≠ s: P.paint(b, 0) = dot.
But ValidCol0 requires nondot_tail: P.paint(b, 0) ≠ dot (since b ≥ b = μQ.colLen(0)).
**Contradiction**! ✗

**Case B**: P.paint(b, 1) = dot (σ.P encodes dot at row b).
Then (b, 1) ∈ dotDiag(P) → (b, 1) ∈ Q → b < μQ.colLen(1).
But Q.colLen(1) = μQ.colLen(1) = shiftLeft(μQ).colLen(0) = σ.Q.colLen(0).
And σ's tail starts at σ.Q.colLen(0). Since σ has SS class with tailLen ≥ 1:
σ.P.paint(σ.Q.colLen(0), 0) = s (first tail cell).
But we said σ.P.paint(b, 0) = dot → σ.Q.colLen(0) > b → b < σ.Q.colLen(0).
And σ.Q.colLen(0) = μQ.colLen(1) ≤ μQ.colLen(0) = b.
So b < σ.Q.colLen(0) ≤ b. **Contradiction**! ✗

Both cases lead to contradiction. So no τ exists. |fiber(σ)| = 0. ∎

**Alternative proof (simpler)**:
Balanced: μP.colLen(1) = b + 1, so (b, 1) ∈ μP. SS class implies σ.P at (b, 0) is either s or involves s-insertion, giving P.paint(b, 1).layerOrd ≤ 1.

For the tail cell P.paint(b, 0):
- If dot: violates nondot_tail (b ≥ μQ.colLen(0))
- If s: violates row_s (P.paint(b, 1) has s in same row via monotone or s-insertion)
- If r/c/d: violates mono_P since (b,0) ≤ (b,1) ∈ P.shape and layerOrd(r/c/d) ≥ 2 > 1 ≥ layerOrd(P.paint(b,1))

All options blocked → no valid τ. ∎

---

## Sorry 4: fiber_card_balanced_DD

**Statement**: Balanced + tailClass(σ) = DD → |fiber(σ)| = tDD + tRC + tSS.

**Proof sketch**:
Balanced: μP.colLen(1) = b + 1. DD class means σ's tailSymbol = d.

At row b: σ.P.paint(b, 0) determines P.paint(b, 1). Since σ has DD class, the bottom of σ's tail is d (layerOrd 4). But row b might not be σ's bottom row — it could be anywhere in σ's tail.

Actually, σ.P.paint(b, 0) is the cell at row b in σ's column 0. In the balanced case:
- σ.P.colLen(0) = μP.colLen(1) = b + 1
- σ.Q.colLen(0) = μQ.colLen(1)
- σ's tail = rows [μQ.colLen(1), b+1)

Row b is the LAST row of σ's column 0 (b < b+1 = σ.P.colLen(0)). So σ.P.paint(b, 0) is the tailSymbol of σ.

If DD class: σ.P.paint(b, 0) = d. So P.paint(b, 1) = d (layerOrd 4).

Monotonicity: P.paint(b, 0).layerOrd ≤ P.paint(b, 1).layerOrd = 4. So ANY symbol at (b, 0) satisfies mono_P.

Row uniqueness: d is column-unique (not row-unique). So no row constraint from P.paint(b, 1) = d on P.paint(b, 0).

So the tail cell at row b is UNCONSTRAINED (any of {s, r, c, d} works), same as primitive case!

The remaining tail cells (rows b+1, ..., c-1) are outside column 1's shape (i > b = μP.colLen(1) - 1). So they have P.paint(i, 1) = dot (outside shape). No constraints.

So the valid tails are exactly the same as in the primitive case: all monotone {s,r,c,d}^k with c/d unique. Count = tDD + tRC + tSS.

The formal proof uses the same sandwich argument as the primitive case, with the observation that the DD constraint makes the first tail cell unconstrained (layerOrd(d) = 4 ≥ everything). ∎

---

## Sorry 5: fiber_card_balanced_RC

**Statement**: Balanced + tailClass(σ) = RC → |fiber(σ)| = scDD + scRC + scSS.

**Proof sketch**:
Balanced: μP.colLen(1) = b + 1. RC class means σ.P.paint(b, 0) ∈ {r, c} (tailSymbol ∈ {r, c}).

At row b: P.paint(b, 1) = σ.P.paint(b, 0) ∈ {r, c}.

**Case σ.P.paint(b, 0) = r (layerOrd 2)**:
- mono_P: P.paint(b, 0).layerOrd ≤ 2. So P.paint(b, 0) ∈ {dot, s, r}.
- nondot_tail: P.paint(b, 0) ≠ dot.
- row_r: P.paint(b, 0) ≠ r (r already at (b, 1)).
- So P.paint(b, 0) = s.

**Case σ.P.paint(b, 0) = c (layerOrd 3)**:
- mono_P: P.paint(b, 0).layerOrd ≤ 3. So P.paint(b, 0) ∈ {dot, s, r, c}.
- nondot_tail: ≠ dot.
- No row constraint from c (c has column uniqueness, not row).
- So P.paint(b, 0) ∈ {s, r, c}.

Wait, this gives different possibilities depending on whether σ's tailSymbol is r or c. The count might differ. Let me re-examine...

Actually, in both sub-cases, the first tail cell is constrained. The remaining cells (rows > b) are unconstrained (outside column 1). So the tail is:

For σ tailSymbol = r: first cell must be s. Tail = s followed by monotone {s,r,c,d}^{k-1} with c/d unique.
Count of such tails: same as monotone {s,r,c,d}^{k-1} with c/d unique (k-1 length, all choices for continuation).
= validTailCount(k-1) total.

Wait, that doesn't match scDD+scRC+scSS either. Let me recalculate.

For σ tailSymbol = r: first cell = s (forced). Remaining k-1 cells form a monotone sequence from {s,r,c,d} with ≥ s (continuation), c/d unique (but accounting for column 0 uniqueness across ALL k cells).

Actually, the c/d uniqueness is across the ENTIRE column 0, not just the continuation. If the first cell is s, then among the remaining k-1 cells, we can still have up to 1 c and 1 d.

Continuation: s^{α'} r^{β'} c^{δc} d^{δd} with α' + β' + δc + δd = k-1.
But the full tail is s^{1+α'} r^{β'} c^{δc} d^{δd} with 1+α'+β'+δc+δd = k, i.e., α'+β'+δc+δd = k-1.

Count of such tails: same as validTailCount(k-1).

For σ tailSymbol = c: first cell ∈ {s, r, c}. But c uniqueness: if first cell = c, no more c allowed. And the full tail is non-decreasing with the first cell fixed.

Hmm, this is getting complicated. Let me re-derive the scDD/scRC/scSS coefficients from the counting.

scDD = 2 * nu(k-2) (for k ≥ 2)
scRC = nu(k-1) + nu(k-2) (for k ≥ 2)
scSS = 1

Hmm, these don't match a simple "first cell forced" argument. There might be a subtler interaction.

Actually, I think the issue is that for the RC class, the constraint depends on WHETHER the tailSymbol is r or c, and these create different fiber sizes. The scDD/scRC/scSS are the WEIGHTED AVERAGE across r and c sub-cases.

This is getting too complex for me to verify right now. Let me just write what I know and mark the RC case as needing more work.

Actually, wait. Let me re-read the paper's notation. The "scattered" coefficients might correspond to a different combinatorial object.

From counting_formulas.md:
```
scDD(k) = ν(k-2) + ν(k-2) = 2(k-1)
scRC(k) = ν(k-1) + ν(k-2) = k + (k-1) = 2k-1
scSS(k) = 1
```

And from the paper: "When x_{τ'} ∈ {c, r} (RC' class): 'scattered' tail coefficients apply (the tail interacts with τ' through the correction)."

I think "correction" refers to the descent correction (from Descent.lean), not just the s-insertion. The balanced case might involve the full descent with correction, which changes the analysis.

This is deep enough that I need to study the paper more. Let me write what I've verified and note the gap.
