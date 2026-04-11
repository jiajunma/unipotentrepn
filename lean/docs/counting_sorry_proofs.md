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

## Sorry 5: fiber_card_balanced_RC (REVISED)

**CRITICAL FINDING**: The per-σ fiber size is NOT constant for RC class!

Verified for dp = [3,3,3] (k=1):
- r-bottom RC σ: fiber = 1 (only s at first tail cell)
- c-bottom RC σ: fiber = 3 (s, r, or c at first tail cell)
- **Aggregate matches**: 2×1 + 2×3 = 8 = RC' × scTotal = 4×2 ✓

### Why fiber varies within RC class

Balanced: μP.colLen(1) = b + 1. At row b: P.paint(b, 1) = σ.P.paint(b, 0) = tailSymbol(σ).

**Sub-case r-bottom** (σ tailSymbol = r, layerOrd 2):
- mono_P: col0(b).layerOrd ≤ 2 → {dot, s, r}
- nondot_tail: ≠ dot → {s, r}
- row_r: ≠ r (r at column 1) → {s}
- col0(b) = s **forced**. 1 choice.

**Sub-case c-bottom** (σ tailSymbol = c, layerOrd 3):
- mono_P: col0(b).layerOrd ≤ 3 → {dot, s, r, c}
- nondot_tail: ≠ dot → {s, r, c}
- No row_r conflict (column 1 has c, not r)
- col_c is per-column (c at col 0 ≠ conflict with c at col 1)
- col0(b) ∈ {s, r, c}. **3 choices**.

Remaining tail cells (rows > b): outside column 1 shape → unconstrained.

### Correct formulation

The per-σ statement `|fiber(σ)| = scDD + scRC + scSS` is **FALSE**.

Correct statement: **aggregate formula**
```
Σ_{σ : RC'} |fiber(σ)| = RC' × (scDD + scRC + scSS)
```

This works because among RC' sub-PBPs, exactly half are r-bottom and half are c-bottom (from the symmetric structure of the TRC polynomial: TRC = ν_{k-1}·c + r·ν_{k-1}, both terms evaluate to nu(k-1) = k at p=q=1).

So: Σ_{RC'} |fiber| = (RC'/2) × fiber_r + (RC'/2) × fiber_c
And scTotal = (fiber_r + fiber_c) / 2.

### For the counting proof: use aggregate, not per-σ

The main theorem |PBPSet(dp)| = countPBP_D(dp) needs:
```
|PBPSet| = Σ|fiber| = DD'×tTotal + Σ_{RC'}|fiber| + 0
         = DD'×tTotal + RC'×scTotal
         = countPBP_D(dp)
```

The DD' and SS' parts are per-σ (constant fiber). Only the RC' part needs the aggregate.

### Proof of RC aggregate (sketch)

Need: Σ_{σ:RC'} |fiber(σ)| = RC' × scTotal.

Approach: decompose RC' into r-bottom (count = RC'/2 = nu(k-1) from sub-problem) and c-bottom (count = RC'/2 = nu(k-1)).

For r-bottom σ (fiber per σ): first cell forced to s, remaining k-1 free.
fiber_r = validTailCount(k-1) = tTotal(k-1) (for k≥2) or 1 (for k=1).

For c-bottom σ (fiber per σ): first cell ∈ {s, r, c}, remaining k-1 depends on first.
fiber_c = validTailCount(k-1) + count(first=r, continuation) + count(first=c, continuation)

The sum: (RC'/2)(fiber_r + fiber_c) = RC' × scTotal.

**Verification for k=1**: fiber_r=1, fiber_c=3. scTotal=2. (1+3)/2=2. ✓
**Verification for k=2**: fiber_r=4, fiber_c=8. scTotal=6. (4+8)/2=6. ✓

### Complete derivation for general k ≥ 1

**fiber_r(k)** = validTailCount(k-1): first cell forced to s, remaining k-1 free.
- k=1: 1. k≥2: 4(k-1).

**fiber_c(k)** = validTailCount(k-1) + rStartCount(k-1) + cStartCount(k-1):
- validTailCount(k-1): first cell = s case
- rStartCount(n) = #{r^β c^δc d^δd : β+δc+δd = n} = 1 + (n≥1?1:0) + (n≥1?1:0) + (n≥2?1:0)
  = 1 (n=0), 3 (n=1), 4 (n≥2)
- cStartCount(n) = #{d^δd : δd ≤ 1, n = δd} = 1 (n≤1), 0 (n≥2)

Computed:
- k=1: fiber_r=1, fiber_c=1+1+1=3
- k=2: fiber_r=4, fiber_c=4+3+1=8
- k≥3: fiber_r=4(k-1), fiber_c=4(k-1)+4+0=4k

**Average = (fiber_r + fiber_c) / 2**:
- k=1: (1+3)/2 = 2 = scTotal(1) ✓
- k=2: (4+8)/2 = 6 = scTotal(2) ✓
- k≥3: (4(k-1)+4k)/2 = (8k-4)/2 = 4k-2 = scTotal(k) ✓

Verification: scTotal(k) = scDD+scRC+scSS = 2(k-1) + (2k-1) + 1 = 4k-2 for k≥2. ✓

**Why the average is exact**: Among RC' sub-PBPs, the TRC polynomial TRC = ν_{k-1}·c + r·ν_{k-1} has exactly ν(k-1) = k terms with r-bottom and k terms with c-bottom (at p=q=1). So #r-bottom = #c-bottom = RC'/2. The weighted sum (RC'/2)(fiber_r + fiber_c) = RC' × scTotal. ✓

### Proof of #r-bottom = #c-bottom

From the sub-problem's counting: RC'(rest) counts PBPs with tailSymbol ∈ {r, c}.
The tailSymbol depends on the BOTTOM cell of the tail: P.paint(P.colLen(0)-1, 0).

From the canonical form s^α r^β c^δc d^δd:
- tailSymbol = r iff δc = δd = 0 and β ≥ 1 (bottom is r): count = nu(k'-1) (where k' is sub tail length)
- tailSymbol = c iff δd = 0 and δc = 1 (bottom is c): count = nu(k'-1)

Equal counts! This uses the sub-problem's tail length k' and the tail polynomial structure. ∎

### Formalization strategy for RC case

Since per-σ is not constant, the theorem statement should be AGGREGATE:

```lean
theorem fiber_aggregate_balanced_RC :
    (Finset.univ.filter (fun σ => tailClass_D σ.val = .RC)).sum
      (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
    Fintype.card (PBPSet_tc .D μP' μQ' .RC) * (scDD + scRC + scSS)
```

This avoids the per-σ statement entirely.
