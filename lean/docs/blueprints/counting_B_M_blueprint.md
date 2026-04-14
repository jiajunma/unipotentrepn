# Blueprint: B/M Counting Proofs (Props 10.11/10.12)

Reference: [BMSZb] Section 10, Propositions 10.11 and 10.12.

## 1. Critical Insight: Tail is Always D-type

From [BMSZb] Section 10.5 (p.70):
> ★_t := D if ★ ∈ {B, D}

The tail PBP τ_t ∈ PBP_D(Ǒ_t) is always D-type, regardless of whether τ is B or D type.
This means:
- The tail enumeration uses D-type `tailCoeffs` (shared between B and D in `Counting.lean`)
- The fiber cardinality machinery (ValidCol0, TSeq, Lift) from the D-type proof is **directly reusable**
- The per-tail-class decomposition (DD/RC/SS) follows the same D-type pattern

This dramatically simplifies the B-type proof.

## 2. Main Theorems

```lean
-- B-type (Prop 10.11): B⁺ + B⁻ combined count
theorem card_PBPSet_B_eq_tripleSum_countPBP_B (dp : DualPart) ...
    : Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ)
      = tripleSum (countPBP_B dp)

-- M-type (Prop 10.12): via B descent
theorem card_PBPSet_M_eq_countPBP_M (dp : DualPart) ...
    : Fintype.card (PBPSet .M μP μQ) = countPBP_M dp
```

## 3. Existing Infrastructure

### Already proved (reusable):
| Component | Location | Reuse for B/M |
|-----------|----------|---------------|
| `descent_inj_B` | Tail.lean:1146 | Direct |
| `ddescent_inj_B` | Tail.lean:1544 | Direct |
| `ddescent_B_determines_colsGe1` | Tail.lean:1329 | Direct |
| `descent_recovery_BM` | Descent.lean:828 | Direct |
| `P_nonDot_eq_c_of_B` | PBP.lean:182 | Direct |
| `Q_countSym_c_zero_of_B` | Tail.lean:759 | Direct |
| `P_countSym_zero_of_B` | Tail.lean:747 | Direct |
| `tailCoeffs` | Counting.lean:26 | Shared (same for B/D) |
| ValidCol0, TSeq, fiber machinery | CountingProof/ | **Reuse via D-type tail** |

### Must create:
| Component | Estimated lines |
|-----------|----------------|
| `dpartColLensP_B`, `dpartColLensQ_B` | ~40 |
| `doubleDescent_B_map` on PBPSet | ~150 |
| Fiber bijection τ ↔ (∇²τ, τ_t) | ~200 |
| Base cases (empty, single row) | ~100 |
| Recursive step (primitive + balanced) | ~300 |
| Main induction | ~150 |
| **Total CorrespondenceB.lean** | **~940** |

| Component | Estimated lines |
|-----------|----------------|
| `descentMB_injective` | ~200 |
| `descentMB_not_SS` (balanced case) | ~100 |
| `liftMB` partial inverse | ~150 |
| Base case + main theorem | ~150 |
| **Total CorrespondenceM.lean** | **~600** |

## 4. Phase 1: B-type (`CorrespondenceB.lean`)

### 4.1 Shape Mapping

For even dual partition dp = [r₁, r₂, r₃, ...] (B-type orbits have even parts):

```
dpartColLensP_B: P column lengths (P is shorter for B)
  [] → []
  [r₁] → []
  r₁ :: r₂ :: rest → [r₂/2] ++ dpartColLensP_B rest

dpartColLensQ_B: Q column lengths (Q is longer for B)  
  [] → []
  [r₁] → [r₁/2]
  r₁ :: r₂ :: rest → [(r₁+1)/2] ++ dpartColLensQ_B rest
```

Note: For B, P cols come from EVEN-indexed rows, Q cols from ODD-indexed rows.
This is OPPOSITE to D type (where P gets odd-indexed).

Verification: dp = [4, 2]
- P colLens = [2/2] = [1], Q colLens = [(4+1)/2] = [2]  
- Tail length k = Q.colLen(0) - P.colLen(0) = 2 - 1 = 1
- (r₁-r₂)/2 + 1 = (4-2)/2 + 1 = 2 ← but wait, k should be 1?

Actually from paper: k = (r₁(Ǒ) - r₂(Ǒ))/2 + 1 for B type.
dp = [4, 2]: r₁ = 4, r₂ = 2. k = (4-2)/2 + 1 = 2.
But tail length = Q.colLen(0) - P.colLen(0) = 2 - 1 = 1?

Hmm, let me re-check. For B with dp = [4, 2]:
- c₁(ι) = r₂/2 = 1 (P col 0 length)
- c₁(j) = (r₁+1)/2 = 2 (Q col 0 length)? No, for B type r₁ is even so (r₁+1)/2 = 5/2 = 2 (integer div)... hmm.

Actually for even r₁=4: (4+1)/2 = 2 (integer div). So Q col 0 = 2.
For r₂=2: r₂/2 = 1. So P col 0 = 1.
Tail = Q.colLen(0) - P.colLen(0) = 2 - 1 = 1.

But k in countPBP_B is (r₁-r₂)/2 + 1 = (4-2)/2 + 1 = 2.

So k ≠ tail length. This means the tail PBP has Ǒ_t = [2k-1, 1] = [3, 1] with 2 rows.
The tail PBP τ_t ∈ PBP_D(Ǒ_t) has its own P/Q, and the P col 0 of τ_t has length k.

The "tail length" (Q.colLen(0) - P.colLen(0) in the B PBP) is related but not identical to k.

Let me re-derive. From [BMSZb] p.70:
- Ǒ_t has rows [2k-1, 1]
- For D type tail: P_t col 0 length = (2k-1+1)/2 = k
                   Q_t col 0 length = (1-1)/2 = 0
- Tail = k cells in P_t col 0

So the D-type tail PBP τ_t has k cells in its P col 0, which is the ValidCol0 giving 4k configurations.

For the B-type original PBP, the correspondence:
- τ ↦ (∇²τ, τ_t) where τ_t has k cells
- The k cells of τ_t correspond to... the Q col 0 tail of τ?

Actually no. The map τ ↦ (∇²τ, τ_t) from Prop 10.9 is:
- ∇²τ = double descent = strip 2 rows
- τ_t = tail PBP = the part of τ that was stripped

The tail τ_t captures all the information in Q col 0 (for B type) that the double descent doesn't determine.

But τ_t is a D-type PBP with shapes determined by Ǒ_t. The ValidCol0 of the D-type tail gives 4k configurations, and this equals the number of valid Q col 0 fillings in the original B-type PBP.

OK, so the key claim is: **the number of valid Q col 0 configurations in B type, given the rest of the PBP, equals 4k = |PBP_D(Ǒ_t)|.** This is what the proof must establish.

### 4.2 Proof Structure

**Induction** on `dp.length` (number of orbit rows, always even for B type).

**Base case**: dp = [] (empty orbit)
- PBPSet .Bplus ⊥ ⊥ has 1 element, PBPSet .Bminus ⊥ ⊥ has 1 element
- Total = 2 = tripleSum (0, 1, 1) ✓

**Single row**: dp = [r₁]
- Direct computation of card(PBPSet .Bplus) + card(PBPSet .Bminus)
- Match with countPBP_B [r₁]

**Recursive step**: dp = r₁ :: r₂ :: rest
1. Define double descent map ∇² : PBPSet_B(μP, μQ) → PBPSet_B(shiftLeft μP, shiftLeft μQ)
2. Show ∇² is well-defined (validate PBP constraints)
3. By `ddescent_inj_B`, ∇² combined with (signature, epsilon) is injective
4. Define fiber: for each σ ∈ PBPSet_B(shiftLeft μP, shiftLeft μQ), count preimages
5. The fiber corresponds to D-type tail PBP τ_t ∈ PBP_D(Ǒ_t)
6. Use the D-type fiber cardinality (tailCoeffs) from Correspondence.lean
7. Distinguish primitive (r₂ > r₃) vs balanced (r₂ = r₃) cases

**Primitive case** (r₂ > r₃):
- Every tail class gives the same fiber size
- card = card(sub) × (tDD + tRC + tSS)
- Triple decomposes: (card_sub × tDD, card_sub × tRC, card_sub × tSS)

**Balanced case** (r₂ = r₃):
- DD class: fiber = tDD from IH_DD + scDD from IH_RC
- RC class: fiber = tRC from IH_DD + scRC from IH_RC  
- SS class: fiber = tSS from IH_DD + scSS from IH_RC
- This gives the matrix multiply structure

### 4.3 B⁺/B⁻ Split

From Prop 10.2: #PBP_B(Ǒ, ℘) is independent of ℘. Since B⁺ and B⁻ are distinguished only by the signature offset (+1 to p or q), and there's a natural involution swapping B⁺ ↔ B⁻:

```lean
theorem card_Bplus_eq_Bminus : card(PBPSet .Bplus μP μQ) = card(PBPSet .Bminus μP μQ)
```

This can be proved by constructing a bijection (swap the B⁺/B⁻ tag while keeping the painting). Then each = tripleSum(countPBP_B dp) / 2.

## 5. Phase 2: M-type (`CorrespondenceM.lean`)

### 5.1 M→B Descent

For M (= C̃) type, descent goes M→B (analogous to C→D).

```lean
def descentMB_PBP (τ : PBP) (hγ : τ.γ = .M) : PBP
-- M-type PBP → B-type PBP by removing Q col 0 and shifting

theorem descentMB_injective : descentMB is injective on PBPSet
-- Mirror of descentCD_injective
```

### 5.2 Primitive vs Balanced

**Primitive** (r₁ > r₂): descent is surjective
```
countPBP_M dp = DD + RC + SS from countPBP_B dp.tail
```

**Balanced** (r₁ = r₂): descent image excludes SS class
```
countPBP_M dp = DD + RC from countPBP_B dp.tail
-- tail symbol s has no M preimage (descentMB_not_SS)
```

### 5.3 Key Lemma: descentMB_not_SS

When r₁ = r₂ (balanced), the M→B descent never produces a B-type PBP with tail symbol s. This is the M analogue of `descentCD_not_SS` in CorrespondenceC.lean.

## 6. Dependencies

```
CorrespondenceB.lean
  ├── imports: CountingProof/Basic, Descent, Fiber, Lift, LiftRC, TSeq
  ├── uses: ddescent_inj_B (Tail.lean)
  ├── uses: P_nonDot_eq_c_of_B, P_countSym_zero_of_B (PBP/Tail)  
  ├── uses: countPBP_B, tailCoeffs (Counting.lean)
  └── uses: ValidCol0, TSeq machinery (CountingProof/TSeq, Fiber)

CorrespondenceM.lean
  ├── imports: CorrespondenceB  
  ├── uses: descentMB_injective (new)
  ├── uses: countPBP_M (Counting.lean)
  └── uses: card_PBPSet_B_eq_tripleSum_countPBP_B (CorrespondenceB)
```

## 7. Verification Plan

Test against `standalone.py` / `#eval`:

| dp | type | expected count | source |
|----|------|---------------|--------|
| [] | B⁺ | 1 | #eval |
| [2] | B⁺ | 3 | #eval |
| [4,2] | B⁺ | 8 | Python |
| [4,4] | B⁺ | 5 | Python |
| [6,4,2] | B⁺ | 64 | Python |
| [] | M | 1 | #eval |
| [2] | M | 2 | #eval |
| [2,2] | M | 5 | Python |
| [4,2] | M | 8 | Python |

## 8. Summary

The key simplification is that the tail is D-type (Section 10.5), so:
- `tailCoeffs` is shared (same for B and D) ← already in `Counting.lean`
- ValidCol0/TSeq/fiber machinery from `CountingProof/` is directly reusable
- Only new work: shape mapping, double descent map, and B⁺/B⁻ handling

| Phase | File | New lines | Difficulty |
|-------|------|-----------|------------|
| 1 | CorrespondenceB.lean | ~940 | Medium-High |
| 2 | CorrespondenceM.lean | ~600 | Medium |
| 3 | Counting.lean additions | ~40 | Low |
| **Total** | | **~1580** | |
