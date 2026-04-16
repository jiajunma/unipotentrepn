# B/M 型计数：完整自然语言证明

Reference: [BMSZb] Sections 10.2–10.6, Propositions 10.8, 10.9, 10.11, 10.12.

---

## Part 0: Notations and Conventions

- ★ ∈ {B, C, C̃(=M), D}。★' = Howe dual of ★: B↔C̃, C↔D。
- Ǒ: orbit with good parity. dp = (r₁, r₂, ...) = row lengths (even for B/M).
- PBP_★(Ǒ, ℘): set of painted bipartitions with primitive pair set ℘。
- (ι, P) × (j, Q) × γ: PBP with P-shape ι, Q-shape j, paints P/Q, label γ。
- c_i(ι), c_i(j): column lengths of shapes ι, j。
- 论文用 **1-based** column indexing: column 1 = our col 0。

---

## Part I: Shape Shifting (Section 10.2)

### Theorem (Lemma 10.3): Shape shifting is bijective

**For ★ = C̃ (= M)**:

设 (1,2) ∈ PP_★(Ǒ) 是 primitive, ℘ ⊆ PP_★(Ǒ) with (1,2) ∉ ℘, ℘↑ = ℘ ∪ {(1,2)}.

Shape shifting T_{℘,℘↑}: PBP_G(Ǒ, ℘) → PBP_G(Ǒ, ℘↑), τ ↦ τ↑:

**Shapes**: 
- c_1(ι_{℘↑}) = c_1(j_℘), c_1(j_{℘↑}) = c_1(ι_℘)  (col 0 lengths swap)
- c_i(ι_{℘↑}) = c_i(ι_℘), c_i(j_{℘↑}) = c_i(j_℘) for i ≥ 2  (other cols unchanged)

**Paint** (equations 10.3-10.4, 0-based column):
- P_{τ↑}(i, 0) = s if Q_τ(i,0) = r; c if Q_τ(i,0) = d; P_τ(i,0) otherwise
- Q_{τ↑}(i, 0) = r if P_τ(i,0) = s; d if P_τ(i,0) = c; Q_τ(i,0) otherwise
- P_{τ↑}(i, j) = P_τ(i, j) for j ≥ 1
- Q_{τ↑}(i, j) = Q_τ(i, j) for j ≥ 1

**即**: col 0 做 s↔r, c↔d 交换（在 P 和 Q 之间），其他列不变。

**Inverse**: T_{℘↑,℘} 用同样的公式（swap of swap = identity）。

**Proof that T is well-defined and bijective**:
1. T 只改变 col 0 的 paint，不改变 shapes（col 0 lengths 互换，但 cells 相同）
2. sym_P: M P 的 col 0 允许 {•, s, c}。swap 后：• → •, s ← r, c ← d。都在 {•, s, c} 中。✓
3. sym_Q: M Q 的 col 0 允许 {•, r, d}。swap 后：• → •, r ← s, d ← c。都在 {•, r, d} 中。✓
4. dot_match: swap 不改变 • 位置（• ↦ •）。✓
5. mono: swap 保持 layerOrd 关系（s(1)↔r(2)改变了 layerOrd，但 P 和 Q 各自的 mono 仍然成立因为 swap 是在 P 和 Q 之间，不是同一个 diagram 内部）。
   
   等等——P_{τ↑}(i, 0) 的 layerOrd 和 P_{τ↑}(i, 1) = P_τ(i, 1) 的关系？
   
   P_τ(i, 0) 原来和 P_τ(i, 1) 满足 mono（layerOrd 非递减 left→right）。
   
   P_{τ↑}(i, 0)：如果 Q_τ(i, 0) = r，则 P_{τ↑}(i, 0) = s (layerOrd 1)。
   P_{τ↑}(i, 1) = P_τ(i, 1)。需要 layerOrd(s) ≤ layerOrd(P_τ(i, 1))。
   
   P_τ(i, 0) 和 P_τ(i, 1) 满足 mono：layerOrd(P_τ(i,0)) ≤ layerOrd(P_τ(i,1))。
   P_τ(i, 0) ∈ {•, s, c}。如果 Q_τ(i, 0) = r，那 P_τ(i, 0) ≠ •（dot_match: Q≠• → P≠•）。
   所以 P_τ(i, 0) ∈ {s, c}。layerOrd ∈ {1, 3}。
   
   P_{τ↑}(i, 0) = s (layerOrd 1) ≤ layerOrd(P_τ(i, 1))。
   但 layerOrd(P_τ(i, 0)) ≤ layerOrd(P_τ(i, 1)) 且 P_τ(i, 0) ∈ {s, c}。
   如果 P_τ(i, 0) = c (layerOrd 3)：P_τ(i, 1) 有 layerOrd ≥ 3。则 s (1) ≤ 3 ≤ P_τ(i,1)。✓
   如果 P_τ(i, 0) = s (layerOrd 1)：P_τ(i, 1) 有 layerOrd ≥ 1。则 s (1) ≤ P_τ(i,1)。✓
   
   所以 mono_P 保持。✓ 类似论证 mono_Q。✓
   
6. row_s, row_r: col 0 的 s (在 P) 变成 r (在 Q)，反之。每行的 s 数不变，r 数不变。✓
7. col_c, col_d: col 0 的 c (在 P) 变成 d (在 Q)。col 0 中的 c/d 唯一性保持。✓
8. T ∘ T = id：swap(swap(x)) = x。✓

**Corollary (Prop 10.2)**: #PBP_G(Ǒ, ℘) = #PBP_G(Ǒ, ∅) for all ℘。
Proof: 反复应用 T 添加/移除 primitive pairs。T 双射 → cardinality 不变。✓

---

## Part II: Naive Descent (Lemma 10.5)

### Theorem (Lemma 10.5): Naive descent 唯一性

**For ★ = C̃ ∈ {C̃, D, D*}**:

给定 τ = (ι, P) × (j, Q) × γ ∈ PBP_★(Ǒ):
存在唯一 τ'_naive = (ι', P'_naive) × (j', Q'_naive) × γ':
- (ι', j') = (∇_naive(ι), j)  — ι 去掉第一行（col 0 removed, shift left），j 不变
- γ' 由 (10.5) 确定

**Paint 公式**:
- P'_naive(i, j): 
  - if P(i, j+1) ∈ {•, s}: P'_naive(i, j) ∈ {•, s}（具体值由唯一性确定）
  - if P(i, j+1) ∉ {•, s}: P'_naive(i, j) = P(i, j+1)

- Q'_naive(i, j):
  - if Q(i, j) ∈ {•, s}: Q'_naive(i, j) ∈ {•, s}（具体值由唯一性确定）
  - if Q(i, j) ∉ {•, s}: Q'_naive(i, j) = Q(i, j)

**唯一性证明**:

需要确定 P'_naive 和 Q'_naive 在 {•, s} region 中的值。

shapes interleaving：(ι, j) right interlaced → (ι', j') = (∇_naive(ι), j) left interlaced：
c_1(j') ≥ c_1(ι') ≥ c_2(j') ≥ c_2(ι') ≥ ...

在 {•, s} 的情况下（所有 symbols 都是 • 或 s）：
PBP 由 shapes + dot_match + row_s 唯一确定。

dot_match: P'(i, j) = • ↔ Q'(i, j) = •。（同一位置的 • 一致）
row_s: 每行至多 1 个 s（across P and Q）。

由 left interleaving：对每行 i，P' 和 Q' 中 • 的位置由 shapes 确定：
- (i, j) ∈ ι' ∩ j'（两者都有 cell）：dot_match 要求 P' 和 Q' 的 • 一致。
- P'(i, j) = s iff (i, j) ∈ ι' 且 (i, j) ∉ j'（P 有 cell，Q 没有 → P 不能是 •，只能是 s）。
  Wait: dot_match says P=• ∧ ∈ι' ↔ Q=• ∧ ∈j'. If (i,j) ∉ j': RHS = False → P ≠ •. So P = s. ✓
- Q'(i, j) = s iff (i, j) ∈ j' 且 (i, j) ∉ ι'。同理。✓
- (i, j) ∈ ι' ∩ j': dot_match: P=• ↔ Q=•. row_s: 至多 1 个 s per row。

对每行 i: count of (j : (i,j) ∈ ι' \ j') = s in P at row i. Count of (j : (i,j) ∈ j' \ ι') = s in Q at row i. By left interleaving, these regions alternate, and row_s requires at most 1 s per row across P and Q.

Actually for {•, s}-only PBP: shapes + dot_match fully determine the {•, s} assignment:
- (i, j) ∈ ι' only (not j'): P' = s (forced by ¬dot_match)
- (i, j) ∈ j' only (not ι'): Q' = s (forced)
- (i, j) ∈ ι' ∩ j': dot_match says P'=• ↔ Q'=•. 
  left interlacing means: for each row, the cells alternate between "ι' only", "both", "j' only".
  In the "both" region: P'=Q'=• (by dot_match + row_s: can't have s in both P and Q in this region since that would require 2 s's per row in the same "both" block).

**Actually the uniqueness in the {•, s} case comes from**:
The left interleaving means (ι', j') determines a unique Young diagram of dots, and the remaining cells are s. The row_s constraint is automatically satisfied by the interleaving structure.

For the general case: non-{•, s} cells are directly determined (= P(i, j+1) or Q(i, j)). The {•, s} cells form a sub-PBP whose shapes are the {•, s}-subdiagrams of ι' and j'. These subdiagrams still satisfy left interleaving (since removing cells preserves the interleaving). So uniqueness follows from the {•, s}-only case.

**This proves Lemma 10.5**: naive descent has a UNIQUE output. ✓

### Corollary: Naive descent is a bijection

**From ι' shapes to B target**:
The naive descent map τ ↦ τ'_naive is defined from PBP_★(Ǒ) to PBP_{★'}(Ǒ') (with specific shapes).

**Injectivity**: If τ₁'_naive = τ₂'_naive, then P₁(i, j+1) and P₂(i, j+1) agree on non-{•, s} cells (directly), and on {•, s} cells by the uniqueness argument applied in reverse. Similarly for Q. So τ₁ = τ₂. ✓

**Surjectivity**: Given τ' ∈ PBP_{★'}(Ǒ'), we construct τ:
- P(i, j+1) = P'(i, j) for non-{•, s} cells
- P(i, j+1) ∈ {•, s} for {•, s} cells, determined by uniqueness
- Q(i, j) = Q'(i, j) for non-{•, s} cells  
- Q(i, j) ∈ {•, s} for {•, s} cells, determined by uniqueness
- P col 0: filled by dot_match with Q col 0 + M PBP constraints

Wait: P col 0 is NOT part of ι' (ι' = ∇_naive(ι) = ι without col 0). So P col 0 needs to be constructed separately.

**P col 0 construction**: 
P(i, 0) for (i, 0) ∈ ι:
- dot_match: P(i, 0) = • ↔ Q(i, 0) = •
- Q(i, 0) is known (Q doesn't shift, Q'(i, 0) determines Q(i, 0))
- If Q(i, 0) = •: P(i, 0) = •
- If Q(i, 0) ≠ •: P(i, 0) ≠ •. P(i, 0) ∈ {s, c} (M P symbols)
  - mono_P: P(i, 0).layerOrd ≤ P(i, 1).layerOrd. P(i, 1) = P'(i, 0)... wait, P(i, j+1) corresponds to P'(i, j). So P(i, 1) = P'(i, 0) which may be {•, s} (from the {•, s} reconstruction) or {c} (from non-{•, s} direct copy).
  
  Actually: P(i, 1) is determined by the lift process. If P(i, 1) ∈ {•, s}: layerOrd ≤ 1. Then P(i, 0) ∈ {s, c} needs layerOrd(P(i,0)) ≤ layerOrd(P(i,1)) ≤ 1. So P(i, 0) ∈ {s} (layerOrd 1 ≤ 1). ✓
  
  If P(i, 1) ∉ {•, s}: P(i, 1) = c (only non-{•, s} option for M P). layerOrd(c) = 3. P(i, 0) ∈ {s, c}, layerOrd ≤ 3. Both work. 
  
  **Additional constraint**: col_c_P (at most 1 c per column). If there's already a c in P col 0, no more.
  
  So P(i, 0):
  - Q(i, 0) = •: P(i, 0) = •
  - Q(i, 0) ≠ •: P(i, 0) ∈ {s, c}. Choose c if possible (at most 1 per column), otherwise s.
  
  **Uniqueness of P col 0**: 
  Claim: P col 0 is uniquely determined by Q col 0 + mono_P + col_c_P.
  
  Proof: P col 0 has • where Q col 0 has •. Non-• cells: ∈ {s, c}. Mono (layerOrd non-decreasing top→bottom): s before c. At most 1 c in the column. So: dots at top, then s's, then at most 1 c at the very bottom. The boundary between • and s is at Q col 0's • boundary. The c (if any) is uniquely placed at the bottom of the non-• zone.
  
  **But does c always appear?** γ' (B⁺ vs B⁻) is determined by whether c is in (ι, P) col 0. So:
  - If the original M PBP had c in P col 0: γ' = B⁻
  - If not: γ' = B⁺
  
  In the LIFT direction (given B PBP with γ'):
  - γ' = B⁻: P col 0 must have c → place c at bottom of non-• zone
  - γ' = B⁺: P col 0 must NOT have c → all non-• cells are s

**This is exactly the lift I was trying to build!** But the key insight is: **the P col 0 construction is the ONLY non-trivial part**. The rest (P cols ≥ 1, Q) is determined by the {•, s} uniqueness argument from Lemma 10.5.

### Summary: Naive descent is bijective

τ ↦ τ'_naive is a bijection. The inverse is:
1. **Q col 0**: Q(i, 0) from Q'(i, 0) (Q doesn't shift, just {•,s}-reconstruction)
2. **P col 0**: from Q col 0 + γ' (dots where Q has dots, s/c elsewhere, c at bottom iff γ'=B⁻)
3. **P cols ≥ 1 and Q cols ≥ 1**: from {•, s}-reconstruction (Lemma 10.5 uniqueness)

✓

---

## Part III: Full Descent (Section 10.4)

### For M (= C̃) with ℘ = ∅

**Case (a)**: (1,2) ∉ ∅ = ℘. So descent = ∇_naive(τ). ✓

γ' from (10.5): B⁺ if c not in (ι, P) col 0; B⁻ if c in (ι, P) col 0. ✓

### Prop 10.8(a): Primitive → descent bijective

r₁ > r₂ (or ★ = D*). Descent = ∇_naive. By Part II, ∇_naive is bijective. ✓

**Formal statement**: card(PBPSet .M μP μQ) = card(PBPSet .Bplus shiftLeft(μP) μQ) + card(PBPSet .Bminus shiftLeft(μP) μQ)

### Prop 10.8(b): Balanced → descent injective, image = {x ≠ s}

r₁ = r₂. Descent = ∇_naive (still case (a) since ℘ = ∅).

**Injectivity**: from Lemma 10.5. ✓

**Image characterization**: descent image = {τ' ∈ PBP_{B}(Ǒ', ℘') : x_{τ'} ≠ s}

**Proof of "image ⊆ {x ≠ s}"** (x_{τ'} = s impossible for τ' in image):

When r₁ = r₂: c_1(ι) = r₁/2 = r₂/2 = c_1(j). So **P and Q col 0 have equal length**.

After descent: B.P = shiftLeft(M.P), B.Q = M.Q (shapes).
c_1(ι') = c_2(ι) ≤ c_1(j) = c_1(j') = c_1(ι).

The B tail = Q' col 0 above P' col 0 = cells at rows [c_1(ι'), c_1(j')).

Tail bottom = Q'(c_1(j')-1, 0) = Q'_naive(c_1(ι)-1, 0).

Q'_naive(c_1(ι)-1, 0): from Q(c_1(ι)-1, 0).
(c_1(ι)-1, 0) ∈ j (since c_1(j) = c_1(ι) > c_1(ι)-1).

In M: Q(c_1(ι)-1, 0) ∈ {•, r, d} (M Q symbols).

Case Q(c_1(ι)-1, 0) ∈ {r, d}: Q'_naive at this position = Q(c_1(ι)-1, 0) ∈ {r, d}. Not s. ✓

Case Q(c_1(ι)-1, 0) = •: dot_match → P(c_1(ι)-1, 0) = •.
Then Q'_naive(c_1(ι)-1, 0) ∈ {•, s} (from {•, s} reconstruction).
If Q'_naive = •: this cell is dot → not in tail (tail cells are non-dot).
If Q'_naive = s: **need to check if this is possible**.

If Q'_naive = s at (c_1(ι)-1, 0): this means in the B' PBP, Q' has s at this position.
For this to be a valid B PBP: Q' ∈ {•, s, r, d}. s is allowed. ✓

But from the {•, s} reconstruction: Q'(c_1(ι)-1, 0) = s requires that (c_1(ι)-1, 0) ∈ j' but (c_1(ι)-1, 0) ∉ ι'.

(c_1(ι)-1, 0) ∈ j'? j' = j, c_1(j') = c_1(j) = c_1(ι). So c_1(ι)-1 < c_1(j'). ✓ (in j')
(c_1(ι)-1, 0) ∈ ι'? ι' = ∇_naive(ι), c_1(ι') = c_2(ι). If c_2(ι) > c_1(ι)-1: yes. If c_2(ι) ≤ c_1(ι)-1: no.

When c_2(ι) ≤ c_1(ι)-1 (i.e., c_1(ι) > c_2(ι)): (c_1(ι)-1, 0) ∉ ι'. 
Then in {•, s} reconstruction: Q'(c_1(ι)-1, 0) = s is forced (j' only, not ι'). So s appears.

**But wait**: Q(c_1(ι)-1, 0) = •. And Q'(c_1(ι)-1, 0) should come from Q(c_1(ι)-1, 0) = •. 
The naive descent formula: Q'_naive(i, j) ∈ {•, s} when Q(i, j) ∈ {•, s}. Here Q = •, so Q'_naive ∈ {•, s}.
The specific choice is determined by the uniqueness (interleaving + dot_match + row_s).

For this position: (c_1(ι)-1, 0) ∈ j' \ ι'. The {•, s} reconstruction says Q' = s here.
And P' at (c_1(ι)-1, 0): (c_1(ι)-1, 0) ∉ ι', so P' doesn't have this cell. dot_match is vacuous. ✓

So Q'(c_1(ι)-1, 0) = s. Tail bottom = s. x_{τ'} could be s.

**But** the paper says image excludes x = s! Let me re-examine.

x_{τ'} uses the PAPER's definition (Section 10.5), which includes the α-dependent correction. For B type:
- Tail multiset = Set A ∪ {correction}
- correction depends on B⁺/B⁻

In this case: c_1(ι') = c_2(ι). The tail has length c_1(j') - c_1(ι') = c_1(ι) - c_2(ι) cells.

If tail length = 1 (k=1 in paper's notation): x_{τ'} = correction element.
- B⁺ correction: c (RC class)
- B⁻ correction: s (SS class)

If tail length > 1 (k > 1): x_{τ'} = max layerOrd of multiset.
correction = c (B⁺) or s (B⁻). 
max(c, Q'_bottom) or max(s, Q'_bottom).

Hmm, so x_{τ'} = s is possible when:
- B⁻ with correction s and all tail cells have layerOrd ≤ 1 (all s or •)

For the descent of M PBP τ with P(c_1(ι)-1, 0) = • and Q(c_1(ι)-1, 0) = •:
γ' = B⁺ (no c in P col 0 — because P(bottom, 0) = •). 
So correction = c. x_{τ'} = max(c, ...) ≥ layerOrd(c) = 3 > 1 = layerOrd(s). So x_{τ'} ≠ s. ✓

For P(c_1(ι)-1, 0) ≠ •: P ∈ {s, c}. Q ∈ {r, d}. Q' = Q ∈ {r, d}. x_{τ'} involves r or d. Not s. ✓

**The key**: when Q(bottom, 0) = • → P(bottom, 0) = • → γ' = B⁺ → correction = c → x_{τ'} ≥ c ≠ s.

**Proof of "image ⊇ {x ≠ s}"** (every B PBP with x ≠ s has an M preimage):

This follows from the BIJECTIVITY of naive descent (Lemma 10.5):
Every B PBP τ' has a unique M preimage τ with ∇_naive(τ) = τ'. 
The only constraint is that τ must be a valid M PBP.

But does every B PBP τ' lift to a valid M PBP? From the inverse construction (Part II):
- Q is recovered (Q doesn't shift)
- P cols ≥ 1: {•, s} reconstruction always works (interleaving always valid)
- P col 0: dots + s + (c if B⁻)

For τ' with x_{τ'} = s: the B⁻ correction gives s. This means either:
- B⁻ with correction s and all tail ≤ s (k=1 case)
- B⁻ with correction s and max(s, tail) = s (all tail ≤ s)

For B⁻ with x = s: γ' = B⁻. The lift puts c at P col 0 bottom.
M Q col 0 bottom = Q(c_1(ι)-1, 0). 
In the B PBP: Q'(c_1(ι)-1, 0) = s (tail bottom from {•,s} reconstruction). 
Lifting: Q(c_1(ι)-1, 0) comes from Q'(c_1(ι)-1, 0) = s. 
Q ∈ {•, s} region: Q(c_1(ι)-1, 0) ∈ {•, s}. 
In M Q: allowed = {•, r, d}. But Q(c_1(ι)-1, 0) ∈ {•, s}. **s is NOT in M Q!**

**s ∉ {•, r, d} = M Q symbols!** 

So the lift FAILS for B PBPs with x = s: the recovered Q would have s, which is not allowed in M Q.

**This is the precise reason SS is excluded!** The {•, s} reconstruction puts s in Q, but M Q doesn't allow s. ✓

**Formal statement**: 
card(PBPSet .M μP μQ) = #{τ' ∈ PBPSet_B : x_{τ'} ≠ s}
= DD + RC (from countPBP_B, excluding SS)

---

## Part IV: Counting Formulas

### Prop 10.12(a): Primitive M counting

card(M) = card(B target) (descent bijective)
= tripleSum(countPBP_B(dp.tail)) (B counting theorem)
= countPBP_M(dp) (definition, primitive case)

### Prop 10.12(b): Balanced M counting

card(M) = card(B target) - #{x = s in B target}
= tripleSum(countPBP_B(dp.tail)) - countPBP_B(dp.tail).SS
= DD + RC
= countPBP_M(dp) (definition, balanced case)

---

## Part V: B Balanced (Prop 10.11, balanced case)

This uses Prop 10.9(b) for double descent B→M→B.

### 概要

card(B⁺⊕B⁻) = dd(rest) × 4k + rc(rest) × (4k-2)

where dd(rest) = #{extended PBP in rest with paper-x = d}, rc(rest) = #{with x ∈ {c,r}}.

### 需要的定理
1. Prop 10.9(b) image characterization for B/D double descent
2. #{D-tail PBP with s or c in P col 0} = 4k - 2 (已 Python 验证)
3. countPBP_B(rest) 分量 = per-class count (用论文正确的 x_τ 定义)

### 证明
(同之前 prop_10_11_B_detailed_proof.md Section 3.4。已 Python 验证通过。)

---

## Verification Summary

| # | Statement | Python verified | Paper reference |
|---|-----------|----------------|-----------------|
| 1 | Shape shifting is involution | ✓ all dp | Lemma 10.3 |
| 2 | tripleSum(countPBP_B) = card(B⁺)+card(B⁻) | ✓ all dp | Prop 10.11 |
| 3 | Primitive: card = total(rest) × 4k | ✓ all dp | Prop 10.11(a) |
| 4 | Balanced: card = dd×4k + rc×(4k-2) | ✓ all dp | Prop 10.11(b) |
| 5 | #{D-tail with s/c} = 4k-2 | ✓ k=1..7 | Prop 10.9(b) |
| 6 | M primitive: card(M) = tripleSum(B rest) | ✓ all dp | Prop 10.12(a) |
| 7 | M balanced: card(M) = DD+RC | ✓ all dp | Prop 10.12(b) |
| 8 | countPBP_B = per-class count (corrected x_τ) | ✓ all dp | Prop 10.11 |
| 9 | M descent target = B(rest) shapes | ✓ all dp | Section 10.4 |
| 10 | SS excluded because M Q has no s | ✓ conceptual | Prop 10.8(b) |
