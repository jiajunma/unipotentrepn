# Shape Shifting for M (= C̃) Type

Reference: [BMSZb] Section 10.2, Lemma 10.3, equations (10.3)-(10.4).

## 1. 定义

### 1.1 Setup

★ = C̃ = M。Ǒ has even row lengths (good parity)。
(1,2) ∈ PP_★(Ǒ) iff (1,2) is primitive（对 M 类型）。

℘ ⊆ PP_★(Ǒ) with (1,2) ∉ ℘。℘↑ := ℘ ∪ {(1,2)}。

### 1.2 Shape shifting T_{℘,℘↑} for C̃

给定 τ = (ι_℘, P_τ) × (j_℘, Q_τ) × α ∈ PBP_G(Ǒ, ℘):

τ↑ = (ι_{℘↑}, P_{τ↑}) × (j_{℘↑}, Q_{τ↑}) × α ∈ PBP_G(Ǒ, ℘↑)

**Shapes**: 对 C̃ type:
(c_i(ι_{℘↑}), c_i(j_{℘↑})) = (c_i(ι_℘), c_i(j_℘)) for all i ≥ 2.
(c_1(ι_{℘↑}), c_1(j_{℘↑})) = (c_1(j_℘), c_1(ι_℘)). **P 和 Q 的 col 0 长度互换**！

Wait: 从 p.64:
For C̃: (c_1(ι_{℘↑}), c_1(j_{℘↑})) = (c_1(j_℘), c_1(ι_℘)).
For i ≥ 2: (c_i(ι_{℘↑}), c_i(j_{℘↑})) = (c_i(ι_℘), c_i(j_℘)).

所以 **col 0 的 P/Q 长度互换**，其他列不变。

### 1.3 Paint transformation (equations 10.3-10.4)

对 (i, j) ∈ Box(ι_{℘↑}):  (使用 1-based column j)

P_{τ↑}(i, j) = 
  s,      if j = 1 and Q_τ(i, j) = r
  c,      if j = 1 and Q_τ(i, j) = d
  P_τ(i,j),  otherwise

对 (i, j) ∈ Box(j_{℘↑}):

Q_{τ↑}(i, j) = 
  r,      if j = 1 and P_τ(i, j) = s
  d,      if j = 1 and P_τ(i, j) = c
  Q_τ(i,j),  otherwise

**Translation to 0-based**: j=1 (1-based) = j=0 (0-based).

P_{τ↑}(i, 0) = s if Q_τ(i, 0) = r;  c if Q_τ(i, 0) = d;  P_τ(i, 0) otherwise.
Q_{τ↑}(i, 0) = r if P_τ(i, 0) = s;  d if P_τ(i, 0) = c;  Q_τ(i, 0) otherwise.

**即在 col 0：P 和 Q 之间交换 s↔r, c↔d。**

### 1.4 Involution

T_{℘↑,℘} 的定义（p.66 bottom, for C̃）：
"given by the formulas (10.3) and (10.4) with the role of ℘ and ℘↑ switched"

即用同样的 swap 公式。因为 swap(swap(x)) = x，所以 T_{℘↑,℘} = T^{-1}_{℘,℘↑}。

**T 是 involution：T ∘ T = id。** ✓ (Python 验证通过)

## 2. Lemma 10.3: T 是双射

**Lemma 10.3**: T_{℘,℘↑} : PBP_G(Ǒ, ℘) → PBP_G(Ǒ, ℘↑), τ ↦ τ↑ 是双射。

**Proof for C̃**:
- T_{℘↑,℘} is the inverse (definition)
- T_{℘↑,℘}(T_{℘,℘↑}(τ)) = τ (swap twice = identity) ✓
- Need to verify τ↑ ∈ PBP_G(Ǒ, ℘↑):
  - Shapes: ι_{℘↑} has col 0 = c_1(j_℘), j_{℘↑} has col 0 = c_1(ι_℘). ✓
  - sym_P: P_{τ↑} at col 0: {s, c} from swap of Q's {r, d}. Plus {•} from P's {•}. 
    M P allowed = {•, s, c}. ✓
  - sym_Q: Q_{τ↑} at col 0: {r, d} from swap of P's {s, c}. Plus {•} from Q's {•}.
    M Q allowed = {•, r, d}. ✓
  - dot_match: at col 0: P_{τ↑}(i,0) = • ↔ P_τ(i,0) = • AND Q_τ(i,0) = • ↔ Q_{τ↑}(i,0) = •.
    The swap only affects non-dot cells, so dot positions preserved. ✓
  - Other constraints (mono, row_s, etc.): "routine to check". ✓

## 3. Prop 10.2: Count independent of ℘

**Prop 10.2**: #PBP_G(Ǒ, ℘) = #PBP_G(Ǒ, ∅) for all ℘.

**Proof**: Apply T repeatedly to add or remove primitive pairs from ℘.
T is bijective → cardinality preserved. ✓

## 4. Naive descent (Lemma 10.5 for C̃)

对 ★ = C̃ ∈ {C̃, D, D*}:

给定 τ = (ι, P) × (j, Q) × γ, 存在**唯一** τ'_naive:
- (ι', j') = (∇_naive(ι), j) — ι shifts left (remove first row), j 不变
- P'_naive(i,j) = {• or s if P(i, j+1) ∈ {•, s}; P(i, j+1) otherwise}
- Q'_naive(i,j) = {• or s if Q(i, j) ∈ {•, s}; Q(i, j) otherwise}

**唯一性**证明（Lemma 10.5 proof on p.68, "similar to Lemma 10.4"）:

当 P 和 Q 的 images 都在 {•, s} 中时：(ι, j) 是 right interlaced:
c_1(ι) ≥ c_1(j) ≥ c_2(ι) ≥ c_2(j) ≥ ...

(ι', j') = (∇_naive(ι), j): ι' = ι 去掉第一列, j' = j. 
So (ι', j') 是 left interlaced:
c_1(ι') ≤ c_1(j') ≤ c_2(ι') ≤ c_2(j') ≤ ...

在 {•, s} 的特殊情况下，PBP 由 shapes 唯一确定（只有 • 和 s，dot_match + row_s 确定分配）。

一般情况：非 {•, s} 的 cells 直接从 P(i, j+1) 或 Q(i, j) 复制。{•, s} 的 cells 由 shapes interleaving + dot_match + row_s 唯一确定。

**关键**：naive descent 是**双射**（唯一 PBP ↔ 唯一 descent）。

## 5. Full descent for M (Section 10.4)

对 ★ = C̃ = M:

**Case (a)**: (1,2) ∉ ℘:
τ' = ∇_naive(τ)

**Case (b)**: (1,2) ∈ ℘ (then ★ ∈ {C, C̃}):
τ' = ∇_naive(τ_{℘↓}) where τ_{℘↓} = T^{-1}_{℘↓,℘}(τ) and ℘↓ = ℘ \ {(1,2)}.

**对 ℘ = ∅** (our focus): (1,2) ∉ ∅, so **case (a) applies**:
descent = ∇_naive(τ). ✓

γ' 由 (10.5) 确定: 
γ' = B⁺ if α = C̃ and c does NOT occur in first column of (ι, P)
γ' = B⁻ if α = C̃ and c OCCURS in first column of (ι, P)

## 6. Prop 10.8: Descent properties

**Prop 10.8(a)**: ★ = D* 或 r₁ > r₂ → descent 双射。

对 M with ℘ = ∅ and r₁ > r₂ (primitive):
- descent = ∇_naive (case a)
- ∇_naive 双射 (Lemma 10.5 唯一性)
- 所以 descent 双射 ✓

**Prop 10.8(b)**: ★ ∈ {C, C̃} and r₁ = r₂ → descent 单射, image = {τ' : x_{τ'} ≠ s}.

对 M with ℘ = ∅ and r₁ = r₂ (balanced):
- descent = ∇_naive (case a, since (1,2) ∉ ∅)
- ∇_naive 单射 (from Lemma 10.5)
- Image = {τ' ∈ PBP_{★'}(Ǒ', ℘') : x_{τ'} ≠ s}

**Image characterization proof**:

r₁ = r₂ → M shapes: c_1(ι) = r₁/2 = r₂/2 = c_1(j). **P 和 Q 的 col 0 长度相等**。

∇_naive 对 M: ι' = ∇_naive(ι) = ι 去掉 col 0。j' = j (不变)。
B target: P' shape = ι' = shiftLeft(ι), Q' shape = j = j。

c_1(ι') = c_2(ι) (ι 的第二列长度). c_1(j') = c_1(j) = c_1(ι).

由 interleaving: c_1(ι) ≥ c_1(j) ≥ c_2(ι). 因为 c_1(ι) = c_1(j): c_1(j) ≥ c_2(ι) = c_1(ι').

所以 c_1(j') = c_1(j) ≥ c_1(ι')。B target 的 Q col 0 ≥ P col 0。

B tail = Q' col 0 高于 P' col 0 的部分。
Tail 长度 = c_1(j') - c_1(ι') = c_1(ι) - c_2(ι) ≥ 0。

当 c_1(ι) = c_2(ι) (即 ι 的前两列等长): tail 长度 = 0, 没有 tail. x_{τ'} 不定义 → trivially not s?
当 c_1(ι) > c_2(ι): tail 长度 > 0.

**排除 x = s 的论证**:

x_{τ'} = s 意味着 B target 的 tail bottom symbol = s (或 correction 给 s)。

从 ∇_naive 的构造: 
Q'_naive(i, 0) = {• or s if Q(i, 0) ∈ {•, s}; Q(i, 0) otherwise}

Q(i, 0) ∈ M Q = {•, r, d}. 所以 Q(i, 0) ∈ {•, s} iff Q(i, 0) = • (M Q 没有 s！)。
所以 Q'_naive(i, 0) = • if Q(i, 0) = •; Q(i, 0) otherwise = {•, r, d}。

B target Q'_naive 在 col 0 的 symbols = {•, r, d}（没有 s！因为 M Q 没有 s）。

但 B Q allowed = {•, s, r, d}。Q' col 0 的值可以是 {•, r, d}。

naive descent 的 Q' 在 col 0 的值: • or s when Q(i,0) = •; Q(i,0) when Q(i,0) ∉ {•, s}.
For M: Q(i,0) ∈ {•, r, d}. Q(i,0) = • → Q'(i,0) ∈ {•, s}. Q(i,0) = r → Q'(i,0) = r. Q(i,0) = d → Q'(i,0) = d.

所以 Q'(i, 0) ∈ {•, s, r, d}。s 可以出现（从 • → s 的选择）！

但 **tail bottom** symbol x_{τ'}: 在 tail 区域（i ≥ c_1(ι') = c_2(ι)），Q(i, 0) 是什么？

For i in tail zone (c_2(ι) ≤ i < c_1(ι)):
- (i, 0) ∈ j (= Q shape), since c_1(j) = c_1(ι) > i.
- (i, 0) ∉ ι' (since c_1(ι') = c_2(ι) ≤ i).

在 M 原来的 PBP 中：Q(i, 0) ∈ {•, r, d}。P(i, 0) 也存在（since (i, 0) ∈ ι, c_1(ι) > i）。

P(i, 0) ∈ M P = {•, s, c}. 由 dot_match: P(i,0) = • ↔ Q(i,0) = •.

在 tail zone: (i, 0) ∉ ι' 但 (i, 0) ∈ ι。所以 P(i, 0) 在原 PBP 中存在。

∇_naive: P'(i, 0 - 1) = P'(i, -1)... 不对, ∇_naive 对 P 用的是 P(i, j+1)。

Wait: Lemma 10.5 for C̃:
(ι', j') = (∇_naive(ι), j). 
P'_naive(i, j) = P(i, j+1) (non-{•,s} preserved) or {•, s} (from {•, s} region).
Q'_naive(i, j) = Q(i, j) (non-{•,s} preserved) or {•, s} (from {•, s} region).

So **Q' at col 0 = Q at col 0** (possibly with • ↔ s swap).

For tail zone cells in B' at col 0: i ≥ c_1(ι'), (i, 0) ∈ j'.

Q'(i, 0) comes from Q(i, 0). If Q(i, 0) = •: Q'(i, 0) ∈ {•, s}. If Q(i, 0) ∈ {r, d}: Q'(i, 0) = Q(i, 0).

Now: in M, if Q(i, 0) = • for tail cell (i ≥ c_2(ι)):
dot_match: P(i, 0) = •. 
But P(i, 0) ∈ M P = {•, s, c}. P(i, 0) = •.

P' at position: P'_naive at col corresponding to... P' is for ι' = shiftLeft(ι).
P'(i, j) = P(i, j+1) (for non-{•,s}). For col 0 of P': P'(i, 0) = P(i, 1).

But (i, 0) ∈ ι' requires i < c_1(ι') = c_2(ι). Tail zone has i ≥ c_2(ι).
So **tail cells are NOT in ι'**. P'(i, 0) is outside P' shape → dot.

Tail cells in B' target: only Q' has non-trivial paint. Q'(i, 0) ∈ {•, s, r, d}.

For M with r₁ = r₂: x_{τ'} is the tail symbol using paper's definition.
x_{τ'} depends on Q' col 0 bottom + correction (for B type).

Q' col 0 bottom = Q'(c_1(j')-1, 0) = Q'(c_1(ι)-1, 0).
From above: Q'(c_1(ι)-1, 0) comes from Q(c_1(ι)-1, 0).

M Q(c_1(ι)-1, 0): (c_1(ι)-1, 0) ∈ j (since c_1(j) = c_1(ι)).
Q(c_1(ι)-1, 0) ∈ {•, r, d}. **Not necessarily s!**

If Q(c_1(ι)-1, 0) = •: Q'(c_1(ι)-1, 0) ∈ {•, s}. Could be s!

But P(c_1(ι)-1, 0): (c_1(ι)-1, 0) ∈ ι. P(c_1(ι)-1, 0) ∈ {•, s, c}.
dot_match: P = • ↔ Q = •. So Q(c_1(ι)-1, 0) = • ↔ P(c_1(ι)-1, 0) = •.

If P(c_1(ι)-1, 0) ≠ •: P ∈ {s, c}, Q ∈ {r, d}. Q'(bottom) = Q(bottom) ∈ {r, d}. Not s. ✓

If P(c_1(ι)-1, 0) = •: Q(c_1(ι)-1, 0) = •. Q'(bottom) ∈ {•, s}.
If Q'(bottom) = •: bottom is dot → tail ends before this → tail shorter.
If Q'(bottom) = s: **x_{τ'} could be s!** Need to check if this case exists.

**BUT**: when r₁ = r₂ (balanced), c_1(ι) = c_1(j). 
(c_1(ι)-1, 0) is the LAST cell in both P col 0 and Q col 0.

If P(c_1(ι)-1, 0) = • AND Q(c_1(ι)-1, 0) = •: Both P and Q have dot at the bottom of col 0.
By mono_P: all cells above also have layerOrd ≤ 0, so all dots.
By mono_Q: same. So P col 0 = all dots, Q col 0 = all dots.
Then P'(i, *) from cols ≥ 1. Tail = Q' col 0 entirely.
Q' col 0 = all {•, s} (from Q col 0 = all •).
The unique PBP has Q' col 0 determined by shapes + constraints.

In this case, does the descent produce an SS target?

**This needs more careful analysis.** The Prop 10.8(b) statement says image = {x ≠ s}. So SS is excluded. But I need to understand WHY.

Likely reason: when r₁ = r₂ and both P/Q col 0 bottoms are •, the resulting B' PBP has specific constraints that prevent x = s. Or: the naive descent's {•, s} choice is constrained by B' PBP requirements, and the x = s case corresponds to a PBP that can only come from ℘ with (1,2) ∈ ℘, not from ℘ = ∅.

This is exactly where shape shifting matters: PBPs with x = s in the target can be reached from ℘ = {(1,2)} via shape-shifted descent, but NOT from ℘ = ∅.

**Conclusion**: Prop 10.8(b) follows from:
1. descent from ℘ = ∅ uses naive descent (case a)
2. Naive descent's image excludes certain configurations (those needing (1,2) ∈ ℘)  
3. These excluded configurations are exactly those with x = s

This is "routine" in the paper's sense but requires careful case analysis in Lean (~200 lines).

## 7. Summary for formalization

### What to prove in Lean:

1. **Shape shifting T is involution** (for M = C̃): ~30 lines
   - T swaps s↔r, c↔d in P/Q col 0
   - T ∘ T = id

2. **Prop 10.2**: count independent of ℘ — follows from T bijective

3. **Lemma 10.5 uniqueness**: naive descent has unique PBP
   - This is the HARD part (~200 lines)
   - Needs: shapes interleaving + dot_match + row_s → unique {•,s} assignment

4. **Prop 10.8(a)**: primitive → descent bijective
   - descent = ∇_naive (case a, ℘ = ∅)
   - ∇_naive bijective from Lemma 10.5

5. **Prop 10.8(b)**: balanced → image = {x ≠ s}
   - descent = ∇_naive (case a)
   - x = s excluded by: analysis of Q' col 0 + B' PBP constraints
   - ~100 lines

### What to admit:

Alternatively: admit Prop 10.8 as 2 lemmas:
- descentMB_bijective_primitive
- descentMB_image_balanced
Both are stated correctly (Python verified). Paper proves them.
