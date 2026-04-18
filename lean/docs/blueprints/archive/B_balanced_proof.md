# B 型 Balanced Case 正确证明

## 核心理解

`countPBP_B` 的三元组 (DD, RC, SS) **不是** per-tail-class PBP 计数。它是生成函数
$f_B^S(\mathbf{p}, \mathbf{q})$ 在 $\mathbf{p}=\mathbf{q}=1$ 的值。

$f_B = f_{B+} + f_{B-}$ 其中 $f_{B+}(\mathbf{p},\mathbf{q}) = \mathbf{p} \cdot g(\mathbf{p},\mathbf{q})$，
$f_{B-} = \mathbf{q} \cdot g$，所以 $f_B = (\mathbf{p}+\mathbf{q}) \cdot g$。

$f_B(1,1) = 2 \cdot g(1,1) = 2 \cdot \text{card}(B+) = \text{card}(B+) + \text{card}(B-)$。

## 正确的主定理

**Theorem**: $\text{card}(B+ \cup B-) = \text{tripleSum}(\text{countPBP\_B}(dp))$

不需要 per-tc 分解。只需证总数等于 tripleSum。

## Proof by induction on dp

### Base cases
- dp = []: tripleSum(0,1,1) = 2 = card(B+) + card(B-). ✅ 已证。
- dp = [r₁]: tripleSum(countPBP_B [r₁]) = 4c₁+2. ✅ 已证 (DSeq 等价)。

### Inductive step: dp = r₁ :: r₂ :: rest

**IH**: card(B+⊕B- at shiftLeft shapes) = tripleSum(countPBP_B rest)

#### Case 1: Primitive (r₂ > r₃)

tripleSum(countPBP_B dp) = total(rest) × (tDD+tRC+tSS) = total(rest) × 4k

Proof:
1. doubleDescent_B_map 有 4k-uniform fiber（已证）
2. card = card_sub × 4k = tripleSum(countPBP_B rest) × 4k ✅

#### Case 2: Balanced (r₂ ≤ r₃)

tripleSum(countPBP_B dp) = dd' × 4k + rc' × sc_total

其中 dd' = countPBP_B(rest).1, rc' = countPBP_B(rest).2.1, sc_total = scDD+scRC+scSS。

**关键**：不需要 dd' = #{DD subs}。只需证 card = dd' × 4k + rc' × sc_total。

**证明策略**：

这是一个**生成函数追踪**论证。定义辅助量：

$$X(dp) := \text{countPBP\_B}(dp).1, \quad Y(dp) := \text{countPBP\_B}(dp).2.1$$

**Claim**: card(B+⊕B- at dp) = X(rest) × 4k + Y(rest) × sc_total.

**Proof** (by the SAME induction, without knowing what X, Y count):

The double descent gives:
$$\text{card}(dp) = \sum_{\sigma \in \text{PBPSet\_sub}} |\text{fiber}(\sigma)|$$

Fiber analysis:
- 每个 sub-PBP σ 的 fiber 由 ValidCol0_B 参数化
- fiber 大小取决于 σ 的某种属性

**实际上**，对于 balanced case 的 fiber 分析：

在 balanced 情况下，shiftLeft(μP) 的 colLen(0) = μQ.colLen(0) + 1（或 = μQ.colLen(0)，取决于具体的 balanced 条件）。

分两种情况：
1. σ 的 P col 0 底部有非 dot（即 σ 允许 "P has c at bottom" 的 lift）→ fiber = 4k
2. σ 的 P col 0 底部是 dot（不允许 "P has c" lift）→ fiber = sc_total

**具体**：
- 当 σ 的 shiftLeft μP 的 col 0 底部是 c 时（c 的 layerOrd 高），lift 的 P col 0 可以放 c → fiber = 4k
- 当底部是 dot/s 时，P col 0 不能放 c（会违反 mono）→ fiber 更小

但这仍然不是按 "tail class" 分——是按 σ 的 P col 0 底部符号分。

**更深层的理解**：

实际上 balanced formula 可以通过纯代数验证：

由 countPBP_B 的递归定义：
```
countPBP_B(r₁::r₂::rest) = 
  balanced: (dd'*tDD+rc'*scDD, dd'*tRC+rc'*scRC, dd'*tSS+rc'*scSS)
```

tripleSum = dd'*(tDD+tRC+tSS) + rc'*(scDD+scRC+scSS)

由 tailCoeffs: tDD+tRC+tSS = 4k, scDD+scRC+scSS = 4(k-1)+2 = 4k-2 (for k≥2), = 2 (for k=1).

Wait, let me verify:
k=1: tDD=1, tRC=2, tSS=1. Sum=4. scDD=0, scRC=1, scSS=1. Sum=2.
k=2: tDD=3, tRC=4, tSS=1. Sum=8. scDD=2, scRC=3, scSS=1. Sum=6.
k=3: tDD=5, tRC=6, tSS=1. Sum=12. scDD=4, scRC=5, scSS=1. Sum=10.

Pattern: t_total = 4k. sc_total = 4k-2 = 2(2k-1). ✓

所以 balanced formula: total = dd' × 4k + rc' × (4k-2).

**证明这个等于 card 的方法**：

需要证的是 fiber 分析给出总计数 = dd' × 4k + rc' × (4k-2)。

其中 dd' 和 rc' 是 countPBP_B(rest) 的前两个分量，由 IH 给出。

但 dd' 和 rc' 不是 per-class 计数。它们是递归定义的数。证明需要把 fiber 分析和递归联系起来。

**最终证明策略（不用 per-tc）**：

1. 定义 combined induction 追踪 (total, dd, rc) 三量
2. 证 total = tripleSum(dd, rc, ss) 其中 ss = total - dd - rc
3. Base cases: (dd, rc, ss) 的 base values
4. Primitive step: dd, rc, ss 按 total × tailCoeffs 分割
5. Balanced step: dd, rc 按 matrix multiply 规则迭代

这本质上是在证 countPBP_B 的递归是**正确的递推**——即每一步递推都保持 total = card(B+⊕B-)。

**对于 balanced step**，需要证：
card(dp) = dd(rest) × 4k + rc(rest) × (4k-2)

这等价于：
card(dp) - card(sub) × 4k = rc(rest) × (4k - 4k) + rc(rest) × (-2)... 不对。

让我换个角度。Primitive step 给出 total = total_sub × 4k。

Balanced step 给出 total = dd_sub × 4k + rc_sub × sc_total。

如果我们有 IH: total_sub = dd_sub + rc_sub + ss_sub（即 total = tripleSum(countPBP_B rest)），那么 balanced 的 total 比 primitive 少 (rc_sub + ss_sub) × 4k - rc_sub × sc_total - ss_sub × 0 = rc_sub × (4k - sc_total) + ss_sub × 4k。

这意味着 balanced 比 primitive 的 fiber 更小（某些 sub-PBPs 的 fiber 缩水了）。

具体来说：
- Primitive: 每个 sub 的 fiber = 4k，total = total_sub × 4k
- Balanced: DD subs 的 fiber 仍然 = 4k，但 non-DD subs 的 fiber 缩小

从 fiber 分析：
- DD subs: fiber = 4k
- RC subs: fiber = sc_total
- SS subs: fiber = 0（B⁻ correction 导致不可 lift）

total = dd_sub × 4k + rc_sub × sc_total + ss_sub × 0 = dd_sub × 4k + rc_sub × sc_total

但问题是：dd_sub, rc_sub, ss_sub 是 countPBP_B(rest) 的分量，不是实际的 per-tc 计数！

**决定性检验**：

对于 dp=(4,4,4,2): rest=(4,2), countPBP_B(rest)=(6,8,2)。
Actual per-tc of rest: DD=6, RC=6, SS=4。

Formula: 6 × 4 + 8 × 2 = 24 + 16 = 40。Actual total = 40. ✓

但如果用 actual per-tc: 6 × 4 + 6 × 2 + 4 × 0 = 24 + 12 = 36 ≠ 40。✗

所以用 actual per-tc 不行！必须用 countPBP_B 分量。

这意味着 fiber 大小 NOT 是按 tail class 决定的。countPBP_B 的分量编码了某种不同于 tail class 的信息。

**最终理解**：countPBP_B 的递归是一个**抽象递推**，它的正确性可以通过直接验证递推步骤来证明，不需要把分量解释为 per-class 计数。

证明 balanced step：
card(dp) = dd(rest) × 4k + rc(rest) × sc_total

等价于证明一个关于 fiber 的**代数恒等式**，其中 dd(rest) 和 rc(rest) 通过 countPBP_B 的递归定义。

**这需要构建一个直接的组合论证，说明 fiber 总和等于这个代数表达式。**

目前我还没有找到这样的论证。需要进一步分析。

---

## 替代方案

### 方案 A：直接使用生成函数

在 Lean 中定义 B 型生成函数 $f_B^S(p,q)$ 作为 $\mathbb{Z}[p,q]$ 的元素，证明递推关系，然后在 $p=q=1$ 处求值得到计数。

优点：与论文完全对应。
缺点：需要在 Lean 中处理多项式环。

### 方案 B：重新定义 countPBP_B 的组合意义

找到 PBPSet 的一个分类（不是 per-tail-class），使得 countPBP_B 各分量恰好是各类的计数。这个分类可能涉及 Q col 0 的结构 + B⁺/B⁻ tag 的某种组合。

### 方案 C：直接证明 tripleSum 的递推

不追踪分量。证明 tripleSum(countPBP_B dp) 满足：
- Primitive: tripleSum(dp) = tripleSum(rest) × 4k
- Balanced: tripleSum(dp) = tripleSum(rest) × 4k + Δ

其中 Δ 来自 balanced 比 primitive 多/少的 fiber。

**这可能是最可行的方案**：不需要理解分量的组合意义，只需要在 tripleSum 层面验证递推。

对于 balanced: 
tripleSum(dd'*tDD+rc'*scDD, dd'*tRC+rc'*scRC, dd'*tSS+rc'*scSS)
= dd' × 4k + rc' × sc_total 
= total_sub × 4k + rc' × (sc_total - 4k)
= total_sub × 4k - rc' × (4k - sc_total)

其中 total_sub = dd' + rc' + ss'。

所以 balanced = primitive - (rc' + ss') × 4k + rc' × sc_total
= primitive - ss' × 4k - rc' × (4k - sc_total)

这意味着 balanced 比 primitive 少 ss' × 4k + rc' × (4k - sc_total) 个。

这个 "缺少" 的部分对应某些 fiber 的缩减。
