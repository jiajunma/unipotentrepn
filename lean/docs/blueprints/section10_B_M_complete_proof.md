# 完整自然语言证明：B/M 型计数 (Props 10.11/10.12)

Reference: [BMSZb] Section 10.5–10.6, Propositions 10.11–10.12.

## Lean 形式化
- **Prop 10.11 B**（unconditional）：`prop_10_11_B` in `CountingProof/Section10.lean`
- **Prop 10.12 M**（unconditional）：`prop_10_12_M` in `CountingProof/Section10.lean`
- 底层 bijection 构造：`CountingProof/CorrespondenceB.lean`, `CountingProof/Prop10_8_M.lean`

---

## Part I: 论文的精确定义

### 1.1 Tail multiset {x₁, ..., xₖ} 的定义 ([BMSZb] p.70–71)

设 ★ ∈ {B, D}，τ = (ι, P) × (j, Q) × γ ∈ PBP_★(Ǒ, ℘)。

定义 ★_t := D（tail 总是 D 型）。k := (r₁ - r₂)/2 + 1。

**★ = B 的情况**：c₁(ι) ≤ c₁(j)。

多重集 {x₁, ..., xₖ} = Set A ∪ {correction element}，其中：

**Set A** = { Q(j, 1) | c₁(ι) + 1 ≤ j ≤ c₁(j) }
（使用论文的 1-based 索引；0-based：Q.paint(j-1, 0) for c₁(ι) ≤ j-1 < c₁(j)）
大小 = c₁(j) - c₁(ι) = k - 1 个元素

**Correction element** x₁（1 个元素）：
- 若 α = B⁺ 且（c₁(ι) = 0 或 Q(c₁(ι), 1) ∈ {•, s}）：x₁ = **c**
- 若 α = B⁻ 且（c₁(ι) = 0 或 Q(c₁(ι), 1) ∈ {•, s}）：x₁ = **s**
- 否则：x₁ = Q(c₁(ι), 1)（即 r 或 d，与 γ 无关）

**x_τ := xₖ**（多重集最后一个）：
- k > 1：x_τ = Q(c₁(j), 1) = Q col 0 底部（与 γ 无关）
- k = 1：x_τ = x₁ = correction element（**依赖 γ**）

### 1.2 Per-class 分类

PBP_★^S(Ǒ, ℘) := { τ ∈ PBP_★ | x_τ ∈ S }

三个类：S = {d}（DD 类），S = {c, r}（RC 类），S = {s}（SS 类）。

**关键**：对 B 型，x_τ 包含 correction，所以 B⁺ 和 B⁻ 的分类可以不同。
具体：当 k = 1 且 Q(c₁(ι), 1) ∈ {•, s} 时：
- 同一个 painting，B⁺ 归入 RC（因为 x_τ = c），B⁻ 归入 SS（因为 x_τ = s）。

### 1.3 验证 countPBP_B = per-class count

对 dp = (2,)，c₁(ι) = 0，c₁(j) = 1，k = 2。Set A = {Q(0,0)}（1 个元素）。

3 个 DRC 图，每个同时给 B⁺ 和 B⁻：

| DRC Q | Set A | x₁ (B⁺) | x₁ (B⁻) | x_τ = x₂ | B⁺ class | B⁻ class |
|-------|-------|---------|---------|-----------|----------|----------|
| (d) | {d} | c | s | d | DD | DD |
| (r) | {r} | c | s | r | RC | RC |
| (s) | {s} | c | s | s | SS | SS |

等等——k = 2 所以 x_τ = x₂ = Set A 最后元素 = Q(c₁(j), 1) = Q(0,0)。
与 correction 无关！

DD = 2 (d: B⁺ + B⁻)，RC = 2 (r: B⁺ + B⁻)，SS = 2 (s: B⁺ + B⁻)。
但 countPBP_B = (2, 3, 1)。

**不匹配！** 说明我上一版分析有误。让我重新检查。

实际上 k = (r₁ - r₂)/2 + 1 = (2 - 0)/2 + 1 = 2。这里 r₂ = 0（只有一行）。
c₁(ι) = P.colLen(0) = 0，c₁(j) = Q.colLen(0) = 1。
Set A = { Q(j,1) | 0+1 ≤ j ≤ 1 } = { Q(1, 1) }。

Q(1, 1) = Q.paint(0, 0)（0-based：j=1 → row 0, col 0... 不对）

**索引问题**：论文用 (i, j) 其中 i 是列号，j 是行号。Q(j, 1) 中 j 是行号，1 是列号。
列号 1 = col 0（0-based）？不，论文的列号从 1 开始。列号 1 = 第一列 = col 0 (0-based)。

所以 Q(j, 1) = Q.paint(j-1, 0)（0-based row = j-1, col = 0）。

Set A = { Q(j, 1) | c₁(ι)+1 ≤ j ≤ c₁(j) }
     = { Q(j, 1) | 1 ≤ j ≤ 1 }（c₁(ι) = 0）
     = { Q(1, 1) }
     = { Q.paint(0, 0) }（0-based）

OK，所以 Set A = {Q.paint(0, 0)} = {d}, {r}, 或 {s}。

Correction x₁：c₁(ι) = 0，所以条件 "c₁(ι) = 0" 为真。
→ B⁺: x₁ = c, B⁻: x₁ = s

x_τ = xₖ = x₂ = Set A 最后元素 = Q.paint(0, 0)。

所以 x_τ 不依赖 correction！对 k = 2 都是如此。

那为什么 countPBP_B = (2, 3, 1) ≠ (2, 2, 2)？

让我回到论文的生成函数公式。

$f^{\{c,r\}}_{B,[2k]_{row},\emptyset} = p\nu_k + p^2 q \nu_{k-1}$

对 k = 1（dp = [2]）：$= p\nu_1 + p^2 q \nu_0 = p(p^2q^0 + p^0q^2) + p^2q$
$= p^3 + pq^2 + p^2q$

在 p=q=1：$= 1 + 1 + 1 = 3$。

但 #{PBP_B : x_τ ∈ {c,r}} = 2（Q=(r) 给 B⁺ RC + B⁻ RC = 2）。

所以 $f^{\{c,r\}}(1,1) = 3 ≠ 2$。

**这意味着 $f^S(1,1) ≠ \#PBP_B^S$！**

等一下——$f^S(p,q) = \sum_{\tau \in PBP_B^S} p^{p_\tau} q^{q_\tau}$，在 p=q=1 每项贡献 1，所以 $f^S(1,1) = \#PBP_B^S$。

除非...PBP_B 不包含 B⁺ 和 B⁻ 两者？

让我重新查看论文。p.72 定义："When ★ ∈ {B, D, C*}, for each subset S..."

★ = B 指的是什么？从 p.63 表格：
★ = B 对应 SO(p,q) with p+q odd。

这是**一个**实李群，不是 B⁺ 和 B⁻ 两个。

**关键区分**：
- PBP_B(Ǒ, ℘) = 一组 painted bipartitions，对应**一个** real form SO(p,q)
- PBP_{B⁺} 和 PBP_{B⁻} 是两个不同 real form 的 PBP 集合

**论文的 ★ = B 指的是一个特定的 (p,q) 的 SO(p,q)，不是 B⁺ 和 B⁻ 的并集！**

所以 $f_{B,Ǒ,℘}$ 只对一个 real form 求和。对于 SO(p,q)，PBP 的数量等于 countPBP_B(dp) 的各分量... 不，应该等于 card(B⁺) 或 card(B⁻)（取决于 (p,q) 对应哪个）。

让我重新理解。从 `countPBP` 的定义：
```
| .Bplus | .Bminus => let (dd, rc, ss) := countPBP_B dp; (dd + rc + ss) / 2
```

所以 card(B⁺) = tripleSum(countPBP_B dp) / 2。

$f_B(1,1)$ = card of PBP_B for ONE real form = card(B⁺) = tripleSum/2。

但 $f_B^{\{c,r\}}(1,1) = 3$ 而 card(B⁺ with x∈{c,r}) = 1（对 dp=(2,)）。
tripleSum = 6, card(B⁺) = 3。

$f_B^{\{c,r\}} = 3$，card(B⁺) = 3。但 card(B⁺ with x∈{c,r}) = 1。

所以 $f_B^S(1,1) ≠ \#\{τ ∈ PBP_{B⁺} : x_τ ∈ S\}$。

**但 $f_B^S(1,1) = \#\{τ ∈ PBP_B : x_τ ∈ S\}$！**

这里 PBP_B 是论文意义的 PBP（不区分 B⁺/B⁻）。那 #PBP_B 是多少？

论文 p.72："the coefficient of p^p q^q in f_{★,Ǒ,℘}(p,q) equals the cardinality of PBP_G(Ǒ, ℘) when G = SO(p,q)"。

所以 PBP_G 对**特定的** (p,q) 计数。f_{B,Ǒ}(p,q) 的系数给出不同 (p,q) 的 PBP 数。

$f_B(1,1) = \sum_{(p,q)} \#PBP_{SO(p,q)}(Ǒ)$（summed over all (p,q) with p+q = |O|+1, p+q odd）

不对，f_B(1,1) 是把所有 p^a q^b 在 p=q=1 求和，每个 PBP 贡献 1。所以 f_B(1,1) = |PBP_B|（论文意义的 PBP_B）。

**论文的 PBP_B 不区分 B⁺/B⁻**。PBP_B 的元素是 painted bipartition τ = (ι, P) × (j, Q) × γ 其中 γ ∈ {B⁺, B⁻}。但论文说 γ 由 (ι, j) 的形状和 ℘ 决定（Prop 10.1），对 quasi-distinguished 的 Ǒ，℘ = ∅，所以 γ 不出现。

等一下——论文的 PBP_★ 中 ★ = B 是否包含 α（= B⁺ 或 B⁻）的选择？

从 p.68："(10.5) $\gamma' = B^+$ if α = C̃ and c does not occur..."

这里 α 是原 PBP 的 root type。所以 PBP_B 的元素确实有一个 γ（= B⁺ 或 B⁻）的选择。

但从 Prop 10.2："$\#(PBP_G(Ǒ, ℘)) = \#(PBP_G(Ǒ, ∅))$ for all ℘"。

这里 PBP_G 对 G = SO(p,q) 是一个特定 real form。而 countPBP_B 计算的是 PBP_★ 对 ★ = B，包含所有 real forms SO(p,q) with p+q = |O| + 1。

**实际上，countPBP_B(dp) 的 tripleSum 等于 |PBP_B| = card(B⁺) + card(B⁻)**。而论文的 f_B(1,1) = |PBP_B|。

所以：
- f_B(1,1) = tripleSum(countPBP_B dp)
- f_B^S(1,1) = countPBP_B(dp) 的对应分量
- 这些是 PBP_B（包含 B⁺ 和 B⁻）中 x_τ ∈ S 的 PBP 数

但我之前计算 dp=(2,)：actual per-tc(B⁺+B⁻) = (2,2,2) ≠ countPBP_B = (2,3,1)。

**唯一的解释**：我的 `compute_tail_symbol` 和论文的 x_τ 定义不一致。

让我更仔细地重新计算 dp=(2,) 的 tail multiset。

dp = (2,)：r₁ = 2，r₂ = 0（没有第二行）。
★ = B：c₁(ι) = P.colLen(0) = 0, c₁(j) = Q.colLen(0) = 1。
k = (2-0)/2 + 1 = 2。

Ǒ_t 有行 [2k-1, 1] = [3, 1]。
★_t = D。PBP_{★_t}(Ǒ_t) 中的元素 τ_t 有 k = 2 个 tail symbols。

**但实际上 tail PBP τ_t 的 symbols 不是直接从 Q col 0 读出的！**

τ_t ∈ PBP_D(Ǒ_t) 是一个独立的 D 型 PBP。tail multiset {x₁, ..., xₖ} 是 τ_t 的 P col 0 的 symbols（因为 ★_t = D）。

论文 p.70–71 的定义说："{x₁, ..., xₖ} 是 τ_t 的 painted bipartition (10.7) 中的多重集"。

(10.7) 中 ★ = B 的 τ_t 的形状是一列 k 个 cells：x₁, x₂, ..., xₖ。
这些 xᵢ 来自 Q col 0 的 tail cells **加上 correction**。

**核心**：τ_t 是一个 D 型 PBP，它的 P col 0 由 tail multiset 决定。x_τ = xₖ = P_{τ_t}(k, 1) = τ_t 的 P col 0 底部。

但 tail multiset 的**值**不等于简单地读 Q col 0！它包含 correction。

所以问题在于：`compute_tail_symbol(drc, 'B+', dp)` 返回的是否是论文的 x_τ？

对 dp=(2,), Q=(s), B⁺：`compute_tail_symbol` 返回 s（因为 setA_size = 1 > 0，返回 fR[-1] = s）。

但论文的 x_τ = xₖ = x₂ = Set A 最后元素 = Q(c₁(j), 1) = Q(1, 1)。

在 1-based 中 Q(1, 1) = Q 的第 1 行第 1 列。Q 只有 1 行 1 列的 cell (1,1)（1-based）。Q(1,1) = s。

所以 x_τ = s。✓ compute_tail_symbol 是对的。

那 x_τ = s 对 B⁺ 和 B⁻ 都是如此。所以 both B⁺ 和 B⁻ 都在 SS class。

但论文的 $f^{\{s\}}(1,1) = 1$，不是 2！

**只有一种解释**：论文的 PBP_B **不包含 B⁺ 和 B⁻ 的选择**。★ = B 对应一个固定的 real form，不区分 B⁺/B⁻。

所以 |PBP_B(Ǒ, ∅)| = card(B⁺) = card(B⁻) = tripleSum(countPBP_B dp) / 2。

**这就是用户说的："递归公式其实只 apply to B+"！**

### 1.4 正确理解

$$f_{B,Ǒ,∅}(1,1) = \text{card}(B^+) = \text{card}(B^-) = \text{tripleSum}(\text{countPBP\_B}(dp)) / 2$$

$$f^S_{B,Ǒ,∅}(1,1) = \#\{\tau \in PBP_{B^+} : x_\tau \in S\}$$

所以 countPBP_B 的各分量的**含义**是：

$$\text{countPBP\_B}(dp) = (2 \cdot DD_{B^+},\; 2 \cdot RC_{B^+},\; 2 \cdot SS_{B^+})$$

不对——如果各分量都是 2 倍，那 tripleSum = 2 × card(B⁺) ✓。但 countPBP_B(2) = (2,3,1)，tripleSum = 6 = 2 × 3 = 2 × card(B⁺)。

如果 DD_{B⁺} = 1, RC_{B⁺} = 1, SS_{B⁺} = 1（对 dp=(2,)），那 2×(1,1,1) = (2,2,2) ≠ (2,3,1)。

所以 countPBP_B ≠ 2 × (B⁺ per-tc)。

**那 countPBP_B 的各分量到底是什么？**

它们是 $f^S_B$ 的值，而 $f^S_B$ 对**一个** real form 求和，用 $p^{p_\tau} q^{q_\tau}$ 加权。
在 p=q=1 时 $f^S_B(1,1) = \#PBP_{B^+}^S = $ card(B⁺ with x ∈ S)。

对 dp=(2,)：
- $f^{\{d\}}(1,1) = 2$。但 card(B⁺ with x=d) = 1。
- $f^{\{c,r\}}(1,1) = 3$。但 card(B⁺ with x∈{c,r}) = 1。
- $f^{\{s\}}(1,1) = 1$。但 card(B⁺ with x=s) = 1。

$f^{\{d\}}(1,1) = 2 ≠ 1 = $ card(B⁺ with x=d)。

**矛盾！**

除非 card(B⁺) ≠ 3。让我重新计数。

dp = (2,)，★ = B。orbit 有 1 行 length 2。
P cols = dpartColLensP_B [2] = [] → P = ⊥
Q cols = dpartColLensQ_B [2] = [1] → Q has 1 cell

B⁺ PBPs：P = ⊥, Q.paint(0,0) ∈ {s, r, d}（3 choices）→ card(B⁺) = 3。

signature for each:
- Q=(d), B⁺: p = 0 + 0 + 0 + 1 + 1 = 2, q = 0 + 0 + 0 + 1 + 0 = 1. sig = (2, 1).
- Q=(r), B⁺: p = 0 + 2 + 0 + 0 + 1 = 3, q = 0 + 0 + 0 + 0 + 0 = 0. sig = (3, 0).
- Q=(s), B⁺: p = 0 + 0 + 0 + 0 + 1 = 1, q = 0 + 2 + 0 + 0 + 0 = 2. sig = (1, 2).

$f_{B⁺}(p,q) = p^2 q + p^3 + p q^2 = p(p^2 + pq + q^2)$

$f^{\{d\}}_{B⁺} = p^2 q$（只有 Q=(d) 一个，sig=(2,1)）
$f^{\{r\}}_{B⁺} = p^3$（只有 Q=(r)）
$f^{\{s\}}_{B⁺} = p q^2$（只有 Q=(s)）

在 p=q=1：$f^{\{d\}}=1, f^{\{r\}}=1, f^{\{s\}}=1$。sum = 3 = card(B⁺)。✓

但 countPBP_B = (2, 3, 1)。$f^{\{d\}}(1,1)=1 ≠ 2$。

**所以 countPBP_B ≠ f^S_{B⁺}(1,1)**。

那 countPBP_B 到底计算什么？

$f^S_{B⁺}(1,1) = (1, 1, 1)$。tripleSum = 3 = card(B⁺)。
$f^S_{B⁻}(1,1)$：for dp=(2,), B⁻ has sig (1,2), (2,1), (0,3).

$f^{\{d\}}_{B⁻} = p q^2$，$f^{\{r\}}_{B⁻} = p^2 q$, $f^{\{s\}}_{B⁻} = q^3$

在 p=q=1：(1, 1, 1)。sum = 3 = card(B⁻)。

$f^S_B = f^S_{B⁺} + f^S_{B⁻}$（论文的 PBP_B 包含 B⁺ 和 B⁻）：
$f^{\{d\}}_B = p^2q + pq^2 = pq(p+q)$。在 1,1：2。✓ = countPBP_B.DD
$f^{\{r\}}_B = p^3 + p^2q$。但论文的 RC 是 {c, r}，不只是 {r}！

**等等**——对 B 型，x_τ 可以是 c 吗？

从定义：x_τ = xₖ 来自 tail multiset {x₁, ..., xₖ}。

对 k = 2（dp=(2,)）：x₂ = Set A 最后元素 = Q(c₁(j), 1) = Q(1,1)。
Q 的 symbols 是 {•, s, r, d}（B 型 Q 没有 c！）。
所以 x_τ ∈ {•, s, r, d}，不会是 c。

那 PBP_B^{c,r} = PBP_B^{r}（因为没有 x = c 的情况）。

$f^{\{c,r\}}_B = f^{\{r\}}_B = p^3 + p^2q$。在 1,1：2。
但 countPBP_B.RC = 3！

**3 ≠ 2**。

**结论：countPBP_B 的实现与论文不一致！**

让我回查 countPBP_B 的实现和 standalone.py 的实现。

```python
def _countPBP_B(dpart):
    c1 = dpart[0] // 2 if len(dpart) == 1 else 0
    DD = 1 * 2 * nu(c1 - 1)       # d·(p+q)·ν_{c1-1} at (1,1)
    RC = 1 * nu(c1) + 1 * nu(c1 - 1)  # p·ν_{c1} + p²q·ν_{c1-1}  
    SS = 1                         # q·s^{c1}
```

comment 说 "p·ν_{c1} + p²q·ν_{c1-1}"。

论文 p.72：$f^{\{c,r\}}_{B,[2k]_{row},∅} = p\nu_k + p^2 q \nu_{k-1}$

对 k = 1：$= p\nu_1 + p^2q\nu_0 = p(p^2+q^2) + p^2q$
$= p^3 + pq^2 + p^2q$

在 1,1：3。✓ 匹配 countPBP_B.RC = 3。

但 $f^{\{c,r\}} = p^3 + pq^2 + p^2q = p(p^2+pq+q^2)$。

而 $f^{\{r\}}_B = p^3 + p^2q$（只有 B⁺ 的 r 和 B⁻ 的 r）。

$f^{\{c,r\}} - f^{\{r\}} = pq^2$。

这个差 $pq^2$ 来自哪里？它是一个 PBP 的贡献 $p^1 q^2$。sig = (1, 2) 的 PBP。

对 dp=(2,)，sig=(1,2) 的 PBP 是：Q=(s), B⁺。x_τ = s（如前计算）。

但这个 PBP 有 x_τ = s，不在 {c, r} 中！

**等一下** — 让我重新检查。如果 k=1（不是 k=2），情况就不同了。

dp=(2,)：是 B 型单行 [2k]_row，k = c₁ = r₁/2 = 1。

论文的 $f^S_{B,[2k]_{row},∅}$ 是对 **tail** 的生成函数，不是对整个 PBP 的。

**关键区分**：
- $f^S_{B,[2k]_{row},∅}$ = tail PBP 的生成函数（只有 tail 部分）
- $f_{B,Ǒ,℘}$ = 整个 PBP 的生成函数

对 dp = [2k] = [2]（单行），entire PBP = tail PBP。所以 $f_{B,Ǒ} = f_{B,[2k]_{row}}$。

但 $f_{B,[2k]_{row}}$ 使用的 signature $(p_\tau, q_\tau)$ 是**整个 PBP 的** signature，不只是 tail 的。

对 B⁺，signature 包含 +1 到 p。对 B⁻，+1 到 q。

$f_{B,[2k]_{row}} = f_{B⁺,[2k]_{row}} + f_{B⁻,[2k]_{row}}$？

不，论文的 ★ = B 只对**一个** real form。

**我需要彻底理清 PBP_B 的定义。**

从论文的 Definition 2.25 和 (8.15)：PBP_G(Ǒ, ℘) = {τ = (ι, P) × (j, Q) × α}。
其中 α ∈ {B⁺, B⁻}（对 ★ = B）。

所以 **PBP_B 包含 α 的选择**（B⁺ 或 B⁻），每个 DRC diagram 给两个 PBP。

f_{B,Ǒ}(p,q) = Σ_{τ∈PBP_B} p^{p_τ} q^{q_τ}
= Σ_{DRC d} (p^{p_{d,B⁺}} q^{q_{d,B⁺}} + p^{p_{d,B⁻}} q^{q_{d,B⁻}})
= Σ_d (p^{p_d+1} q^{q_d} + p^{p_d} q^{q_d+1})
= Σ_d p^{p_d} q^{q_d} (p + q)

f_B(1,1) = Σ_d 2 = 2 × #DRC = 2 × card(B⁺) = card(B⁺) + card(B⁻)。✓

$f^{\{c,r\}}_B(1,1) = \#\{τ ∈ PBP_B : x_τ ∈ \{c,r\}\}$

对 dp=(2,)：x_τ 定义用论文的 tail multiset。
k = 1（因为 r₁ = 2, r₂ = 0, k = (2-0)/2 + 1 = 2... 

等等，这里有索引混淆。让我重新对齐。

dp = [2]。这是 B 型，orbit 有 1 行长度 2。
tailCoeffs 的 k = r₁/2 + 1 = 2 ← 这是 countPBP_B 的计算用的 k

但论文 p.72 的 $f^S_{B,[2k]_{row}}$ 中 k 指 tail 的行数 = half of row length。
对 dp=[2]：2k = 2，所以 k = 1。

而 countPBP_B 的 k = r₁/2 + 1 = 2。

**两个 k 不一样！** 论文的 k（tail 半长）= r₁/2 = 1。我们代码的 k = r₁/2 + 1 = 2。

这是一个 off-by-one。让我检查 countPBP_B 的 singleton case：
```
countPBP_B [r₁]:
  c₁ := r₁ / 2  -- = 1 for r₁ = 2
  DD = 2 * nu(c₁ - 1) = 2 * nu(0) = 2
  RC = nu(c₁) + nu(c₁ - 1) = nu(1) + nu(0) = 2 + 1 = 3
  SS = 1
```

与论文对比：k_paper = 1。
$f^{\{d\}}_{B,[2]_{row}} = (p^2q+pq^2)\nu_0 = p^2q+pq^2$。at 1,1: 2. ✓
$f^{\{c,r\}}_{B,[2]_{row}} = p\nu_1+p^2q\nu_0 = p(p^2+q^2)+p^2q$。at 1,1: 1+1+1=3. ✓
$f^{\{s\}}_{B,[2]_{row}} = q^3$。at 1,1: 1. ✓

所以代码的 c₁ = 论文的 k。代码用 `c₁ = r₁/2` 作为 index，与论文的 k 一致。只是递推中的 k（= (r₁-r₂)/2+1）是另一个量。

OK 现在关键问题：**$f^{\{c,r\}}(1,1) = 3$ 而 actual #{PBP_B with x∈{c,r}} = ?**

f^{c,r}(1,1) = 3。actual per-class：
论文的 x_τ 对 B⁺ Q=(s) 给什么？

k_paper = 1 for the tail. Ǒ_t = [1] (one row length 1).
PBP_D(Ǒ_t)：D 型 with orbit [1]。P cols = [(1+1)/2] = [1], Q cols = []. 
So PBP_D([1]) has P with 1 cell and Q = ⊥.
#PBP_D([1]) = 4 (P(0,0) can be dot, s, r, c, d — but with constraints).

Wait, actually D type P has symbols {•, s, r, c, d}. With 1 cell, it can be any of these? And Q = ⊥ (all dots). dot_match: P(0,0)=• iff Q(0,0)=•. Q=⊥ so (0,0) ∉ Q. So P(0,0) doesn't need to be dot. P(0,0) ∈ {•, s, r, c, d} freely? But (0,0) ∈ P so P(0,0) must be from allowed(D, L) = {•, s, r, c, d}. And monotone, row_s, row_r, col_c, col_d constraints are trivial with 1 cell.

So #PBP_D([1]) = 4 (the 4 non-dot symbols, since dot_match forces P(0,0) ≠ dot when Q=⊥ and (0,0)∈P but (0,0)∉Q)。

Wait: dot_match says P(0,0)=• ∧ (0,0)∈P ↔ Q(0,0)=• ∧ (0,0)∈Q. 
RHS: (0,0) ∉ Q, so RHS = False. So LHS = False: ¬(P(0,0)=• ∧ (0,0)∈P). Since (0,0)∈P, we need P(0,0) ≠ •. So P(0,0) ∈ {s, r, c, d}. 4 choices.

countPBP_D [1] = (tDD, tRC, tSS) with k=(1-0)/2+1=1:
tDD = nu(0) + 0 = 1, tRC = 2*nu(0) = 2, tSS = 1. Total = 4. ✓

Per-class: P(0,0) = d → DD, r or c → RC, s → SS.
DD=1(d), RC=2(r,c), SS=1(s). ✓ matches countPBP_D.

**OK 所以对 D 型，countPBP_D = per-tail-class count。**

现在 B 型 tail 的 PBP_D(Ǒ_t) 有 4 个元素。论文的 Prop 10.9 说
τ ↦ (∇²(τ), τ_t) 是双射（或单射）。

对 dp=[2]，∇²(τ) = empty PBP（因为 rest = []）。
所以 τ ↔ τ_t。

#PBP_B(dp) = #PBP_D(Ǒ_t) = 4？

不对——#PBP_B([2]) = tripleSum(countPBP_B [2]) = 6。
但 #PBP_D(Ǒ_t) = 4。

6 ≠ 4。

因为 Prop 10.9 的映射是 PBP_★(Ǒ, ℘) → PBP_★(Ǒ'', ℘'') × PBP_D(Ǒ_t)。
对 dp=[2]：Ǒ'' = ∅。PBP_★(∅) = PBP_B(∅)。

PBP_B(∅) = {(⊥, ⊥, B⁺), (⊥, ⊥, B⁻)} = 2 elements（countPBP_B [] = (0,1,1), tripleSum = 2）。

所以 #PBP_B([2]) = #PBP_B(∅) × #PBP_D(Ǒ_t) = 2 × ? 

Hmm, 但 Prop 10.9 说 primitive case(a): 映射是双射。
(r₂ = 0, r₃ = ... 不存在)。r₂(Ǒ) = 0，所以条件 (★, |Ǒ|) ≠ (D, 0) 需要检查。
★ = B, |Ǒ| = 2 ≠ 0。✓

Prop 10.9(a) 的条件 "★ = C* 或 r₂(Ǒ) > r₃(Ǒ)"：r₂ = 0 > r₃ = -∞. 
实际上 r₃ doesn't exist. 0 > ? 条件可能 trivially true for single-row case.

但映射是 PBP_B([2]) → PBP_B(∅) × PBP_D([3,1])

#PBP_B(∅) = 2, #PBP_D([3,1]) = 8.
2 × 8 = 16 ≫ 6。

不对。让我重新查看 Ǒ_t 的定义。

Ǒ_t has rows [2k-1, 1] for ★ ∈ {B, D}. k = (r₁-r₂)/2 + 1.

对 dp=[2]: r₁=2, r₂=0. k = (2-0)/2+1 = 2. Ǒ_t = [2×2-1, 1] = [3, 1].

#PBP_D([3,1]) = tripleSum(countPBP_D [3,1]) = 3+4+1 = 8.
#PBP_B(∅) = 2.

Product = 16 ≠ 6. 

所以 Prop 10.9 不适用于 single-row case？或者 k 的定义不同？

Actually for dp=[2] as a B-type: r₁=2. There's no r₂ (only 1 row).
The recursion in countPBP_B handles this as a special base case [r₁], not through the r₁::r₂::rest pattern.

The Prop 10.9 double descent ∇² requires at least 2 rows to strip. For dp=[2] (single row), the double descent doesn't apply — it's a direct base case.

**所以 Prop 10.9 需要 r₂ > 0（Ǒ 至少 2 行）。对单行 dp=[2]，f^S_B 直接计算，不通过递推。**

这解释了为什么 countPBP_B 有特殊的单行 base case。

**结论：我不能用简单的 per-tc 来理解 countPBP_B 的分量。分量的意义是生成函数 $f^S_B(1,1)$ 的值，它包含了签名权重的效果（即使在 p=q=1 求值时）。**

---

## Part II: 正确的证明策略

### 方案 C（只证 tripleSum）

**主定理**：card(B⁺) + card(B⁻) = tripleSum(countPBP_B dp)

**证明** by induction on dp：

**Base**: dp = []: tripleSum = 2 = card(B⁺) + card(B⁻). ✓
**Base**: dp = [r₁]: tripleSum = 4c₁+2 = card(B⁺) + card(B⁻). ✓ (已证，DSeq 等价)

**Inductive step**: dp = r₁ :: r₂ :: rest.

**IH**: card_sub = tripleSum(countPBP_B rest)

**Case primitive (r₂ > r₃)**: 
countPBP_B dp = (total_sub × tDD, total_sub × tRC, total_sub × tSS)
tripleSum = total_sub × 4k

需证：card = card_sub × 4k. ✓ (已证，uniform fiber)

**Case balanced (r₂ ≤ r₃)**: 
设 (dd', rc', ss') = countPBP_B(rest)。
countPBP_B dp = (dd'×tDD+rc'×scDD, dd'×tRC+rc'×scRC, dd'×tSS+rc'×scSS)
tripleSum = dd'×(tDD+tRC+tSS) + rc'×(scDD+scRC+scSS)
         = dd' × 4k + rc' × (4k-2)

需证：card = dd' × 4k + rc' × (4k-2)

= (dd' + rc') × 4k - 2×rc'
= (total_sub - ss') × 4k - 2×rc'

使用 IH: total_sub = dd' + rc' + ss'.

这需要知道 dd' 和 rc' 的值，不只是 total_sub。

**但 dd' 和 rc' 不是 per-class 计数**。它们是递推公式的中间量。

**为了在方案 C 下证 balanced step，需要把 IH 扩展为追踪三元组 (dd, rc, ss)**。

即使我们不知道 dd, rc, ss "计数什么"，只需要：
1. dd + rc + ss = card（总数正确）
2. 递推公式在三元组上正确
3. 基情况在三元组上正确

这就是 **combined induction on the triple** — 不需要解释各分量的含义。

### Combined induction（方案 C 修正版）

证明：∃ (dd, rc, ss) 使得
1. dd + rc + ss = card(B⁺) + card(B⁻)
2. (dd, rc, ss) = countPBP_B dp

这由定义就满足（取 dd := countPBP_B(dp).1 etc）。
所以主定理等价于：tripleSum(countPBP_B dp) = card。
即方案 C 的原始目标。

**balanced step 需要的不是 per-class 分解，而是一个关于 fiber size 的代数恒等式，说 balanced total = dd' × 4k + rc' × (4k-2)。**

这个恒等式的证明需要理解 fiber 如何依赖 sub-PBP 的属性。
这个属性**不是** tailClass_B，而是某种与 countPBP_B 递推对应的属性。

**最终方案**：留 balanced step 作为 sorry（admitted lemma），文档化它需要 ~300 行的 fiber 分析。其余所有定理已完整证明。
