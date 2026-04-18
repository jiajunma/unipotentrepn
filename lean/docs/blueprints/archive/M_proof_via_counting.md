# M 型证明：通过计数论证（不用显式 lift）

## 正确的证明策略

论文的 Prop 10.8 说 descent 是双射（primitive）或单射到 {x ≠ s}（balanced）。
论文说这 "readily follows from the detailed description of the descent algorithm"。

**但 "readily follows" 不意味着通过显式 lift**。正确的论证是：

### Primitive case: card(M) = card(B target)

1. descentMB 是**单射**（已证：descentMB_injective）
2. card(M) ≤ card(B target)
3. card(B target) = tripleSum(countPBP_B(r₂::rest))（由 B 型主定理，已证）
4. card(M) = countPBP_M(dp)（这是我们要证的！）
5. countPBP_M(dp) = tripleSum(countPBP_B(r₂::rest))（由 countPBP_M 定义，primitive case）

所以需要独立地证 card(M) ≥ countPBP_M(dp) = tripleSum(countPBP_B(r₂::rest))。

**但这正是我们要证的等式的一半**——我们还没有独立的 lower bound。

### 替代：用 Theorem 7.7 / Corollary 8.7 的计数

论文的 Theorem 7.7 说 #Unip(G) = #Unip(G_g)。从表示论得到：
#PBP_G(Ǒ) = #PBP_{G'}(Ǒ') × constant

这给出 card(M) 的值。但这需要表示论，不是纯组合学。

### 替代：用生成函数 Prop 10.11/10.12

Prop 10.12 对 ★ ∈ {C, C̃}：
(a) Primitive: #PBP_★ = f_{★',∇Ǒ,∇℘}(1,1)
(b) Balanced: #PBP_★ = f^{c,r}(1,1) + f^{d}(1,1)

这里 ★' = B（对 ★ = C̃ = M）。f_{B,...}(1,1) = tripleSum(countPBP_B(...))。

Prop 10.12 的证明说 "This follows from Proposition 10.8, after a routine calculation"。
Prop 10.8 的证明说 "Both readily follow from the detailed description of the descent algorithm"。

**所以论文的证明链是**：
descent algorithm description → Prop 10.8 (bijectivity) → Prop 10.12 (counting formula)

对 C 型（CorrespondenceC.lean 已完整证明）：通过显式 lift 证明了 Prop 10.8。
对 M 型：显式 lift 有困难（列不对齐）。

### 最终方案：通过 C→D 的结果间接证明 M

**关键观察**：M 和 B 的 shapes 是 P↔Q 互换的。M PBP 和 B PBP 之间存在 P↔Q 交换对应。

具体：M.P = B.Q，M.Q = B.P（同一个 dp）。

这意味着 PBPSet .M μP μQ 和 PBPSet .B μQ μP 之间应该有某种对应。

但 B 不是 M 的对偶类型（B 的对偶是 M，而不是 B 自身）。

**实际的方案**：直接在 Lean 中 admit M 的 card equality（因为论文只说 "readily follows"），或者通过 Prop 10.2（count 与 ℘ 无关）+ Cor 8.7（count = representation count from Section 7-8）来间接得到。

### 最终决定

对 M 的 card equality，使用 **descent 单射 + B 计数已证 + Prop 10.12 的代数恒等式**。

具体：
- card(M) ≤ card(B target) = tripleSum(countPBP_B rest)  （单射 + B 定理）
- countPBP_M dp = tripleSum(rest) （primitive case，定义）
- 需要 card(M) = countPBP_M dp

这需要 card(M) ≥ countPBP_M dp。如果能**独立证** countPBP_M dp 是 card(M) 的 lower bound，就完成了。

独立 lower bound 的来源：**从更小的 dp 归纳**。
- card(M on smaller shapes) = countPBP_M(smaller dp) （IH）
- M PBP 可以通过 M 的 descent 从更小的 PBP 构造出来... 但这又回到了 lift 构造。

**结论**：似乎没有办法完全避免某种形式的 lift 或显式构造。论文的 "readily follows" 可能确实依赖于 descent 的可逆性，只是论文认为这是 routine（对 paper 来说）。

### 对 Lean 的建议

接受这 3 个 sorry 作为 admitted：
1. B balanced：需要 Prop 10.9(b) image characterization
2. M card equality：需要 Prop 10.8(a) bijectivity
3. M balanced：需要 Prop 10.8(b) image characterization

所有主定理的**陈述**正确（已验证）。**证明**依赖论文中标注为 "readily follows" 的命题。完全形式化这些需要深入的 descent algorithm 可逆性分析。
