# 自然语言证明：B/M 型计数剩余定理

Reference: [BMSZb] Section 10, Propositions 10.11-10.12.

## 1. B 型 Lift 构造 (`extractCol0_B_surjective_on_fiber`)

### 1.1 目标

给定子 PBP σ ∈ PBPSet(.Bplus, shiftLeft μP, shiftLeft μQ) 和有效 col 0 数据 v ∈ ValidCol0_B，构造一个 PBP τ ∈ PBPSet(.Bplus, μP, μQ) 使得：
1. doubleDescent_Bplus_map(τ) = σ（τ 在 fiber 中）
2. extractCol0_B(τ) = v（提取恢复原数据）

### 1.2 构造

ValidCol0_B = DSeq(tail_len) ⊕ DSeq(tail_len + 1) 其中 tail_len = μQ.colLen(0) - μP.colLen(0)。

**情况 A**：v = inl(d)，d ∈ DSeq(tail_len)。P col 0 全为 dot。

定义 τ 的 paint 函数：
- **P paint**：
  - P(i, 0) = • (dot) 对所有 i < μP.colLen(0)
  - P(i, j+1) = σ.P.paint(i, j) 对所有 j ≥ 0
  - P(i, j) = • 对 (i,j) ∉ μP

- **Q paint**：
  - Q(i, 0) = • 对 i < μP.colLen(0)（dot 区域，与 P 的 dot_match 一致）
  - Q(i, 0) = d.val(i - μP.colLen(0)) 对 μP.colLen(0) ≤ i < μQ.colLen(0)（尾部）
  - Q(i, j+1) = σ.Q.paint(i, j) 对所有 j ≥ 0
  - Q(i, j) = • 对 (i,j) ∉ μQ

**情况 B**：v = inr(d)，d ∈ DSeq(tail_len + 1)。P col 0 底部有 c。

定义 τ 的 paint 函数：
- **P paint**：
  - P(i, 0) = • 对 i < μP.colLen(0) - 1
  - P(μP.colLen(0) - 1, 0) = c
  - P(i, j+1) = σ.P.paint(i, j)

- **Q paint**：
  - Q(i, 0) = • 对 i < μP.colLen(0) - 1（与 P 的 dot 区域一致）
  - Q(i, 0) = d.val(i - (μP.colLen(0) - 1)) 对 μP.colLen(0) - 1 ≤ i < μQ.colLen(0)
  - Q(i, j+1) = σ.Q.paint(i, j)

### 1.3 约束验证（13 项）

1. **sym_P**：B+ 的 P 允许 {•, c}。col 0 只有 • 和 c（情况 B）。cols ≥ 1 继承 σ 的 P（σ 是 B+ 类型，满足 sym_P）。✓

2. **sym_Q**：B+ 的 Q 允许 {•, s, r, d}。col 0 由 DSeq 填充，DSeq 元素 ∈ {s, r, d}。cols ≥ 1 继承 σ 的 Q。✓

3. **dot_match**：P(i,j) = • ⟺ Q(i,j) = •。
   - j = 0：dot 区域 P 和 Q 都是 •。尾部区域 P 是 •（情况 A）或 c（情况 B），Q 是 DSeq（非 dot）。需验证：
     - 情况 A：P col 0 全 dot，Q col 0 在 i < μP.colLen(0) 是 dot（✓），在 i ≥ μP.colLen(0) 是 DSeq 非 dot（P 在这些行不在 μP 中，所以 dot_match 不适用——(i,0) ∉ μP，只需 (i,0) ∈ μQ 时 Q 非 dot 无矛盾）。
     
     实际 dot_match 条件：(i,j) ∈ μP ∧ P(i,j) = • ⟺ (i,j) ∈ μQ ∧ Q(i,j) = •。
     
     - 对 i < μP.colLen(0)：(i,0) ∈ μP。情况 A：P(i,0) = •，需 (i,0) ∈ μQ ∧ Q(i,0) = •。由 hle（μP.colLen(0) ≤ μQ.colLen(0)），(i,0) ∈ μQ。Q(i,0) = • 因为 i < μP.colLen(0) 在 dot 区域。✓
     - 情况 B 对 i = μP.colLen(0) - 1：P(i,0) = c ≠ •，所以左→右不成立（无需验证）。右→左：如果 Q(i,0) = • 且 (i,0) ∈ μQ，需 P(i,0) = •。但 Q(i,0) = DSeq 值 ≠ •（因为 DSeq 尾部从这里开始）。✓
   - j ≥ 1：P(i,j) = σ.P(i,j-1)，Q(i,j) = σ.Q(i,j-1)。由 σ 的 dot_match 得。✓

4. **mono_P**：layerOrd 非递减（从左上到右下）。
   - col 0 内部：• 的 layerOrd = 0，c 的 layerOrd = 3。从上到下：dots 然后 c，单调。✓
   - col 0 → col 1：P(i,0) 的 layerOrd ≤ P(i,1) = σ.P(i,0) 的 layerOrd。
     - 情况 A：P(i,0) = •，layerOrd = 0 ≤ anything。✓
     - 情况 B：P(μP.colLen(0)-1, 0) = c，layerOrd = 3。需 σ.P(μP.colLen(0)-1, 0) 的 layerOrd ≥ 3。
       
       在 primitive 情况下：μP.colLen(0) - 1 ≥ μQ.colLen(0)（因为 shiftLeft μP 的 colLen(0) = μP.colLen(1) ≤ μQ.colLen(0) ← primitive 条件）。所以 σ.P 在这些行是 dot（outside shape），layerOrd = 0 < 3。矛盾！
       
       等等——这意味着情况 B（P col 0 有 c）在 primitive 情况可能不总是有效？
       
       让我重新分析。对于 B 型 primitive 情况：
       - r₂ > r₃ 意味着 μQ.colLen(1) ≥ μP.colLen(0) + 2（has23_B 条件）
       - shiftLeft μP 的 colLen(0) = μP.colLen(1)
       - shiftLeft μQ 的 colLen(0) = μQ.colLen(1)
       
       primitive 条件意味着 shiftLeft μQ 的 col 0 比 shiftLeft μP 的 col 0 长很多。
       
       但 μP.colLen(0) 与 shiftLeft 的关系是：μP.colLen(0) 是原始的，shiftLeft 的 colLen(0) = μP.colLen(1)。
       
       对于 B 型：μP.colLen(0) = r₂/2，μP.colLen(1) 是下一个偶数行。
       
       实际上，P col 0 有 c 的情况（情况 B）需要 μP.colLen(0) > 0。而在这个位置 σ.P(μP.colLen(0)-1, 0) 是否在 σ 的 shape 内取决于 μP.colLen(1)（= shiftLeft μP 的 colLen(0)）。
       
       如果 μP.colLen(0) - 1 < μP.colLen(1)（= shiftLeft μP.colLen(0)），那么 (μP.colLen(0)-1, 0) ∈ shiftLeft μP，所以 σ.P 在该位置有非 dot 值。由于 σ 是 B+ 类型，σ.P 只有 {•, c}，所以 σ.P(μP.colLen(0)-1, 0) ∈ {•, c}。如果是 c（layerOrd 3），mono 条件满足。如果是 •（layerOrd 0），则 c → • 违反 mono！
       
       这意味着情况 B 只在特定条件下有效。需要更仔细地分析 mono_P 约束。
       
       **关键发现**：B 型的 lift 比 D 型复杂，因为 P col 0 有 c 时，需要与 σ.P 的 col 0（= μP 的 col 1）的 paint 兼容。这不是在所有情况下都自动满足的。

       这与 D 型不同：D 型的 Q 全是 dot，所以 lift 只需填 P col 0，不与 Q 交互。B 型需要同时填 P col 0 和 Q col 0，且与 σ 的 cols ≥ 1 兼容。
       
       **解决方案**：LiftCondition（类似 D 型的）。在 primitive 情况下，P col 0 的 c 只出现在行 i，如果 σ.P(i, 0) 也是 c 或 layerOrd ≥ 3。这需要额外条件。
       
       实际上，回顾 D 型 lift：D 型 ValidCol0 允许 {s, r, c, d}，但 lift 需要 LiftCondition 确保 σ.P 在 tail 行没有 s/r（避免 row uniqueness 冲突）。B 型类似但 P 只有 {•, c}，限制更强。
       
       在 B 型 primitive 情况下：
       - tail 行 i ≥ μP.colLen(0) 在 σ.P 中是 outside shape → dot。所以 P(i, j+1) = dot 对 j ≥ 0。
       - P col 0 在这些行也是 dot（因为 i ≥ μP.colLen(0) 在 μP 之外）。
       - 所以情况 B（c at bottom of P col 0）的 c 在 i = μP.colLen(0) - 1，这在 μP 内。σ.P(μP.colLen(0)-1, 0) 可能是 c 或 dot。
       
       如果 σ.P(μP.colLen(0)-1, 0) = dot：则 P(μP.colLen(0)-1, 0) = c 但 P(μP.colLen(0)-1, 1) = dot（layerOrd 0），违反 mono_P（3 > 0）。
       
       所以情况 B 只在 σ.P 的对应位置也是 c（或 layerOrd ≥ 3）时有效。
       
       但等等——ValidCol0_B 被定义为 DSeq(tail_len) ⊕ DSeq(tail_len+1)，没有考虑这个 mono 约束。这意味着 **ValidCol0_B 的定义可能有问题**——它过度计数了。
       
       让我重新检查 fiber 的实际大小...

### 1.4 修正

回顾 B 型 fiber 的正确分析：

实际上，在 B 型中 P col 0 的情况是：
- P col 0 的非 dot 部分只有 c，且至多 1 个 c
- c 必须在最底部（mono 约束）
- c 在 P col 0 的行 i 处时，需要 P(i, j) 对 j ≥ 1 有 layerOrd ≥ 3

在 **primitive 情况下**：
- 行 i = μP.colLen(0) - 1
- σ.P(i, 0) = σ.P.paint(μP.colLen(0)-1, 0)
- 如果 i ≥ shiftLeft(μP).colLen(0) = μP.colLen(1)：σ.P 在该行 outside shape，paint = dot。此时 c → dot 违反 mono。
- 如果 i < μP.colLen(1)：σ.P 在 shape 内，可能是 c 或 dot。

所以 ValidCol0_B 的 inr 分支（P col 0 有 c）只在 μP.colLen(0) - 1 < μP.colLen(1) 时有效。即 μP.colLen(0) ≤ μP.colLen(1)。

由 Young diagram 反单调性，μP.colLen(0) ≥ μP.colLen(1)。所以 μP.colLen(0) ≤ μP.colLen(1) ⟹ μP.colLen(0) = μP.colLen(1)。

这意味着情况 B 只在 "balanced" 情况下有效！在 primitive 情况下 μP.colLen(0) > μP.colLen(1)，所以情况 B **不存在**，ValidCol0_B 退化为只有 inl 分支 = DSeq(tail_len)。

但这与 fiber 大小 4k 矛盾——DSeq(tail_len) 只有 2·tail_len+1 个元素，不是 4k = 4(tail_len+1)。

**需要重新分析 fiber 结构。**

等等，让我重新检查。对于 B 型 double descent，fiber 不只是 (P col 0, Q col 0)。double descent B→M→B 去掉了 P 和 Q 各一列。所以 fiber 实际上是同时恢复 **P col 0 和 Q col 0** 的所有有效方式。

D 型中：Q 全是 dot，所以 Q col 0 自动确定（全 dot），fiber = P col 0 的有效 paint = ValidCol0。

B 型中：P 有 {•, c}，Q 有 {•, s, r, d}。P col 0 和 Q col 0 通过 dot_match 耦合。

正确的 fiber 分析：

**P col 0 的选择：**
- 选择 1：全 dot
- 选择 2：dot + 底部有 c（但只在 mono 兼容时）

**Q col 0 的选择（给定 P col 0）：**
- dot_match：Q(i,0) = • ⟺ P(i,0) = •
- Q 的非 dot 区域从 P 的第一个非 dot 行开始（或从 μP.colLen(0) 开始如果 P 全 dot）
- Q 非 dot 区域填 DSeq

所以：
- P 全 dot（选择 1）：Q 的 dot 区域 = [0, μP.colLen(0))，tail = [μP.colLen(0), μQ.colLen(0))，长度 = tail_len。DSeq 选择 = 2·tail_len + 1。
- P 有 c 在底（选择 2）：Q 的 dot 区域 = [0, μP.colLen(0)-1)，tail = [μP.colLen(0)-1, μQ.colLen(0))，长度 = tail_len + 1。DSeq 选择 = 2·(tail_len+1) + 1 = 2·tail_len + 3。

总 fiber = (2·tail_len + 1) + (2·tail_len + 3) = 4·tail_len + 4 = 4·(tail_len + 1) = 4k。✓

但选择 2 需要 mono 兼容性。让我更仔细地检查...

在 primitive 情况下，μP.colLen(0) > μP.colLen(1)。P 在行 μP.colLen(0)-1 处有 c。σ.P 在行 μP.colLen(0)-1 处的 col 0（= 原始的 col 1）的 paint：

如果 μP.colLen(0) - 1 ≥ μP.colLen(1)（primitive 情况下成立，因为 μP.colLen(0) > μP.colLen(1)），那么 (μP.colLen(0)-1, 1) ∉ μP。所以 σ.P(μP.colLen(0)-1, 0) 实际上是原始 P(μP.colLen(0)-1, 1)，它 ∉ μP 的 shape（因为 col 1 的长度 = μP.colLen(1) ≤ μP.colLen(0) - 1）。

等等，这里有混淆。让我重新理清 lift paint 的定义。

τ.P.paint(i, j) = 
  if j = 0 then col0_paint(i)
  else σ.P.paint(i, j-1)  -- = 原始 P 的 col j 的 paint

σ 是 shiftLeft 后的 PBP，所以 σ.P.paint(i, j) 对应原始 τ 的 P.paint(i, j+1)。

mono_P 要求：对 i₁ ≤ i₂ 且 j₁ ≤ j₂ 且 (i₂, j₂) ∈ μP：
  τ.P.paint(i₁, j₁).layerOrd ≤ τ.P.paint(i₂, j₂).layerOrd

关键情况：j₁ = 0, j₂ = 1。即 col0_paint(i₁).layerOrd ≤ σ.P.paint(i₂, 0).layerOrd。

如果 col0_paint(i₁) = c (layerOrd 3) 且 (i₂, 1) ∈ μP：
需要 σ.P.paint(i₂, 0).layerOrd ≥ 3。

σ.P.paint(i₂, 0) 是 σ 的 P 在 (i₂, 0) 处的 paint。σ 的 P shape = shiftLeft(μP)，所以 (i₂, 0) ∈ shiftLeft(μP) ⟺ (i₂, 1) ∈ μP。

如果 (i₂, 1) ∈ μP，则 (i₂, 0) ∈ σ.P.shape。σ.P 是 B+ 类型，所以 σ.P.paint(i₂, 0) ∈ {•, c}。

- 如果 σ.P.paint(i₂, 0) = c (layerOrd 3)：3 ≥ 3 ✓
- 如果 σ.P.paint(i₂, 0) = • (layerOrd 0)：0 < 3 ✗ mono 违反！

所以情况 B（P col 0 有 c 在底）只在 σ.P 在对应位置也是 c 时有效。

但在 primitive 情况下，i₁ = μP.colLen(0) - 1 且 i₂ ≥ i₁。(i₂, 1) ∈ μP 要求 i₂ < μP.colLen(1)。而 i₁ = μP.colLen(0) - 1 ≥ μP.colLen(1)（primitive: μP.colLen(0) > μP.colLen(1)）。所以 i₂ ≥ i₁ ≥ μP.colLen(1) > (μP.colLen(1) - 1)，故 i₂ ≥ μP.colLen(1)，(i₂, 1) ∉ μP。

这意味着在 primitive 情况下，(i₂, 1) ∉ μP 对所有 i₂ ≥ μP.colLen(0) - 1。所以 mono_P 的 j₁=0, j₂≥1 情况中 (i₂, j₂) ∉ μP，约束空成立！

**结论**：在 primitive 情况下，情况 B（P col 0 有 c）是合法的！mono_P 约束空成立因为没有 (i₂, j₂ ≥ 1) ∈ μP 且 i₂ ≥ μP.colLen(0) - 1。

这是因为 primitive 意味着 μP 的 col 1 比 col 0 短至少 2（μP.colLen(1) ≤ μP.colLen(0) - 2），所以行 μP.colLen(0) - 1 在 col 1 之外。

所以 ValidCol0_B = DSeq(tail_len) ⊕ DSeq(tail_len+1) 确实是正确的 fiber 大小，至少在 primitive 情况下。

### 1.5 Lift 构造的完整验证（primitive 情况）

以下逐项验证 13 个 PBP 约束：

设 hP = μP.colLen(0), hQ = μQ.colLen(0), k = hQ - hP + 1。

**情况 A**（P col 0 全 dot，v = inl d，d ∈ DSeq(hQ - hP)）：

P paint: P(i, 0) = • 对 i < hP; P(i, j+1) = σ.P(i, j)
Q paint: Q(i, 0) = • 对 i < hP; Q(i, 0) = d(i - hP) 对 hP ≤ i < hQ; Q(i, j+1) = σ.Q(i, j)

1. **sym_P**: P col 0 = •, cols ≥ 1 继承 σ。B+ P 允许 {•, c}。✓
2. **sym_Q**: Q col 0 = • 或 DSeq(∈ {s,r,d})。B+ Q 允许 {•,s,r,d}。✓
3. **dot_match**: 
   - j = 0: P(i,0) = • ⟺ i < hP ⟺ Q(i,0) = •（因为 Q 在 i < hP 也是 dot，i ≥ hP 时 P ∉ μP）。✓
   - j ≥ 1: 继承 σ 的 dot_match。✓
4. **mono_P**: col 0 全 dot (layerOrd 0)。col0 → col1: 0 ≤ anything。cols ≥ 1 继承 σ。✓
5. **mono_Q**: 
   - col 0 内部: • (0) → DSeq values。DSeq 单调 (layerOrd non-decreasing)。✓
   - col 0 → col 1: Q(i,0) 对 i < hP 是 •，Q(i,1) = σ.Q(i,0)。如果 σ.Q(i,0) 是 • 则 0 ≤ 0 ✓。如果非 dot 则 0 ≤ anything ✓。
   - 对 i ≥ hP: Q(i,0) = DSeq value, Q(i,1) = σ.Q(i,0)。primitive 情况下 (i,1) ∉ μQ（因为 hQ.colLen(1) ≤ hP），所以 σ.Q(i,0) = dot，约束 vacuous ((i,1) ∉ μQ)。✓
6. **row_s**: col 0 的 s 只在 Q tail 中。cols ≥ 1 中的 s 只在 σ 中。因为 s 在 Q col 0 的 tail (i ≥ hP) 且 σ.Q 在这些行是 outside shape，不会有 col ≥ 1 的 s 在同一行。✓
7. **row_r**: 类似 row_s。✓
8. **col_c_P**: P col 0 无 c（情况 A）。cols ≥ 1 继承 σ 的 col_c_P。✓
9. **col_c_Q**: Q 没有 c（B 型 Q 不允许 c）。✓
10. **col_d_P**: P 没有 d（B 型 P 不允许 d）。✓
11. **col_d_Q**: Q col 0 有至多 1 个 d（DSeq 约束）。cols ≥ 1 继承 σ 的 col_d_Q。需要 Q col 0 的 d 和 cols ≥ 1 的 d 不在同一列——但它们在不同列（col 0 vs col ≥ 1），所以 col_d_Q 对 col 0 和 cols ≥ 1 分别满足。✓

**情况 B**（P col 0 底有 c，v = inr d，d ∈ DSeq(hQ - hP + 1)）：

P paint: P(i, 0) = • 对 i < hP - 1; P(hP - 1, 0) = c; P(i, j+1) = σ.P(i, j)
Q paint: Q(i, 0) = • 对 i < hP - 1; Q(i, 0) = d(i - (hP-1)) 对 hP-1 ≤ i < hQ; Q(i, j+1) = σ.Q(i, j)

验证同上，关键差异：
4. **mono_P**: P(hP-1, 0) = c (layerOrd 3)。需 P(i₂, j₂).layerOrd ≥ 3 对 i₂ ≥ hP-1, j₂ ≥ 1, (i₂,j₂) ∈ μP。但 primitive 情况下 hP-1 ≥ μP.colLen(1)，所以 (i₂, j₂ ≥ 1) ∉ μP。约束 vacuous。✓
8. **col_c_P**: P col 0 有恰好 1 个 c。cols ≥ 1 可能也有 c。但 col_c_P 约束是每列至多 1 个 c，这里 col 0 有 1 个，cols ≥ 1 继承 σ 的约束。✓

### 1.6 Round-trip 验证

**doubleDescent_Bplus_map(τ) = σ**：
- double descent 去掉 P col 0 和 Q col 0，重新分配 dot/s。结果应该是 σ。
- 具体：doubleDescent 的 P paint = B→M→B 的 double descent paint。
- 由构造：τ.P(i, j+1) = σ.P(i, j) 和 τ.Q(i, j+1) = σ.Q(i, j)。double descent 恢复 cols ≥ 1 → 得到 σ。✓（需要形式化验证 doubleDescent_B_paintL/R 的具体公式）

**extractCol0_B(τ) = v**：
- extractCol0_B 检查 P_col0_has_c 然后提取 Q tail 为 DSeq。
- 情况 A：P col 0 无 c → inl 分支。提取 Q tail 从 hP 开始 → 得到 d。✓
- 情况 B：P col 0 有 c → inr 分支。提取 Q tail 从 hP-1 开始 → 得到 d。✓

## 2. B 型 Balanced Case

### 2.1 目标

在 balanced 情况（r₂ = r₃）下证明：
```
card(B+ + B-) = dd'·tDD + rc'·scDD + dd'·tRC + rc'·scRC + dd'·tSS + rc'·scSS
```

### 2.2 证明思路

Balanced 情况需要 per-tail-class 分解。这与 D 型的 `card_PBPSet_D_balanced_step`（LiftRC.lean）完全类似：

1. 将 PBPSet 按 tail class 分类：DD, RC, SS
2. DD class fiber = tDD（完整 ValidCol0）
3. RC class fiber = scRC（受限 ValidCol0）
4. SS class fiber = 0（lift 不存在）
5. 组装得到 matrix multiply

这需要 ~250 行的 per-tail-class fiber 分析。与 D 型的区别：
- D 型 tail 在 P col 0，B 型在 Q col 0
- D 型 Q 全 dot，B 型 P 和 Q 都有非平凡 paint
- 但基本论证结构相同

### 2.3 Balanced 情况的关键：SS class fiber = 0

当 sub-PBP σ 的 tail class = SS（tail symbol = s 或 tail 为空）时：
- 在 balanced 情况下，shiftLeft μP 的 colLen(0) = μQ.colLen(0) + 1
- σ.P.paint(μQ.colLen(0), 0) = s（从 SS class 定义）
- Lift 时 P col 0 要填 c 在某行 i₂ ≤ μQ.colLen(0)
- 但 σ.P(μQ.colLen(0), 0) = s (layerOrd 1)
- mono_P 需要 c (layerOrd 3) ≤ s (layerOrd 1)，矛盾
- 所以没有有效的 lift → fiber = 0

## 3. M 型 Descent 单射 (`descentMB_injective`)

### 3.1 目标

M→B descent 是单射：如果 descentMB_PBP(τ₁) = descentMB_PBP(τ₂)，则 τ₁ = τ₂。

### 3.2 证明

M→B descent 去掉 P col 0（对 M 型）。P cols ≥ 1 和 Q 完全保留在 descent 结果中（经过 dot/s 重分配）。

从 descent 结果可以恢复：
1. P cols ≥ 1（直接从 descent P paint 恢复）
2. Q 完全（descent 保留 Q）

剩余：P col 0 需要从 (signature, epsilon) + cols ≥ 1 恢复。

M 型 P 有符号 {•, s, c}。P col 0 由以下确定：
- dot 区域：由 dot_match 与 Q 确定
- 非 dot 区域：{s, c}，由 mono 约束和 (p, q, ε) 确定

具体：单射性从以下推导：
1. descent 结果相同 → P cols ≥ 1 和 Q 相同（descent recovery）
2. (p, q, ε) 从 descent 结果唯一确定（因为 descent 保留 signature）
3. P col 0 由 cols ≥ 1 + (p, q, ε) + Q 唯一确定（类似 descent_inj_col0_D）

这与 C→D 的 `descentCD_injective` 完全类似。

### 3.3 需要的前提

- `descentMB_PBP` 的具体构造（当前 sorry）
- descent recovery 引理（从 descent 结果恢复 P cols ≥ 1 和 Q）

## 4. M 型主定理 Inductive Step

### 4.1 Primitive 情况（r₁ > r₂）

M→B descent 满射。所以：
```
card(PBPSet .M μP μQ) = card(PBPSet .Bplus target_μP target_μQ) + card(PBPSet .Bminus target_μP target_μQ)
                      = tripleSum(countPBP_B dp.tail)
                      = countPBP_M dp
```

### 4.2 Balanced 情况（r₁ = r₂）

M→B descent 的 image 排除 SS class。所以：
```
card(PBPSet .M μP μQ) = DD + RC (from countPBP_B dp.tail, excluding SS)
                      = countPBP_M dp
```
