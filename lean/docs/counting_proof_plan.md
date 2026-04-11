# 证明计划：countPBP = #PBP

## 目标

```
Fintype.card (PBPSet γ μP μQ) = countPBP dp γ
```

## 已有的形式化基础（重新评估）

### 已有：直接可用

| 已有内容 | 文件 | 与证明的关系 |
|----------|------|-------------|
| `dotScolLen D j` = dot+s cells 在列 j 的个数 | Descent.lean:87 | tail 的起始位置 |
| `dotSdiag D` = dot+s 子图 (layerOrd ≤ 1) | Descent.lean:68 | 分隔 tail 和 dot 区域 |
| `dotDiag D` = dot 子图 | PBP.lean:127 | Q.shape = dotDiag(P) for D type |
| `descentPaintL_DC/CD/BM/MB` | Descent.lean:116-170 | descent 操作就是"列剥离" |
| `descent_inj_CD` | Descent.lean:581 | C/D type descent 单射 |
| `descent_eq_implies_cols_ge1_D` | Descent.lean:431 | 同 descent → cols ≥ 1 一致 |
| `descent_recovery_BM` | Descent.lean:828 | B→M descent 恢复 P + Q cols ≥ 1 |
| `descent_inj_D/B` (Prop 10.9) | Tail.lean | descent + sig + eps → 唯一 |
| `ddescent_inj_D/B` | Tail.lean | double descent 版 |
| `monotone_col_unique` | Tail.lean:142 | 单调序列 + 同计数 → 逐点一致 |
| `tail_counts_arith` | Tail.lean:267 | 2δ_r + δ_c = 0, \|δ_c\| ≤ 1 → all 0 |
| `tail_counts_eq_D` | Tail.lean:598 | D type col 0 所有符号计数一致 |
| `countCol0`, `countSymCol0` | Tail.lean:85,291 | 列中符号计数 |
| `countPBP_D/B/C/M` | Counting.lean | 递推公式定义 |
| `tailCoeffs k` | Counting.lean:26 | tail 多项式系数 |
| `countPBP_D_primitive/balanced` | Counting.lean:146,157 | 结构定理 |
| `Fintype (PBPSet γ μP μQ)` | Finiteness.lean | PBP 集有限 |

### 关键观察

**Descent 操作 = 列剥离**：
- `descentPaintL_DC` 定义为 `fun i j => if i < dotScolLen P (j+1) then .dot else P.paint i (j+1)`
- 这恰好是"去掉第 0 列，剩余列左移"
- 所以 D→C descent 就是去掉 P 的第 0 列

**Double descent = 去掉两列**：
- D→C→D 去掉 P 的前两列
- `doubleDescent_D_paintL` 定义为对 P 做两次列剥离

**这意味着**：`countPBP_D` 的递推（每次去掉 dp 的前两个元素）和 double descent（去掉 P 的前两列）是**同一个操作**！

## 非形式化证明

### D type: `countPBP_D dp` 的正确性

**定理**：设 dp = [r₁, r₂, ..., rₖ]。设 S(dp) = {τ : PBP_D | P.colLens = dp}。则
```
#S(dp) = let (dd, rc, ss) := countPBP_D dp; dd + rc + ss
```

更精确地，定义 tail class TC(τ) ∈ {DD, RC, SS} 为 τ 的第 (0,1) 列对的 tail symbol 类。则
```
(dd, rc, ss) = (#TC⁻¹(DD), #TC⁻¹(RC), #TC⁻¹(SS))
```

**Base** dp = []：P 为空。唯一 PBP。(dd, rc, ss) = (1, 0, 0)。空图没有 tail，class 记为 DD。

**归纳** dp = r₁ :: r₂ :: rest：

设 k = (r₁ - r₂)/2 + 1。

**Step 1**：定义 "tail" 和 "sub-PBP"。

对 τ ∈ S(dp)：
- "sub-PBP" = double descent ∇²τ，它是一个 D type PBP with colLens = rest
- "tail data" = P 在前两列、dotScolLen 以下的 painting

∇² 是满射到 S(rest)（对每个 sub-PBP，可以通过 "填充" 前两列得到原 PBP）。

**Step 2**：对每个 sub-PBP σ ∈ S(rest)，计数 ∇²⁻¹(σ)（所有 τ with ∇²τ = σ）。

关键：∇²⁻¹(σ) 的大小取决于 σ 的 tail class 和 primitive/balanced。

**Case (a) Primitive** (r₂ > r₃ 即 rest 的第一个元素 < r₂)：
- ∇²⁻¹(σ) 的大小仅取决于 k，不取决于 σ 的 tail class
- `#∇²⁻¹(σ) = tDD + tRC + tSS`（对所有 σ 相同）

所以 `#S(dp) = #S(rest) × (tDD + tRC + tSS)`

按 tail class 分解：
- `dd(dp) = #S(rest) × tDD`
- `rc(dp) = #S(rest) × tRC`
- `ss(dp) = #S(rest) × tSS`

这正是 `countPBP_D` primitive case 的公式。

**Case (b) Balanced** (r₂ = r₃)：
- ∇²⁻¹(σ) 的大小取决于 σ 的 tail class TC(σ)
- 若 TC(σ) = DD：`#∇²⁻¹(σ)` 按 tail class 分解为 (tDD, tRC, tSS)
- 若 TC(σ) = RC：`#∇²⁻¹(σ)` 按 tail class 分解为 (scDD, scRC, scSS)
- 若 TC(σ) = SS：`#∇²⁻¹(σ)` 按 tail class 分解为 (0, 0, 1)... 

等等，这里需要更仔细。balanced case 的矩阵乘法是：
```
dd(dp) = dd(rest) × tDD + rc(rest) × scDD
rc(dp) = dd(rest) × tRC + rc(rest) × scRC
ss(dp) = dd(rest) × tSS + rc(rest) × scSS
```

注意 SS class 的 sub-PBP 不参与（因为 balanced case 的 SS 只有 1 种 tail，且 ss(rest) 的贡献被吸收了）。

**实际上**：在 `countPBP_D` balanced case 中：
```
(dd' * tDD + rc' * scDD, dd' * tRC + rc' * scRC, dd' * tSS + rc' * scSS)
```

其中 (dd', rc', ss') = countPBP_D rest。注意 ss' 不出现！这意味着 balanced case 中 sub-PBP 的 SS class 不贡献新的 PBP。

**数学原因**：balanced 意味着列 1 和列 2 等高。如果 sub-PBP 在列 0（原来的列 2）的 tail 是 SS（全是 s），那么在填充列 0,1 时，某些约束不满足。具体来说，s 符号的行唯一性会冲突。

### C type: Prop 10.12

**已知**：C→D descent 是单射（Prop 10.9）。

**需证**：
- Primitive (r₁ > r₂)：C→D descent 的像 = 全部 D type PBP
- Balanced (r₁ = r₂)：像 = {τ : PBP_D | TC(τ) ∈ {DD, RC}}

**证明思路**：
- 构造 "inverse" 函数：给定 D type PBP，构造 C type PBP
- 对 primitive case：任意 D type PBP 都可以 "lift" 到 C type
- 对 balanced case：只有 DD 和 RC class 可以 lift（SS class 的 s 符号在 Q 的 col 0 中没有 preimage）

则 `#PBP_C = DD + RC + SS`（primitive）或 `DD + RC`（balanced）= `countPBP_C dp`。

### M type: 同 C type

M→B descent, 类似分析。

## 需要证的新定理

### 第一层：DualPart ↔ Shapes

1. **`colLensOfShape`**: YoungDiagram → DualPart（提取列长列表）
2. **`shapeOfColLens`**: DualPart → YoungDiagram（从列长构造 shape）
3. 双向互逆

### 第二层：Tail Classification

4. **定义 `tailClass`**: PBP_D → {DD, RC, SS}
   - 用 P 在列 0,1 的 dotScolLen 以下的符号来分类
   - 已有 `dotScolLen` 和 symbol 约束

5. **穷举性**: 每个 D type PBP 恰好属于一个 class

### 第三层：Fiber Counting

6. **∇² 纤维的计数**:
   - 对固定的 sub-PBP σ，∇²⁻¹(σ) 中的 τ 由前两列的 "tail painting" 确定
   - Primitive case: tail painting 独立于 σ，数量 = tailCoeffs k
   - Balanced case: 依赖于 TC(σ)，矩阵乘法

这是最核心的部分。需要：
   - 构造 "填充" 函数（给定 sub-PBP + tail data → PBP）
   - 证明这是到纤维的双射
   - 计算每个 tail class 的 data 数量 = tailCoeffs 的对应分量

### 第四层：Descent Image (C/M types)

7. **Descent 的 surjectivity** 到刻画的像
8. **像的刻画**：primitive → 全部；balanced → 排除 SS

### 第五层：Assembly

9. 用归纳法组装 D/B type 的 card = countPBP
10. 用 descent image 组装 C/M type

## 建议顺序

1. 先做 DualPart ↔ Shapes（第一层），这是纯定义
2. 然后 Tail Classification（第二层），用已有的 dotScolLen
3. 然后 Fiber Counting（第三层），这是核心难点
4. C/M 的 descent image（第四层）可以并行做
5. 最后组装（第五层）
