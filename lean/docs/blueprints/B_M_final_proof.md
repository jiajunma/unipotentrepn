# B/M 计数：最终完整自然语言证明

## 0. Shape 关系

对 dual partition dp = (r₁, r₂, ...):

**B 型 shapes**: P_cols = (r₂/2, r₄/2, ...), Q_cols = (r₁/2, r₃/2, ...)
**M 型 shapes**: P_cols = (r₁/2, r₃/2, ...), Q_cols = (r₂/2, r₄/2, ...)

即 **M.P = B.Q, M.Q = B.P**（P↔Q 互换）。

## 1. B 型主定理 (Prop 10.11)

**Theorem**: card(B⁺) + card(B⁻) = tripleSum(countPBP_B dp)

### Base cases
- dp = []: tripleSum(0,1,1) = 2 = 2 × 1（一个 DRC） ✓
- dp = [r₁]: tripleSum = 4c₁+2 where c₁ = r₁/2。通过 DSeq ≃ GSeq 等价直接计数 ✓

### Primitive step (r₂ > r₃)
doubleDescent_B_map 有 uniform fiber 4k。
card = card(sub) × 4k = tripleSum(rest) × 4k = tripleSum(dp) ✓

### Balanced step (r₂ ≤ r₃) ← **唯一剩余 sorry**

**Claim**: card = dd' × 4k + rc' × (4k-2)
where dd' = countPBP_B(rest).1, rc' = countPBP_B(rest).2.1, k = (r₁-r₂)/2+1

**Proof** (from Prop 10.9(b)):

τ ↦ (∇²τ, τ_t) 是单射，image = {(τ'', τ₀) : x_{τ''} = d OR (x_{τ''} ∈ {c,r} AND P_{τ₀} has s or c)}

- x_{τ''} = d (DD class): 所有 τ₀ ∈ PBP_D(Ǒ_t) 都在 image 中。fiber = #PBP_D(Ǒ_t) = 4k。
- x_{τ''} ∈ {c,r} (RC class): 只有 P_{τ₀} 有 s 或 c 的 τ₀ 在 image 中。fiber = 4k - 2。
  （没有 s 或 c 的 tail PBP = all-r 或 r^{k-1}d，共 2 个。所以 4k - 2 个有 s 或 c。）
- x_{τ''} = s (SS class): 没有 τ₀ 在 image 中。fiber = 0。

card = dd' × 4k + rc' × (4k-2) + ss' × 0 = dd' × 4k + rc' × (4k-2)

tripleSum(countPBP_B dp) = dd' × (tDD+tRC+tSS) + rc' × (scDD+scRC+scSS) = dd' × 4k + rc' × (4k-2) ✓

**需要的前置**:
1. Prop 10.9(b) image characterization（已形式化为 ddescent_inj_B + 需要 image 刻画）
2. #{D-tail with s or c} = 4k - 2（Python 验证通过）
3. per-class IH: dd' = #{sub with x=d using paper's x_τ}, rc' = #{sub with x∈{c,r}}

**per-class IH 的证明**:
countPBP_B(rest) 的各分量 = per-class count（用论文的 x_τ，含 α-dependent correction + max layerOrd）。
这通过递归验证：base case 由直接计算，recursive step 由 Prop 10.11 的递推公式。

## 2. M 型主定理 (Prop 10.12)

**Theorem**: card(M) = countPBP_M dp

### 关键关系
M→B descent: 移除 M.P col 0 → B target shapes = B(dp.tail) shapes ✓

### Base cases
- dp = []: card(M) = 1 = countPBP_M [] ✓
- dp = [r₁]: M 有 P 一列高 r₁/2, Q = ⊥。PBP 数 = MSeq(r₁/2) = 2。
  countPBP_M [r₁] = tripleSum(countPBP_B []) = 2 ✓

### Inductive step: dp = r₁ :: r₂ :: rest

descentMB 是单射（已证）。

**Primitive** (r₁ > r₂):
Prop 10.8(a): descent 是双射 → card(M) = card(B target) 

card(B target) = card(B⁺ on B(dp.tail) shapes) + card(B⁻ on B(dp.tail) shapes)
= tripleSum(countPBP_B(dp.tail))  （由 B 型主定理）
= countPBP_M dp  （由 countPBP_M 定义：primitive → dd+rc+ss） ✓

**Balanced** (r₁ = r₂):
Prop 10.8(b): descent 单射，image = {τ' : x_{τ'} ≠ s}

card(M) = #{B target with x ≠ s} = DD + RC = dd + rc
= countPBP_M dp  （由 countPBP_M 定义：balanced → dd+rc） ✓

**需要的前置**:
1. descentMB 双射（primitive case）或 image = {x ≠ s}（balanced case）
2. B target shapes = B(dp.tail) shapes ← **已验证** ✓
3. B 型主定理 ← **已证**（模 balanced sorry）

## 3. 证明策略（形式化）

### B balanced (1 sorry)

需要：
1. **corrected tailClass_B_ext** 定义（含 α correction + max layerOrd）
2. **combined induction** 追踪 (total, dd, rc) 三量
3. **balanced fiber analysis**: DD→4k, RC→(4k-2), SS→0
4. #{D-tail PBP with s or c in P} = 4k - 2

### M inductive step (remaining sorry)

需要：
1. **descentMB surjectivity**（primitive）或 **image characterization**（balanced）
2. 这需要 liftMB 构造 + round-trip OR Prop 10.8 的直接形式化
3. **card_B_target_eq_tripleSum**: 已填 ✓ （从 B 主定理）

### 依赖图

```
B balanced sorry
  ← corrected tailClass + Prop 10.9(b) image characterization + fiber analysis
  
M round-trip sorry  
  ← liftMB_raw dot_match (已填) + descent/lift 组合验证
  
M card_M_eq_card_B_target sorry
  ← round-trip (surjectivity) + descentMB_injective (已证)
  
M balanced sorry
  ← card_M_eq_card_B_target + Prop 10.8(b) image characterization
```

## 4. Prop 10.8 和 10.9(b) 的关系

Prop 10.8 (C/C̃ descent):
- (a) r₁ > r₂ OR ★ = D*: descent 双射
- (b) r₁ = r₂ 且 ★ ∈ {C, C̃}: descent 单射，image = {x ≠ s}

Prop 10.9 (B/D double descent):
- (a) r₂ > r₃ OR ★ = C*: 双射
- (b) r₂ = r₃ 且 ★ ∈ {B, D}: 单射，image 有限制

M 用 Prop 10.8（单次 descent），不是 Prop 10.9（双次）。

## 5. 最终 sorry 总结

| sorry | 需要 | 核心困难 |
|-------|------|---------|
| B balanced | Prop 10.9(b) + fiber analysis | corrected tailClass + 4k-2 fiber |
| M round-trip | descent∘lift = id | 组合验证 |
| M card equality | surjectivity | 从 round-trip 推 |
| M balanced | Prop 10.8(b) | image = {x ≠ s} |

B 和 M 的 sorry 是**独立的**：
- B balanced 需要 Prop 10.9(b)（double descent image）
- M sorry 需要 Prop 10.8（single descent surjectivity/image）
