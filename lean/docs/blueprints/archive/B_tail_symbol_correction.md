# B 型 Tail Symbol 修正

## 问题

当前 `tailClass_B` 只看 Q col 0 的底部 cell，但论文的 x_τ 对 B⁺ 和 B⁻ 有不同定义。

## 论文定义 ([BMSZb] Section 10.5, p.70-71)

对 ★ = B，τ = (ι, P) × (j, Q) × γ，设 c₁ := c₁(ι) = P.colLen(0)，c₁(j) = Q.colLen(0)。

tail 多重集 {x₁, ..., xₖ}（k = (r₁-r₂)/2 + 1）定义为：

**Set A** = {Q(i, 0) | c₁ + 1 ≤ i ≤ c₁(j)} （Q col 0 的 tail 部分）
大小 = c₁(j) - c₁ 个元素

**Correction** 添加 1 个元素 x₁：
- 如果 α = B⁺ 且（c₁ = 0 或 Q(c₁, 0) ∈ {•, s}）：x₁ = **c**
- 如果 α = B⁻ 且（c₁ = 0 或 Q(c₁, 0) ∈ {•, s}）：x₁ = **s**
- 否则：x₁ = Q(c₁, 0)（即 r 或 d）

所以 **x_τ = xₖ**（多重集的最后一个元素）：
- 如果 k > 1（Set A 非空）：x_τ = Q(c₁(j), 0) = Q col 0 的最底部（与 γ 无关）
- 如果 k = 1（Set A 为空）：x_τ = x₁ = correction element（**依赖 γ**）

## 正确的 tailClass_B

需要区分 γ：

```
def tailClass_B_correct (τ : PBP) : TailClass :=
  let c1P := τ.P.shape.colLen 0
  let c1Q := τ.Q.shape.colLen 0
  let setA_size := c1Q - c1P  -- = k - 1
  if c1Q ≤ c1P then .SS  -- no tail
  else if setA_size > 0 then
    -- k > 1: x_τ = Q bottom cell (与 γ 无关)
    match τ.Q.paint (c1Q - 1) 0 with
    | .d => .DD | .r | .c => .RC | .s | .dot => .SS
  else
    -- k = 1: x_τ depends on γ via correction
    let q_at_c1 := τ.Q.paint c1P 0  -- Q(c₁(ι), 0)
    if q_at_c1 = .dot ∨ q_at_c1 = .s then
      -- Correction: B⁺ → c (RC class), B⁻ → s (SS class)
      match τ.γ with
      | .Bplus => .RC
      | .Bminus => .SS
      | _ => .SS
    else
      -- q_at_c1 ∈ {r, d}: use directly
      match q_at_c1 with
      | .d => .DD | .r | .c => .RC | _ => .SS
```

## 验证

dp = (4, 4)（balanced，k = 1 = (4-4)/2+1）：
- DRC `c|d`：Q(c₁, 0) = d → DD（γ 无关）。✓
- DRC `c|r`：Q(c₁, 0) = r → RC（γ 无关）。✓
- DRC `c|s`：Q(c₁, 0) = s → correction。B⁺ → RC，B⁻ → SS。✓
- DRC `.|.`：c₁(ι) = 0, Q(0, 0) = dot → correction。B⁺ → RC，B⁻ → SS。✓

实际分布：
- DD: B⁺=1, B⁻=1, total=2 ✓ (countPBP_B.DD = 2)
- RC: B⁺=3, B⁻=1, total=4 ✓ (countPBP_B.RC = 4)
- SS: B⁺=0, B⁻=2, total=2 ✓ (countPBP_B.SS = 2)

dp = (2,)（singleton，k = 2/2+1 = 2, setA_size = 1 > 0）：
- 对所有 tail symbol：使用 Q 底部 cell（γ 无关）
- DD=2, RC=2, SS=2

但 countPBP_B = (2, 3, 1)! Total = 6 ✓，但 per-tc 不匹配。

**Wait** — dp = (2,) 时 k = r₁/2 + 1 = 2。c₁(ι) = 0（P = ⊥），c₁(j) = 1（Q 有 1 列高 1）。
setA_size = c₁(j) - c₁(ι) = 1 - 0 = 1 > 0。

所以 k = 2 但 Set A 只有 1 个元素。总共 k = 2 个元素 = 1 correction + 1 Set A。
x_τ = x₂ = Set A 的最后元素 = Q(1, 0)。但 Q 只有 1 cell 在 (0,0)。Q(1, 0) outside shape = dot。

Hmm 这不对。让我重新检查 indexing。

论文用 1-based indexing。"Q(j, 1)" 中 j 是行号（1-based），1 是列号（1-based = col 0 in 0-based）。

对 dp = (2,)：
- c₁(ι) = P.colLen(0) = 0
- c₁(j) = Q.colLen(0) = 1
- Set A = {Q(j, 1) | 0+1 ≤ j ≤ 1} = {Q(1, 1)}
  1-based → 0-based：Q(0, 0)
- Correction x₁: c₁ = 0 → B⁺ gives c, B⁻ gives s

x_τ = x_k = x_2 = Set A 的元素 Q(0, 0)（与 γ 无关）。

所以对 dp = (2,)：x_τ = Q(0, 0) = {s, r, d}。
这给出 DD=2, RC=2, SS=2。但 countPBP_B = (2, 3, 1)。

不匹配！countPBP_B.(DD,RC,SS) = (2,3,1) ≠ actual per-tc (2,2,2)。

所以对 singleton case，countPBP_B 的三元组确实**不等于**简单的 per-tail-class 计数。

让我重新检查 countPBP_B 到底计算什么。

## countPBP_B 的真正含义

countPBP_B 计算的是生成函数 $f^S(p,q)$ 在 p=q=1 的值。但 $f^S(p,q) = \sum_{\tau \in PBP_B^S} p^{p_\tau} q^{q_\tau}$，在 p=q=1 时确实等于 $\#PBP_B^S$。

等等，$p^{p_\tau} q^{q_\tau}$ 在 p=q=1 总是 1。所以 $f^S(1,1) = \#PBP_B^S$。

那为什么 countPBP_B = (2, 3, 1) 但实际 per-tc = (2, 2, 2)？

让我重新检验 Python 的 `compute_tail_symbol`，看它对 dp = (2,) 的结果。

我之前运行的结果：
```
dp = (2,): DD: B+=1, B-=1, total=2; RC: B+=1, B-=1, total=2; SS: B+=1, B-=1, total=2
```

这给出 (DD=2, RC=2, SS=2)。但 countPBP_B = (2, 3, 1)。

所以 **countPBP_B 不等于 #PBP_B^S** for S = {d}, {c,r}, {s}。

这说明 countPBP_B 的 (DD, RC, SS) 有其他含义——可能是论文的 "generating function value" 在某种特殊意义下。

实际上论文的 Prop 10.11 说的是生成函数的**递归关系**，不是直接给出 #PBP^S。countPBP_B 实现了这个递归。在 p=q=1 处，tripleSum(countPBP_B) = total count，但各分量不一定等于 per-class count。

这意味着：**per-tc 定理需要被完全重新思考**。countPBP_B 的三元组不是 per-tail-class 计数，而是生成函数的中间量。balanced case 的证明需要理解这些中间量的组合意义。

## 结论

1. `per_tc_B_*` 定理陈述确实是**错误的**
2. balanced case 不能通过简单的 per-tc 来证明
3. 需要理解 countPBP_B 三元组的真正组合意义
4. 或者找到一个不依赖 per-tc 的证明方法

可能的方案：直接用 D 型结果 + B⁺/B⁻ 对称性来证明 B 型计数。
