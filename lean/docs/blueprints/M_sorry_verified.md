# M sorry 验证结果

## 已验证的结论（Python 对所有测试 dp 通过）

### 1. B target shapes = B(rest) shapes
对 M dp = (r₁, r₂, rest)：
- M shapes: P_cols = dpartColLensP_M(dp), Q_cols = dpartColLensQ_M(dp)  
- B target: shiftLeft(P)_cols = tail(P_cols), Q_cols = Q_cols
- B(rest) shapes: P_cols = dpartColLensP_B(r₂::rest_tail), Q_cols = dpartColLensQ_B(r₂::rest_tail)

**结论**: shiftLeft(M P) = B(rest) P 且 M Q = B(rest) Q。总是成立。

### 2. card_B_target_eq_tripleSum
card(B⁺ shiftLeft(μP) μQ) + card(B⁻ shiftLeft(μP) μQ) = tripleSum(countPBP_B(r₂::rest))

这直接来自 B 型主定理 `card_PBPSet_B_eq_tripleSum_countPBP_B` 应用于 dp = r₂::rest。

### 3. Primitive (r₁ > r₂)
card(M) = tripleSum(countPBP_B(r₂::rest)) = dd+rc+ss

验证：dp=(4,2) card=6=6 ✓, dp=(6,4,2) card=16=16 ✓

### 4. Balanced (r₁ ≤ r₂)  
card(M) = dd+rc where (dd,rc,ss) = countPBP_B(r₂::rest)

验证：dp=(4,4) card=9=dd+rc=4+5=9 ✓, dp=(2,2) card=5=2+3=5 ✓, dp=(4,4,4,4) card=17=4+13=17 ✓

## Round-trip 证明思路

descentMB(liftMB(σ)) = σ。

descentMB 对 M PBP τ 做：
- P' paint = descentPaintL_MB(τ) = if i < dotScolLen(τ.P, j+1) then dot else τ.P(i, j+1)
- Q' paint = descentPaintR_MB(τ) = if i < dotScolLen(τ.P, j+1) then dot elif i < dotScolLen(τ.Q, j) then s else τ.Q(i, j)

liftMB(σ) 做：
- P(i, 0) = dot/s fill, P(i, j+1) = σ.P(i, j)
- Q(i, j) = if σ.Q(i,j) layerOrd ≤ 1 then dot else σ.Q(i,j)

所以 descentMB(liftMB(σ))：
- P' paint at (i, j)：
  = if i < dotScolLen(liftP, j+1) then dot else liftP(i, j+1)
  = if i < dotScolLen(liftP, j+1) then dot else σ.P(i, j)
  
  dotScolLen(liftP, j+1) = #{i : liftP(i, j+1) layerOrd ≤ 1} = #{i : σ.P(i,j) layerOrd ≤ 1}
  对 B 型 σ：σ.P 只有 {dot(0), c(3)}。layerOrd ≤ 1 iff dot。
  所以 dotScolLen(liftP, j+1) = #{i : σ.P(i,j) = dot} = dotScolLen(σ.P, j)。
  
  结果：P'(i,j) = if i < dotScolLen(σ.P, j) then dot else σ.P(i, j)
  
  对 B 型 σ.P（只有 dot 和 c）：
  - i < dotScolLen(σ.P, j)：σ.P(i,j) = dot → dot ✓
  - i ≥ dotScolLen(σ.P, j)：σ.P(i,j) = c（非 dot）→ σ.P(i,j) = c ✓
  
  所以 P'(i,j) = σ.P(i,j) ✓

- Q' paint at (i, j)：
  = if i < dotScolLen(liftP, j+1) then dot elif i < dotScolLen(liftQ, j) then s else liftQ(i, j)
  
  dotScolLen(liftP, j+1) = dotScolLen(σ.P, j)（如上）
  dotScolLen(liftQ, j) = #{i : liftQ(i,j) layerOrd ≤ 1} = #{i : σ.Q(i,j) layerOrd ≤ 1}
  = dotScolLen(σ.Q, j)（因为 liftQ 把 layerOrd ≤ 1 变 dot，其他不变）
  
  结果：Q'(i,j) = 
    if i < dotScolLen(σ.P, j) then dot 
    elif i < dotScolLen(σ.Q, j) then s 
    else liftQ(i,j)
  
  liftQ(i,j) = if σ.Q(i,j) layerOrd ≤ 1 then dot else σ.Q(i,j)
  
  但 i ≥ dotScolLen(σ.Q, j) 意味着 σ.Q(i,j) layerOrd > 1，所以 liftQ(i,j) = σ.Q(i,j)。
  
  最终：Q'(i,j) = descentPaintR_MB(σ 视为 B→M descent 的 source)(i, j)
  
  这就是 σ.Q 经过 refill 得到的值。但我们需要 Q'(i,j) = σ.Q(i,j)！
  
  Q'(i,j) 和 σ.Q(i,j) 的关系：
  - i < dotScolLen(σ.P, j)：Q' = dot。σ.Q(i,j) = ?
    如果 σ = descentMB(τ)，那 σ.Q(i,j) = descentPaintR_MB(τ)(i,j)。
    descentPaintR_MB(τ)(i,j) = if i < dotScolLen(τ.P, j+1) then dot elif ... 
    这取决于原始 τ。不能直接推出 σ.Q(i,j) = dot。
  
  **问题**：round-trip Q'(i,j) = σ.Q(i,j) 不是对所有 σ 成立，只对 descent image 中的 σ 成立。
  
  对于 GENERAL B PBP σ（不在 descent image 中），round-trip 会失败。
  
  所以 round-trip 需要额外假设：σ 在 descent image 中，即存在 M PBP τ with descentMB(τ) = σ。

## card_M_eq_card_B_target 证明思路

不需要 round-trip！可以用：

1. descentMB 是单射 → card(M) ≤ card(B target)
2. card(B target) = tripleSum(countPBP_B rest) （从 B 型主定理）
3. countPBP_M(dp) = tripleSum(rest)（primitive）或 dd+rc（balanced）
4. 需要证 card(M) = countPBP_M(dp)

这是循环的 —— 我们正在证 card(M) = countPBP_M(dp)。

**非循环方法**：
- card(M) ≤ card(B target) = tripleSum(rest)  （单射 + B 主定理）
- card(M) ≥ countPBP_M(dp)  （需要独立论证）

或者：用 Prop 10.2 (count 与 ℘ 无关) + Thm 7.7 (count = representation count) 来独立确定 card(M)。但这需要表示论。

**最简单方法**：直接证 lift 给出 descentMB 的右逆（on the image）。即对 descent image 中的 σ，lift(σ) 存在且 descent(lift(σ)) = σ。这给出 surjectivity onto image → card equality。
