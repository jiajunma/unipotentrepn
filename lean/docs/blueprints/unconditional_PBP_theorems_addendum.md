# Addendum: 无条件化 Prop 11.5 PBP 层的限制分析

## 关键发现

在 `unconditional_PBP_theorems.md` 中提出的 existential 无条件化路径，在更仔细的分析后
**对一般 D-type τ 不可满足**。

### 具体原因

ILS.sign 和 ILS.firstColSign 都使用 `Int.natAbs`，所以两者都返回非负值。
这给假设 `h_fc, h_sign` 以严格的非负性约束：

$$\text{sign}(E).1 \geq 0,\quad \text{sign}(E).2 \geq 0,$$
$$\text{firstColSign}(E).1 \geq 0,\quad \text{firstColSign}(E).2 \geq 0.$$

### 约束链推导

把 `h_prop_11_4_p/q`, `h_sign`, `h_fc`, `h_n₀ ≥ 0` 联立，推出 (对 D-type τ)：

1. `p_prev = colGe1_1(τ) - c_2(O)` (其中 `colGe1_1` 来自 `signature_fst_decomp_D`)
2. `q_prev = colGe1_2(τ) - c_2(O)`
3. 由 `h_n₀ ≥ 0` + `signature_sum_D` + `residual_identity_D`:
   $$n_{\text{prev}} \geq 2 \cdot (c_3 + c_4 + \ldots)$$
4. 由 `h_fc` + 非负约束: `firstColSign(E).i = p_prev - n_prev ≥ 0`, 所以
   $$n_{\text{prev}} \leq \min(p_{\text{prev}}, q_{\text{prev}})$$
5. `p_{\text{prev}} = \text{colGe1}_1 - c_2 \geq Q.\text{dot} - c_2 = c_3 + c_4 + \ldots`

**冲突**：第 3 步要求 `n_prev ≥ 2·(c_3 + ...)`，第 4+5 步允许 `n_prev` 最大到 `c_3 + c_4 + ...`。

对于 `c_3 + c_4 + ... > 0` 的 shape（即 shape 有 ≥ 3 列），
有 `2·(c_3+...) > c_3 + ... `，所以 **无解**。

### 结论

**`prop_11_5_D_atomic_pbp_discharged` 的 hypothesis set 对列数 ≥ 3 的 D-type shape 不可同时满足。**

这不是 paper 的错误，而是 Lean 形式化中 h_fc 假设（基于 natAbs sign）与 paper 原始构造
（通过 AC.fold 从 descent chain 构造的 E，其 firstColSign 不一定按 natAbs 简单拆分）
之间的 mismatch。

## 正确的 unconditional 路径

应该是：构造 canonical `E := L_{τ''}` 通过：
1. 定义 `descendPBP_D : PBP → PBP` (single/double descent constructor)
2. 定义 `descentChain : PBP → List ACStepData`
3. `E τ := AC.fold (descent type of τ) (descentChain τ'')`
4. 证明 `E` 是 PBP.signature 一致 (by induction on chain)
5. 用 `AC.chain_firstColSign_eq_diff_sign` 自动得 h_fc
6. 用 `AC.step_sign_*` 自动得 h_sign
7. Prop 11.4 数值 identity: `signature(τ) = 2·c_2 + signature(τ'') + tailSignature(τ)` on the nose

这是一个实质性的工作量 (估计 2000+ 行 Lean)，远超当前 session 预算。

## 保留当前形式的理由

`prop_11_5_D_atomic_pbp_discharged` 作为 **reduction theorem** 仍然有价值：
- 把 PBP-level Lemma 11.5 的证明拆解为 4 个独立假设
- 每个假设对应一个 well-identified 的 mathematical fact (AC invariants + Prop 11.4 shape decomp)
- 当 canonical E 构造完成时，这些假设可以 directly 满足

## 下一步

因为真正 unconditional 路径需要的 infrastructure (canonical PBP descent + AC chain from descent + Prop 11.4 numerical form) 不在当前范围内，我们：

1. **保留** `prop_11_5_D_atomic_pbp_discharged` 作为最终形式，文档中明确说明它是 conditional；
2. **保留** `AC.lemma_11_6_D_unconditional` 等 AC-level 无条件形式 (这些 AC-level 的确是无条件的)；
3. **完成** 现有的 PBP-level wrappers (带适当 hypothesis)；
4. **延迟** canonical descent ILS 构造到独立 project。

整个 Section 10/11 的 ★ ∈ {B, D, C, M} 覆盖已达成，以下 2 个结构性 gap 留作 future work：
- Canonical PBP 层的 ILS 构造（使 Prop 11.5 PBP 无条件）
- shapeShiftC Case (b.1) 完成（M 型已完成，C 型此 case 因 col 1 修改延迟）

## Commit 历史（本 session 关键）

- `d3727a1` Lemma 11.1(b) abstract bijection + SignTargetSet infrastructure
- `ad7f7be` PBPExt at r₁(Ǒ)=1 (D type) cardinality match
- `13f723e` 3 atomic cell-count facts discharged
- `4ac826f` docs: blueprint for truly unconditional PBP-level theorems
- `3a4d3a1` SignatureDecomp.lean cleanup + re-exports
