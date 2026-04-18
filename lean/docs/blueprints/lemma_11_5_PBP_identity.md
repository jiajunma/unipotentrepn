# Lemma 11.5 核心 PBP Identity — 自然语言证明

## 目标

设 ★ ∈ {B, D}，$\check{\mathcal{O}}$ 有 good parity 且 $\mathbf{r}_2(\check{\mathcal{O}}) > \mathbf{r}_3(\check{\mathcal{O}})$（primitive case）。令：
- $\tau \in \text{PBP}_\star(\check{\mathcal{O}})$
- $\tau' = \nabla(\tau) \in \text{PBP}_{\star'}(\check{\mathcal{O}}')$（单次 descent，$\star' = C$ for $\star = D$；$\star' = \tilde C$ for $\star \in \{B^\pm\}$）
- $\tau'' = \nabla^2(\tau) = \nabla(\tau') \in \text{PBP}_\star(\check{\mathcal{O}}'')$
- $\tau_t \in \text{PBP}_D(\check{\mathcal{O}}_t)$（尾部 PBP）
- $(p_\tau, q_\tau) = \text{Sign}(\tau)$，$(p_{\tau''}, q_{\tau''}) = \text{Sign}(\tau'')$，$(p_{\tau_t}, q_{\tau_t}) = \text{Sign}(\tau_t)$
- $\mathcal{L}_\tau, \mathcal{L}_{\tau'}, \mathcal{L}_{\tau''}$ 对应的组合 AC
- $n_0 = (\mathbf{c}_1(\mathcal{O}') - \mathbf{c}_2(\mathcal{O}'))/2$（inner augment）
- $k = (\mathbf{r}_1(\check\mathcal{O}) - \mathbf{r}_2(\check\mathcal{O}))/2 + 1$（tail 长度）

**待证的 PBP Identity**（Lemma 11.5 的核心）：

经过两步 theta lift 复合后，outer C→D (或 M→B) lift 的 augmentation 参数 $(\text{addp}_{\text{outer}}, \text{addn}_{\text{outer}})$ 恰好等于 $(p_{\tau_t}, q_{\tau_t})$。

严格地，设 $E = \mathcal{L}_{\tau''}$。记内层 lift 后的 ILS 为 $\text{inner} = T^{\gamma_1}((n_0, n_0) :: E)$（这里 $\gamma_1$ 是 inner lift 的 char twist 参数；$\oplus$ 对应于 augment 即 cons）。则：

$$\text{addp}_{\text{outer}} := p_\tau - \text{sign}(\text{inner})_1 - \text{firstColSign}(\text{inner})_2 = p_{\tau_t}$$

$$\text{addn}_{\text{outer}} := q_\tau - \text{sign}(\text{inner})_2 - \text{firstColSign}(\text{inner})_1 = q_{\tau_t}$$

## 证明策略

Lean 中 `ILS.lemma_11_5_D` 已证：**在假设** $p - 2 n_{\text{inner}} + (\text{sign } E).2 = p_t$ 下，outer augment addp 等于 $p_t$。此假设就是 PBP identity 的精简等价形式。所以**只需证 PBP identity**。

### Step 1：展开 sign(inner) 和 firstColSign(inner)

inner = charTwistCM(augment(n₀, n₀) E) γ₁。

**Fact 1**（Lean 已证：`charTwistCM_sign`, `charTwistCM_firstColSign`）:
$$\text{sign}(T^\gamma F) = \text{sign}(F), \quad \text{firstColSign}(T^\gamma F) = \text{firstColSign}(F)$$

所以 sign(inner) = sign(augment(n₀, n₀) E) 且 firstColSign(inner) = firstColSign(augment(n₀, n₀) E)。

**Fact 2**（Lean 已证：`sign_cons_nonneg`, `firstColSign_cons`，对 $n_0 \geq 0$）:
$$\text{sign}((n_0, n_0) :: E) = (n_0 + \text{sign}(E)_1, n_0 + \text{sign}(E)_2)$$
$$\text{firstColSign}((n_0, n_0) :: E) = (n_0 + \text{firstColSign}(E)_2, n_0 + \text{firstColSign}(E)_1)$$

（firstColSign 在 cons 时 swap 后两个 component — 这是 eq (9.12) 的性质。）

代入：
- $\text{sign}(\text{inner})_1 = n_0 + \text{sign}(E)_1$
- $\text{firstColSign}(\text{inner})_2 = n_0 + \text{firstColSign}(E)_1$

故：
$$\text{addp}_{\text{outer}} = p_\tau - 2n_0 - \text{sign}(E)_1 - \text{firstColSign}(E)_1$$

### Step 2：归纳假设 — sign 和 firstColSign 的 PBP 解释

**Claim A (induction hypothesis on $\mathcal{L}_{\tau''}$)**:
$$\text{sign}(\mathcal{L}_{\tau''}) = \text{Sign}(\tau'') = (p_{\tau''}, q_{\tau''})$$

**证明**：$\mathcal{L}_{\tau''}$ 是 $\tau''$ 的 AC。已知 AC sign preservation（Lean 已证 `AC.step_sign_D/Bplus/Bminus/C/M`）：每步 AC.step 保持 sign 等于 outer PBP signature。基础 case (`AC.base_sign`) 也一致。于是归纳到 sign(L_{τ''}) = Sign(τ'')。$\square$

**Claim B**:
$$\text{firstColSign}(\mathcal{L}_{\tau''})_1 = \text{firstColSign}(\mathcal{L}_{\tau''})_2 = 0 \text{ 若 } \tau'' \text{ 的 shape 满足特定小秩条件}$$

实际上我们需要更强的声明：

**Claim B'（精确版）**: firstColSign of $\mathcal{L}_{\tau''}$ 由 $\tau''$ 的**首列信息**决定。具体地，

$$\text{firstColSign}(\mathcal{L}_{\tau''})_1 = \#\{i : \mathcal{P}_{\tau''}(i, 1) \in \{\bullet, s\}, \ i \text{ 奇}\} + \#\{i : \mathcal{P}_{\tau''}(i, 1) \in \{r, c, d\}, \ i \text{ 偶}\}$$

（大意）。这是 firstColSign 定义（eq 9.12）在 PBP 层的 unravel。

此处证明要用到 Lemma 11.1(a)（r₁≤1 base case 的 firstColSign 具体值）作为归纳基础。

### Step 3：外层 sign identity（Prop 11.4 应用到 τ）

由 Prop 11.4（signature decomposition for D/B type）：
$$p_\tau = \mathbf{c}_2(\mathcal{O}) + p_{\tau''} + p_{\tau_t}$$

所以：
$$p_{\tau_t} = p_\tau - \mathbf{c}_2(\mathcal{O}) - p_{\tau''}$$

### Step 4：比对

我们有两个表达式：
$$\text{addp}_{\text{outer}} = p_\tau - 2n_0 - \text{sign}(E)_1 - \text{firstColSign}(E)_1$$
$$p_{\tau_t} = p_\tau - \mathbf{c}_2(\mathcal{O}) - p_{\tau''}$$

相等当且仅当：
$$2n_0 + \text{sign}(E)_1 + \text{firstColSign}(E)_1 = \mathbf{c}_2(\mathcal{O}) + p_{\tau''}$$

用 Claim A ($\text{sign}(E)_1 = p_{\tau''}$)，化简为：
$$2n_0 + \text{firstColSign}(E)_1 = \mathbf{c}_2(\mathcal{O})$$

### Step 5：$n_0$ 与 $\mathbf{c}_2(\mathcal{O})$ 的关系

$n_0 = (\mathbf{c}_1(\mathcal{O}') - \mathbf{c}_2(\mathcal{O}'))/2$。

$\mathcal{O}' = \tilde{\nabla}(\check\mathcal{O})$ 是 dual descent（去掉首行）后的 BV dual。而 $\check{\mathcal{O}}'' = \tilde\nabla^2(\check\mathcal{O})$。

记 $c_i = \mathbf{c}_i(\mathcal{O})$（即原 shape 的列长）、$c_i' = \mathbf{c}_i(\mathcal{O}')$、$c_i'' = \mathbf{c}_i(\mathcal{O}'')$。

**事实**（来自 [BMSZb] Section 9.1-9.3 shape relations）:
- $\mathcal{O}' = \tilde\nabla(\check\mathcal{O}) = (\nabla_{\text{naive}}(\check\mathcal{O}))^{\text{BV}}$
- 列长关系：$c_1' = c_2$（$\mathcal{O}'$ 首列 = $\mathcal{O}$ 第二列，因为 BV 对偶把"去首行"映为"去首列"）
- 类似 $c_2' = c_3$
- 故 $c_1' - c_2' = c_2 - c_3$
- $n_0 = (c_2 - c_3)/2$

对 primitive case $\mathbf{r}_2 > \mathbf{r}_3$，$c_2 - c_3 \geq 1$，且 $2n_0 = c_2 - c_3$。

### Step 6：firstColSign(E) 的内容

待证：
$$\text{firstColSign}(\mathcal{L}_{\tau''})_1 = \mathbf{c}_2(\mathcal{O}) - 2n_0 = c_2 - (c_2 - c_3) = c_3$$

即 $\text{firstColSign}(\mathcal{L}_{\tau''})_1 = c_3 = \mathbf{c}_3(\mathcal{O}) = \mathbf{c}_1(\mathcal{O}'')$.

这实际是在说：**$\mathcal{L}_{\tau''}$ 的 firstColSign 首项等于 $\tau''$ 所在 shape 的第一列长。**

这个 identity 在 base case（$\mathcal{L}_{\tau''}$ 为 $r_1(\mathcal{O}'') \leq 1$，即 Lemma 11.1 的适用范围）成立：

- $|\check{\mathcal{O}}''| = 0$: $\mathcal{L}_{\tau''}$ 为 $[(1, 0)]$ (B⁺)、$[(0, -1)]$ (B⁻) 或 $[]$ (D)；$c_1(\mathcal{O}'') = 0$ 或 1。
- $r_1(\mathcal{O}'') = 1$: $\mathcal{L}_{\tau''} = [(p_{\tau''}, (-1)^{\varepsilon_{\tau''}} q_{\tau''})]$；firstColSign 在 length-1 row 上（位置 0）直接取 $(|p|, |q|)$。所以 $\text{firstColSign}_1 = p_{\tau''}$. And paper's $\mathbf{c}_1(\mathcal{O}'')$ at $r_1 = 1$ corresponds to... hmm, need to verify 正好等于 $p_{\tau''}$.

**归纳步骤**：设 $\tau''$ 可进一步 descend。Prop 11.4 给出 $p_{\tau''} = \mathbf{c}_2(\mathcal{O}'') + p_{\tau''''} + p_{(\tau'')_t}$。但这是递归关系，需要巧妙的 invariant。

**关键 invariant**（猜想，需验证）：$\text{firstColSign}(\mathcal{L}_\sigma)_1 = \mathbf{c}_1(\mathcal{O}_\sigma)$ 对所有有效 PBP $\sigma$ 成立。

此 invariant 通过对 AC.step 的分析归纳传递：每次 AC.step 对 firstColSign 的作用可按 thetaLift 公式追踪。

## 结论与缺口

我刚才给出的是**证明框架**，不是完整严格证明。未闭合的关键缺口：

1. **Claim B'**（firstColSign 的 PBP 解释）— 需要按 eq (9.12) 展开，对每行根据 parity 组合 |p_i|, |q_i|。具体公式我没完全推。

2. **invariant $\text{firstColSign}(\mathcal{L}_\sigma)_1 = \mathbf{c}_1(\mathcal{O}_\sigma)$** — 对 base case 需要验证（Lemma 11.1 级别），对归纳步骤需要追 firstColSign 经 thetaLift 的变化律。

3. **Step 5 shape relations** — $c_1' = c_2$ 是 dual descent 的基础性质，Lean 中应有对应引理（在 `ILS.lean` 或 shape 级模块里）。需要具体引用。

4. **balanced case (11.5b)** — 我完全没写 $r_2 = r_3$ 情形。

**真相**：Lemma 11.5 的严格 PBP-level 证明需要 firstColSign 在 theta lift 下的 tracking 公式，这在 [BMSZ] 附录或代码验证里可能有暗示，但没有完整严格呈现。我仍未给出完整证明 — 我给出的是路线图。

**后续**：
- 补完 Claim B' 的 firstColSign 展开
- 验证 invariant at base + inductive step
- 写 balanced case (11.5b) 
- 然后才能去 Lean 形式化

## 替代方案

如果精确追踪 firstColSign 太复杂，一个**更保守的路线**：
- 将 Lemma 11.5 的 PBP identity 作为 **axiom** 标注"computationally verified up to dp size 10+"
- 在 Lean 中用 `axiom` 声明
- 但这**违反** user "B/D/C/M 必须完整"的要求

所以需要坚持上述严格路线。此文档是进度快照，不是最终证明。
