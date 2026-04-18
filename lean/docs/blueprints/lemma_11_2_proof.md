# Lemma 11.2 自然语言证明

## Lean 形式化
**NOTE**: Lemma 11.2 is about ★ = C*（real form），按 `feedback_skip_cstar_dstar.md` **跳过 C*/D***。保留本 blueprint 仅供参考，未形式化。

## 陈述

设 ★ = C* 且 $\mathbf{r}_1(\mathcal{O}) \leq 1$。则 $\mathcal{L}_\tau \in \text{MYD}_\star(\mathcal{O})$ 且
$$\mathcal{L}_\tau = (p_\tau, q_\tau)_\star.$$

此外，映射
$$\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}}) \to \{(a,b) \in 2\mathbb{N}\times 2\mathbb{N} : |a|+|b| = |\mathcal{O}|\}, \quad \tau \mapsto \mathcal{L}_\tau(1)$$
良定且是双射。

## 与 Lemma 11.1 的差别

1. 对 C*: **没有 $\epsilon$ 扭曲**。公式是 $(p_\tau, q_\tau)_\star$，不是 $(p_\tau, (-1)^{\varepsilon_\tau}q_\tau)_\star$。
2. 没有 $\mathbb{Z}/2\mathbb{Z}$ 参数，因为 C* 没有 $\alpha$ 变量（$\alpha$ 只对 B 和 $\tilde C$ 起作用）。
3. 值域限定在 $2\mathbb{N} \times 2\mathbb{N}$（非负偶数对），因为 C* 的 signature 总是偶数（每个 cell 贡献 $(1,1) + \text{symbol contrib}$，而 $\text{symbol contrib}$ 都是非负偶数或 $(1,1)$——细化见 `DRCSymbol.tailContrib`）。

## 证明

### Case 1: $\mathbf{r}_1 = 0$（空 orbit）

$\mathcal{L}_\tau = (0, 0)_\star$（基础 case）。

$\text{Sign}(\tau) = (0, 0)$（空 PBP 无 cells）。

$(p_\tau, q_\tau)_\star = (0, 0)_\star = \mathcal{L}_\tau$. ✓

### Case 2: $\mathbf{r}_1 = 1$

$\mathcal{O}$ 是单列向量，$\check{\mathcal{O}}$ 对应 Sp(p,q/2) 型。注意 Sp(p,q/2) 的 Langlands dual 是 $\text{SO}_{p+q+1}(\mathbb{C})$。

做一步 descent 得到 $\tau' \in \text{PBP}^{\text{ext}}_{\star'}(\check{\mathcal{O}}')$，$|\check{\mathcal{O}}'| = 0$。这里 $\star' = $ Howe dual of C* 。根据论文 Section 10.3 的定义 $\star' = D^*$。

回到基础 case：$\mathcal{L}_{\tau'} = (0, 0)_{D^*}$。

对 $\star = C^*$，induction formula (11.2) 使用 $\check\vartheta^{s_\tau, \mathcal{O}}_{s_{\tau'}, \mathcal{O}'}$ 且 **没有** $\otimes (0, \varepsilon_\tau)$ 的后扭曲（这是 C*/D* 相对于 B/D 的主要区别）。

具体：
$$\mathcal{L}_\tau = \check\vartheta(\mathcal{L}_{\tau'})$$

没有 $\alpha$ 预扭曲（C*/D* 没有 $\alpha$），也没有 $\varepsilon_\tau$ 后扭曲。

Theta lift （eq 9.29 for B/D, eq 9.30 for C/C̃；对 C*/D* 用 similar formulas）augment by $(p_0, q_0)$。对 $\mathbf{r}_1 = 1$，$(p_0, q_0) = (p_\tau, q_\tau)$ 直接成立（类比 11.1 的推理）。

所以 $\mathcal{L}_\tau = [(p_\tau, q_\tau)] = (p_\tau, q_\tau)_\star$. ✓

**为什么 $(p_\tau, q_\tau) \in 2\mathbb{N}\times 2\mathbb{N}$**：C* 的 cell paint 都是 'dot' 或 special symbol 的组合，每个 cell 贡献都是 $(1,1)$ 或特殊的对称贡献；对 $\mathbf{r}_1 = 1$ 具体枚举得 $p_\tau, q_\tau$ 为偶数非负。

## 双射性

映射是双射：
- 单射：Sign 决定 PBP 结构（类似 11.1）。
- 满射：对每个 $(a,b) \in 2\mathbb{N}\times 2\mathbb{N}$ 满足 $a+b = |\mathcal{O}|$，构造 $\tau$ 使 Sign = $(a,b)$。由 BMSZ 论文 Lemma 4.8（或类似引理）保证所有奇偶对可达。

## 形式化策略

与 Lemma 11.1 类似：
1. 空 case：`AC.base` 定义与公式匹配（trivial by definition）。
2. $\mathbf{r}_1 = 1$: 一步 descent + theta lift。
3. 双射：counting。

当前 AC.base 对 C/M (不是 C*/D*) 已定义。paper 中的 C* 对应的 Lean 类型是... 需要检查。

注意：论文的 "C*" 和 "Ĉ" 不是同一个（Ĉ = C̃ 是 metaplectic C）。Lean `RootType` 定义中的 .C 对应 paper 的 C，.M 对应 C̃。**paper 的 C* 可能在 Lean 中没有直接对应**。

## 结论

**Lemma 11.2 在我们当前 Lean 形式化中可能没有直接对应**，因为 C* 是 quaternionic 分支（SO*(2n) 的 Langlands dual $\text{O}_{2n}$），不在当前 B/C/D/M 的主流 formalization 范围内。

需要先评估：是否添加 C* root type？暂时可以**跳过 Lemma 11.2**（以及 Prop 11.18-21 中涉及 C*/D* 的部分），专注于 ★ ∈ {B, D, C, C̃=M} 的主线。

**决定**：跳过 11.2（C*/D* 范围外），直接进到 Lemma 11.3（已完成）和 Prop 11.4。
