# Lemma 11.1 自然语言证明

## Lean 形式化
- (a) empty: `lemma_11_1_a_empty`, `lemma_11_1_a_empty_first_entry` in `CombUnipotent/MYD.lean`
- (a) r₁=1: `lemma_11_1_a_r1_one`, `lemma_11_1_a_r1_one_first_entry` in `CombUnipotent/MYD.lean`
- (b) bijection: `lemma_11_1_b_bijection`, `lemma_11_1_b_bijection_concrete`, `PBPExt_at_r1_eq_1_D` in `MYD.lean`, `CombUnipotent/MYD/Lemma11_1_b.lean`

## 陈述

设 ★ ∈ {B, D}。

**(a)** 若 $\mathbf{r}_1(\mathcal{O}) \leq 1$，则 $\mathcal{L}_\tau \in \text{MYD}_\star(\mathcal{O})$ 且
$$\mathcal{L}_\tau = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)_\star.$$

**(b)** 若 $\mathbf{r}_1(\mathcal{O}) = 1$，则映射
$$\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}}) \times \mathbb{Z}/2\mathbb{Z} \to \{(a,b) \in \mathbb{Z}\times\mathbb{Z} : |a|+|b| = |\mathcal{O}|\}, \quad (\tau, \epsilon) \mapsto (-1)^\epsilon \mathcal{L}_\tau(1)$$
是双射。

## 记号约定

- $|\mathcal{O}| = \sum_i r_i(\mathcal{O})$ 是 orbit 总格数。
- $(a,b)_\star$ 表示 $\text{MYD}_\star$ 中第一位为 $(a,b)$、其余为 $(0,0)$ 的（唯一）标记 Young 图（若存在）。
- $\mathcal{L}_\tau \in \mathbb{Z}[\text{MYD}_\star(\mathcal{O})]$ 由 (11.2) 递归定义。

## 证明 (a)

### Case 1: $\mathbf{r}_1(\mathcal{O}) = 0$（空 orbit）

此时 $|\mathcal{O}| = 0$，$\mathcal{O}$ 是空 Young 图。对应地 $\check{\mathcal{O}}$ 也是空 orbit。

$\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})$ 的元素 $\tau = (\iota_\wp, \mathcal{P}) \times (\jmath_\wp, \mathcal{Q}) \times \alpha$ 中 $\iota_\wp = \jmath_\wp = \emptyset$（空 shape），故 $\mathcal{P}, \mathcal{Q}$ 都是"空函数"。

由 (11.2) 的基础 case：
$$\mathcal{L}_\tau := \begin{cases}(1,0)_\star & \alpha_\tau = B^+\\ (0,-1)_\star & \alpha_\tau = B^-\\ (0,0)_\star & \text{otherwise (D, C*, D*)}\end{cases}$$

计算 $(p_\tau, q_\tau) = \text{Sign}(\tau)$（eq 3.3 加上 $\alpha$ 的修正项）：
- 空 PBP 的基础 sign 都是 $(0,0)$。
- $\alpha = B^+$ 贡献 $+1$ 到 $p$ 分量，故 Sign = $(1, 0)$。
- $\alpha = B^-$ 贡献 $+1$ 到 $q$ 分量，故 Sign = $(0, 1)$。
- 其他情形 Sign = $(0, 0)$。

计算 $\varepsilon_\tau$（eq 3.6，$\varepsilon = 0$ 当且仅当 $\mathcal{P}$ 或 $\mathcal{Q}$ 第一列含 $d$）：
- 空 PBP 没有任何 cells，尤其没有 $d$ 符号，故 $\varepsilon_\tau = 1$。

验证 $\mathcal{L}_\tau = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)_\star$：

| $\alpha$ | $p_\tau$ | $q_\tau$ | $\varepsilon_\tau$ | $(-1)^{\varepsilon_\tau} q_\tau$ | $(p_\tau, (-1)^{\varepsilon_\tau}q_\tau)_\star$ | $\mathcal{L}_\tau$ |
|---|---|---|---|---|---|---|
| $B^+$ | 1 | 0 | 1 | $-0 = 0$ | $(1, 0)_\star$ | $(1, 0)_\star$ ✓ |
| $B^-$ | 0 | 1 | 1 | $-1$ | $(0, -1)_\star$ | $(0, -1)_\star$ ✓ |
| 其他 | 0 | 0 | 1 | 0 | $(0, 0)_\star$ | $(0, 0)_\star$ ✓ |

故 (a) 在 $\mathbf{r}_1 = 0$ 时成立。 $\square$

### Case 2: $\mathbf{r}_1(\mathcal{O}) = 1$

此时 $\mathcal{O}$ 是列向量（所有 $r_i = 1$），$|\mathcal{O}| = m$（行数）。对应的 $\check{\mathcal{O}}$：
- $\star = B$: $\check{\mathcal{O}}$ 是 BV 对偶，单行 $(2m+1)$ 长，因为 B 型 odd total。实际上要分析行长决定的。
- $\star = D$: $\check{\mathcal{O}}$ 是 single row of length $2m$。

对 $\tau \in \text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})$，做一步 descent：
$$\tau' = \nabla(\tau) \in \text{PBP}^{\text{ext}}_{\star'}(\check{\mathcal{O}}')$$

其中 $\check{\mathcal{O}}'$ 是 $\check{\mathcal{O}}$ 去掉第一行，变成**空**（因为 $\check{\mathcal{O}}$ 单行）。这样 $|\check{\mathcal{O}}'| = 0$，落到 Case 1。

应用 (11.2) 一次：
$$\mathcal{L}_\tau = \check{\vartheta}^{s_\tau, \mathcal{O}}_{s_{\tau'}, \mathcal{O}'}(\mathcal{L}_{\tau'}) \otimes (0, \varepsilon_\tau)$$

Base $\mathcal{L}_{\tau'}$ 来自 Case 1。由 (9.29)：theta lift $\check\vartheta$ 先做 $T^\gamma$（char twist），然后 augment by $(p_0, q_0)$；再应用 $\otimes (0, \varepsilon_\tau)$ 做 sign twist。

**关键**：对于 $\mathbf{r}_1(\mathcal{O}) = 1$，$\mathcal{O}$ 只有一"层"，所以 theta lift 的 augment 参数 $(p_0, q_0)$ 直接等于 $(p_\tau - \text{shift}, q_\tau - \text{shift})$，其中 shift 来自已经计入 base case 的 $(\pm 1, 0)$ 或 $(0, \pm 1)$。

具体计算（以 $\star = D$, $\check{\mathcal{O}} = [1]$ 为例）：
- $\mathcal{L}_{\tau'}$ 来自 D 空 orbit：$\mathcal{L}_{\tau'} = (0,0)_D = []$（空 MYD）或单元 $(0,0)$。
- Theta lift $C \to D$ augment：$\text{addp} = p_\tau - \text{sign}(\mathcal{L}_{\tau'})_1 - \text{fcSign}(\mathcal{L}_{\tau'})_2$。
- 当 $\mathcal{L}_{\tau'} = (0,0)$ 时，sign = (0,0), fcSign = (0,0)，故 $\text{addp} = p_\tau$, $\text{addn} = q_\tau$。
- 故 augment 后 $\mathcal{L} = [(p_\tau, q_\tau)]$。
- 再做 $\otimes (0, \varepsilon_\tau)$：第一行 length 1（奇），$(p_\tau, q_\tau) \mapsto (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)$（eq 9.15 at index 0）。
- 最终 $\mathcal{L}_\tau = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)_\star$. ✓

对 $\star = B$ 同理，theta lift $M \to B$ 给出类似结构。 $\square$

## 证明 (b)

若 $\mathbf{r}_1(\mathcal{O}) = 1$，由 (a)：每个 $\tau \in \text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})$ 对应 $\mathcal{L}_\tau(1) = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)$。

映射 $(\tau, \epsilon) \mapsto (-1)^\epsilon \mathcal{L}_\tau(1) = (-1)^\epsilon (p_\tau, (-1)^{\varepsilon_\tau} q_\tau) = ((-1)^\epsilon p_\tau, (-1)^{\epsilon + \varepsilon_\tau} q_\tau)$.

**单射性**：
- 若两对 $(\tau_i, \epsilon_i)$ 映射到同一 $(a, b)$，由 $|a| = p_{\tau_i}$ 且 $p_\tau \geq 0$，sign 决定 $p_{\tau_1} = p_{\tau_2} = |a|$。
- 类似 $q_{\tau_1} = q_{\tau_2} = |b|$。
- Sign $(p_\tau, q_\tau)$ 由 $(\tau)$ 的 PBP 结构唯一确定——对于 $\mathbf{r}_1 = 1$（single column orbit），PBP 由 $\alpha$ 和每个 cell 的 paint 决定，它们各自地定义 $p_\tau, q_\tau$ 和 $\varepsilon_\tau$。
- 所以 Sign 相等意味着 PBP 结构相等（对低秩 orbit 容易枚举）。具体地：$\tau$ 由 $(\alpha, \{paint of col 0 cells\})$ 决定，而 sign 和 $\varepsilon$ 分辨这些 paint。
- $\epsilon$ 由 $a$ 的符号决定（或 $b$ 的相对 sign）。

**满射性**：对任意 $(a, b)$ 且 $|a|+|b| = |\mathcal{O}| = m$，我们需要构造 $(\tau, \epsilon)$ 使 $(-1)^\epsilon \mathcal{L}_\tau(1) = (a, b)$。
- $p_\tau + q_\tau$（即 $|\mathcal{O}|$）必须 $= |a| + |b|$，由 $\text{sign}(\tau)_\text{total} = |\mathcal{O}|$ 保证。
- 对每个 $(|a|, |b|)$ 带 $|a|+|b|=m$，存在正好一个 $\tau$ 使 Sign $= (|a|, |b|)$：即 $|a|$ 个 cells 贡献 $p$，$|b|$ 个 cells 贡献 $q$；具体是 B+/B- 的选择 + paint 符号的选择。
- 选 $\epsilon \in \{0, 1\}$ 以匹配 $(a, b)$ 的符号组合（和 $\varepsilon_\tau$ 一起决定两个 $\pm$）。

对 B 型（$|\mathcal{O}| = 2m+1$ odd）、D 型（$|\mathcal{O}| = 2m$ even），详细枚举可验证基数相等，配合单射即得双射。$\square$

## 形式化策略

对 Lean：
1. **Part (a) $|\check{\mathcal{O}}|=0$**：直接验证 `AC.base γ` = 对应 $(p_\tau, (-1)^{\varepsilon_\tau}q_\tau)_\star$ 的 list。
   - Lean 中 PBP 没有 "空 γ" 的 canonical construction；需要把 "空 PBP for γ" 定义为 $\tau_\emptyset(\gamma)$。
2. **Part (a) $\mathbf{r}_1=1$**：用 AC.step 一次 + `thetaLift_CD/MB_first_entry` + `twistBD_first_entry`。
3. **Part (b)**：计数即可；用 `surjectivity_from_counting`。

当前 Lean 已有 `AC.base_first_entry`（第一项 $\geq 0$）；需补：
- `AC.base_eq_formula γ τ` — 对空 PBP，AC.base γ 等于 $(p_\tau, (-1)^{\varepsilon_\tau}q_\tau)$ 列表
- `lemma_11_1_a_r1_one` — 一步 descent 情形
- `lemma_11_1_b_bijection` — 用 counting 导出 bijection

## 规模估计

- (a) $|\check{\mathcal{O}}|=0$: ~30 行 Lean（case analysis on γ）
- (a) $\mathbf{r}_1=1$: ~100 行 Lean（one descent + theta lift + twist）
- (b) bijection: ~80 行 Lean（counting + injectivity）

合计约 **200 行**。分类为 **mirror**（模仿已有 AC.base + theta_lift 证明模式）。
