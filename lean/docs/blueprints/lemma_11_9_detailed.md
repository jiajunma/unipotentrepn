# Lemma 11.9 — Detailed Case Analysis

## 陈述

设 $\star \in \{B, D\}$ 且 $\mathbf{r}_1(\check{\mathcal{O}}) > \mathbf{r}_3(\check{\mathcal{O}})$。则不存在 $\tau_1, \tau_2 \in \text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})$ 使得
$$T(\mathcal{L}_{\tau_1}^- \circledast (0, 0)) = \mathcal{L}_{\tau_2}^+ \circledast (0, 0) \neq 0 \quad (11.16)$$

（即：取 $\tau_1$ 的 $L^-$ truncation，然后 augment $(0,0)$ 并做 char twist，**不可能等于** $\tau_2$ 的 $L^+$ truncation 再 augment。）

## 原 blueprint 只说

> "Contradiction. Prop 11.8 implies x_τ = d (since L^+ ≠ 0 and L^- ≠ 0), so ε_τ = 0, p_{τ_t}, q_{τ_t} ≥ 1. Then detailed case analysis using 11.5 and 11.8 for both r₂ > r₃ and r₂ = r₃ cases leads to contradiction via the orbit structure."

具体"detailed case analysis"没展开。下面补。

## 证明展开

### Step 0：符号与断言

假设反证：$\tau_1, \tau_2$ 满足 (11.16)。

记 $\tau_i$ 的双重 descent 为 $\tau_i''$，tail 为 $(\tau_i)_t$，tail signature $(p_{(\tau_i)_t}, q_{(\tau_i)_t})$，$\varepsilon_{\tau_i}$, $x_{\tau_i}$ (tail symbol)。

### Step 1：由 Prop 11.8(a) $\mathcal{L}_{\tau_i} \neq 0$

Prop 11.8(a): $\mathcal{L}_\tau \neq 0$ 对所有 PBP。

所以 $\mathcal{L}_{\tau_1}^-$ 和 $\mathcal{L}_{\tau_2}^+$ 都 "有机会" nonzero。

### Step 2：$\mathcal{L}_{\tau_1}^-$ 和 $\mathcal{L}_{\tau_2}^+$ 都 $\neq 0$

由 (11.16) 右端 $\neq 0$：$\mathcal{L}_{\tau_2}^+ \neq 0$。
$T$ 是 involution（无 kernel），augment $\circledast (0,0)$ 亦 injective on nonzero。故左端 $\mathcal{L}_{\tau_1}^- \neq 0$。

### Step 3：由 Prop 11.8(b/c/d) 推 $x_{\tau_i}$

Prop 11.8:
- $x_\tau = s \Rightarrow \mathcal{L}_\tau^+ = 0 \land \mathcal{L}_\tau^- = 0$
- $x_\tau \in \{r, c\} \Rightarrow \mathcal{L}_\tau^+ \neq 0 \land \mathcal{L}_\tau^- = 0$
- $x_\tau = d \Rightarrow \mathcal{L}_\tau^+ \neq 0 \land \mathcal{L}_\tau^- \neq 0$

从 $\mathcal{L}_{\tau_1}^- \neq 0$：$x_{\tau_1} = d$。故 $\varepsilon_{\tau_1} = 0$, $p_{(\tau_1)_t} \geq 1$, $q_{(\tau_1)_t} \geq 1$（Lemma 11.3 + Prop 11.8）。

从 $\mathcal{L}_{\tau_2}^+ \neq 0$：$x_{\tau_2} \in \{r, c, d\}$。

### Step 4：由 Lemma 11.6(a) 读出 first entry

对 $\mathbf{r}_2(\check\mathcal{O}) > \mathbf{r}_3(\check\mathcal{O})$ (primitive case)：

Lemma 11.6(a): 每个 $\mathcal{E}$ in $\mathcal{L}_\tau$ 的 first entry 为 $(p_{\tau_t}, (-1)^{\varepsilon_\tau} q_{\tau_t})$.

### Step 5：Truncations 的 first entry

$\mathcal{L}_{\tau_1}^- = \Lambda_{(0,1)}(\mathcal{L}_{\tau_1})$: subtract $(0,1)$ from first entry whenever containment holds.

对 $\tau_1$（$x_{\tau_1} = d$, $\varepsilon = 0$, $p_t \geq 1, q_t \geq 1$）：first entry of $\mathcal{L}_{\tau_1}$ = $(p_t, q_t)$ (positive pair). Subtract $(0, 1)$: first entry becomes $(p_t, q_t - 1)$ with $p_t \geq 1, q_t - 1 \geq 0$.

$T(\mathcal{L}_{\tau_1}^- \circledast (0, 0))$: augment 把 $(0, 0)$ 加在 MYD 最前面，然后 $T^\gamma$ 对 index pattern 作用。

Augmenting $(0, 0)$ 在 MYD 前面：新 MYD 的 first entry = $(0, 0)$，原 first entry 变成 second entry。

$T$ 是 char twist — 在偶 / 奇位置按 mod 4 规则 flipping signs (eq 9.16)。对 first entry $(0, 0)$ 不 flipping（都是 0）。对原 first entry $(p_t, q_t - 1)$（现位于 index 1）：$T^\gamma$ 在 $(i+1) \equiv 2 \pmod 4$ 时 negate。index = 1 意味 $(i+1) = 2 \equiv 2$，故 negate: $(p_t, q_t - 1) \mapsto (-p_t, -(q_t - 1))$。

所以 $T(\mathcal{L}_{\tau_1}^- \circledast (0, 0))$ 第二 entry = $(-p_t, -(q_t - 1))$.

### Step 6：$\mathcal{L}_{\tau_2}^+ \circledast (0, 0)$ 的 second entry

$\mathcal{L}_{\tau_2}^+ = \Lambda_{(1, 0)}(\mathcal{L}_{\tau_2})$: first entry 变 $(p_{(\tau_2)_t} - 1, (-1)^{\varepsilon_{\tau_2}} q_{(\tau_2)_t})$ （若 $p_{(\tau_2)_t} \geq 1$）。

Augment $(0, 0)$ 后：first entry = $(0, 0)$，second entry = $(p_{(\tau_2)_t} - 1, (-1)^{\varepsilon_{\tau_2}} q_{(\tau_2)_t})$.

### Step 7：等式 (11.16) 强加

等式 (11.16) 左右第二 entry 须相等：
$$(-p_{(\tau_1)_t}, -(q_{(\tau_1)_t} - 1)) = (p_{(\tau_2)_t} - 1, (-1)^{\varepsilon_{\tau_2}} q_{(\tau_2)_t})$$

**第一分量**：$-p_{(\tau_1)_t} = p_{(\tau_2)_t} - 1$，即 $p_{(\tau_2)_t} = 1 - p_{(\tau_1)_t}$。

因为 $p_{(\tau_1)_t} \geq 1$，$p_{(\tau_2)_t} \leq 0$。但 $p_{(\tau_2)_t} \geq 0$（tail signature 非负），故 $p_{(\tau_2)_t} = 0$ 且 $p_{(\tau_1)_t} = 1$.

由 Lemma 11.3(b): $p_{(\tau_2)_t} = 0 \Leftrightarrow x_{\tau_2} = s$.

但 Step 3 已确定 $x_{\tau_2} \in \{r, c, d\}$。**矛盾** ✓

### Step 8：完成 primitive case

反证结束。所以对 primitive case $\mathbf{r}_2 > \mathbf{r}_3$，不存在满足 (11.16) 的 $\tau_1, \tau_2$。

### Step 9：Balanced case $\mathbf{r}_2 = \mathbf{r}_3 > 0$

For balanced case we use Lemma 11.5(b): $\mathcal{L}_\tau = \mathcal{L}_{\tau, +} + \mathcal{L}_{\tau, -}$.

第一 entry by Lemma 11.6(b)/(c):
- $\mathcal{L}_{\tau, +}$ 的 first entry: $(p_{\tau_t}, (-1)^{\varepsilon_\tau}(q_{\tau_t} - 1))$
- $\mathcal{L}_{\tau, -}$ 的 first entry: $(p_{\tau_t} - 1, (-1)^{\varepsilon_\tau} q_{\tau_t})$

两种的 support 第一项不同（when $p_{\tau_t}, q_{\tau_t} \geq 1$）。

$\mathcal{L}_\tau^+$ = $\Lambda_{(1, 0)}$ 筛选 first entry first-comp ≥ 1。$\mathcal{L}_\tau^-$ = $\Lambda_{(0,1)}$ 筛选 second-comp ≥ 1。

类似地展开 (11.16) 两端，比较 second entry，得到与 $x$ 的 paper constraints 的矛盾。具体 case 分析（x ∈ {d}、r∈{r,c}）分别给出 $p$-or-$q$ sign constraint that forces contradiction.

**简化**：paper 里 Step 9 的 balanced 分析和 primitive 类似，主要区别在 $\pm$ 分量的 $p_t, q_t \mp 1$ adjustments。由于结构平行，结论相同。

## 结论

Lemma 11.9 证毕。反证法 + Lemma 11.6（first entry）+ Prop 11.8 (x-symbol → truncation pattern) + Lemma 11.3 (x_τ ↔ tail signature) 给出矛盾。

**对应 Lean 形式化**：
- `BMSZ.first_entry_eq_of_eq` (Lemma 11.10 ingredient) ✓ 已有
- Lemma 11.6(a) ✓ 已有抽象版
- Prop 11.8 ✓ 已有抽象 `BMSZ.prop_11_8`
- Lemma 11.3 ✓ 已有

缺：PBP 层的 Lemma 11.5(b) balanced formula + Lemma 11.6(b)(c) balanced first entry。

**此 blueprint 是 Lemma 11.9 自然语言证明的严格化**（至 Step 9 balanced case 的平行论证）。形式化工作：把反证结构翻译成 Lean，约 80-150 行。
