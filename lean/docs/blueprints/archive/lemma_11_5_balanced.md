# Lemma 11.5(b) — Balanced Case

## 陈述

设 $\star \in \{B, D\}$ 且 $\mathbf{r}_2(\check\mathcal{O}) = \mathbf{r}_3(\check\mathcal{O})$ (balanced)。则

$$\mathcal{L}_\tau = \mathcal{L}_{\tau, +} + \mathcal{L}_{\tau, -} \quad (11.12)$$

其中
$$\mathcal{L}_{\tau, +} := T^{\gamma_\tau}(\mathcal{L}_{\tau''}^+ \circledast (0, 0)) \oplus (p_{\tau_t}, q_{\tau_t} - 1) \otimes (0, \varepsilon_\tau) \quad (11.13)$$
$$\mathcal{L}_{\tau, -} := T^{\gamma_\tau}(\mathcal{L}_{\tau''}^- \circledast (0, 0)) \oplus (p_{\tau_t} - 1, q_{\tau_t}) \otimes (0, \varepsilon_\tau) \quad (11.14)$$

## 背景：balanced case 的 descent 结构

$\mathbf{r}_2 = \mathbf{r}_3 > 0$：第二和第三行长相等。此时 descent map (11.6) 不是 bijective 而是 injective，像有 restricted form。

由 Prop 11.4(b): Sign $(\tau) = (\mathbf{c}_2(\mathcal{O}) - 1, \mathbf{c}_2(\mathcal{O}) - 1) + \text{Sign}(\tau'') + \text{Sign}(\tau_t)$。

注意这里 $-1$ 的扰动 vs primitive case。

## 证明

用归纳公式 (11.2) 两次：

**Outer step**（$\star \in \{B, D\}$，lift $\star' \to \star$, $\star' \in \{C, \tilde C\}$）：
$$\mathcal{L}_\tau = \hat\theta^{s_\tau, \mathcal{O}}_{s_{\tau'}, \mathcal{O}'}(\mathcal{L}_{\tau'}) \otimes (0, \varepsilon_\tau) \quad (11.2 \text{ for } \star \in \{B, D\})$$

**Inner step**（$\star' \in \{C, \tilde C\}$, lift $\star'' \to \star'$, $\star'' = \star$）：
$$\mathcal{L}_{\tau'} = \hat\theta^{s_{\tau'}, \mathcal{O}'}_{s_{\tau''}, \mathcal{O}''}(\mathcal{L}_{\tau''} \otimes (\varepsilon_{\wp'}, \varepsilon_{\wp'})) \quad (11.2 \text{ for } \star' \in \{C, \tilde C\})$$

### 关键差异：balanced case 的 $\delta' = 1$

Theta lift (9.30) for $\star' \in \{C, \tilde C\}$ 形式：
$$\hat\theta(E) = \sum_{j=0}^{\delta'} \Lambda_{(j, \delta' - j)}(E \oplus (n_0', n_0'))$$

其中 $\delta' = \mathbf{c}_1(\mathcal{O}') - \mathbf{c}_2(\mathcal{O}')$。

**Primitive case $\mathbf{r}_2 > \mathbf{r}_3$**: $\delta' = 0$（因为 $\mathbf{c}_i(\mathcal{O}') = \mathbf{c}_{i+1}(\mathcal{O})$ 且 primitive 下 $\mathbf{c}_2(\mathcal{O}) > \mathbf{c}_3(\mathcal{O})$... wait 需仔细对照）。$\Lambda_{(0,0)}$ = identity，所以 $\hat\theta(E) = E \oplus (n_0, n_0)$ 单项。

**Balanced case $\mathbf{r}_2 = \mathbf{r}_3$**: $\delta' = 1$（对应 $\mathbf{r}_3 - \mathbf{r}_2$ jump 为 0，descended 后差为 1 step）。$\sum_{j=0}^{1} \Lambda_{(j, 1-j)} = \Lambda_{(0, 1)} + \Lambda_{(1, 0)}$。

Expand：
$$\hat\theta(E) = \Lambda_{(1, 0)}(E \oplus (n_0, n_0)) + \Lambda_{(0, 1)}(E \oplus (n_0, n_0))$$

### 代入 outer step

$\mathcal{L}_{\tau'}$ 分成两项（balanced）：
$$\mathcal{L}_{\tau'} = \Lambda_{(1, 0)}(F) + \Lambda_{(0, 1)}(F)$$
其中 $F = \mathcal{L}_{\tau''} \otimes (\varepsilon_{\wp'}, \varepsilon_{\wp'}) \oplus (n_0, n_0)$。

代入 outer:
$$\mathcal{L}_\tau = \hat\theta^{s_\tau, \mathcal{O}}_{s_{\tau'}, \mathcal{O}'}(\Lambda_{(1, 0)}(F) + \Lambda_{(0, 1)}(F)) \otimes (0, \varepsilon_\tau)$$

Outer theta lift (9.29) 对 B/D 是单项 $T^\gamma(\cdot \oplus (p_0, q_0))$（no $\Lambda$ split）。注意 $\hat\theta$ 对 sum 是 linear：
$$\mathcal{L}_\tau = [T^{\gamma_\tau}(\Lambda_{(1, 0)}(F) \oplus (p_t^+, q_t^+)) + T^{\gamma_\tau}(\Lambda_{(0, 1)}(F) \oplus (p_t^-, q_t^-))] \otimes (0, \varepsilon_\tau)$$

其中 $(p_t^+, q_t^+)$ 和 $(p_t^-, q_t^-)$ 是两项各自的 outer augmentation parameters。

### Claim：$(p_t^+, q_t^+) = (p_{\tau_t}, q_{\tau_t} - 1)$ 以及 $(p_t^-, q_t^-) = (p_{\tau_t} - 1, q_{\tau_t})$

这是 balanced case 的关键签名 identity，类比 primitive case 的 Lemma 11.5(a) identity。

**证明思路**：
- $\Lambda_{(1, 0)}(F)$ 在 first entry 上减 $(1, 0)$
- sign, firstColSign 受 first entry 的影响通过 (9.10), (9.12) 定义显式可计算
- 对 $\Lambda_{(1, 0)}(F)$: sign 减少 1 in first component（行 index 0 = odd row, contributes $(|p|, |q|)$ to sign direct）；firstColSign 减少 1 in "swapped" position
- 代入 outer addp/addn 公式，得到 $(p_{\tau_t}, q_{\tau_t} - 1)$ 等（for $\Lambda_{(1,0)}$ 分支）
- 类似 $\Lambda_{(0, 1)}$ 分支给 $(p_{\tau_t} - 1, q_{\tau_t})$

更精确细节需要 firstColSign 在 $\Lambda$ 下的 tracking，类比 primitive case 的 Lemma 11.5(a) 论证。

### Claim：$\Lambda_{(1, 0)}(F) = \mathcal{L}_{\tau''}^+ \circledast (0, 0)$（up to first entry)

$F = \mathcal{L}_{\tau''} \otimes \text{twist} \oplus (n_0, n_0)$. $\Lambda_{(1,0)}$ on $F$：如果 first entry of $F$ first-comp $\geq 1$, subtract 1; else discard.

$F$ first entry = $(n_0, n_0)$ (由 augment). 若 $n_0 \geq 1$: $\Lambda_{(1, 0)}(F)$ 保留，first entry = $(n_0 - 1, n_0)$。

Hmm 这个不完全符合 "$\mathcal{L}_{\tau''}^+ \circledast (0, 0)$" 的形式。让我重审。

实际上 (11.13) 说 $\mathcal{L}_{\tau, +} = T^{\gamma_\tau}(\mathcal{L}_{\tau''}^+ \circledast (0, 0)) \oplus (p_{\tau_t}, q_{\tau_t} - 1) \otimes \text{sign twist}$.

$\mathcal{L}_{\tau''}^+ = \Lambda_{(1, 0)}(\mathcal{L}_{\tau''})$。Augment $(0, 0)$ 在前面得到新 MYD，first entry $(0, 0)$，second entry = $\mathcal{L}_{\tau''}^+$ 的 first entry 等。

对比：我们从 outer step 得到 $T^\gamma(\Lambda_{(1, 0)}(F))$ 形式，而 paper 给 $T^\gamma(\mathcal{L}_{\tau''}^+ \circledast (0, 0))$ 形式。两者相同当：

$\Lambda_{(1, 0)}(F) = \Lambda_{(1, 0)}(\mathcal{L}_{\tau''} \otimes \text{twist} \oplus (n_0, n_0))$

vs

$\mathcal{L}_{\tau''}^+ \circledast (0, 0) = \Lambda_{(1, 0)}(\mathcal{L}_{\tau''}) \circledast (0, 0)$

我需要验证：$\Lambda_{(1, 0)}(M \oplus (n_0, n_0)) = \Lambda_{(1, 0)}(M) \circledast (0, 0)$ 当 $n_0 = 1$（特定情况）or 更一般的关系。

这涉及 $\Lambda$ 和 $\oplus$ 交换律。Paper 中有 eq (9.28) "note that $(\tau_t)_t = \tau_t$" 暗示 $\Lambda$ 在特定情况与 augment 交换。

具体细节需要 [BMSZ] eq 9.18-9.19 + Section 11.3 的 $\Lambda^\pm$ 定义。

## 结论

Lemma 11.5(b) 的证明骨架已写出。具体 chain：
1. Inner step (11.2) 给 $\mathcal{L}_{\tau'} = \Lambda_{(1,0)}(F) + \Lambda_{(0,1)}(F)$ (balanced $\delta' = 1$)
2. Outer step 对 sum 是线性，两项分别 augment 得到 $\mathcal{L}_{\tau, \pm}$
3. 每项 augment 参数为 balanced-case signature identity 给出 $(p_{\tau_t}, q_{\tau_t} \mp 1)$

**缺口**：
- Step 2 中 $(p_t^\pm, q_t^\pm)$ 公式的精确推导（类 Lemma 11.5(a) 的 signature identity，需 firstColSign tracking）
- $\Lambda$ 和 $\oplus$ augment 的交换关系具体化

这两点也是 Lemma 11.5 primitive case 证明中的同类缺口。一旦 Lemma 11.5(a) 的 firstColSign PBP identity 严格证出，(b) 的类似结构也可走通。

## 形式化路线

1. 先补 Lemma 11.5(a) 的 PBP identity（`lemma_11_5_PBP_identity.md` 中列出）
2. 再做 balanced case 的类似推导（此 blueprint）
3. 得到 `ILS.lemma_11_5_D_balanced` 定理，签名类 `ILS.lemma_11_5_D`
