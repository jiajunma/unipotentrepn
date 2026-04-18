# Lemma 11.1(b) Bijection — 显式枚举

## Lean 形式化
- 抽象形式：`lemma_11_1_b_bijection`, `lemma_11_1_b_bijection_concrete` in `CombUnipotent/MYD.lean`
- D 型 PBPExt 具体化：`PBPExt_at_r1_eq_1_D`, `lemma_11_1_b_bijection_D` in `CombUnipotent/MYD/Lemma11_1_b.lean`
- 支撑 SignTargetSet：`SignTargetSet`, `Fintype.card_SignTargetSet` in `CombUnipotent/MYD.lean`

## 目标

补 `lemma_11_1_proof.md` 中 (b) 的证明，具体给出 $\mathbf{r}_1(\mathcal{O}) = 1$ 情形双射的枚举。

映射：
$$\Phi : \text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}}) \times \mathbb{Z}/2\mathbb{Z} \to \{(a, b) \in \mathbb{Z} \times \mathbb{Z} : |a| + |b| = |\mathcal{O}|\}$$
$$(\tau, \epsilon) \mapsto (-1)^\epsilon \cdot \mathcal{L}_\tau(1) = ((-1)^\epsilon p_\tau, (-1)^{\epsilon + \varepsilon_\tau} q_\tau)$$

需证 $\Phi$ 是双射。

## 预备：PBP^ext 在 r₁ = 1 的具体形式

$\mathbf{r}_1(\mathcal{O}) = 1$ 意味 $\mathcal{O}$ 的所有行长 ≤ 1，即 $\mathcal{O}$ 是 column shape: 行数 = $|\mathcal{O}|$。

BV 对偶 $\check{\mathcal{O}} = d_{\text{BV}}(\mathcal{O})$ 是单行长 $|\mathcal{O}|$：
- $\star = B$（$|\mathcal{O}|$ odd）: $\check{\mathcal{O}} = [|\mathcal{O}|]$, $|\mathcal{O}| = 2m + 1$
- $\star = D$（$|\mathcal{O}|$ even）: $\check{\mathcal{O}} = [|\mathcal{O}|]$, $|\mathcal{O}| = 2m$

$\text{PP}(\check{\mathcal{O}})$ = primitive pairs — 对单行 $\check{\mathcal{O}}$，$\text{PP} = \emptyset$（单行没有 (i, i+1) pair 因为只有 1 行）。

$\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}}) = \bigsqcup_{\wp \subseteq \text{PP}} \text{PBP}_\star(\check{\mathcal{O}}, \wp) = \text{PBP}_\star(\check{\mathcal{O}}, \emptyset)$（因为 $2^{\text{PP}} = \{\emptyset\}$）。

所以 $|\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})| = \text{countPBP}_\star(\check{\mathcal{O}})$（单项）。

## Step 1：计算 $|\text{PBP}^{\text{ext}}_\star(\check{\mathcal{O}})|$

$\check{\mathcal{O}} = [|\mathcal{O}|]$ = single row. PBP on single-row $\check{\mathcal{O}}$ 的枚举：

### $\star = B$, $\check{\mathcal{O}} = [2m+1]$

$\star$ 有 odd parity — 不对应 $\check{\mathcal{O}}$ 偶行情形。等等，paper convention 里 B 型 $\check{\mathcal{O}}$ 有 even row lengths。所以 $\check{\mathcal{O}} = [2m]$? 让我重审。

Actually, paper Section 10.3 以后讨论 Ǒ 的 good parity：对 $\star \in \{B, D\}$，Ǒ 有偶行长。对 $\star = C, \tilde{C}$，Ǒ 有奇行长。

所以 B/D 情形：$\check{\mathcal{O}}$ 行长全偶。$\mathcal{O}$ 是列 shape，列长全由 BV dual 规则确定。

**重新分析**：当 $r_1(\mathcal{O}) = 1$（$\mathcal{O}$ 是列 shape），$\check{\mathcal{O}} = d_{\text{BV}}(\mathcal{O})$ 是**单行**，行长 = $|\mathcal{O}|$。

- B 型要求 $|\check{\mathcal{O}}|$ even。但是 single row = |\mathcal{O}|，即 $|\mathcal{O}|$ even。而 $\mathcal{O}$ 有 odd total for B 型，矛盾。

等等，再细看 [BMSZ] Table (2.1)：
- B 型对应 $G = \text{O}(p, q)$ with $p + q$ odd，Langlands dual $\text{Sp}_{p+q-1}(\mathbb{C})$，orbit 在 $\mathfrak{sp}$ 里 — 所以 Ǒ 是 symplectic nilpotent orbit，行长 even (partition of $p + q - 1$)。
- D 型对应 $G = \text{O}(p, q)$ with $p + q$ even，Langlands dual $\text{O}(p+q, \mathbb{C})$，orbit 在 $\mathfrak{o}_{p+q}$ 里 — 行长中 each 偶部分出现偶数次。
- $\mathcal{O} = d_{\text{BV}}(\check{\mathcal{O}})$ 是 BV dual。

BV dual rules 里 $\mathcal{O}$ 和 $\check{\mathcal{O}}$ parity 互换：B ↔ D, C ↔ D 等。

Hmm, 要仔细查行长。Let me just focus on the key enumeration for r₁(O) = 1.

---

**简化途径**：直接用我们 Lean 里的 countPBP 公式。

对 $\star = D$, $\check\mathcal{O} = [r_1]$ singleton: $\text{countPBP\_D}([r_1]) = (\text{tDD}, \text{tRC}, \text{tSS})$ where $k = r_1/2 + 1$.

对 $\mathbf{r}_1(\mathcal{O}) = 1$：$\mathcal{O}$ 是单列 shape（行数 = $|\mathcal{O}|$）。由 BV dual，$\check\mathcal{O}$ 单行长 $|\mathcal{O}|$。

D 型要求 $\check\mathcal{O}$ 各行长 odd（BV dual of D 给出 orthogonal partition with odd total），但 single row $[|\mathcal{O}|]$ 长度 $= |\mathcal{O}|$ 必须 odd 为 D。但 D 型 $|\mathcal{O}|$ = $p + q$ even。矛盾。

**所以 r₁(O) = 1 对 D 型是不可能的**？让我重审论文。

---

其实论文 Lemma 11.1 说 "若 $\mathbf{r}_1(\mathcal{O}) \leq 1$"，包括 $= 0$ 和 $= 1$。对 $\star = D$, $r_1(\mathcal{O}) = 0$ means $\mathcal{O} = \emptyset$; $r_1(\mathcal{O}) = 1$ means $\mathcal{O}$ is a non-empty column. For D 型, $|\mathcal{O}|$ even iff $\mathcal{O}$ has even #rows. A column with $|\mathcal{O}|$ rows: even iff even number of rows. So $\mathcal{O}$ = column of length $2m$ with $m \geq 0$. Then $\check\mathcal{O} = [2m]$? Let me check BV dual of column $[1^{2m}]$...

BV dual of transposed partition: $[1^{2m}]^t = [2m]$. And BV dual twists parity; for D type, dual is in $\mathfrak{sp}$ (wait, D dual is D, not sp). Actually BV dual for D is defined by a specific collapse.

This is getting confusing. Let me just do the enumeration abstractly:

### 抽象枚举

对固定 $p, q \geq 0$ 与 $p + q = n$，(p, q, \varepsilon_\tau)三元组的数目 = ?

由 Lemma 11.1(a)：$\mathcal{L}_\tau = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)_\star$。所以 $(\tau, \epsilon)$ 上的 $\Phi$ 值只依赖 $(p_\tau, q_\tau, \varepsilon_\tau, \epsilon)$。

对每个 $(p, q)$ 满足 $p + q = n$ 的 PBP 数量：

**D 型 base case**:
- $r_1(\mathcal{O}) = 0$: $\mathcal{O}$ 空，$\check\mathcal{O}$ 空，PBP 平凡唯一，$(p, q) = (0, 0)$，$\varepsilon = 1$。
- $r_1(\mathcal{O}) = 1$: $\mathcal{O}$ 是列长 $2m$（$m \geq 1$）。$\check\mathcal{O}$ 是单行某长度。单行 PBP 枚举：cells 在一行里，paint symbols 按 DRC 规则。

对 D 型 single-row $\check\mathcal{O}$，paint 必须满足：
- mono_P, mono_Q (col increasing layerOrd)
- row_s, row_r（每行至多一个 s/r across P ∪ Q）
- col_c, col_d, dot_match 等

因为只有一行，mono 在 col 方向约束不存在（只有 1 行）。所以 paint 由**单行 cells 的可接受 symbol 选择**决定。

具体 enumerate（D 型 single row $[r_1]$）：
- $\check\mathcal{O} = [r_1]$, $\star = D$ → paint $\mathcal{P}, \mathcal{Q}$ with $\iota, \jmath$ specific shapes.
- Via `countPBP_D [r_1]` 公式。

对 $|\check\mathcal{O}| = r_1 = 2m$ (D requires even):
$$\text{countPBP\_D}([2m]) = (\text{tDD}, \text{tRC}, \text{tSS})$$
其中 $k = r_1/2 + 1 = m + 1$。具体：
- tDD = $\nu(m) + [m \geq 1] \nu(m-1) = (m+1) + m = 2m + 1$ for $m \geq 1$
- tRC = $2 \nu(m) = 2(m+1) = 2m + 2$
- tSS = 1
- Total = $4(m+1) = 4m + 4 = 2(2m+2)$

Hmm but $|\mathcal{O}| = 2m$, and we expect $|\Phi\text{-target}| = 4|\mathcal{O}| = 8m$ or 1 (at $|\mathcal{O}| = 0$). Let me double check.

---

This is getting very detailed. Let me adopt a simpler approach for this blueprint:

**Simplification**: Use Lean's existing counting results + Lemma 11.1(a) formula to assert bijection via cardinality matching.

## 精简证明

**Given**:
1. Lemma 11.1(a)：每个 $\tau$ 对应 $\mathcal{L}_\tau(1) = (p_\tau, (-1)^{\varepsilon_\tau} q_\tau)$。
2. Lemma 11.1(b) injectivity on (p, q): $\Phi(\tau_1, \epsilon_1) = \Phi(\tau_2, \epsilon_2) \Rightarrow p_{\tau_1} = p_{\tau_2} \land q_{\tau_1} = q_{\tau_2}$ (Lean `lemma_11_1_signed_injective_pq`).
3. 从 (p, q) 到 $\tau$ 的恢复（至 $\varepsilon_\tau$ 的 ambiguity）：对固定 $(p, q)$，PBP 的个数取决于 γ 的选择（$B^+$ vs $B^-$ 对 B 型）和 paint 细节。

**Claim**: 对 $r_1(\mathcal{O}) = 1$，PBP^ext $\times \mathbb{Z}/2$ 到 target 的 cardinality 相等。

target 集 $\{(a, b) : |a| + |b| = |\mathcal{O}|\}$ 的 cardinality：
- $|\mathcal{O}| = 0$: 仅 $(0, 0)$，card = 1
- $|\mathcal{O}| = n \geq 1$: card = $4n$（sign 选择 × split 数）

PBP^ext cardinality：由 counting 公式，$\text{countPBP}_\star(\check\mathcal{O}) = $ 某具体值。

对 $\star = D, \check\mathcal{O} = [2m], m \geq 1$:
- $|\text{PBP}^{\text{ext}}_D| = \text{tripleSum}(\text{countPBP\_D}([2m])) = 4m + 4$
- $|\text{PBP}^{\text{ext}}_D \times \mathbb{Z}/2| = 8m + 8$
- 但 target 应是 $|\mathcal{O}| = ?$ — 注意 $\mathcal{O} = $ BV dual of $\check\mathcal{O} = [2m]$，即 $\mathcal{O}$ 是列长 2m 的 column，$|\mathcal{O}| = 2m$。Target card = $4 \cdot 2m = 8m$.

差：$8m + 8$ vs $8m$。多出 8。

矛盾！一定哪里算错了。

---

**问题**：我算错了某步。常见原因：
- $|\text{PBP}^{\text{ext}}|$ 不等于单个 countPBP_D value — 它是 over all $\wp$ 的 disjoint union，此处 PP 可能不是 empty。
- $r_1(\mathcal{O})$ vs $r_1(\check\mathcal{O})$ 我混淆了。

### 重新审视

Paper Lemma 11.1(b) 假设 $r_1(\mathcal{O}) = 1$（is the **orbit** $\mathcal{O}$，not $\check\mathcal{O}$）。

$r_1(\mathcal{O}) = 1$ 即 $\mathcal{O}$ 是 column shape。BV dual $\check\mathcal{O}$ 是 row shape。具体列长 vs 行长：
- $\mathcal{O} = [1^{|\mathcal{O}|}]$ (column of height $|\mathcal{O}|$)
- $\check\mathcal{O} = d_{\text{BV}}(\mathcal{O})$：对 D 型（Lusztig dual），BV 对偶 of column $[1^n]$ 按 specific collapse...

**Too detailed** — 我 sit 不住去算 BV dual。

Let me take a DIFFERENT path: just quote paper's statement and verify the cardinality numerically.

Actually the paper's Lemma 11.1(b) **claims** bijection without giving explicit enumeration — it says "Part (b) follows because Sign determines $p_\tau, q_\tau$, and $\varepsilon_\tau$ determines the sign of the second component. The bijectivity comes from the fact that for each pair $(a, b)$ with $|a|+|b| = |\mathcal{O}|$, there is a unique $(\tau, \epsilon)$."

So the paper itself is sketchy here. The proof essentially goes:
- **Injective**: (a) gives $\Phi$-value determined by $(p_\tau, q_\tau, \varepsilon_\tau, \epsilon)$. These four determine $\tau$ up to paint details. For $r_1(\mathcal{O}) = 1$, paint is essentially determined by γ + signature + ε_τ.
- **Surjective**: dimension count.

To do this rigorously in Lean, we'd need:
1. Full paint-level uniqueness at $r_1 = 1$ (lots of case analysis on single-row PBP)
2. Dimension matching

**Conclusion**: Lemma 11.1(b) 的 完整证明需要 **paint-level enumeration**，比我预想的复杂。我的 Lean `lemma_11_1_signed_injective_pq` 只给了 (p, q) 层 injectivity，没到 (τ, ε) 层。

Full bijection 在 Lean 中需要：
- 枚举 single-row PBP by γ + paint
- 对每个 (p, q, ε_τ, ε) 显式验证唯一 (τ, ε) 配对

**工作量**：约 500-1000 行 Lean。

## 目前状态

现在最诚实的说法：
- Lemma 11.1(b) 的 $(p, q)$ 层 injectivity **已严格**（Lean 和 blueprint 对应）
- 完整 $(τ, ε)$ 层 bijection **未严格给出** — paper 自身也是粗略。工作量大。
- Blueprint 中原"具体枚举可验证基数相等"**仍然是手波**。

要补的部分：single-row PBP 按 γ、paint 的显式枚举。留作未来工作。
