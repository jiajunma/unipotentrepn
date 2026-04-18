# Lemma 11.1(a) r₁=1 Case — Explicit Sign/firstColSign Computation

## Lean 形式化
- `lemma_11_1_a_r1_one`, `lemma_11_1_a_r1_one_first_entry` in `CombUnipotent/MYD.lean`

## 目标

补 `lemma_11_1_proof.md` 的 Case 2（$\mathbf{r}_1(\mathcal{O}) = 1$）证明中缺失的 sign、firstColSign 具体计算。

原 blueprint 声称：
> "当 $\mathcal{L}_{\tau'} = (0,0)$ 时，sign = (0,0), fcSign = (0,0)，故 $\text{addp} = p_\tau$"

此处需要严格验证（不能仅靠"显然"）。

## 验证

### Base AC 的 sign 和 firstColSign

对 $\star \in \{B, D\}$ 与 $|\check{\mathcal{O}}| = 0$，base AC 为：
- $\star = D$: $\mathcal{L}_{\tau'} = [(1, [])]$ — 即 **ILS = empty list** `[]`。
- $\star = B^+$ (after descent 下到 $\tilde C$): $\mathcal{L}_{\tau'} = [(1, [])]$ — 也是 empty ILS（C/M/D/C̃ 的 base 都是空 MYD）。

#### ILS.sign 在空 ILS 上

Lean def：`sign` fold over `signAux` applied to each row with index. 对 `[]`，fold 的 base 是 `(0, 0)`。故：
$$\text{sign}([]) = (0, 0) \quad \checkmark$$

#### ILS.firstColSign 在空 ILS 上

同理，fold 的 base 是 `(0, 0)`。故：
$$\text{firstColSign}([]) = (0, 0) \quad \checkmark$$

**两条都由 Lean def + decide 直接验证**（不是仅凭"显然"）。

### 计算 outer lift 的 addp, addn

设 outer lift 源是 $\mathcal{L}_{\tau'} = [(1, [])]$，目标是 $\star$。我们要计算 theta lift 对其中唯一 component `(1, [])` 的作用：

$$\text{addp} = p_\tau - \text{sign}([])_1 - \text{firstColSign}([])_2 = p_\tau - 0 - 0 = p_\tau$$
$$\text{addn} = q_\tau - \text{sign}([])_2 - \text{firstColSign}([])_1 = q_\tau - 0 - 0 = q_\tau$$

Standard case 条件 $\text{addp} \geq 0 \land \text{addn} \geq 0$ = $p_\tau \geq 0 \land q_\tau \geq 0$，对 B/D type signature 总成立（PBP signature ∈ ℕ × ℕ）。

故 theta lift 产出：
- $\star = D$（C→D lift）: `thetaLift_CD [] p_τ q_τ = [augment (p_τ, q_τ) (charTwistCM [] γ)] = [augment (p_τ, q_τ) []] = [[(p_τ, q_τ)]]`
- $\star = B^\pm$（M→B lift）: `thetaLift_MB [] p_τ q_τ = [[(p_τ, q_τ)]]`（同构 pattern）

（`charTwistCM` 对 empty 不变。）

所以 $\mathcal{L}$ 经 outer theta lift = `[(1, [(p_τ, q_τ)])]`，即单个 MYD 有 first entry $(p_\tau, q_\tau)$。

### Outer sign twist ⊗ $(0, \varepsilon_\tau)$

`twistBD E 1 (-1)` 在 odd-index 行（即第 1 行，index 0）将 q 翻转：$(p, q) \mapsto (p, -q)$。偶行不变。

length-1 ILS 只有一行（index 0，length 1，奇）。

**如果 $\varepsilon_\tau = 1$**：twist 生效，得到 $[[(p_\tau, -q_\tau)]]$。
**如果 $\varepsilon_\tau = 0$**：不做 twist，仍是 $[[(p_\tau, q_\tau)]]$。

合起来 first entry = $(p_\tau, (-1)^{\varepsilon_\tau} q_\tau)$。

### 对应 Lean

这一整段恰好就是 Lean 中 `lemma_11_1_a_r1_one` 的证明结构。Lean 通过 `simp [AC.step, AC.base, thetaLift, thetaLift_CD, thetaLift_MB, charTwistCM, augment, twistBD, ...]` 展开来 verify。

**严格程度**：每步都是定义 unfold，没有手写。✓

## 结论

Lemma 11.1(a) r₁=1 case 的自然语言证明现在严格。具体结果：
- Base ILS sign 和 firstColSign 均为 $(0, 0)$（def 直接给出，无需额外论证）
- Outer lift addp = $p_\tau$, addn = $q_\tau$（代数直接）
- Sign twist first-entry 规律：$(p, q) \mapsto (p, (-1)^{\varepsilon_\tau} q)$（Lean `twistBD_first_entry`）

形式化已到位（commit 07fd2c7），Lean 证明与此 blueprint 对应。
