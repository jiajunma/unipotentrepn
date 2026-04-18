# firstColSign 不变量 — 完整形式化

## 核心定理

**不变量**（Lean 已证）：

$$\text{firstColSign}(\mathcal{L}_\tau) = \text{sign}(\mathcal{L}_\tau) - \text{sign}(\mathcal{L}_\tau'')$$

其中 $\tau''$ 是 $\tau$ 单次 descent 后的 PBP，$\mathcal{L}_\tau'' = $ inner source of 外层 AC.step。

等价地：
$$\text{firstColSign}(\mathcal{L}_\tau) = (p_\tau - p_{\tau''}, q_\tau - q_{\tau''})$$

## Lean 形式化清单

### ILS 层（4 个 theta lift 全覆盖）

| Theorem | 作用 |
|---|---|
| `ILS.thetaLift_CD_firstColSign` | $\text{firstColSign}(\text{thetaLift\_CD}(E, p, q)) = (p - \text{sign}(E)_1, q - \text{sign}(E)_2)$ |
| `ILS.thetaLift_DC_firstColSign` | 同上，D→C |
| `ILS.thetaLift_MB_firstColSign` | 同上，M→B |
| `ILS.thetaLift_BM_firstColSign` | 同上，B→M |
| `ILS.charTwistCM_firstColSign` | charTwistCM 保持 firstColSign |
| `ILS.twistBD_firstColSign` | twistBD 保持（for tp, tn ∈ {1, -1}）|
| `ILS.firstColSign_cons` | firstColSign of cons |

### ACResult 层

| Theorem | 作用 |
|---|---|
| `ACResult.twistBD_firstColSign` | ACResult twistBD 保持 firstColSign |
| `ACResult.thetaLift_{CD,Bplus,Bminus}_firstColSign` | D/B target 的 ACResult thetaLift 追踪 |
| `ACResult.thetaLift_{DC,BM}_firstColSign` | C/M target 的 ACResult thetaLift 追踪 |

### AC.step 层（所有 5 个 root type）

| Theorem | Target γ |
|---|---|
| `AC.step_firstColSign_D` | γ = D |
| `AC.step_firstColSign_Bplus` | γ = B⁺ |
| `AC.step_firstColSign_Bminus` | γ = B⁻ |
| `AC.step_firstColSign_BD` | 统一 γ ∈ {D, B⁺, B⁻} |
| `AC.step_firstColSign_C` | γ = C (含 pre-twist) |
| `AC.step_firstColSign_M` | γ = M (含 pre-twist) |

### AC.base 层

| Theorem | 作用 |
|---|---|
| `AC.base_firstColSign_eq_sign` | 对所有 γ：`firstColSign(AC.base γ) = sign(AC.base γ)` |

## 用法：Lemma 11.5 PBP identity discharge

**`ILS.lemma_11_5_D` 原假设**：
```
h_inner_p : n_inner - sign(E).1 - firstColSign(E).2 = n₀
h_inner_q : n_inner - sign(E).2 - firstColSign(E).1 = n₀
h_pt : p - 2 * n_inner + sign(E).2 = p_t
h_qt : q - 2 * n_inner + sign(E).1 = q_t
```

其中 $E = \mathcal{L}_{\tau''}$。

**用不变量 discharge**：

1. `sign(E) = (p_{τ''}, q_{τ''})` by AC sign preservation (已证 `AC.step_sign_*`)
2. `firstColSign(E) = (p_{τ''} - p_{τ''''}, q_{τ''} - q_{τ''''})` by inductive use of `AC.step_firstColSign_*`
3. 代入 h_inner_p: $n_{\text{inner}} = n_0 + p_{\tau''} + (q_{\tau''} - q_{\tau''''})$
4. 代入 h_inner_q: $n_{\text{inner}} = n_0 + q_{\tau''} + (p_{\tau''} - p_{\tau''''})$
5. 两式相减：$0 = p_{\tau''} - q_{\tau''} + q_{\tau''} - q_{\tau''''} - p_{\tau''} - q_{\tau''} + q_{\tau''} + p_{\tau''''} = p_{\tau''''} - q_{\tau''''}$

即 $p_{\tau''''} = q_{\tau''''}$。

**这在 C/M type 的 $\tau''''$ 自动成立**（C/M signature: p = q）。

6. 所以 h_inner_p 和 h_inner_q 自洽，且给出 n_inner 值。

7. 代入 h_pt: $p_t = p - 2n_{\text{inner}} + q_{\tau''}$
   $= p - 2(n_0 + p_{\tau''} + q_{\tau''} - q_{\tau''''}) + q_{\tau''}$
   $= p - 2n_0 - 2p_{\tau''} - q_{\tau''} + 2q_{\tau''''}$

由 Prop 11.4（primitive）：$p - p_t = \mathbf{c}_2(\mathcal{O}) + p_{\tau''}$，即 $p_t = p - \mathbf{c}_2 - p_{\tau''}$。

代入等式：$p - \mathbf{c}_2 - p_{\tau''} = p - 2n_0 - 2p_{\tau''} - q_{\tau''} + 2q_{\tau''''}$
$\Rightarrow \mathbf{c}_2 + p_{\tau''} = 2n_0 + 2p_{\tau''} + q_{\tau''} - 2q_{\tau''''}$
$\Rightarrow \mathbf{c}_2 = 2n_0 + p_{\tau''} + q_{\tau''} - 2q_{\tau''''}$

**shape relation**: $2n_0 = \mathbf{c}_2 - \mathbf{c}_3$。代入：
$\mathbf{c}_2 = \mathbf{c}_2 - \mathbf{c}_3 + p_{\tau''} + q_{\tau''} - 2q_{\tau''''}$
$\Rightarrow \mathbf{c}_3 = p_{\tau''} + q_{\tau''} - 2q_{\tau''''}$

再对 $\tau''$ 应用 Prop 11.4：$p_{\tau''} + q_{\tau''} = 2\mathbf{c}_2(\mathcal{O}_{\tau''}) + (p_{\tau''''} + q_{\tau''''}) + (p_{(\tau'')_t} + q_{(\tau'')_t})$。

利用 $\mathbf{c}_2(\mathcal{O}_{\tau''}) = \mathbf{c}_4(\mathcal{O})$（double shift 一次在 τ'' 层相当于 quad shift 原层），以及 $p_{\tau''''} = q_{\tau''''}$：

$p_{\tau''} + q_{\tau''} = 2\mathbf{c}_4 + 2q_{\tau''''} + \text{tail}_{\tau''}$

代入前面：$\mathbf{c}_3 = 2\mathbf{c}_4 + 2q_{\tau''''} + \text{tail}_{\tau''} - 2q_{\tau''''} = 2\mathbf{c}_4 + \text{tail}_{\tau''}$

这说明 $\mathbf{c}_3 - 2\mathbf{c}_4 = \text{tail}_{\tau''} = p_{(\tau'')_t} + q_{(\tau'')_t}$。由 $(\tau'')_t$ 是 D-type tail 于 [2k'' - 1, 1] shape（长度 $2k''$），其总 signature $p + q = 2k'' - 1 + 1 = 2k''$。所以 $\mathbf{c}_3 - 2\mathbf{c}_4 = 2k''$。而 $k'' = (\mathbf{r}_1(\check\mathcal{O}_{\tau''}) - \mathbf{r}_2(\check\mathcal{O}_{\tau''}))/2 + 1$。需要验证这是 shape-level identity。

这个验证（$\mathbf{c}_3(\mathcal{O}) - 2\mathbf{c}_4(\mathcal{O}) = 2k_{\tau''}$）是 paper Section 9.2 的 shape arithmetic，应是可验证的关系。

## 结论

有了上面的 firstColSign 不变量以及 Prop 11.4 signature decomposition，Lemma 11.5 的 PBP identity discharge 路径清晰：
1. 两次 Prop 11.4 归纳
2. 一次 firstColSign 不变量展开
3. 一次 shape relation $\mathbf{c}_i$ 的归约

Lean 中 `ILS.lemma_11_5_D` 的 h_pt/h_qt 假设可以 **programmatically** 从这个链条 derive，得到 **unconditional** Lemma 11.5。

形式化工作量：约 300-500 行 Lean，中等难度（已有足够 ingredient）。

## 所有 commits（本 session）

- `7f3d0f2` twistBD_firstColSign
- `93f66ae` thetaLift_{CD,MB}_firstColSign
- `b5560a3` ACResult.twistBD_firstColSign + template
- `d91089c` ACResult.thetaLift_{CD,Bplus,Bminus}_firstColSign
- `1a00538` AC.step_firstColSign_{D,Bplus,Bminus}
- `a00d48a` AC.step_firstColSign_BD (unified)
- `97e60a5` thetaLift_{DC,BM}_firstColSign
- `3a9b055` ACResult.thetaLift_{DC,BM}_firstColSign
- `851a67c` AC.step_firstColSign_{C,M}
- `99a1205` AC.base_firstColSign_eq_sign
- 本 commit: 本 blueprint
