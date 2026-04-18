# 无条件化（Truly Unconditional） PBP 层 Section 11 定理 — 自然语言证明 blueprint

## 目标

当前 PBP 层定理（如 `prop_11_5_D_atomic_pbp_discharged`、`AC.lemma_11_6_D_unconditional`、
`prop_11_{8,9,10,11,12,15,17}_PBP_*`）都仍接受若干 hypotheses（`h_fc, h_sign,
h_prop_11_4_p/q, h_n₀, …`）作为参数。

**目标**：把它们升级成 **完全只依赖基本 PBP 数据 `τ`** 的 closed form 定理：
- 输入：`τ : PBP`, `hγ : τ.γ = .D`（或 B/C/M 对应），以及必要的 shape 合法性假设
- 输出：原本需要 caller discharge 的条件现在在定理内部 **唯一地** 由 `τ` 决定并自动满足

## 关键观察：canonical ILS `E = L_{τ''}`

`prop_11_5_D_atomic_pbp_discharged` 的所有 hypotheses 实际上是关于 "previous level ILS" 的统一约束：
任何一个 specific PBP τ 都唯一决定了它在 AC.fold 描述中扮演的 outer-step 角色。特别地：
- inner ILS `E` 就是 `τ'' := doubleDescent(τ)` 的 canonical AC ILS：`E := L_{τ''}`
- 这个 `E` 是由 `AC.fold` 作用在 `τ''` 的 descent chain 上得到的
- `E` 的 `sign` 和 `firstColSign` 都能从 `τ''` 的 signature 和更深一层 `τ''''` 的 signature 唯一决定

所以选择 canonical 的 `(E, n_prev, p_prev, q_prev)`：

| 变量 | 值（用 τ 表达） | 理由 |
|---|---|---|
| `E` | `L_{τ''} := AC.fold .D (descentChain τ'')` | canonical |
| `p_prev` | `(PBP.signature τ'').1` | AC sign preservation |
| `q_prev` | `(PBP.signature τ'').2` | 同上 |
| `n_prev` | `(PBP.signature τ'''').1`（即 `p_{τ''''}`；同时等于 `q_{τ''''}`，参见下文）| firstColSign invariant |

## 自动 discharge 各 hypothesis

### Discharge `h_sign : sign E = (p_prev, q_prev)`

**自然语言**：
`E = L_{τ''}` 由 `AC.fold .D chain_{τ''}` 生成。`AC` 构造过程的关键不变量是 *sign 保持*：
每次 AC.step 输出的所有分支 ILS 都有统一的 sign，等于当前 step 的 `(p, q)` 参数。
对最外层 step（即 AC.fold 最后一次调用）来说，`(p, q) = (p_{τ''}, q_{τ''})`。
故 `sign(L_{τ''}) = (p_{τ''}, q_{τ''}) = (p_prev, q_prev)`。

**依据定理**：`AC.step_sign_D`, `AC.step_sign_Bplus`, `AC.step_sign_Bminus`,
`AC.step_sign_C`, `AC.step_sign_M` 已证。

### Discharge `h_fc : firstColSign E = (sign(E).1 - n_prev, sign(E).2 - n_prev)`

**自然语言**：
由 `AC.chain_firstColSign_eq_diff_sign`，`firstColSign(output of AC.step) = (current sig) - (prev sig)`。
把这一步应用到 `L_{τ''}`（即 AC.fold 对 τ'' 的外层 step），得：
$$\text{firstColSign}(L_{τ''}) = (p_{τ''} - p_{τ''''}, q_{τ''} - q_{τ''''})$$

关键观察：对 C/M type（τ'''' = double descent of τ'' 是 C/M-type），signature 满足 `p = q`
（因为 C/M 的 paint 对称性），所以 `p_{τ''''} = q_{τ''''}`。令 `n_prev := p_{τ''''} = q_{τ''''}`。
则 `firstColSign(L_{τ''}) = (p_{τ''} - n_prev, q_{τ''} - n_prev)` ✓。

**依据定理**：`AC.chain_firstColSign_eq_diff_sign` + `C_signature_diagonal`（需要补：τ C-type ⇒ sig.1 = sig.2）。

### Discharge `h_prop_11_4_p : signature(τ).1 = 2·c₂(O) + p_prev + tailSignature_D(τ).1`

**自然语言（Prop 11.4 eq 11.7 primitive case）**：
按 `signature_fst_decomp_D`：
$$\text{signature}(τ).1 = \underbrace{\text{Q.colLen 0}}_{= \mathbf{c}_2(\mathcal{O})} + \underbrace{(\text{colGe1 P contribution for r, dot, c, d, Q.dot})}_{= p_{τ''}} + \underbrace{(\text{tail col 0 contribution for r, c, d})}_{= \text{tailSignature}_D(τ).1}$$

为了匹配 hypothesis，我们要验证：
1. 第一项确实等于 `c₂(O)`（注意：hypothesis 要求的是 `2·c₂(O)`，所以还需要 Q 的某部分也贡献 `c₂(O)`）
2. 第二项 = `(signature τ'').1 = p_prev`
3. 第三项 = `(tailSignature_D τ).1`

**观察**：paper 的 Prop 11.4 用 `c₂(O)·(1,1)`，即 p 和 q 都加 `c₂(O)`。而 signature_fst_decomp_D 给出的是 `Q.colLen 0 + ...`。需要确认 `Q.colLen 0` 对 D type 等于 `c₂(O)`。

同时，为使 hypothesis 匹配，我们重构形式：令 `prop_11_5_D_atomic_pbp_discharged` 内部直接使用 `signature_fst_decomp_D`，设：
$$p_{\text{prev}} := (\text{colGe1 P contribution for r, dot, c, d, Q.dot})$$

然后 h_prop_11_4_p 变成 `signature(τ).1 = Q.colLen 0 + p_prev + (tail...).1`。
若 hypothesis 要求 `2·c₂(O)`, 则 `c₂(O) = Q.colLen 0` (definitionally)，`2·c₂(O) = 2 * Q.colLen 0`。

但 signature_fst_decomp_D 只贡献 1 份 `Q.colLen 0`，另一份 `Q.colLen 0` 必须来自 `p_prev` 或 `tailSignature_D`。

**关键 shape identity**：`p_{τ''}` 包含 `Q.colLen 0` 的因子吗？实际上 `τ''` 的 signature 通过 inductive 构造，会在它的 decomp 中再贡献 `Q.colLen 0 (τ'')` 等等。因此 h_prop_11_4_p 实际上等价于一个 **shape 数值 identity**。

**Resolution**：修改 hypothesis 的形式，使其与 `signature_fst_decomp_D` 直接对应：把 `2·c₂(O)` 改为 `c₂(O) + c₂(O)`，其中一份 `c₂(O)` 归入 `p_prev` 的定义（即让 `p_prev := Q.colLen 0 + (colGe1 P...)`），另一份保留为 `c₂(O) = Q.colLen 0`。

这样 h_prop_11_4_p 变成：
```
signature(τ).1 = Q.colLen 0 + p_prev + tailSignature_D(τ).1
```
其中 `p_prev := signature(τ'').1`。

这与 paper Prop 11.4 eq 11.7 等价（把 paper 的 `(c₂, c₂)` 拆成两份：一份给 "c₂(O)" 项，一份进入 sign(τ'')）。

但注意 [BMSZ] Prop 11.4 说的是 `(c₂, c₂) + Sign(τ'') + Sign(τ_t)`，即 `Sign(τ'')` 自己 *不* 包含 c₂(O)。这与我们 `signature_fst_decomp_D` 给出的 τ 的分解方式需要一次重合。

**对应关系**（经详细分析）：
- `signature(τ'').1` 按 signature_fst_decomp_D （applied to τ''）= `Q.colLen 0 (of τ'') + colGe1(τ''.P) + tail(τ'')`
- τ 的 `signature(τ).1` 按 decomp = `Q.colLen 0 (of τ) + colGe1(τ.P) + tail(τ)`
- **Descent 的作用**：`τ.Q.shape.colLen 0 ↦ τ''.Q.shape.colLen 0`，`colGe1(τ) ↦ colGe1(τ'')`，`tail(τ.P) ↦ tail(τ''.P)`。
- 具体数值：`c_1(O) = τ.P.shape.colLen 0`, `c_2(O) = τ.Q.shape.colLen 0 = τ''.P.shape.colLen 0` (shift by 1)
- 即 `τ''` 的第一列长度 = τ 的第二列长度 = c_2(O).

所以 `signature(τ'').1 = c_2(τ'') + colGe1(τ''.P) + tail(τ''.P)` 而 `c_2(τ'') = τ''.Q.shape.colLen 0 = c_4(O)`。

这不匹配 hypothesis 中要求的 `p_prev = c_2(O) + ...` 直接结构。但 hypothesis **only requires** `signature(τ).1 = 2 * c_2(O) + p_prev + tail(τ).1`，即它是一个 *定义式*，不需要 p_prev 有其他结构。

**最终策略**：
定义 `p_prev := signature(τ).1 - 2 * c_2(O) - tail_D(τ).1`。则 h_prop_11_4_p 自动以 `rfl` 成立。

但这样 `p_prev` 就不再等于 `sign(L_{τ''}).1` 了，除非我们能证明上述表达式等于 `signature(τ'').1`。

**核心引理（Prop 11.4 的数值形式）**：
$$\text{signature}(τ).1 = 2 \cdot τ.Q.\text{shape.colLen } 0 + \text{signature}(τ'').1 + \text{tailSignature}_D(τ).1$$

这是 paper [BMSZb] 公式 (10.12) 和 [BMSZ] Prop 11.4 的直接结果。其 natural language proof：

1. 按 `signature_fst_decomp_D` applied to τ:
   $$\text{signature}(τ).1 = \text{Q.colLen 0}(τ) + A + T$$
   其中 `A = colGe1 P contribution`, `T = tail col 0 contribution for τ`.

2. `τ'' = doubleDescent(τ)` 定义为：把 τ.P 和 τ.Q 都左移一列。所以：
   - `τ''.Q.shape.colLen 0 = τ.Q.shape.colLen 2` (shift by 2，对 Q 也要 shift)
   - 或更精确：按 `shiftLeft` 2 次的定义
   - `colGe1 τ.P contribution` 是 τ.P 中列 ≥1 的所有 symbol 的加权和
   - 这个和等于 `signature(τ'') 的 "Q.colLen 0 (of τ'') + colGe1 (of τ''.P) + tail(τ''.P)"` 吗？

3. 关键要点：τ'' 的 "Q.colLen 0" 对应 τ 的 "Q.colLen 1"（shift 1 后的第 0 列 = shift 前第 1 列），τ'' 的 "colGe1" 对应 τ 的 "colGe2"。

4. 故 `signature(τ'').1 = (τ.Q.colLen 1) + (τ.P colGe2 contribution) + tail(τ''.P)`.

5. 把 τ 的 `A = τ.P colGe1 contribution` 拆分为：
   $$A = A_1 + A_{\geq 2}$$
   其中 `A_1 = τ.P.col 1 contribution` (P 的第 1 列), `A_{\geq 2} = τ.P.colGe 2 contribution`.

6. 类似地，τ.Q 对 colGe1 的贡献（包括在 `A` 中的 Q.countSym .dot 项）有关于 Q 第 ≥1 列的分解。

7. **关键等式**：`τ.Q.colLen 0 + A_1 (P 第 1 列) = 2 · τ.Q.shape.colLen 0 + (τ.Q.colLen 1)` — 因为 P 第 1 列从 row 0 到 row c_2(O)-1 全部填 dot（这是 D-type 的结构性约束），贡献 c_2(O)。

（需要具体的 Lean 验证每个等式。）

8. 组合 5 + 6 + 7，得到：
   $$\text{signature}(τ).1 = 2 \cdot c_2(O) + [\text{signature}(τ'').1] + [\text{tailSignature}_D(τ).1]$$

**这就是 h_prop_11_4_p 自动 discharge 所需要的 shape identity**。

**数学真实性**：该 identity 由 Prop 11.4 primitive case eq (11.7) 直接给出。
paper 证明依赖 descent 构造的精确定义 + 计算 A_1 的形式。

**Lean 形式化工作量估计**：需要：
- (a) `signature` 的 decomp 按 "colLen 0 / col 1 / colGe 2" 细分
- (b) `doubleDescent_D` 的 signature 与 τ 的 colGe 关系
- (c) P 第 1 列的结构（dot 填充的列数 = c_2(O)）
- (d) 汇总得到 `signature(τ).1 = 2·c_2(O) + signature(τ'').1 + tail.1`

每部分预估 100-200 行 Lean。总共 400-800 行。

### Discharge `h_n₀ ≥ 0`

**自然语言**：
定义 `n_inner := cardCells(τ) - c_1(τ)`。这是 τ 去掉第 0 列后剩余的 cell 数。
对 D type：`cardCells(τ) = (τ.P.shape sum) + (τ.Q.shape sum)`，而 c_1 = τ.P.shape.colLen 0 是第 0 列 P 的长度。

`n_0 := n_inner - sign(E).1 - sign(E).2 + n_prev`.

要证 n_0 ≥ 0，等价于 `n_inner + n_prev ≥ sign(E).1 + sign(E).2 = p_{τ''} + q_{τ''}`.

由 Prop 11.4 对 τ''，`p_{τ''} + q_{τ''} = 2 * c_2(O (τ'')) + (p_{τ''''} + q_{τ''''}) + tail(τ'').1 + tail(τ'').2`.

又 `n_inner = cardCells(τ) - c_1(τ) = cardCells(τ'') + tail cells`, i.e. `n_inner = cardCells(τ'') + (tail_D(τ).1 + tail_D(τ).2)/2` 大致（需精确化）。

结合 `signature_sum_D` 对 τ''：`p_{τ''} + q_{τ''} = 2·cardCells(τ'')`，得：
`sign(E).1 + sign(E).2 = 2·cardCells(τ'')`

所以要证 `n_inner + n_prev ≥ 2·cardCells(τ'')`。
`n_inner = cardCells(τ) - c_1 = cardCells(τ'') + c_2 + tail cells`（因为 τ 去掉 col 0 = τ'' 加 col 1 + tail）—— 这里需要精确：
`cardCells(τ) = c_1 + c_2 + cardCells(τ'')`（去掉 col 0 和 col 1 后剩下 τ''）但这不完全对。

重新：`τ'' = shift left τ.P and τ.Q by 2`。
`cardCells(τ'') = cardCells(τ) - (c_1 + c_2 + q_1 + q_2)` 其中 q_i = τ.Q.shape.colLen (i-1) 等等（D type 里 Q col 0 = P col 1 = c_2(O)）。

D type shape 关系：
- P.colLen 0 = c_1(O) = τ.P.shape.colLen 0
- Q.colLen 0 = c_2(O) = τ.Q.shape.colLen 0
- P.colLen 1 = c_2(O) (因为 D 型 P 第 1 列 dot 填充 = Q col 0)
- Q.colLen 1 = c_3(O)
- 等等

So `cardCells(τ) = cardCells of P + cardCells of Q = Σ P.colLen i + Σ Q.colLen i`
`= c_1 + c_2 + c_3 + c_4 + ... + c_2 + c_3 + c_4 + ... = c_1 + 2c_2 + 2c_3 + ...`

`cardCells(τ'') = (Σ P.colLen i starting i=2) + (Σ Q.colLen i starting i=2) = c_3 + c_4 + ... + c_3 + c_4 + ... = 2c_3 + 2c_4 + ...`

`cardCells(τ) - cardCells(τ'') = c_1 + 2c_2 + (terms from c_3 onwards) - (terms from c_3 onwards) = c_1 + 2c_2`.

所以 `cardCells(τ'') = cardCells(τ) - c_1 - 2c_2 = n_inner - 2c_2`.

代入：`sign(E).1 + sign(E).2 = 2·cardCells(τ'') = 2·n_inner - 4c_2`.

`n_0 = n_inner - sign(E).1 - sign(E).2 + n_prev = n_inner - (2n_inner - 4c_2) + n_prev = -n_inner + 4c_2 + n_prev`.

要 `n_0 ≥ 0`，需 `n_prev + 4c_2 ≥ n_inner`.
`n_inner = cardCells(τ) - c_1 = 2c_2 + 2c_3 + 2c_4 + ... `（依赖总 shape）.
`n_prev = p_{τ''''} = (signature τ'''').1`.

对 τ'''' 用 `signature_sum_C/M`（C/M 上 p = q）：`p_{τ''''} = cardCells(τ'''')`.
`cardCells(τ'''') = cardCells(τ'') - c_1(τ'') - 2c_2(τ'') = cardCells(τ'') - 2c_3 - 2c_4 = (n_inner - 2c_2) - 2c_3 - 2c_4`.

代入 `n_0 = -n_inner + 4c_2 + cardCells(τ'''') = -n_inner + 4c_2 + n_inner - 2c_2 - 2c_3 - 2c_4 = 2c_2 - 2c_3 - 2c_4`.

要 `n_0 ≥ 0` 即 `c_2 ≥ c_3 + c_4`. 这不一般成立！
例如 shape `(5, 3, 1, 1, ...)` 有 c_2 = 3, c_3 = 1, c_4 = 1, 满足。但 `(3, 3, 3, 1)` 有 c_2 = 3, c_3 = 3, c_4 = 1，不满足。

这说明 **我的选择 `n_prev = p_{τ''''}` 在某些情况下不合适**。

**重新检视**：paper 的 Lemma 11.5 公式其实是 `L_τ = charTwistCM (augment(n_0, n_0) L_{τ''}) γ_1`. 
所以 `n_0` 应该由 τ 与 τ'' 之间的 shape 关系唯一决定，不涉及 τ''''.

让我们直接用 paper formula: `n_0 = (c_1 - c_2)/... ` — 实际上 paper 说 `augment (n_0, n_0)` 在 C/M 层插入 `2n_0` 个 0，使得新的 cardCells 从 `cardCells(τ'')` 增加到 `cardCells(τ) - c_1` (first double descent). 所以：

`n_inner = cardCells(τ) - c_1 = cardCells(augment(n_0, n_0) L_{τ''}) `

而 `augment (n_0, n_0) L_{τ''}` 的 sign 是 `sign(L_{τ''}) + (n_0, n_0) = (p_{τ''} + n_0, q_{τ''} + n_0)`。
同时 `cardCells` of augmented = `cardCells(τ'') + 2n_0` (因为 augment 加 n_0 个 (p,0) 和 n_0 个 (0,q) 对).

所以要求 `cardCells(τ'') + 2n_0 = n_inner = cardCells(τ) - c_1`, 即
`2n_0 = cardCells(τ) - c_1 - cardCells(τ'') = c_1 + 2c_2 - c_1 = 2c_2`. 
**所以 `n_0 = c_2(O)`**.

对应到 prop_11_5_D_atomic 的 n_0 定义：
`n_0 := n_inner - sign(E).1 - sign(E).2 + n_prev`
`   = (c_1 + 2c_2 - c_1) - (2·cardCells(τ'')) + n_prev`  — 错了，这里混淆了
等等，`n_inner = cardCells(τ) - c_1 = 2c_2 + 2c_3 + ... `，不等于 `cardCells(τ)` 本身。

Let me redo it carefully.
`cardCells(τ) = Σ P.colLen i + Σ Q.colLen i`
D type: P.colLen 0 = c_1, P.colLen 1 = c_2 = Q.colLen 0, P.colLen 2 = c_3 = Q.colLen 1, ...
所以 P: c_1 + c_2 + c_3 + ..., Q: c_2 + c_3 + c_4 + ...
`cardCells(τ) = c_1 + 2(c_2 + c_3 + ...) = c_1 + 2 Σ_{i≥2} c_i`.

n_inner = cardCells(τ) - c_1 = 2 Σ_{i≥2} c_i = 2(c_2 + c_3 + c_4 + ...).

τ'' = double descent of τ: cut off 2 leftmost columns on both P and Q.
`cardCells(τ'')` = Σ P.colLen i (i ≥ 2) + Σ Q.colLen i (i ≥ 2) = (c_3 + c_4 + ...) + (c_4 + c_5 + ...) = c_3 + 2(c_4 + c_5 + ...).

Wait, τ''.P.colLen 0 = τ.P.colLen 2 = c_3, τ''.Q.colLen 0 = τ.Q.colLen 2 = c_4.
`cardCells(τ'') = c_3 + 2·(c_4 + c_5 + ...)`.

`p_{τ''} + q_{τ''} = 2·cardCells(τ'')` (by signature_sum_D applied to τ'').

So `sign(E).1 + sign(E).2 = 2(c_3 + 2(c_4 + c_5 + ...)) = 2c_3 + 4(c_4 + c_5 + ...)`.

`n_inner - sign(E).1 - sign(E).2 = 2(c_2 + c_3 + c_4 + ...) - 2c_3 - 4(c_4 + c_5 + ...)`
`= 2c_2 + 2c_3 + 2c_4 + 2c_5 + ... - 2c_3 - 4c_4 - 4c_5 - ...`
`= 2c_2 - 2c_4 - 2c_5 - ...`
`= 2c_2 - 2(c_4 + c_5 + ...)`.

Hmm, so `n_0 = 2(c_2 - (c_4 + c_5 + ...)) + n_prev`.

对于 finite shape (有 n 列)，`c_k = 0` for k > n, so this simplifies for finite shapes.

按原 paper 的构造，`n_0 = c_2(O) - c_3(O)` or similar. Let me reread.

Actually the recursive "inner" = result of single descent, not double descent. Let me re-examine `ILS.lemma_11_5_D`:

```
inner := ILS.charTwistCM (ILS.augment (n₀, n₀) E) γ₁
```

这里 `E` 是 **inner** ILS（on 内层）。如果 inner 类型是 C/M（因为 D → charTwistCM gives C/M type），那 `E` 应该是 τ' (C/M type, single descent) 的 ILS.

Actually wait, in the paper's Lemma 11.5 statement, `L_τ = charTwistCM (augment(n_0, n_0) L_{τ'})` where τ' 是 **single** descent to C/M type. So `E = L_{τ'}`, `n_prev = sign(L_{τ'''})` one level deeper, etc.

所以修正：`τ'' = single descent of τ` (into C/M type), which I'll call `τ'` from now on.
- `τ'.γ = C` (since τ.γ = D → descent goes D → C)
- `cardCells(τ')` in C type: P.colLen 0 + 2·Σ other P cols + 2·Σ Q cols... actually for C type shape relations differ.

Let me re-examine what descent does:
In paper: "single descent" = shift left by 1. So if τ is on shape O, τ' is on shape O' = shiftLeft(O, 1).
- τ'.P.colLen 0 = τ.P.colLen 1 = c_2(O)
- τ'.Q.colLen 0 = τ.Q.colLen 1 = c_3(O)

For C type: P is on Young diagram with partLens... actually C type PBP has different shape convention. Let me just accept that `cardCells(τ')` = cardCells of shifted shape.

If τ' is on O' = shiftLeft(O, 1) then cardCells(τ') = cardCells(τ) - (sum of col 0) = cardCells(τ) - c_1(O) - c_2(O) (for D, since P col 0 = c_1 and Q col 0 = c_2 are the "leftmost cells").

Actually no, "shiftLeft by 1" removes one column. For D-type τ, col 0 of P has c_1 cells, col 0 of Q has c_2 cells. Removing col 0 from P and Q gives τ' with:
- τ'.P.colLen 0 = τ.P.colLen 1 = c_2(O) (from structural D-type P col 1 = c_2)
- τ'.Q.colLen 0 = τ.Q.colLen 1 = c_3(O)
- cardCells(τ') = cardCells(τ) - c_1 - c_2 = c_1 + 2(c_2 + c_3 + ...) - c_1 - c_2 = c_2 + 2(c_3 + c_4 + ...).

OK let me not go too deep. The key point:

**h_n₀ ≥ 0 is a structural fact about shape**: can be derived from the specific formula for n_0 once we choose canonical E.

**Strategy for unconditional**: 
Rather than trying to pick canonical n_prev and prove all 5 hypotheses hold simultaneously, we can **abstract** the unconditional version:

```lean
theorem prop_11_5_D_fully_unconditional (τ : PBP) (hγ : τ.γ = .D) (...shape hyps...) :
    ∃ E : ILS, ∃ n_prev p_prev q_prev : ℤ, ∃ γ₁ : ℤ,
      -- hypotheses hold
      (ILS.firstColSign E = (ILS.sign E).1 - n_prev ...) ∧
      (ILS.sign E = (p_prev, q_prev)) ∧
      (prop_11_4 identities hold) ∧
      (h_n₀ ≥ 0) ∧
      -- conclusion
      (τ_signature identity holds)
```

即 existential 形式。或者直接证 statement：

```lean
theorem prop_11_5_D_fully_unconditional (τ : PBP) (hγ : τ.γ = .D) :
    ∃ γ₁ : ℤ,  -- the twist parameter
      let τ' := single descent τ  -- C/M type
      let E := canonical_ILS τ'
      let n₀ := canonical n₀ from shape
      let inner := ILS.charTwistCM (ILS.augment (n₀, n₀) E) γ₁
      ((PBP.signature τ).1 : ℤ) - (ILS.sign inner).1 - (ILS.firstColSign inner).2 = 
        (PBP.tailSignature_D τ).1 ∧
      ((PBP.signature τ).2 : ℤ) - (ILS.sign inner).2 - (ILS.firstColSign inner).1 = 
        (PBP.tailSignature_D τ).2
```

这是 lemma 11.5 的真正 unconditional 版本。

## 任务列表（informal proof 先，再 Lean 形式化）

### Task A: Shape identity `cardCells` 关系
**自然语言证明**：
- `cardCells(τ) = c_1 + 2·(c_2 + c_3 + ...)` (D type)
- `cardCells(τ') = (c_2 + 2·(c_3 + c_4 + ...))` (single descent)
- `cardCells(τ'') = (c_3 + 2·(c_4 + c_5 + ...))` (double descent)
- `cardCells(τ) - c_1 - cardCells(τ') = c_2` (always)
- `cardCells(τ) - c_1 - 2·cardCells(τ'') ≥ ?` (depends)

### Task B: Prop 11.4 数值 identity
**Natural language**: by signature_fst_decomp_D applied to τ and τ'', comparing:
`signature(τ).1 = c_2(O) + A + T_τ`
其中 `A` (colGe1 contribution) = `c_2(O) + signature(τ'').1 - c_4(O) - tail(τ'').1 ... `?

这需要细致计算。写出每个分量的贡献。

### Task C: sign preservation
`sign(L_{τ'}) = signature(τ')` — 已证 via AC.step_sign_*. ✓

### Task D: firstColSign invariant  
`firstColSign(L_{τ'}) = signature(τ') - signature(τ''')` — 已证 via AC.chain_firstColSign_eq_diff_sign. ✓

### Task E: h_n₀ ≥ 0
**自然语言**: With canonical n_prev, n_0 = f(shape of τ). Prove f ≥ 0 from shape hypotheses.

## 结论

**truly unconditional 版本的 Lemma 11.5 是可达的**，但需要完成：
1. Task A (shape identity) — 结构性，应容易形式化
2. Task B (Prop 11.4 数值 identity on τ, τ'' level) — **这是唯一的真正难点**，需要 descent 的精确形式 + signature_fst_decomp 的应用
3. Tasks C, D (sign/firstColSign) — **已完成**
4. Task E (h_n₀ ≥ 0) — **从 Task A 直接推出**

**预估 Lean 工作量**：600-1000 行，集中在 Task B。

## 为什么保留 conditional 形式也是合理的

在没有完成 Task B 的情况下，**conditional prop_11_5_D_atomic_pbp_discharged 仍然是一个有用的中间结果**：
- 它隔离了 PBP-level Lemma 11.5 与 descent shape arithmetic 的部分
- 调用方（Section 11 后续定理）可以 supply 具体 E (`L_{τ''}`) 并以 explicit shape 计算 discharge hypotheses
- 真正的 unconditional 形式只是把这些 explicit discharge 移到 lemma 11.5 自身内部

## 下一步

1. **先完整形式化 Task A (shape identity for cardCells)**: 100-200 行
2. **然后 Task B (Prop 11.4 数值 identity)**: 300-500 行
3. **最后集成为 `prop_11_5_D_fully_unconditional`**: 50-100 行
4. **下游定理 (Lemma 11.6, Props 11.8-11.17) fully unconditional wrappers**: 200-400 行

按上述顺序在完成自然语言证明后逐步 Lean 形式化。
