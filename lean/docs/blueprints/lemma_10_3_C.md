# Lemma 10.3 C-type — Shape Shifting 自然语言证明

## 陈述

设 ★ = C，$\check{\mathcal{O}}$ 具 good parity，$(1,2) \in \text{PP}_\star(\check{\mathcal{O}})$。令 $\wp \subseteq \text{PP}_\star(\check{\mathcal{O}})$ 且 $(1,2) \notin \wp$，$\wp_\uparrow := \wp \cup \{(1,2)\}$。

则存在双射
$$T_{\wp, \wp_\uparrow} : \text{PBP}_G(\check{\mathcal{O}}, \wp) \to \text{PBP}_G(\check{\mathcal{O}}, \wp_\uparrow), \quad \tau \mapsto \tau_\uparrow$$

该双射是 shape-shifting：交换 $\iota_{\wp}$ 和 $\iota_{\wp_\uparrow}$ 的第一列（相差 1 格），$\jmath$ 形状不变。

## 与 M 型对比

已形式化的 M 型 shape-shift（`shapeShiftM`）对应 $\star = \tilde{C}$，交换 $\iota$ 和 $\jmath$ col 0 的角色，paint 用 `translateM` 函数翻译（r↔s, c↔d）。

C 型 shape-shift 不同：
- **Paint 翻译更复杂**：分多个 case 根据 $\mathcal{P}_\tau(c_1(\iota_\wp), 1)$ 的值
- **不交换 P/Q 角色**，只是修改 P col 0

## 定义：C 型 shape-shift 的 paint 函数

对 $\tau = (\iota_\wp, \mathcal{P}) \times (\jmath_\wp, \mathcal{Q}) \times \alpha \in \text{PBP}_G(\check{\mathcal{O}}, \wp)$，定义 $\tau_\uparrow \in \text{PBP}_G(\check{\mathcal{O}}, \wp_\uparrow)$：

注意：
- $\mathbf{c}_1(\iota_{\wp_\uparrow}) > \mathbf{c}_1(\iota_\wp) \geq 1$，因为 $(1,2) \in \text{PP}$
- $\jmath$ 形状不变，故 $\mathcal{Q}_{\tau_\uparrow}(i, j) := \mathcal{Q}_\tau(i, j)$

### Case (a): $\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp), 1) \neq \bullet$

记 $\alpha_0 := \mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp), 1) \in \{s, r, c, d\}$。

#### Sub-case (a.1): $\mathbf{c}_1(\iota_\wp) \geq 2$ 且 $\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp) - 1, 1) = c$
$$\mathcal{P}_{\tau_\uparrow}(i, j) := \begin{cases}
r, & j = 1 \text{ 且 } \mathbf{c}_1(\iota_\wp) - 1 \leq i \leq \mathbf{c}_1(\iota_{\wp_\uparrow}) - 2 \\
c, & (i,j) = (\mathbf{c}_1(\iota_{\wp_\uparrow}) - 1, 1) \\
d, & (i,j) = (\mathbf{c}_1(\iota_{\wp_\uparrow}), 1) \\
\mathcal{P}_\tau(i, j), & \text{otherwise}
\end{cases}$$

#### Sub-case (a.2): 否则
$$\mathcal{P}_{\tau_\uparrow}(i, j) := \begin{cases}
r, & j = 1 \text{ 且 } \mathbf{c}_1(\iota_\wp) \leq i \leq \mathbf{c}_1(\iota_{\wp_\uparrow}) - 1 \\
\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp), 1), & (i,j) = (\mathbf{c}_1(\iota_{\wp_\uparrow}), 1) \\
\mathcal{P}_\tau(i, j), & \text{otherwise}
\end{cases}$$

### Case (b): $\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp), 1) = \bullet$

#### Sub-case (b.1): $\mathbf{c}_2(\iota_\wp) = \mathbf{c}_1(\iota_\wp)$ 且 $\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp), 2) = r$
$$\mathcal{P}_{\tau_\uparrow}(i, j) := \begin{cases}
r, & j = 1 \text{ 且 } \mathbf{c}_1(\iota_\wp) \leq i \leq \mathbf{c}_1(\iota_{\wp_\uparrow}) - 1 \\
c, & (i,j) = (\mathbf{c}_2(\iota_\wp), 2) \\
d, & (i,j) = (\mathbf{c}_1(\iota_{\wp_\uparrow}), 1) \\
\mathcal{P}_\tau(i, j), & \text{otherwise}
\end{cases}$$

#### Sub-case (b.2): 否则
$$\mathcal{P}_{\tau_\uparrow}(i, j) := \begin{cases}
r, & j = 1 \text{ 且 } \mathbf{c}_1(\iota_\wp) \leq i \leq \mathbf{c}_1(\iota_{\wp_\uparrow}) - 2 \\
c, & (i,j) = (\mathbf{c}_1(\iota_\wp) - 1, 1) \\
d, & (i,j) = (\mathbf{c}_1(\iota_{\wp_\uparrow}), 1) \\
\mathcal{P}_\tau(i, j), & \text{otherwise}
\end{cases}$$

## 引理 10.3 双射性证明

### Step 1: $\tau_\uparrow$ 是合法 PBP

需验证：
1. **paint 符号集合**：新 paint 仍在 C 型允许集合 $\{\bullet, s, r, c, d\}$（Def 2.25）
2. **mono_P**：列方向 layerOrd 单调递增
3. **mono_Q**：Q 未改动，由原 $\tau$ 的 mono_Q 继承
4. **row_s, row_r**：每行 s/r 至多 1 个（跨 P, Q）
5. **col_c_P, col_d_P**：每列 c/d 至多 1 个
6. **dot_match**：$\mathcal{P}(i,j) = \bullet \iff (i,j) \in \iota_{\wp_\uparrow}$ 且 $\mathcal{Q}(i,j) = \bullet$（对 C，后者自动 dot）

**详细验证**（Case a.1 为例）：
- 新 paint 值 $\in \{r, c, d, \mathcal{P}_\tau(i,j)\}$ 全在 $\{\bullet, s, r, c, d\}$ ✓
- mono_P: layerOrd 是 r(2) → c(3) → d(4)，递增 ✓
- col_c_P: 新增一个 c 在 $(\mathbf{c}_1(\iota_{\wp_\uparrow}) - 1, 1)$，原来 $\mathcal{P}_\tau(\mathbf{c}_1(\iota_\wp) - 1, 1) = c$ 的位置改为 r，所以 col 1 仍只一个 c ✓
- col_d_P: 新增 d 在 col 1 底部，唯一 ✓
- row_r: 第 $i$ 行（$\mathbf{c}_1(\iota_\wp) - 1 \leq i \leq \mathbf{c}_1(\iota_{\wp_\uparrow}) - 2$）新 paint r，需与原 $\tau$ 同行 s/r 位置不冲突——由 Q 同行无 s 保证（C 型 Q 只有 $\{\bullet, s\}$，同行 s 唯一）✓

类似地验证其他 case。

### Step 2: 形状匹配 $\wp_\uparrow$

新的 $\iota_{\wp_\uparrow}$ col 0 比原来多 1 格（来自 $(1,2) \in \wp_\uparrow$）。$\tau_\uparrow$ 的 paint 在这些新格上填入具体值（d 在最底，c 在倒数第二，r 填中间），对应 $(1,2)$ primitive 的 paint convention。

### Step 3: $T_{\wp_\uparrow, \wp}$（逆映射）

对 $\tau' \in \text{PBP}_G(\check{\mathcal{O}}, \wp_\uparrow)$，按反 case 构造 $\tau \in \text{PBP}_G(\check{\mathcal{O}}, \wp)$：
- 从 $\mathcal{P}_{\tau'}(\mathbf{c}_1(\iota_{\wp_\uparrow}) - 1, 1)$ 的值判断 case
- 逆向恢复 Case (a)/(b) 及 sub-cases
- 恢复 $\mathcal{P}_\tau$ on original $\iota_\wp$ 形状

详细算法见 [BMSZb] p.66 Proof of Lemma 10.3。

### Step 4: 双射性

- $T_{\wp,\wp_\uparrow} \circ T_{\wp_\uparrow,\wp} = \text{id}$: 通过 case 对应关系直接验证
- $T_{\wp_\uparrow,\wp} \circ T_{\wp,\wp_\uparrow} = \text{id}$: 同上

## Lean 形式化策略

类比 `CombUnipotent/CountingProof/ShapeShift.lean` 中 M 型的结构：

1. **`translateC : DRCSymbol → DRCSymbol`** (可能不需要单独 translate，因 C 版直接按 case 填 paint 值)
2. **`shiftPaintP_C : PBP → (ℕ → ℕ → DRCSymbol)`**：定义新 P paint 函数（分 case a.1/a.2/b.1/b.2）
3. **`shiftPaintQ_C := Q.paint`**（不改）
4. **辅助引理**：
   - `shiftPaintP_C_allowed`：新 paint 是 C 型 allowed
   - `shiftPaintP_C_mono`：列单调
   - `shiftPaintP_C_row_s/r`：行约束
   - `shiftPaintP_C_col_c/d`：列 c/d 唯一
   - `shiftPaintP_C_dot_match`：dot_match 条件
5. **`shapeShiftC : PBP → PBP`**：构造 $\tau_\uparrow$
6. **`shapeShiftC_inverse`**：逆映射 $\tau'↓$
7. **`shapeShiftC_involution`**：$T \circ T^{-1} = \text{id}$
8. **`card_PBPSet_C_shapeShift`**：双射给出 cardinality equality

**预估工作量**：约 400-600 行 Lean（对标 `ShapeShift.lean` M 型的 789 行，C 型 case 更复杂但 Q 不变更简单）。

## 结论

- Lemma 10.3 C 型的自然语言证明清晰（paper 已给详细 case 分析）
- 形式化策略对标已完成的 M 型 `shapeShiftM`，结构明确
- 完成后，`prop_10_2_PBP_C` 可从 `rfl` 升级到真正的双射版本（类比 `prop_10_2_PBP_M`）
