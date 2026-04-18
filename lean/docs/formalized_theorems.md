# 已形式化的关键定理与依赖关系

所有定理 0 sorry，全部编译通过。

## 文件结构

```
Basic.lean → PBP.lean → Signature.lean
                ↓
           Descent.lean → Tail.lean
                             ↓
                        Counting.lean (独立，仅 import Basic)
                        Finiteness.lean (import PBP + Mathlib.Data.Fintype.{Pi,Prod})
```

---

## Basic.lean

| 名称 | 类型 | 说明 |
|------|------|------|
| `RootType` | inductive | B⁺/B⁻/C/D/M |
| `DRCSymbol` | inductive | dot/s/r/c/d |
| `DRCSymbol.layerOrd` | def | • < s < r < c < d → 0,1,2,3,4 |
| `DRCSymbol.allowed γ s σ` | def | 符号约束表 |
| `Fintype DRCSymbol` | instance | 5 个元素 |

## PBP.lean

| 名称 | 类型 | 依赖 | 说明 |
|------|------|------|------|
| `PaintedYoungDiagram` | structure | Mathlib YoungDiagram | shape + paint + paint_outside |
| `layerMonotone D` | def | layerOrd | 单调性条件 |
| `paintBySide P Q` | def | | 按 Side 选择 paint |
| `PBP` | structure | PYD | 5 组约束 (sym, dot_match, mono, row, col) |
| `dotDiag D hm` | def | layerMonotone | dot 子图 (YoungDiagram) |
| `dotDiag_eq τ` | theorem | dot_match | P 和 Q 的 dot 子图相等 |
| `Q_all_dot_of_D` | theorem | sym_Q | D type: Q 全是 dot |
| `Q_le_P_of_D` | theorem | dot_match, Q_all_dot_of_D | D type: Q.shape ≤ P.shape |
| `Q_eq_dotDiag_of_D` | theorem | Q_all_dot_of_D, dot_match | D type: Q.shape = dotDiag(P) |
| `P_nonDot_eq_c_of_B` | theorem | sym_P | B type: P 的非 dot = c |
| `Q_nonDot_eq_s_of_C` | theorem | sym_Q | C type: Q 的非 dot = s |

## Signature.lean

| 名称 | 类型 | 依赖 | 说明 |
|------|------|------|------|
| `PYD.countSym D σ` | def | | 符号 σ 在 D 中的个数 |
| `PBP.signature τ` | def | countSym | (p, q) 签名 |
| `PYD.hasDInCol0 D` | def | | 列 0 是否有 d |
| `PBP.epsilon τ` | def | hasDInCol0 | ε ∈ {0, 1} |

## Descent.lean

### 子图定义
| 名称 | 类型 | 依赖 | 说明 |
|------|------|------|------|
| `dotSdiag D hm` | def | layerMonotone | dot+s 子图 (layerOrd ≤ 1) |
| `dotScolLen D j` | def | | 列 j 的 dot+s 计数 |
| `dotScolLen_eq_dotSdiag_colLen` | theorem | | dotScolLen = dotSdiag.colLen |

### Descent paint 函数
| 名称 | 说明 |
|------|------|
| `descentPaintL_DC` | D→C: P'(i,j) = dot if i < dotScolLen(P,j+1), else P(i,j+1) |
| `descentPaintR_DC` | D→C: Q'(i,j) = dot/s/dot 分段 |
| `descentPaintL_CD` | C→D: P'(i,j) = dot/s/P(i,j) 分段 |
| `descentPaintR_CD` | C→D: Q'(i,j) = Q(i,j+1) |
| `descentPaintL_BM` | B→M: 类似 D→C |
| `descentPaintR_BM` | B→M: 类似 D→C |
| `descentPaintL_MB` | M→B: 类似 C→D |
| `descentPaintR_MB` | M→B: 类似 C→D |

### Descent 单射性
| 名称 | 依赖 | 说明 |
|------|------|------|
| `descent_inj_CD` | descentPaint*, PBP constraints | C/D: 同 descent paint + 同 shapes → 同 PBP |
| `descent_eq_implies_cols_ge1_D` | descentPaintL_DC | D: 同 descent → P cols ≥ 1 一致 |
| `descent_eq_implies_cols_ge1_MB` | descentPaintL_BM, descentPaintR_BM | M/B: 同 descent → P,Q cols ≥ 1 一致 |
| `descent_recovery_BM` | descent_eq_implies_cols_ge1_MB, col0 analysis | B: 同 descent → P 完全一致 + Q cols ≥ 1 |

### 辅助引理
| 名称 | 说明 |
|------|------|
| `Q_s_rightmost_of_C` | C type: Q 的 s 在行中最右 |
| `Q_dot_left_of_C` | C type: Q cell 有右邻 → 本 cell 是 dot |
| `dotDiag_colLen_ge_Q_colLen_succ_of_C` | C type: dotDiag.colLen(k) ≥ Q.colLen(k+1) |
| `Q_colLen_succ_le_dotScolLen_C` | C type: Q.colLen(j+1) ≤ dotScolLen(P,j) |

## Tail.lean

### 列 0 分析工具
| 名称 | 依赖 | 说明 |
|------|------|------|
| `countCol0 paint σ a n` | def | 列 0 中 [a, a+n) 范围内 σ 的计数 |
| `countCol0_total` | | 所有 5 个符号的 countCol0 之和 = n |
| `countCol0_le_one_of_unique` | col_c/d | 唯一性 → 计数 ≤ 1 |
| `countSymCol0 D σ` | def | 列 0 中 σ 的总计数 |
| `countSymColGe1 D σ` | def | 列 ≥ 1 中 σ 的总计数 |
| `countSym_split` | | countSym = countSymCol0 + countSymColGe1 |
| `countSymColGe1_eq` | | 同 paint on cols ≥ 1 → countSymColGe1 一致 |

### 关键分析工具
| 名称 | 依赖 | 说明 |
|------|------|------|
| `monotone_col_unique` | layerOrd | 单调序列 + 同 symbol 计数 → 逐点一致 |
| `tail_counts_arith` | | 算术引理: 2δ_r + δ_c = 0, \|δ_c\| ≤ 1 → all δ = 0 |

### D type Prop 10.9 证明链
| 名称 | 依赖 | 说明 |
|------|------|------|
| `col0_dot_below_Q_D` | Q_all_dot_of_D | D type: col 0 中 Q 以下是 dot |
| `descent_col0_dot_D` | col0_dot_below_Q_D | D type: col 0 dot 区一致 |
| `descent_col0_outside` | paint_outside | col 0 shape 外一致 |
| `tail_nd_eq` | epsilon, hasDInCol0 | tail 中 d 计数一致 (from ε) |
| `tail_weighted_sums_eq` | signature, countSym_split | tail 的加权和一致 (from sig) |
| `tail_counts_eq_D` | tail_nd_eq, tail_weighted_sums_eq, tail_counts_arith | **D type: col 0 tail 所有符号计数一致** |
| `descent_inj_col0_D` | tail_counts_eq_D, monotone_col_unique | **D type: col 0 逐点一致** |
| `descent_inj_D` | descent_inj_col0_D, descent_eq_implies_cols_ge1_D | **Prop 10.9 D type** |

### B type Prop 10.9 证明链
| 名称 | 依赖 | 说明 |
|------|------|------|
| `P_countSym_zero_of_B` | sym_P, P_nonDot_eq_c_of_B | B type: P.countSym(r) = P.countSym(d) = 0 |
| `Q_countSym_c_zero_of_B` | sym_Q | B type: Q.countSym(c) = 0 |
| `col0_Q_dot_below_P_B` | dot_match | B type: Q col 0 在 P 以下是 dot |
| `descent_inj_col0_B` | tail_counts_arith, monotone_col_unique, signature, epsilon | **B type: Q col 0 一致 (given P)** |
| `descent_inj_B` | descent_recovery_BM, descent_inj_col0_B, signature parity | **Prop 10.9 B type** |

### Double descent
| 名称 | 依赖 | 说明 |
|------|------|------|
| `doubleDescent_D_paintL` | descentPaintL_DC, descentPaintL_CD | ∇²(D→C→D) 的 P paint |
| `doubleDescent_B_paintL/R` | descentPaintL_BM, descentPaintL_MB | ∇²(B→M→B) 的 P/Q paint |
| `ddescent_D_determines_single` | dotScolLen, paint_ne_dot | ∇² → ∇ (D type) |
| `ddescent_B_determines_colsGe1` | dotScolLen | ∇² → P,Q cols ≥ 1 (B type) |
| `ddescent_inj_D` | ddescent_D_determines_single, descent_inj_D | **Prop 10.9 D type (∇² 版)** |
| `ddescent_inj_B` | ddescent_B_determines_colsGe1, descent_inj_B, **hγ_eq** | **Prop 10.9 B type (∇² 版, 需 γ₁=γ₂)** |

## Counting.lean

| 名称 | 类型 | 说明 |
|------|------|------|
| `DualPart` | abbrev | List ℕ |
| `nu n` | def | n + 1 |
| `tailCoeffs k` | def | tail 多项式系数 ((tDD,tRC,tSS), (scDD,scRC,scSS)) |
| `countPBP_D dp` | def | D type 递推: (DD, RC, SS) |
| `countPBP_B dp` | def | B type 递推: (DD, RC, SS) |
| `countPBP_C dp` | def | C type: 用 D type + descent |
| `countPBP_M dp` | def | M type: 用 B type + descent |
| `countPBP dp γ` | def | 总计数 |
| `countPBP_D_primitive` | theorem | D type primitive case 结构 |
| `countPBP_D_balanced` | theorem | D type balanced case 结构 |
| `countPBP_C_primitive` | theorem | C type primitive: DD + RC + SS |
| `countPBP_C_balanced` | theorem | C type balanced: DD + RC |

## Finiteness.lean

| 名称 | 依赖 | 说明 |
|------|------|------|
| `PYD.restrict D μ h` | paint | 限制 paint 到 cells |
| `PYD.ext'` | | shape + paint 相同 → PYD 相同 |
| `PBP.ext''` | | γ + P + Q 相同 → PBP 相同 |
| `PYD.restrict_injective` | paint_outside | 同 shape + 同 restrict → PYD 相同 |
| `PBPSet γ μP μQ` | def | {τ : PBP // γ, shapes 固定} |
| `PBPSet.restrict_injective` | PYD.restrict_injective, PBP.ext'' | **PBP 注入到有限类型** |
| `Finite (PBPSet γ μP μQ)` | instance | Finite.of_injective |
| `Fintype (PBPSet γ μP μQ)` | instance | Fintype.ofFinite |

## CountingProof.lean

### YoungDiagram.colLens (列长 ↔ 形状)
| 名称 | 类型 | 说明 |
|------|------|------|
| `YoungDiagram.colLens μ` | def | 列长列表 = μ.transpose.rowLens |
| `YoungDiagram.ofColLens w hw` | def | 从列长构造 YoungDiagram |
| `length_colLens` | simp | colLens.length = rowLen 0 |
| `getElem_colLens` | simp | colLens[j] = colLen j |
| `colLens_sorted` | theorem | 列长非增 |
| `pos_of_mem_colLens` | theorem | 列长正 |
| `ofColLens_colLens` | theorem | **往返: ofColLens(colLens μ) = μ** |
| `colLens_ofColLens` | theorem | **往返: colLens(ofColLens w) = w** |
| `colLen_ofColLens` | theorem | ofColLens 的 colLen j = w[j] |

### Orbit → PBP 形状 (D type)
| 名称 | 类型 | 说明 |
|------|------|------|
| `dpartColLensP_D` | def | orbit → P 列长: r₁, r₃, ... 取 (r+1)/2 |
| `dpartColLensQ_D` | def | orbit → Q 列长: r₂, r₄, ... 取 (r-1)/2 |
| `dpartColLensP_D_cons₂` | theorem | **去掉2个orbit行 = 去掉P列头 (by rfl)** |
| `dpartColLensQ_D_cons₂` | theorem | Q 列长类似递推 |

### Tail 分类
| 名称 | 类型 | 说明 |
|------|------|------|
| `TailClass` | inductive | DD / RC / SS |
| `tailClass_D` | def | 用 tailLen_D + tailSymbol_D 分类 |

### Double descent 结构
| 名称 | 依赖 | 说明 |
|------|------|------|
| `doubleDescent_D_paintL_dot_iff` | Q_colLen_le_dotScolLen_of_D, dotScolLen_le_colLen | **∇² 在 P.colLen(j+1) 以外为 dot** |

### 基础情况
| 名称 | 依赖 | 说明 |
|------|------|------|
| `emptyPYD` | def | 空 PYD: shape = ⊥, paint = dot |
| `emptyPBP γ` | def | 空 PBP: 两边都空 |
| `PYD_eq_emptyPYD_of_shape_bot` | paint_outside | shape = ⊥ → PYD 唯一 |
| `PBPSet_bot_unique` | PYD_eq_emptyPYD, PBP.ext'' | PBPSet γ ⊥ ⊥ 中元素唯一 |
| `card_PBPSet_bot` | PBPSet_bot_unique | **Fintype.card (PBPSet γ ⊥ ⊥) = 1** |

---

## 依赖图 (主要定理)

```
PBP constraints
  │
  ├─ dotDiag_eq ─── Q_eq_dotDiag_of_D
  │                       │
  ├─ layerMonotone ─ monotone_col_unique
  │                       │
  ├─ signature ──── tail_weighted_sums_eq ──┐
  │                                          │
  ├─ epsilon ───── tail_nd_eq ──────────────┤
  │                                          │
  │                 tail_counts_arith ───────┤
  │                                          ▼
  │                                  tail_counts_eq_D
  │                                          │
  │                                          ▼
  │                                  descent_inj_col0_D
  │                                          │
  ├─ descent_eq_implies_cols_ge1_D ─────────┤
  │                                          ▼
  │                                    descent_inj_D (Prop 10.9 D)
  │                                          │
  │                              ddescent_D_determines_single
  │                                          │
  │                                          ▼
  │                                    ddescent_inj_D
  │
  ├─ descent_recovery_BM ──┐
  │                         ▼
  │                  descent_inj_col0_B ──── descent_inj_B (Prop 10.9 B)
  │                                                │
  │                              ddescent_B_determines_colsGe1
  │                                                │
  │                                                ▼
  │                                          ddescent_inj_B (需 γ₁=γ₂)
  │
  ├─ PBPSet.restrict_injective
  │         │
  │         ▼
  │  Finite (PBPSet) ── Fintype (PBPSet)
  │
  ▼
  countPBP_D/B/C/M (递推公式)
  │
  ├─ YoungDiagram.colLens / ofColLens (双向转换)
  │
  ├─ dpartColLensP_D / dpartColLensQ_D (orbit → 形状)
  │     │
  │     └─ dpartColLensP_D_cons₂ (去2行 = 去列头)
  │
  ├─ TailClass + tailClass_D (DD/RC/SS 分类)
  │
  ├─ doubleDescent_D_paintL_dot_iff (∇² 列长关系)
  │
  ├─ emptyPBP + card_PBPSet_bot = 1 (基础情况 ✓)
  │
  ▼
  card_PBPSet = countPBP (待证: 纤维计数 + descent 像)
```
