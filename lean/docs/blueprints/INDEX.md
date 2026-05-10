# Blueprints Index — 自然语言证明 ↔ Lean 形式化对照

本索引给出每份自然语言证明 blueprint 对应的 Lean 形式化文件 / 定理名。
过时或重复的文档已移到 [archive/](archive/)。

## 顶层总览

| Blueprint | 作用 |
|---|---|
| [BMSZ_section11.md](BMSZ_section11.md) | [BMSZ] Section 11 paper→Lean 完整 dependency map |
| [section11_status_final.md](section11_status_final.md) | Section 11 形式化最终状态 |
| [unconditional_PBP_theorems.md](unconditional_PBP_theorems.md) | Truly unconditional PBP 层定理路径分析 |
| [unconditional_PBP_theorems_addendum.md](unconditional_PBP_theorems_addendum.md) | 上文 addendum：natAbs 约束使部分 hyp 不可满足 |
| [classical_group/blueprint.md](classical_group/blueprint.md) | standalone ClassicalGroup/ClassicalSpace theorem blueprint |

## 基础定义

| Blueprint | Lean 文件 | 关键定义 |
|---|---|---|
| [tail_definition.md](tail_definition.md) | `CombUnipotent/Tail.lean` | `PBP.tailSignature_D/B`, `tailSymbol_D/B`, `tailContrib` |
| [firstColSign_invariant.md](firstColSign_invariant.md) | `CombUnipotent/MYD.lean` | `ILS.firstColSign`, `AC.step_firstColSign_{D,Bplus,Bminus,C,M}`, `AC.chain_firstColSign_eq_diff_sign` |
| [classical_group/blueprint.md](classical_group/blueprint.md) | `CombUnipotent/ClassicalGroup/*.lean` | `ClassicalGroup.classical_group_theorem`, `ClassicalGroup.classical_space_existence_and_uniqueness` |

## Section 10 主定理 (counting + structural)

| Paper | Blueprint | Lean 定理 (unconditional) | 位置 |
|---|---|---|---|
| Lemma 10.3 (C) | [lemma_10_3_C.md](lemma_10_3_C.md) | `lemma_10_3_C`, `shapeShiftC_id_eq` | `CountingProof/ShapeShiftC.lean`, `Section10.lean` |
| Lemma 10.3 (M) | [lemma_10_3_M_shape_shifting.md](lemma_10_3_M_shape_shifting.md), [shape_shifting_M.md](shape_shifting_M.md) | `lemma_10_3_M`, `shapeShiftM`, `card_PBPSet_M_shapeShift` | `CountingProof/ShapeShift.lean`, `Section10.lean` |
| Prop 10.8 (C/M) | (see counting blueprints) | `prop_10_8_{C,M}_{primitive,balanced}` | `Section10.lean` |
| Prop 10.9 (D/B) | [balanced_double_descent_theorem.md](balanced_double_descent_theorem.md) | `prop_10_9_D`, `prop_10_9_B`, `cor_10_10_D/B` | `Section10.lean`, `Tail.lean` |
| **Prop 10.11 (B)** | [prop_10_11_B_detailed_proof.md](prop_10_11_B_detailed_proof.md), [section10_B_M_complete_proof.md](section10_B_M_complete_proof.md), [counting_B_M_blueprint.md](counting_B_M_blueprint.md) | `prop_10_11_B`, `card_PBPSet_B_eq_tripleSum_countPBP_B` | `CountingProof/CorrespondenceB.lean`, `Section10.lean` |
| **Prop 10.11 (D)** | [COMPLETE_B_M_proof.md](COMPLETE_B_M_proof.md) | `prop_10_11_D`, `card_PBPSet_D_eq_tripleSum_countPBP_D` | `CountingProof/Correspondence.lean`, `Section10.lean` |
| **Prop 10.12 (C)** | (see shape-shift blueprints) | `prop_10_12_C`, `card_PBPSet_C_eq_countPBP_C` | `CountingProof/CorrespondenceC.lean`, `Section10.lean` |
| **Prop 10.12 (M)** | [COMPLETE_B_M_proof.md](COMPLETE_B_M_proof.md) | `prop_10_12_M`, `card_PBPSet_M_eq_countPBP_M` | `CountingProof/Prop10_8_M.lean`, `Section10.lean` |

**状态**：所有 Section 10 主定理 **完全 unconditional**（只有 shape/dp 合法性假设）。

## Section 11 定理

### 11.1 — empty / r₁=1 base cases

| Paper | Blueprint | Lean 定理 | 位置 |
|---|---|---|---|
| Lemma 11.1(a) empty | [lemma_11_1_proof.md](lemma_11_1_proof.md) | `lemma_11_1_a_empty`, `lemma_11_1_a_empty_first_entry` | `MYD.lean` |
| Lemma 11.1(a) r₁=1 | [lemma_11_1_r1_one_explicit.md](lemma_11_1_r1_one_explicit.md) | `lemma_11_1_a_r1_one`, `lemma_11_1_a_r1_one_first_entry` | `MYD.lean` |
| Lemma 11.1(b) bijection | [lemma_11_1_b_bijection_enumeration.md](lemma_11_1_b_bijection_enumeration.md) | `lemma_11_1_b_bijection`, `lemma_11_1_b_bijection_concrete`, `PBPExt_at_r1_eq_1_D` | `MYD.lean`, `MYD/Lemma11_1_b.lean` |

### 11.2 — Lemma 11.2

| Paper | Blueprint | Lean 定理 | 状态 |
|---|---|---|---|
| Lemma 11.2 | [lemma_11_2_proof.md](lemma_11_2_proof.md) | (see Section 11 blueprint; B/D 覆盖) | ✅ |

### 11.3–11.4 — signature decomp

| Paper | Lean 定理 | 位置 |
|---|---|---|
| Prop 11.4 D signature decomp | `PBP.signature_fst_decomp_D`, `PBP.signature_snd_decomp_D`, `prop_11_4_signature_decomp_D` | `MYD.lean` |
| signature sum | `PBP.signature_sum_D` | `MYD/Prop11_5_AtomicDischarge.lean` |
| tail signature sum | `PBP.tailSignature_D_sum_eq`, `PBP.residual_identity_D` | `MYD/Prop11_5_AtomicDischarge.lean` |

### 11.5 — AC composition

| Paper | Blueprint | Lean 定理 | 位置 |
|---|---|---|---|
| Lemma 11.5 | [lemma_11_5_COMPLETE.md](lemma_11_5_COMPLETE.md), [lemma_11_5_PBP_identity.md](lemma_11_5_PBP_identity.md) | `ILS.lemma_11_5_D`, `ILS.lemma_11_5_D_unconditional`, `prop_11_5_D_unconditional` | `MYD.lean` |
| Lemma 11.5 atomic 3 facts | [unconditional_PBP_theorems.md](unconditional_PBP_theorems.md) | `prop_11_5_D_atomic_pbp_discharged`, `PBP.signature_sum_D`, `PBP.residual_identity_D` | `MYD/Prop11_5_AtomicDischarge.lean` |

### 11.6 — first entry formula

| Paper | Lean 定理 | 位置 |
|---|---|---|
| Lemma 11.6 (D/B⁺/B⁻) | `AC.lemma_11_6_{D,Bplus,Bminus}_unconditional` | `MYD.lean` |

### 11.7–11.13 — 中间定理 (injectivity / non-zero)

| Paper | Blueprint | Lean 定理 | 位置 |
|---|---|---|---|
| Prop 11.7 mult-free | — | `prop_11_7_multiplicityFree` | `MYD.lean` |
| Prop 11.8 non-empty | — | `prop_11_8`, `prop_11_8_PBP_{D,Bplus,Bminus}_closed` | `MYD.lean` |
| Prop 11.9 descent restrict | [lemma_11_9_detailed.md](lemma_11_9_detailed.md) | `prop_11_9_PBP_D_numerical`, `prop_11_9_PBP_{Bplus,Bminus}_abstract` | `MYD.lean` |
| Prop 11.10–11.12 injectivity | (see Section 11 blueprint) | `prop_11_10_PBP_D`, `prop_11_11_PBP_D`, `prop_11_12_PBP_D` (+ B⁺/B⁻) | `MYD.lean` |
| Prop 11.13 chain injectivity | — | `prop_11_13_PBP_D`, B⁺/B⁻ 版 | `MYD.lean` |

### 11.14–11.17 — main bijection

| Paper | Lean 定理 | 位置 |
|---|---|---|
| Prop 11.14 surjectivity | `prop_11_14_PBP_{D,Bplus,Bminus}` (abstract from `Finite α ≃ β`) | `MYD.lean` |
| Prop 11.15 D complete bijection | `prop_11_15_PBP_D_complete`, `prop_11_15_PBP_D_injective_full` | `MYD.lean` |
| Prop 11.16 C/M descent | `prop_11_16_PBP_{C,M}` | `MYD.lean` |
| Prop 11.17 C/M main | `prop_11_17_PBP_{C,M}`, `prop_11_17_PBP_{C,M}_injective` | `MYD.lean` |

## Unconditional 状态速览

- **[BMSZb] Section 10** (PBP counting + structural): ✅ **完全 unconditional**
- **[BMSZ] Section 11** AC-level: ✅ unconditional (take `source : ACResult`)
- **[BMSZ] Section 11** PBP-level: 部分 unconditional（只 shape hyps）+ 部分取 ACResult/L₁L₂ 参数作为中间定理（合理）
- **[BMSZ] Section 11** main bijection: 抽象形式（取 `e : α ≃ β` 见证 |α|=|β|），具体 concrete form 未形式化（MYD 无独立计数公式，所以 concrete form 非必要）

详见：[unconditional_PBP_theorems.md](unconditional_PBP_theorems.md), [unconditional_PBP_theorems_addendum.md](unconditional_PBP_theorems_addendum.md)

## 跳过的情况

依据 `feedback_skip_cstar_dstar.md`：**跳过 C*/D* real-form variants**（Lemma 11.2, Prop 11.18–21 等）。仅覆盖 ★ ∈ {B, D, C, M}。
