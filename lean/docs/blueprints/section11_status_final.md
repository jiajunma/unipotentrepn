# [BMSZ] Section 11 Formalization — Status

## Lean 形式化
核心实现全部在 `CombUnipotent/MYD.lean` 及其子目录 `CombUnipotent/MYD/*.lean`。
详细定理对照见 [INDEX.md](INDEX.md)。

## 总览

Section 11 Associated Cycles combinatorial aspect (for ★ ∈ {B, D, C, M = C̃};
C*/D* 跳过) 的形式化进度。

## 已完成 — Abstract (ACResult/ILS) 层 ✅

### Foundational infrastructure

| Area | Lean |
|---|---|
| MYD / ILS / ACResult types | ✅ |
| `charTwistCM`, `augment`, `twistBD`, `thetaLift_{CD,DC,MB,BM}` | ✅ |
| sign, firstColSign definitions | ✅ |
| `sign/firstColSign` preservation through charTwistCM, twistBD | ✅ |
| `AC.base`, `AC.step`, `AC.fold` | ✅ |

### Sign/firstColSign tracking (本 session 完成)

| Theorem | ✅ |
|---|---|
| `ILS.thetaLift_{CD,DC,MB,BM}_firstColSign` | ✅ 新 |
| `ACResult.thetaLift_{CD,DC,MB,BM,Bplus,Bminus}_firstColSign` | ✅ 新 |
| `AC.step_firstColSign_{D,Bplus,Bminus,C,M}` (all 5 root types) | ✅ 新 |
| `AC.step_firstColSign_BD` unified | ✅ 新 |
| `AC.base_firstColSign_eq_sign` | ✅ 新 |
| `AC.two_step_firstColSign_BD_outer` | ✅ 新 |
| `AC.chain_firstColSign_eq_diff_sign` | ✅ 新 |

### Section 11 theorems at abstract level

| Paper | Lean | Status |
|---|---|---|
| **Lemma 11.1**(a) empty | `lemma_11_1_a_empty` | ✅ |
| **Lemma 11.1**(a) r₁=1 | `lemma_11_1_a_r1_one` | ✅ |
| **Lemma 11.1**(b) (p,q) injectivity | `lemma_11_1_signed_injective_pq` | ✅ |
| **Lemma 11.3** | `tailSymbol_*_iff`, `tail_all_s_*` 等 | ✅ |
| **Prop 11.4** signature decomp | `prop_11_4_signature_decomp_D` | ✅ |
| **Prop 11.5** conditional | `prop_11_5_D` (takes PBP identity as hyp) | ✅ |
| **Lemma 11.6** abstract | `BMSZ.first_entry_after_twist` | ✅ |
| **Prop 11.7** | `prop_11_7_multiplicityFree` | ✅ |
| **Prop 11.8**(a) | `prop_11_8_nonzero` | ✅ |
| **Prop 11.8**(b/c/d) | `BMSZ.prop_11_8` | ✅ |
| **Lemma 11.10** | `BMSZ.first_entry_eq_of_eq` | ✅ |
| **Lemma 11.11** | `prop_11_11_no_det` | ✅ |
| **Prop 11.12** | `prop_11_12` | ✅ |
| **Lemma 11.13** | `BMSZ.ac_chain_injective` + family | ✅ |
| **Lemma 11.14** | `BMSZ.ac_twist_charTwist_surjective` etc. | ✅ |
| **Prop 11.15** | `prop_11_15` (injectivity mod twist) | ✅ |
| **Prop 11.16** | `card_PBPSet_C_eq_countPBP_C` (counting side) | ✅ |
| **Prop 11.17** | `prop_11_17` | ✅ |

## 尚待完成 — PBP Level Integration

**核心剩余工作**：将所有抽象 (ACResult/ILS-level) 定理实例化到 PBP 层面，
即建立 **AC.fold(descent chain of τ) = 𝓛_τ** 的连接。

### Primary blocker：Lemma 11.5 PBP identity discharge

现状：
- `ILS.lemma_11_5_D` 取 `h_pt/h_qt` 作为 explicit hypothesis
- 用 firstColSign 不变量（本 session 新增）可以 **algebraically** discharge
- 需要写 `lemma_11_5_D_PBP_unconditional` 把 PBP 实际值代入 + 用 Prop 11.4

### Secondary PBP connections

- Lemma 11.6 PBP 层：first entry 公式 in PBP signature 术语
- Prop 11.8 PBP 层：nonzero + truncation pattern
- Prop 11.15 PBP 层：main bijection (已有 `prop_11_15_PBP` partial)

### 估计工作量

- Lemma 11.5 unconditional：~200 行 Lean（代数展开 + shape relations）
- PBP layer glue for 11.6/11.8/11.15：~300-500 行
- Prop 11.17 PBP version：~200 行

**总量**：~800-1200 行 Lean additional work。

## 下一步 action

用户已要求 "持续形式化，直到所有定理证明了"。下一步做的事：

1. **证明 Lemma 11.5 PBP unconditional**（用 firstColSign 不变量 + Prop 11.4）
2. **形式化 AC.fold ↔ PBP 连接定理**（关键 glue）
3. **Propagate to 11.6, 11.8, 11.15, 11.17 PBP 层**

各步骤都是在已有 infrastructure 之上的组合工作，不再有"缺自然语言证明"问题。

## 当前 commits (本 session)

14 个新 commits pushed to `origin/lean`:
- `596281e` Lemma 11.1(a) empty
- `07fd2c7` Lemma 11.1(a) r₁=1
- `95390b1` Lemma 11.1(b) (p,q) injectivity
- `5c99a3b` Prop 11.4 signature decomp
- `4efad46` Prop 11.5 named wrapper
- `9fddbd8` Lemma 11.6 reference
- `23fe450` Prop 11.7
- `f58e54c` Prop 11.8/11/12/15/17 aliases
- `8015ed6` 5 natural-language blueprints
- `7f3d0f2` twistBD_firstColSign
- `93f66ae`, `97e60a5` thetaLift firstColSign
- `b5560a3`, `d91089c`, `3a9b055` ACResult firstColSign
- `1a00538`, `851a67c`, `a00d48a` AC.step_firstColSign
- `99a1205` AC.base_firstColSign_eq_sign
- `7527b27` two_step
- `5674c4a` firstColSign invariant blueprint
- `5841009` chain_firstColSign_eq_diff_sign
- (本 commit) section 11 status final

**Build**: GREEN, 0 sorries in MYD.lean.
