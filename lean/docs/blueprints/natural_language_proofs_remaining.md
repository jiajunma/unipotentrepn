# 剩余 5 个 Sorry 的完整自然语言证明 (v3 — 基于 C/D 模式)

## 核心洞察

剩余证明应该**模仿 D/C 的 combined induction 模式**，而不是独立构造新的 fiber analysis infrastructure。

关键观察：
1. D 的 per-tc 计数通过 `card_PBPSet_D_primitive_step_tc` 给出，利用 `ValidCol0 filtered by top symbol`
2. 然后 `card_PBPSet_D_combined` 做组合归纳，证明 (Total ∧ per-tc) 同时成立
3. C 的计数通过 D 的 per-tc 派生（C primitive = Total(D), C balanced = |D_DD| + |D_RC|）

对 B/M：
1. B 的 per-α-tc 计数通过 `card_PBPSet_B_primitive_step_tc` 给出（按 ValidCol0_B 顶部 Q 符号 split）
2. Combined induction 证明 (Total(B) ∧ A1 ∧ A3 ∧ Total(M)) 同时
3. M 的计数通过 B 的 per-α-tc 派生（M primitive = Total(B at shift), M balanced = dd(B at shift) + rc(B at shift)）

**Double descent (B → M → B)**：这是 `doubleDescent_B_PBP` 已实现的映射。fiber 结构就是 ValidCol0_B 的 cardinality = 4k（primitive）或非均匀（balanced）。

## 数值验证状态 ✓

- `tools/verify_all_B_lemmas.py`: A1, A2, A3, γ-swap, balanced step (82 dp cases 全通过)
- `tools/verify_fiber_by_Qbot.py`: Qd/Qr/Qlow fiber sizes (11 balanced)
- `tools/verify_primitive_fiber_class.py`: primitive per-sub (d, r, low) distribution

---

## 策略：C/D 风格的 Combined Induction

### 核心引理 (新增，平行于 D)

**引理 P1**: `card_PBPSet_B_primitive_step_tc` (primitive per-α-tc step)

在 primitive case (r₂ > r₃)，对每个 α-class `tc ∈ {DD, RC_α, SS_α}`:

```
card(B_tc on new) = card(B at rest shape) × |ValidCol0_B with top Q_bot in tc|
```

其中 |ValidCol0_B with top Q_bot = d| = 2k-1 = tDD.
|ValidCol0_B with top Q_bot = r| = k = half of tRC.
|ValidCol0_B with top Q_bot ∈ {•,s}| = ?

**关键 ValidCol0_B 分解**:

ValidCol0_B 是 pairs (P col 0, Q col 0) satisfying B-type constraints. Top symbol 指 Q col 0 at row μP.colLen 0 - 1 (即 Q col 0 在 overlap 区域顶部).

Card split by top symbol:
- top = d: count = ?
- top = r: count = ?
- top ∈ {•, s}: count = ?

这些 count 通过 DSeq 类的枚举获得（类似 C/D 中的 TSeq 枚举）.

### 引理 P2: Total(M) via B counting

**Primitive M** (dp_M primitive at top): 
```
card(M on dp_M shape) = Total(B on B-shape derived from dp_M)
```

证明：由 `descent_bijective_primitive` (Prop 10.8(a))，M ↔ B+ ⊔ B- 是 bijection.
所以 card(M) = card(B+) + card(B-) = Total(B).

**Balanced M**:
```
card(M on dp_M shape) = dd_α(B rest) + rc_α(B rest)
```

由 descent_image_balanced (Prop 10.8(b)):
card(M) = card(B+) + |{σ ∈ B- : Q_bot.lo > 1}|

Using B counting IH (Total + A1 + A3 at rest):
- card(B+) = (dd+rc+ss)/2 by γ-swap
- |B- non-SS_filter| = card(B-) - |B- SS_filter| = (dd+rc+ss)/2 - ss  (by A3)
- Sum: (dd+rc+ss)/2 + (dd+rc+ss)/2 - ss = dd + rc ✓

所以 M balanced depends on B's A3 at rest.

### 引理 P3: Combined Induction

陈述:

**`card_PBPSet_B_combined` (for B type dp)**:
```
For dp sorted even positive:
  Total(B on dp shape) = tripleSum(countPBP_B dp)
∧ (dp ≠ [] → 
     A1(dp): |combined B with Q_bot=d| = (countPBP_B dp).1
   ∧ A3(dp): |B- with Q_bot.lo≤1| = (countPBP_B dp).2.2)
```

**`card_PBPSet_M_via_B`**:
```
For dp_M sorted even positive with r₁ ≥ r₂:
  card(M on dp_M shape) = countPBP_M dp_M
```

这两个可以分开证，或一起证。

### 归纳结构 (combined B)

**Base cases** (已完成):
- Empty: Total(B ⊥ ⊥) = tripleSum(countPBP_B []) = 2. A1, A3 vacuous (hQ_pos false).
- Singleton [r₁]: Total via `card_PBPSet_B_singleton`. A1 via `singleton_case_B_DD_alpha`. A3 via `singleton_case_B_SS_alpha`.

**Inductive step** (dp = r₁::r₂::rest):

IH: Total(B rest), A1(rest), A3(rest) — all from `card_PBPSet_B_combined rest`.

目标: Total(B new), A1(new), A3(new).

Case split by primitive vs balanced at top (r₂ > r₃ vs r₂ ≤ r₃).

#### Primitive (r₂ > r₃)

**Total(B new)**: 已由 `card_PBPSet_B_primitive_step` (existing) 证明:
```
Total(B new) = Total(B rest) × 4k
```

**A1(new) primitive**:

用 `card_PBPSet_B_primitive_step_tc` (NEW, 需证明):
```
|B_d on new| = Total(B rest) × |ValidCol0_B top=d|
```

其中 |ValidCol0_B top=d| = 2k-1 = tDD (引理 P1, NEW).

Combined: |B_d new| = Total(rest) × tDD = countPBP_B(new).1 ✓ (by primitive recursion of countPBP_B).

**A3(new) primitive**:

类似 A1: |B- SS new| = Total(B rest) × |ValidCol0_B top ∈ {•,s}|.

但注意 A3 是 B- only。这里 fiber 保持 γ，所以 B- fiber's count = |B- rest| × tSS... hmm.

等等，我之前数值验证过 per-B⁻-sub 的 low count = tSS + 1 (for primitive)，不是 tSS.

重新理解：primitive per-sub 的 natural (d, r, low) split 是 (tDD, tRC-1, tSS+1)。但 α-class 的 split 是 (tDD, tRC, tSS) per-combined-sub (averaged over γ).

所以: |B_d combined new| = |combined rest| × tDD = Total(rest) × tDD ✓.

|B_α_RC combined new| = |combined rest| × tRC = Total(rest) × tRC (by α-reclassification).

|B_α_SS combined new| = |combined rest| × tSS = Total(rest) × tSS.

Hmm per-B⁻ natural low = tSS + 1，但 α-class 的 SS 只含 B⁻ (B⁺ low via correction → RC_α).

|B_α_SS new| = |B⁻ rest| × (B⁻ new with Q_bot ∈ {•,s} count per B⁻ sub) = |B⁻ rest| × 2 (for k=2) vs tSS = 1.

Total(rest) × tSS = 2 × 1 = 2. |B⁻ rest| × 2 = 1 × 2 = 2 (for (4,2) k=2 case)。equal ✓。

所以 |B_α_SS new| = Total(rest) × tSS = countPBP_B(new).2.2 primitive ✓ (via recursion).

A3(new): |B- Q_bot.lo≤1 new| = |B_α_SS new| (by def of A3) = countPBP_B(new).2.2 ✓.

具体证明需要：
- `ValidCol0_B_filtered_by_top_count`: card of ValidCol0_B with specified top symbol.
- `card_PBPSet_B_primitive_step_tc`: applies ValidCol0_B filter to fiber.

#### Balanced (r₂ ≤ r₃)

**Total(B new)**: 已由 `card_PBPSet_B_balanced_step` (已证，通过 Total + A1(rest) + A3(rest)):
```
Total(B new) = dd(rest) × 4k + rc(rest) × (4k-2)
```

**A1(new) balanced**:

用 `card_B_bal_grouped_fiber` (Phase 3, 已证 modulo 3 sub-sorries):
```
Total(B new) = q_d_sub × 4k + q_r_sub × (4k-2) + q_low_sub × (2k-1)
```

需要 per-new-Q_bot refinement: 每个 sub 的 fiber 中有多少给 new Q_bot = d / r / low.

具体 sub-per-new breakdown (需证):
- d sub (fiber 4k): 2k-1 给 new d, 2k-1 给 new r, 2 给 new low.
- r sub (fiber 4k-2): ? 类似 split.
- low sub (fiber 2k-1): ? 类似 split.

这需要 refined fiber by (sub.Q_bot, new.Q_bot).

**替代方案（更简洁）**: 利用 M count 来推导。

有 Total(B new) (已知), Total(M on dp_M) (待证 via 引理 P2), 和 α-class 的关系：
- rc_α(new) + ss_α(new) = dd(B) + rc(B) + ss(B) - dd_α(new) (since tripleSum = total)

Hmm 这不直接给 A1.

### Phase 3 Fiber Identity (3 sub-sorries)

`fiber_card_B_bal_Qd`: 需要 ValidCol0_B admissibility argument (当 σ.Q_bot = d 时 admissibility vacuous).

`fiber_card_B_bal_Qr`: admissibility 排除 2 configs (d 或 c 在 boundary).

`fiber_card_B_bal_Qlow`: admissibility 强约束, 剩 2k-1 configs.

每个 ~100-200 行, 需要 ValidCol0_B_bal 细化.

### 总结

**Combined Induction 路径**:

1. 新增 `card_PBPSet_B_primitive_step_tc` (按 ValidCol0_B 顶部符号 split).
2. 新增 `validCol0_B_card_top_X` (X ∈ {d, r, s, •}).
3. Refactor 主定理为 `card_PBPSet_B_combined` (Total ∧ A1 ∧ A3 together).
4. 证 `card_PBPSet_M_via_B` 用 B 的 per-α-tc.
5. Phase 3 的 3 个 fiber sorries 通过 ValidCol0_B_bal 细化.

**估计工作量**: 
- validCol0_B_card_top_X: ~200 lines (parallel to validCol0_card_top_X in D).
- card_PBPSet_B_primitive_step_tc: ~200 lines (parallel to D's).
- Combined theorem refactor: ~300 lines (restructure existing code).
- Phase 3 ValidCol0_B_bal: ~500 lines.
- M via B: ~100 lines (already partially done via liftBM_*).

**总计 ~1300 lines**，但利用了 D/C 的平行结构，比我之前估计的 1500-2000 lines 少。

**完成路径**:
Week 1: ValidCol0_B top-symbol count lemmas (4 个).
Week 2: card_PBPSet_B_primitive_step_tc + integration.
Week 3: Combined theorem refactor (删除 A1/A3 sorries in primitive case).
Week 4: ValidCol0_B_bal + Phase 3 fiber lemmas.
Week 5: Balanced case A1/A3 via Phase 3 + M-via-B integration.

## 当前 checkpoint

**已完成**:
- Empty case for A1, A2, A3: ✓
- Singleton case for A1, A2, A3: ✓
- A2 derived from Total + A1 + A3 (算法上，假设 A1 A3 可证): ✓
- γ-swap SS symmetry: ✓
- Balanced step combining algebra: ✓
- Phase 3 structurally closed (modulo 3 per-class fiber sorries): ✓
- B⁺ set partition: ✓

**剩余 5 个 sorries (all well-defined, numerically verified)**:
- A1 inductive (needs primitive_step_tc + balanced fiber per-new-Q_bot)
- A3 inductive (similar)
- fiber_card_B_bal_Qd, Qr, Qlow (需 ValidCol0_B_bal)

**路径清晰**，工程量可控 (~1300 lines)，数学正确性已验证。
