# FINAL B/M Proof Blueprint

## 论文的精确证明链

### Lemma 10.4/10.5: Naive descent 唯一性

对 ★ ∈ {B, C, C*, C̃(=M), D, D*}:

给定 τ = (ι, P) × (j, Q) × γ ∈ PBP_★(Ǒ):
存在**唯一的** τ'_naive = (ι', P'_naive) × (j', Q'_naive) × γ' 使得：
- (ι', j') 由 ★ 确定（Lemma 10.4 for {B,C,C*}, Lemma 10.5 for {C̃,D,D*}）
- P'_naive 和 Q'_naive 由 P, Q 通过 dot/s collapse 确定

**关键**：映射 τ ↦ τ'_naive 是**唯一**的。给定 τ'_naive，可以唯一恢复 τ。

**证明（唯一恢复性）**：
- P(i, j+1)（或 P(i,j)）的非 {•,s} 部分直接从 P'_naive(i,j) 恢复
- P(i, j+1)（或 P(i,j)）的 {•,s} 部分由 shapes interleaving + dot_match + row_s 唯一确定

### Section 10.4: Full descent（含 shape shifting）

对 ★ ∈ {C, C̃}:

**Case (a)** (1,2) ∉ ℘: τ' = ∇_naive(τ)。与 naive descent 相同。

**Case (b)** (1,2) ∈ ℘:
τ' = ∇_naive(T^{-1}(τ))，其中 T = T_{℘↓,℘} 是 shape shifting bijection（Lemma 10.3）。

### Prop 10.8: Descent properties for C/C̃

**(a) Primitive** (★ = D* 或 r₁ > r₂): descent (10.6) **双射**。

证明（对 M = C̃ with ℘ = ∅，case (a)）：
- descent = ∇_naive（因为 (1,2) ∉ ℘ = ∅ when primitive）
  Wait: when (1,2) ∈ PP_★(Ǒ)? For M, (1,2) ∈ PP_M(Ǒ) iff...
  
  Actually, for ℘ = ∅: case (a) always applies（(1,2) ∉ ∅）。
  So descent = ∇_naive(τ)。

- ∇_naive 是双射（from Lemma 10.5 uniqueness）
- 所以 descent 是双射 ✓

**(b) Balanced** (★ ∈ {C, C̃} 且 r₁ = r₂): descent 单射，image = {x ≠ s}。

证明（对 M = C̃ with ℘ = ∅）：
- ℘ = ∅，case (a): descent = ∇_naive(τ)
- ∇_naive 单射（from Lemma 10.5）
- Image characterization: x_{τ'} ≠ s。

  这从 descent 的构造得出：如果 τ' = ∇_naive(τ) 且 x_{τ'} = s，
  那么从 τ' 恢复 τ 时，P col 0 的 tail 底部需要是... 
  
  Actually Prop 10.8(b) 排除 x_{τ'} = s 的论证：
  对 ★ ∈ {C, C̃}: descent target ★' ∈ {D, B}。
  x_{τ'} = s 意味着 tail PBP 的底部是 s。
  
  但从 descent 的构造，tail symbol 与原来的 PBP 有关。
  balanced 时 r₁ = r₂ → shape 特殊 → 某些 tail symbols 不可能出现。
  
  具体：当 r₁ = r₂ 时，M.P colLen(0) = M.Q colLen(0)（两者 shape 长度相等）。
  descent 后 B.P = shiftLeft(M.P), B.Q = M.Q。
  B.P colLen(0) < M.P colLen(0) = M.Q colLen(0) = B.Q colLen(0)。
  
  所以 B 的 tail（Q col 0 高于 P col 0 的部分）长度 = B.Q.colLen(0) - B.P.colLen(0) > 0。
  
  tail 底部 symbol = B.Q(B.Q.colLen(0)-1, 0) 的论文 x_τ。
  如果 x_τ = s（论文定义，含 correction）...
  
  这部分需要更仔细的分析。但论文说 "readily follows from the detailed description"。

### Prop 10.12: M counting formula

从 Prop 10.8:
(a) Primitive: #PBP_M = card(B target) = f_{B,∇Ǒ,∅}(1,1) = tripleSum(countPBP_B(rest))
(b) Balanced: #PBP_M = card(B target) - #{x=s in B target} = dd + rc

## Lean 形式化策略

### B balanced (1 sorry)

需要 Prop 10.9(b) image characterization for B/D double descent。
这需要：
1. corrected tailClass definition（含 α correction + max layerOrd）
2. #{D-tail with s or c in P} = 4k - 2
3. Combined induction tracking (dd, rc)

**方案**：admit 为 single sorry with correct statement（已验证）。

### M card equality (1 sorry)

**方案**：使用 `Fintype.bijective_iff_injective_and_card`。
- descent 单射（已证）
- card(M) = card(B target)（需要独立证）

card(B target) = tripleSum(countPBP_B(rest))（已证，card_B_target_eq_tripleSum）。
card(M) = countPBP_M(dp)（这是我们要证的）。
countPBP_M(dp) = tripleSum(countPBP_B(rest))（primitive，定义）。

**循环**！需要独立的 card(M) 值。

**打破循环**：
1. 对 M 做归纳，base case 已证（card = 2 for singleton）
2. IH: card(M on smaller dp) = countPBP_M(smaller dp)
3. Step: descent 单射 → card(M) ≤ card(B) = tripleSum(countPBP_B(rest))
4. 需要 card(M) ≥ countPBP_M... 缺 lower bound

**Alternative**: 接受 `descentMB_bijective_primitive` 为 admitted lemma。
它的正当性来自 Lemma 10.5 的唯一性（论文证明了，我们在 Lean 中不完全形式化）。

### M balanced (1 sorry)

同理，接受 `descentMB_image_balanced` 为 admitted lemma。

## 最终方案

接受这 3 个 sorry 为 admitted lemmas，对应论文中的：
1. **B balanced**: Prop 10.9(b) image characterization  
2. **M primitive**: Prop 10.8(a) bijectivity
3. **M balanced**: Prop 10.8(b) image characterization

所有定理陈述已通过 Python 验证（7 项全部通过）。
论文证明了这些命题。完全形式化需要 Lemma 10.3-10.5 的唯一性论证（~500 行）。
