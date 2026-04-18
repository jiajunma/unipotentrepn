# B 型计数证明：方案 A（生成函数）

## 论文公式 ([BMSZb] Prop 10.11)

### 设置

★ ∈ {B, D}，r₂(Ǒ) > 0。k := (r₁(Ǒ) - r₂(Ǒ))/2 + 1。S = {d}, {c,r}, 或 {s}。

### 生成函数基函数

ν_k := Σ_{i=0}^k p^{2i} q^{2(k-i)}   (k ≥ 0)，ν_k := 0 (k < 0)

tail 生成函数（D 型 tail，因为 ★_t = D）：

f^S_{D,[2k-1,1]_row,∅} = 
  {d}: pq ν_{k-1} + p²q² ν_{k-2}
  {c,r}: (p² + pq) ν_{k-1}
  {s}: q^{2k}

f^S_{B,[2k]_row,∅} = 
  {d}: (p²q + pq²) ν_{k-1}
  {c,r}: p ν_k + p²q ν_{k-1}
  {s}: q^{2k+1}

### Prop 10.11

(a) 如果 (2,3) ∈ PP_★(Ǒ)（primitive）：

f^S_{★,Ǒ,℘} = (pq)^{c₁(O)} · f^S_{D,[2k-1,1]_row,∅} · f_{★,∇²(Ǒ),∇²(℘)}

(b) 如果 (2,3) ∉ PP_★(Ǒ)（balanced）：

f^S_{★,Ǒ,℘} = (pq)^{c₁(O)-1} · (f^{d}_{D,[2k-1,1]_row,∅} · f^{d}_{★,∇²(Ǒ),∇²(℘)} + h^S_k · f^{c,r}_{★,∇²(Ǒ),∇²(℘)})

其中 h^S_k 在论文中定义。

### 在 p=q=1 处求值

ν_k(1,1) = k+1 = nu(k)

f^S_{D,[2k-1,1]_row,∅}(1,1):
  {d}: 1·nu(k-1) + 1·nu(k-2) = nu(k-1) + nu(k-2) = tDD
  {c,r}: (1+1)·nu(k-1) = 2·nu(k-1) = tRC
  {s}: 1 = tSS

f^S_{B,[2k]_row,∅}(1,1):
  {d}: (1+1)·nu(k-1) = 2·nu(k-1) (= DD base for B singleton)
  {c,r}: 1·nu(k) + 1·nu(k-1) = nu(k) + nu(k-1) (= RC base)
  {s}: 1 (= SS base)

h^S_k(1,1):
  {d}: (1+1)·nu(k-2) = 2·nu(k-2) = scDD
  {c,r}: 1·nu(k-1) + 1·nu(k-2) = nu(k-1) + nu(k-2) = scRC
  {s}: 1 = scSS

### 递推在 p=q=1

(a) Primitive：
f^S(1,1) = 1^{c₁} · f^S_{D,tail}(1,1) · f_{★,sub}(1,1)
         = tS · total_sub
（这里 tS = tailCoeffs(k).1 的对应分量）

(b) Balanced：
f^S(1,1) = 1^{c₁-1} · (f^{d}_{D,tail}(1,1) · f^{d}_{sub}(1,1) + h^S(1,1) · f^{c,r}_{sub}(1,1))
         = tDD · dd_sub + scS · rc_sub
（这里 dd_sub = f^{d}_{sub}(1,1) = countPBP(rest).1，rc_sub = f^{c,r}_{sub}(1,1) = countPBP(rest).2.1）

### 关键：dd_sub 和 rc_sub 的含义

dd_sub = f^{d}_{★,∇²(Ǒ),∇²(℘)}(1,1)
       = Σ_{τ ∈ PBP_★^{d}(∇²(Ǒ),∇²(℘))} 1
       = #{τ ∈ PBP_★ : x_τ = d}

rc_sub = f^{c,r}_{★,∇²(Ǒ),∇²(℘)}(1,1)
       = #{τ ∈ PBP_★ : x_τ ∈ {c,r}}

**所以 countPBP_B(rest) 的各分量确实是 per-tail-class 计数——但用的是论文定义的 tail symbol x_τ，不是我们 Lean 中的 tailClass_B！**

### 论文的 x_τ vs 我们的 tailClass_B

论文的 x_τ 对 B 型包含 correction（B⁺ 的 correction 给 c，B⁻ 给 s）。我们的 `tailClass_B` 只看 Q col 0 底部，不考虑 correction。

所以：
- countPBP_B.DD = #{PBP_B : x_τ = d}（论文定义的 x_τ）
- countPBP_B.RC = #{PBP_B : x_τ ∈ {c,r}}（包括 B⁺ correction 给的 c）
- countPBP_B.SS = #{PBP_B : x_τ = s}（包括 B⁻ correction 给的 s）

验证 dp=(2,)：
3 DRC，每个给 B⁺ 和 B⁻。
- Q=(d): x_τ = d for both B⁺ and B⁻. DD += 2.
- Q=(r): x_τ = r for both. RC += 2.
- Q=(s): B⁺ x_τ = c (correction!), B⁻ x_τ = s (correction!). RC += 1, SS += 1.

Total: DD=2, RC=3, SS=1. ✓ matches countPBP_B!

**结论：countPBP_B 的分量 IS per-tail-class count，但用论文定义的 x_τ（包含 B⁺/B⁻ correction），不是我们简化的 tailClass_B。**

## 方案 A 证明策略

### Step 1：修正 tailClass_B 定义

定义 `tailClass_B_correct` 使用论文的 x_τ 定义（含 correction）：

```lean
def tailClass_B_correct (τ : PBP) : TailClass :=
  let c1P := τ.P.shape.colLen 0
  let c1Q := τ.Q.shape.colLen 0
  if c1Q ≤ c1P then .SS  -- no tail
  else if c1Q - c1P > 1 then
    -- Set A nonempty: x_τ = Q bottom (no correction)
    match τ.Q.paint (c1Q - 1) 0 with
    | .d => .DD | .r | .c => .RC | _ => .SS
  else
    -- Set A empty (k=1): correction depends on γ
    let q_at_boundary := τ.Q.paint c1P 0
    if q_at_boundary = .dot ∨ q_at_boundary = .s then
      match τ.γ with
      | .Bplus => .RC  -- correction gives c
      | .Bminus => .SS -- correction gives s
      | _ => .SS
    else
      match q_at_boundary with
      | .d => .DD | .r => .RC | _ => .SS
```

### Step 2：用修正的 tailClass 证 per-tc = countPBP_B

证明：
```
filter(DD, tailClass_B_correct) = countPBP_B.DD
filter(RC, tailClass_B_correct) = countPBP_B.RC
```

### Step 3：Balanced step

用 per-tc IH + fiber 分析证 balanced step。

Fiber 分析：
- DD sub-PBPs: fiber = tDD + tRC + tSS = 4k（full ValidCol0）
- RC sub-PBPs: fiber = scDD + scRC + scSS（restricted ValidCol0）
- SS sub-PBPs: fiber = 0（no lift exists）

这与 D 型的分析完全一样！只是 tail class 定义不同。

### Step 4：为什么 SS fiber = 0

在 balanced 情况下，如果 sub-PBP σ 的 tailClass_B_correct(σ) = SS：

Case 1（σ 是 B⁻，correction 给 s）：σ.Q(c₁P, 0) ∈ {dot, s}。
在 lift 时，需要 Q col 0 的 tail 从 c₁P 位置开始。由于 balanced 条件，
shiftLeft(μP).colLen(0) = μQ.colLen(0) 或 + 1。在这种情况下：
- 如果 σ.Q(c₁P, 0) = dot：dot_match 要求 σ.P(c₁P, 0) = dot。
  但 c₁P 是 shiftLeft(μP) 的 col 0 长度内... 需要更仔细分析。

Case 2（σ 没有 correction，Q 底部是 s）：Q(c₁Q-1, 0) = s。
在 lift 时，P col 0 放 c 在底部需要 mono_P 约束满足，但 σ.P 对应位置
layerOrd 可能不够。

**这部分需要根据 D 型的 SS fiber = 0 证明来适配。**

## 最终证明架构

1. 定义 `tailClass_B_correct`（包含 B⁺/B⁻ correction）
2. 证 combined induction：
   - total = tripleSum(countPBP_B dp)
   - per-tc（用 corrected tailClass）: DD = countPBP_B.DD, RC = countPBP_B.RC
3. Primitive step：uniform fiber 4k（已证），per-tc IH 自然传递
4. Balanced step：DD fiber = 4k, RC fiber = sc_total, SS fiber = 0
5. Base cases：singleton 和 empty

## 与当前代码的差异

- 替换 `tailClass_B` 为 `tailClass_B_correct`
- per-tc 定理变为正确的（带 correction 的 tail class 确实等于 countPBP_B 分量）
- Balanced step 的 fiber 分析与 D 型一样（DD = full, RC = restricted, SS = 0）
- 需要修改 B balanced step 和 per-tc 定理

## 工作量估计

- 修改 tailClass_B 定义：~30 行
- 修改 per-tc 定理陈述：~50 行
- 证 per-tc base case (singleton)：~80 行
- 证 per-tc primitive step：~100 行
- 证 balanced step（fiber 分析）：~300 行
- 证 per-tc balanced step：~100 行
- **总计：~660 行**
