# Lemma 10.3: M 型 Shape Shifting 完整证明

Reference: [BMSZb] Section 10.2, Lemma 10.3.

---

## 0. 记号

- M 型 PBP τ = (P, Q, M)，P 有符号 {•, s, c}，Q 有符号 {•, r, d}。
- layerOrd: •=0, s=1, r=2, c=3, d=4。
- translateM: •↔•, s↔r, c↔d。即 translateM 在 {•,s,c} 和 {•,r,d} 之间做对应。
- c_k(X) := X.colLen(k-1)（1-based 列号），本文用 0-based：P.colLen(j)。
- PBP axioms: sym_P, sym_Q, dot_match, mono_P, mono_Q, row_s, row_r, col_c_P, col_c_Q, col_d_P, col_d_Q。
- layerMonotone(D) := ∀ i₁ j₁ i₂ j₂, i₁≤i₂ → j₁≤j₂ → (i₂,j₂) ∈ D.shape → D.paint(i₁,j₁).lo ≤ D.paint(i₂,j₂).lo。
  注意 (i₁,j₁) 不要求在 shape 内；若不在，则 paint = •(lo=0)，条件自动满足。

---

## 1. 前置条件

设 τ 是 M 型 PBP，P.shape = μP，Q.shape = μQ。

存在两种交错（interleaving）情况：

**(A) (1,2) ∉ ℘（右交错）**: P.colLen(0) ≥ Q.colLen(0) ≥ P.colLen(1) ≥ Q.colLen(1) ≥ ...

**(B) (1,2) ∈ ℘（左交错）**: Q.colLen(0) ≥ P.colLen(0) ≥ Q.colLen(1) ≥ P.colLen(1) ≥ ...

两种情况的共同性质（设 p = P.colLen(0), q = Q.colLen(0)）：
- **Shape 有效性条件**：q ≥ P.colLen(1) 且 p ≥ Q.colLen(1)。
  - 情况 A：q ≥ P.colLen(1)（交错）；p ≥ q ≥ Q.colLen(1)（交错+单调）。✓
  - 情况 B：p ≥ Q.colLen(1)（交错）；q ≥ p ≥ P.colLen(1)（交错+单调）。✓

---

## 2. 定义 T(τ)

**目标 shapes**:
- μP' := "col 0 长度为 q = μQ.colLen(0)，其余列与 μP 相同"
- μQ' := "col 0 长度为 p = μP.colLen(0)，其余列与 μQ 相同"

成员关系：
- (i, 0) ∈ μP' ↔ i < q ↔ (i, 0) ∈ μQ
- (i, j+1) ∈ μP' ↔ (i, j+1) ∈ μP
- (i, 0) ∈ μQ' ↔ i < p ↔ (i, 0) ∈ μP
- (i, j+1) ∈ μQ' ↔ (i, j+1) ∈ μQ

μP' 是合法 YD：需 q ≥ μP.colLen(1)。由前置条件保证。✓
μQ' 是合法 YD：需 p ≥ μQ.colLen(1)。由前置条件保证。✓

**Paint 定义**:

```
T(τ).P.paint(i, 0) = translateM(τ.Q.paint(i, 0))
T(τ).P.paint(i, j+1) = τ.P.paint(i, j+1)

T(τ).Q.paint(i, 0) = translateM(τ.P.paint(i, 0))
T(τ).Q.paint(i, j+1) = τ.Q.paint(i, j+1)
```

**paint_outside**: 若 (i,j) ∉ shape，则 paint = •。
- (i,0) ∉ μP' → (i,0) ∉ μQ → τ.Q.paint(i,0) = • → translateM(•) = •。✓
- (i,j+1) ∉ μP' → (i,j+1) ∉ μP → τ.P.paint(i,j+1) = •。✓
- 对 Q' 类似。✓

---

## 3. PBP axiom 验证

### 3.1 sym_P: T(τ).P.paint(i,j) ∈ {•, s, c}（M 左允许集）

- **j = 0**: translateM(Q(i,0))。若 (i,0) ∈ μQ：Q(i,0) ∈ {•,r,d} → translateM 给 {•,s,c}。✓
  若 (i,0) ∉ μQ：Q(i,0) = • → translateM = •。✓
- **j ≥ 1**: P(i,j) ∈ {•,s,c}（原 sym_P）。✓

### 3.2 sym_Q: T(τ).Q.paint(i,j) ∈ {•, r, d}（M 右允许集）

- 对称论证。✓

### 3.3 dot_match: T(τ).P(i,j) = • ∧ (i,j) ∈ μP' ↔ T(τ).Q(i,j) = • ∧ (i,j) ∈ μQ'

- **j = 0**:
  LHS = translateM(Q(i,0)) = • ∧ i < q
      = Q(i,0) = • ∧ (i,0) ∈ μQ   （translateM 保持 •）

  RHS = translateM(P(i,0)) = • ∧ i < p
      = P(i,0) = • ∧ (i,0) ∈ μP

  原 dot_match：P(i,0) = • ∧ (i,0) ∈ μP ↔ Q(i,0) = • ∧ (i,0) ∈ μQ。
  所以 LHS ↔ RHS。✓

- **j ≥ 1**:
  LHS = P(i,j) = • ∧ (i,j) ∈ μP
  RHS = Q(i,j) = • ∧ (i,j) ∈ μQ
  与原 dot_match 相同。✓

### 3.4 mono_P: layerMonotone(T(τ).P)

需证：∀ i₁ j₁ i₂ j₂, i₁≤i₂ → j₁≤j₂ → (i₂,j₂) ∈ μP' → T(τ).P(i₁,j₁).lo ≤ T(τ).P(i₂,j₂).lo。

**Case 1: j₁ ≥ 1, j₂ ≥ 1**
T(τ).P(i,j) = P(i,j)。由原 mono_P 且 (i₂,j₂) ∈ μP' ↔ (i₂,j₂) ∈ μP（j₂ ≥ 1）。✓

**Case 2: j₁ = 0, j₂ = 0**（两点都在 col 0）
T(τ).P(i₁,0) = translateM(Q(i₁,0))，T(τ).P(i₂,0) = translateM(Q(i₂,0))。
(i₂,0) ∈ μP' → (i₂,0) ∈ μQ → (i₂,0) ∈ τ.Q.shape。

- 若 (i₁,0) ∈ μQ：Q(i₁,0), Q(i₂,0) ∈ {•,r,d}。
  原 mono_Q：Q(i₁,0).lo ≤ Q(i₂,0).lo。
  translateM 在 {•,r,d} 上保序（•(0)→•(0), r(2)→s(1), d(4)→c(3)，相对顺序不变）。
  所以 translateM(Q(i₁,0)).lo ≤ translateM(Q(i₂,0)).lo。✓

- 若 (i₁,0) ∉ μQ：(i₁,0) ∉ τ.Q.shape → Q(i₁,0) = • → translateM = •(lo=0) ≤ 任何值。✓

**Case 3: j₁ ≥ 1, j₂ = 0**
j₁ ≥ 1 > 0 = j₂，与 j₁ ≤ j₂ 矛盾。不可能。

**Case 4: j₁ = 0, j₂ ≥ 1**（col 0 → col ≥ 1，**关键 case**）

T(τ).P(i₁,0) = translateM(Q(i₁,0))。
T(τ).P(i₂,j₂) = P(i₂,j₂)（j₂ ≥ 1）。
(i₂,j₂) ∈ μP' → (i₂,j₂) ∈ μP → (i₂,j₂) ∈ τ.P.shape。

**Sub-case 4a**: (i₁,0) ∉ μP'（即 (i₁,0) ∉ μQ）
T(τ).P(i₁,0) = •（paint_outside），lo = 0 ≤ 任何值。✓

**Sub-case 4b**: (i₁,0) ∈ μP'（即 (i₁,0) ∈ μQ，i₁ < q）且 (i₁,0) ∈ μP（i₁ < p）

两种 shapes 都包含 (i₁,0)。此时可用原 PBP 的 dot_match。

Q(i₁,0) ∈ {•,r,d}。分三种情况：

- **Q(i₁,0) = •**: translateM = •(lo=0) ≤ 任何值。✓

- **Q(i₁,0) = r**: translateM = s(lo=1)。需证 P(i₂,j₂).lo ≥ 1。

  dot_match（原）：Q(i₁,0) ≠ • 且 (i₁,0) ∈ μQ。而 (i₁,0) ∈ μP。
  所以 P(i₁,0) ≠ •（否则 dot_match 的 LHS 成立而 RHS 不成立）。
  P(i₁,0) ∈ {s,c}，lo ≥ 1。
  原 mono_P：P(i₁,0).lo ≤ P(i₂,j₂).lo（因 i₁≤i₂, 0≤j₂, (i₂,j₂) ∈ μP）。
  所以 P(i₂,j₂).lo ≥ 1 = translateM(r).lo。✓

- **Q(i₁,0) = d**: translateM = c(lo=3)。需证 P(i₂,j₂).lo ≥ 3。

  同上，P(i₁,0) ≠ •，P(i₁,0) ∈ {s,c}。

  - 若 **P(i₁,0) = c** (lo=3)：原 mono_P 直接给 P(i₂,j₂).lo ≥ 3。✓

  - 若 **P(i₁,0) = s** (lo=1)：
    先证 (i₁,1) ∈ μP：由 lower set，(i₁,1) ≤ (i₂,j₂)（i₁≤i₂, 1≤j₂），(i₂,j₂) ∈ μP → (i₁,1) ∈ μP。

    P(i₁,1) 的值：
    - P(i₁,1).lo ≥ P(i₁,0).lo = 1（mono_P）
    - P(i₁,1) ≠ s（**row_s**：P(i₁,0) = s，每行至多 1 个 s）
    - P(i₁,1) ∈ {•,s,c} \ {s} 且 lo ≥ 1。
      • 有 lo=0 < 1，排除。s 已排除。剩 c(lo=3)。
    - 所以 P(i₁,1) = c，lo = 3。

    原 mono_P：P(i₁,1).lo ≤ P(i₂,j₂).lo。所以 P(i₂,j₂).lo ≥ 3。✓

**Sub-case 4c**: (i₁,0) ∈ μP' 但 (i₁,0) ∉ μP（即 i₁ < q 但 i₁ ≥ p；仅在 p < q 时发生）

此时 (i₁,0) ∉ μP，所以 P(i₁,0) = •（paint_outside）。
需证 (i₂,j₂) ∈ μP 是否可能（j₂ ≥ 1）。

i₂ ≥ i₁ ≥ p = P.colLen(0) ≥ P.colLen(j₂)（YD 列长单调递减）。
所以 i₂ ≥ P.colLen(j₂)，即 (i₂,j₂) ∉ μP。
但 (i₂,j₂) ∈ μP'（前提），而 j₂ ≥ 1 → (i₂,j₂) ∈ μP' ↔ (i₂,j₂) ∈ μP。矛盾。

**所以 sub-case 4c 不可能发生**（hmem₂ 不满足）。✓

### 3.5 mono_Q: layerMonotone(T(τ).Q)

完全对称于 mono_P，交换 P↔Q 的角色：
- translateM_mono_L 代替 translateM_mono_R
- row_r 代替 row_s
- 其余结构相同

具体：Case 4b 中 P(i₁,0) = c → translateM = d(lo=4)，需 Q(i₂,j₂).lo ≥ 4：
- Q(i₁,0) ∈ {r,d}（dot_match）
- 若 Q(i₁,0) = d(lo=4)：mono_Q 直接给出。✓
- 若 Q(i₁,0) = r(lo=2)：(i₁,1) ∈ μQ（lower set）。Q(i₁,1) ≠ r（**row_r**），Q(i₁,1).lo ≥ 2，Q(i₁,1) ∈ {•,r,d} \ {r} 且 lo ≥ 2。• 排除（lo=0），r 排除。剩 d(lo=4)。mono_Q 给出。✓

Sub-case 4c 类似：不可能发生。✓

### 3.6 row_s: 每行至多 1 个 s（跨 T(τ).P 和 T(τ).Q）

M 型 Q 的允许集是 {•,r,d}，**不含 s**。T(τ).Q = translateM(P) 或 Q，其值域：
- T(τ).Q(i,0) = translateM(P(i,0))：P ∈ {•,s,c} → translateM 给 {•,r,d}。**无 s**。
- T(τ).Q(i,j+1) = Q(i,j+1) ∈ {•,r,d}。**无 s**。

所以 s 只在 T(τ).P 中。需证每行至多 1 个 s 在 T(τ).P 中。

设 T(τ).P(i,j₁) = s 且 T(τ).P(i,j₂) = s，j₁ < j₂。

**Case j₁ = 0, j₂ ≥ 1**:
- T(τ).P(i,0) = translateM(Q(i,0)) = s → Q(i,0) = r。
- T(τ).P(i,j₂) = P(i,j₂) = s。

  dot_match（原）：Q(i,0) = r ≠ • → P(i,0) ≠ •（若 (i,0) ∈ μP）。
  P(i,0) ∈ {s,c}。

  - 若 P(i,0) = s：原 row_s → P(i,j₂) ≠ s（j₂ ≥ 1 ≠ 0）。矛盾。✓
  - 若 P(i,0) = c(lo=3)：mono_P → P(i,j₂).lo ≥ 3。但 s.lo = 1 < 3。矛盾。✓
  - 若 (i,0) ∉ μP（即 p ≤ i < q，sub-case 4c）：P(i,j₂) = •（同 4c 论证：i ≥ p ≥ P.colLen(j₂)）。s ≠ •。矛盾。✓

**Case j₁ ≥ 1, j₂ ≥ 1**:
T(τ).P(i,j₁) = P(i,j₁) = s，T(τ).P(i,j₂) = P(i,j₂) = s。
原 row_s → j₁ = j₂ 且 side₁ = side₂。✓

### 3.7 row_r: 每行至多 1 个 r（跨 T(τ).P 和 T(τ).Q）

对称于 row_s：r 只在 T(τ).Q 中（T(τ).P 的值域是 {•,s,c}，无 r）。
论证用 row_r + mono_Q，完全对称。✓

### 3.8 col_c_P: T(τ).P 每列至多 1 个 c

- **col 0**: T(τ).P(i,0) = translateM(Q(i,0)) = c ↔ Q(i,0) = d。
  原 col_d_Q：Q 每列至多 1 个 d → col 0 至多 1 个 d → translateM 后至多 1 个 c。✓

- **col j ≥ 1**: T(τ).P(i,j) = P(i,j)。原 col_c_P。✓

### 3.9 col_c_Q: T(τ).Q 每列至多 1 个 c

T(τ).Q 的值域是 {•,r,d}（M 右允许集）。**不含 c**。所以 col_c_Q 空真。✓

（具体：col 0 translateM({•,s,c}) = {•,r,d}，无 c；col ≥ 1 是原 Q ∈ {•,r,d}，无 c。）

### 3.10 col_d_P: T(τ).P 每列至多 1 个 d

T(τ).P 的值域是 {•,s,c}（M 左允许集）。**不含 d**。空真。✓

### 3.11 col_d_Q: T(τ).Q 每列至多 1 个 d

- **col 0**: T(τ).Q(i,0) = translateM(P(i,0)) = d ↔ P(i,0) = c。
  原 col_c_P → col 0 至多 1 个 c → translateM 后至多 1 个 d。✓

- **col j ≥ 1**: T(τ).Q(i,j) = Q(i,j)。原 col_d_Q。✓

---

## 4. Involution（T ∘ T = id）

设 τ' = T(τ)。则 T(τ') 有：
- T(τ').P.paint(i,0) = translateM(τ'.Q.paint(i,0)) = translateM(translateM(τ.P.paint(i,0))) = τ.P.paint(i,0)
- T(τ').P.paint(i,j+1) = τ'.P.paint(i,j+1) = τ.P.paint(i,j+1)
- T(τ').Q.paint(i,0) = translateM(τ'.P.paint(i,0)) = translateM(translateM(τ.Q.paint(i,0))) = τ.Q.paint(i,0)
- T(τ').Q.paint(i,j+1) = τ'.Q.paint(i,j+1) = τ.Q.paint(i,j+1)

Shapes: T(τ') 的 P'.shape 有 col 0 长度 = τ'.Q.colLen(0) = μP.colLen(0) = p，cols ≥ 1 = τ'.P = μP。
所以 T(τ').P.shape = μP = τ.P.shape。类似 T(τ').Q.shape = μQ。

γ 不变（都是 M）。

所以 T(T(τ)) = τ（paint 和 shape 都还原）。✓

---

## 5. Prop 10.2: card 相等

T: PBPSet .M μP μQ → PBPSet .M μP' μQ' 是良定义映射（第 3 节证明了 PBP axioms）。

T 的逆是 T 本身（应用于 (μP', μQ') → (μP, μQ)），因为 T ∘ T = id（第 4 节）。

所以 T 是双射。因此：

$$\text{card}(\text{PBPSet}\;.\text{M}\;\mu_P\;\mu_Q) = \text{card}(\text{PBPSet}\;.\text{M}\;\mu_{P'}\;\mu_{Q'})$$

其中 μP'.colLen(0) = μQ.colLen(0)，μQ'.colLen(0) = μP.colLen(0)，其余列不变。✓

---

## 验证摘要

| Axiom | 关键论证 | 用到的原 axiom |
|-------|---------|---------------|
| sym_P | translateM: {•,r,d} → {•,s,c} | sym_Q |
| sym_Q | translateM: {•,s,c} → {•,r,d} | sym_P |
| dot_match | translateM 保持 •；原 dot_match | dot_match |
| mono_P | Case 4b: dot_match + mono_P + **row_s** | mono_P, mono_Q, row_s, dot_match |
| mono_Q | Case 4b: dot_match + mono_Q + **row_r** | mono_Q, mono_P, row_r, dot_match |
| row_s | s 只在 P'；mono_P + row_s 排除冲突 | row_s, mono_P, dot_match |
| row_r | r 只在 Q'；mono_Q + row_r 排除冲突 | row_r, mono_Q, dot_match |
| col_c_P | col 0: translateM(d)=c，用 col_d_Q | col_d_Q, col_c_P |
| col_c_Q | Q' ⊆ {•,r,d}，无 c。空真 | sym_Q |
| col_d_P | P' ⊆ {•,s,c}，无 d。空真 | sym_P |
| col_d_Q | col 0: translateM(c)=d，用 col_c_P | col_c_P, col_d_Q |
