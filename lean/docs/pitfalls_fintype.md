# 踩坑记录：Lean 4 + Mathlib 中的 Fintype/Finite

## 背景

证明 `Fintype {τ : PBP // τ.γ = γ ∧ τ.P.shape = μP ∧ τ.Q.shape = μQ}` 时踩了大量坑。

## 失败方案：等价 + 有界表示（500+ 行，最终放弃）

想法：定义 `BPaint μ := μ.cells → DRCSymbol`（有界绘画），证明 `FinPBPSet ≃ PBPSet`，导出 Fintype。

### 坑 1：`open Classical` 杀死 `Fintype` 合成

`Pi.instFintype` 的签名：
```lean
instance Pi.instFintype {α} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] : Fintype ((a : α) → β a)
```

需要 **computable** 的 `DecidableEq α`。但 `open Classical` 提供 noncomputable 的 `DecidableEq`，导致 instance search 找到 classical 版本后无法构造 computable 的 `Fintype`。

**症状**：`inferInstance : Fintype (↥μ.cells → DRCSymbol)` 在 `open Classical` 之前成功，之后失败。

**教训**：`Fintype` instance 必须在 `open Classical` / `noncomputable section` **之前**声明。

### 坑 2：`abbrev` 对 instance search 不透明

```lean
abbrev BPaint (μ : YoungDiagram) := μ.cells → DRCSymbol
-- inferInstance : Fintype (BPaint μ)  -- 失败！
-- inferInstance : Fintype (μ.cells → DRCSymbol)  -- 成功！
```

`abbrev` 虽然是 reducible 的，但 instance search 不总是展开它。

**解决**：用 `inferInstanceAs (Fintype (μ.cells → DRCSymbol))` 或直接声明 instance。

### 坑 3：缺少 import

`Fintype (α → β)` 需要 `import Mathlib.Data.Fintype.Pi`。
`Fintype (α × β)` 需要 `import Mathlib.Data.Fintype.Prod`。

这些 **不会** 被 `Mathlib.Combinatorics.Young.YoungDiagram` 传递 import。不 import 的话 `inferInstance` 会默默失败。

### 坑 4：深嵌套 ∧ 的 Decidable

18 个 conjunct 的 `∧` 链，`Decidable` 的 instance search 会超时或失败。需要手动拆成 2-3 组。

### 坑 5：`↑c₁ ≤ ↑c₂` 的 DecidableRel

`↥μ.cells` 的元素 coerce 到 `ℕ × ℕ` 后，`≤` 用的是 Mathlib 的 `Prod` 上的偏序。`Decidable (↑c₁ ≤ ↑c₂)` 不自动合成，因为 coercion 隐藏了具体类型。

### 坑 6：`deriving Fintype` 不支持

`inductive DRCSymbol ... deriving Fintype` 会报错 "No deriving handlers"。必须手写：
```lean
instance : Fintype DRCSymbol where
  elems := {.dot, .s, .r, .c, .d}
  complete := fun x => by cases x <;> simp
```

## 成功方案：注入法（80 行）

**核心思路**：不需要等价，只需**注入**到有限类型。

```lean
-- 把 paint 限制到有限的 cells 上
def PaintedYoungDiagram.restrict (D : PaintedYoungDiagram) (μ : YoungDiagram)
    (_h : D.shape = μ) : ↥μ.cells → DRCSymbol :=
  fun ⟨(i, j), _⟩ => D.paint i j

-- 注入是单射（同 shape 的 PYD 由 restrict 唯一确定）
theorem restrict_injective ... : D₁ = D₂  -- 用 paint_outside 处理 shape 外

-- PBP 注入到 (cells→DRCSymbol) × (cells→DRCSymbol)
theorem PBPSet.restrict_injective ...

-- Finite 从注入得到
instance : Finite (PBPSet γ μP μQ) := Finite.of_injective _ ...

-- Fintype 从 Finite 得到（noncomputable）
noncomputable instance : Fintype (PBPSet γ μP μQ) := Fintype.ofFinite _
```

### 为什么有效

- **不需要 `Decidable`**：`Finite.of_injective` 不需要目标类型的 `Decidable`
- **不需要 `open Classical`**：`Fintype.ofFinite` 只需标 `noncomputable`
- **不需要约束转换**：不需要证明有界约束 ↔ 无界约束
- **`Fintype` 放在 `open Classical` 之前**：`instFintypeCellsPaint` 在文件开头声明

## 经验总结

| 需要 | 用什么 |
|------|--------|
| 有限类型的函数空间 Fintype | `import Mathlib.Data.Fintype.Pi`，在 `open Classical` 之前 |
| 有限类型的积 Fintype | `import Mathlib.Data.Fintype.Prod` |
| 子类型是有限的 | `Finite.of_injective` + `Fintype.ofFinite` |
| 小归纳类型的 Fintype | 手动 `instance : Fintype T where elems := {...}` |
| instance search 不展开 abbrev | `inferInstanceAs (Fintype (展开后的类型))` |
| `open Classical` 下的 Fintype | 把 Fintype instance 放在 `open Classical` 之前 |
