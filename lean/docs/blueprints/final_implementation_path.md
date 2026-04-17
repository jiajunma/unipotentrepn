# 最终实施路径 — liftPBP_B_bal_Qd 的精确修改

## 5 个 hprimQ 使用点的具体替换

### Line 1530 (mono_Q, Case 1 `inl`)
原：
```lean
by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
· exfalso; have := hprimQ (j₂ + 1) (by omega); omega
```

替换为：
```lean
by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
· exfalso
  -- i₂ < μQ.colLen (j₂+1). In balanced: μQ.colLen (j₂+1) ≤ μP.colLen 0.
  -- Combined with i₁ ≥ μP.colLen 0 ∧ i₁ ≤ i₂: contradiction.
  have h_weak : μQ.colLen (j₂ + 1) ≤ μP.colLen 0 := by
    -- From balanced condition (h_bal) + sigma_shape_inc_of_dp
    ...
  omega
```

### Line 1535 (mono_Q, Case 2 `inr`) — MOST COMPLEX
原：
```lean
by_cases hc : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
· exfalso; have := hprimQ (j₂ + 1) (by omega); omega
```

替换为：
```lean
by_cases hc : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
· have h_weak : μQ.colLen (j₂+1) ≤ μP.colLen 0 := by ...
  have hi₂_lt_hP : i₂ < μP.colLen 0 := lt_of_lt_of_le hi₂ h_weak
  -- So i₁, i₂ ∈ {μP.colLen 0 - 1} (tight squeeze)
  have hi_eq : i₁ = μP.colLen 0 - 1 := by omega
  have hi₂_eq : i₂ = μP.colLen 0 - 1 := by omega
  -- (i₂, j₂) ∈ σ.val.Q.shape by shift reverse of hmem₂
  have hmemσ : (μP.colLen 0 - 1, j₂) ∈ σ.val.Q.shape := by
    rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft]
    rw [← hi₂_eq]; exact hmem₂
  -- σ.Q(μP.colLen 0 - 1, j₂) = d by d-propagation
  rw [hi₂_eq]
  rw [sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₂ hmemσ]
  -- Goal: liftCol0Q_B ... i₁ .layerOrd ≤ .d.layerOrd = 4
  rw [hi_eq]
  -- liftCol0Q_B at (μP.colLen 0 - 1) for .inr: may = d.val ⟨0, _⟩ or .dot
  -- In any case layerOrd ≤ 4
  unfold liftCol0Q_B
  split_ifs <;> first 
  | (simp [DRCSymbol.layerOrd]) 
  | (rcases d.prop.1 ⟨_, _⟩ with h | h | h <;> simp [h, DRCSymbol.layerOrd])
```

### Line 1586 (row_s, case j₁=0, j₂=succ)
原：
```lean
have := hprimQ (j₂ + 1) (by omega); omega
```

替换为：
```lean
-- Similar squeeze: i₁ ≥ μP.colLen 0 - 1 (from hi_tail), i < μQ.colLen (j₂+1) ≤ μP.colLen 0
-- In balanced, μQ.colLen (j₂+1) ≤ μP.colLen 0 (not strict)
-- So i ∈ {μP.colLen 0 - 1}, same as above
have h_weak : μQ.colLen (j₂ + 1) ≤ μP.colLen 0 := ...
have hi_eq : i = μP.colLen 0 - 1 := by omega
-- But we have: τ.Q(i, 0) = s (non-dot in tail region) AND τ.Q(i, j₂+1) = s
-- τ.Q(i, j₂+1) = σ.Q(i, j₂) = d (by d-propagation) ≠ s. Contradiction.
have hmemσ : (μP.colLen 0 - 1, j₂) ∈ σ.val.Q.shape := ...
have : σ.val.Q.paint (μP.colLen 0 - 1) j₂ = .d :=
  sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₂ hmemσ
rw [hi_eq] at h₂; simp only [liftPaint_B_Q] at h₂
rw [this] at h₂; exact absurd h₂ (by decide)
```

### Line 1595, 1638, 1647: Parallel to 1586, with s → r in final lines for row_r.

## 辅助引理还需（在 liftPBP_B_bal_Qd 的 preamble）

```lean
have h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 := by
  intro j hj
  -- Use dpartColLens structure + balanced condition
  ...
```

## Step 组合

```lean
private noncomputable def liftPBP_B_bal_Qd 
    {r₁ r₂ : ℕ} {rest : DualPart} {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    PBPSet .Bplus μP μQ := by
  -- derive: hle, hP_pos, hprimP (standard), h_hQσ_eq, h_weak (balanced-Qd specific)
  ...
  -- Copy liftPBP_B body; modify 5 hprimQ uses as above.
```

## 完成后的 downstream

- `liftPBP_B_bal_Qd_round_trip`: 80 行 parallel to primitive version
- `liftPBP_B_bal_Qd_injective`: 80 行  
- `validCol0_B_le_fiber_bal_Qd`: 20 行
- `fiber_card_B_bal_Qd`: 5 行 via le_antisymm
- `fiber_card_B_bal_Qr/Qlow`: 需 ValidCol0_B_bal proper subtype (更复杂)
- `card_B_DD/SS_alpha_eq_countB_*` inductive balanced cases: 用 refined fiber-by-new-Q_bot

## 工作量估计
- Qd 闭合: ~600 行
- Qr 闭合: ~800 行 (需 admissibility subtype)
- Qlow 闭合: ~800 行
- A1/A3 inductive: ~300 行

**总计 ~2500 行**，需专门 3-5 session 完成。

## 数学验证
82 dp cases 全通过数值验证 (`tools/verify_all_B_lemmas.py`, `tools/verify_fiber_by_Qbot.py`).
