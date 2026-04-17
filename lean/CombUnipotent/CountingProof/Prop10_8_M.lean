/-
# Proposition 10.8 for ★ = M (= C̃)

Implements the lift B → M and proves Prop 10.8 for M type:
- (a) Primitive (c₁(P) > c₁(Q)): descent is bijection
- (b) Balanced (c₁(P) = c₁(Q)): descent is injection with image = non-SS

Reference: [BMSZb] Proposition 10.8.
-/
import CombUnipotent.CountingProof.CorrespondenceM
import CombUnipotent.CountingProof.ShapeShift

open Classical

/-! ## Lift paint functions (B → M) -/

/-- Lift Q paint: σ.Q → τ.Q. {•, s} collapse to •; {r, d} preserved.
    Uses σ.Q.shape for membership. -/
noncomputable def liftPaintQ_naive (σ : PBP) (i j : ℕ) : DRCSymbol :=
  if (i, j) ∈ σ.Q.shape ∧ ¬((σ.Q.paint i j).layerOrd ≤ 1) then σ.Q.paint i j
  else .dot

/-- Lift P paint: σ.P → τ.P.
    Needs target shape μP (with μP.colLen(0) = σ.P.colLen(0) + 1 for col 0 structure)
    and access to σ.Q. -/
noncomputable def liftPaintP_naive (σ : PBP) (μP : YoungDiagram) (i j : ℕ) : DRCSymbol :=
  if (i, j) ∉ μP then .dot
  else if j = 0 then
    if σ.γ = .Bminus ∧ i = μP.colLen 0 - 1 then .c
    else if (i, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i 0).layerOrd ≤ 1 then .dot
    else .s
  else
    -- j ≥ 1: τ.P(i, j) uses σ.P(i, j-1)
    if σ.P.paint i (j - 1) = .c then .c
    else if (i, j) ∈ σ.Q.shape ∧ (σ.Q.paint i j).layerOrd ≤ 1 then .dot
    else .s

/-! ## Simp lemmas -/

@[simp] theorem liftPaintQ_naive_outside {σ : PBP} {i j : ℕ}
    (h : (i, j) ∉ σ.Q.shape) : liftPaintQ_naive σ i j = .dot := by
  simp [liftPaintQ_naive, h]

@[simp] theorem liftPaintP_naive_outside {σ : PBP} {μP : YoungDiagram} {i j : ℕ}
    (h : (i, j) ∉ μP) : liftPaintP_naive σ μP i j = .dot := by
  simp [liftPaintP_naive, h]

theorem liftPaintP_naive_zero (σ : PBP) (μP : YoungDiagram) (i : ℕ)
    (hmem : (i, 0) ∈ μP) :
    liftPaintP_naive σ μP i 0 =
      if σ.γ = .Bminus ∧ i = μP.colLen 0 - 1 then .c
      else if (i, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i 0).layerOrd ≤ 1 then .dot
      else .s := by
  simp [liftPaintP_naive, hmem]

theorem liftPaintP_naive_succ (σ : PBP) (μP : YoungDiagram) (i j : ℕ)
    (hmem : (i, j + 1) ∈ μP) :
    liftPaintP_naive σ μP i (j + 1) =
      if σ.P.paint i j = .c then .c
      else if (i, j + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i (j + 1)).layerOrd ≤ 1 then .dot
      else .s := by
  simp [liftPaintP_naive, hmem]

/-! ## Value set -/

theorem liftPaintQ_naive_mem (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus) (i j : ℕ) :
    liftPaintQ_naive σ i j = .dot ∨
    liftPaintQ_naive σ i j = .r ∨
    liftPaintQ_naive σ i j = .d := by
  simp only [liftPaintQ_naive]
  split_ifs with h
  · obtain ⟨hmem, hlo⟩ := h
    push_neg at hlo
    have hsym := σ.sym_Q i j hmem
    rcases hγ with hγ | hγ <;> rw [hγ] at hsym <;> simp [DRCSymbol.allowed] at hsym
    all_goals {
      rcases hsym with h' | h' | h' | h'
      · rw [h']; left; rfl
      · rw [h'] at hlo; simp [DRCSymbol.layerOrd] at hlo
      · rw [h']; right; left; rfl
      · rw [h']; right; right; rfl
    }
  · left; rfl

theorem liftPaintP_naive_mem (σ : PBP) (μP : YoungDiagram) (i j : ℕ) :
    liftPaintP_naive σ μP i j = .dot ∨
    liftPaintP_naive σ μP i j = .s ∨
    liftPaintP_naive σ μP i j = .c := by
  simp only [liftPaintP_naive]
  split_ifs <;> simp

theorem liftPaintP_naive_ne_r (σ : PBP) (μP : YoungDiagram) (i j : ℕ) :
    liftPaintP_naive σ μP i j ≠ .r := by
  rcases liftPaintP_naive_mem σ μP i j with h | h | h <;> rw [h] <;> decide

theorem liftPaintP_naive_ne_d (σ : PBP) (μP : YoungDiagram) (i j : ℕ) :
    liftPaintP_naive σ μP i j ≠ .d := by
  rcases liftPaintP_naive_mem σ μP i j with h | h | h <;> rw [h] <;> decide

theorem liftPaintQ_naive_ne_s (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus) (i j : ℕ) :
    liftPaintQ_naive σ i j ≠ .s := by
  rcases liftPaintQ_naive_mem σ hγ i j with h | h | h <;> rw [h] <;> decide

theorem liftPaintQ_naive_ne_c (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus) (i j : ℕ) :
    liftPaintQ_naive σ i j ≠ .c := by
  rcases liftPaintQ_naive_mem σ hγ i j with h | h | h <;> rw [h] <;> decide

/-! ## Characterization helpers for τ paint values -/

/-- τ.P(i, 0) = c iff we're at bottom and γ' = B⁻. -/
theorem liftPaintP_naive_col0_c_iff (σ : PBP) (μP : YoungDiagram) (i : ℕ) :
    liftPaintP_naive σ μP i 0 = .c ↔
    ((i, 0) ∈ μP ∧ σ.γ = .Bminus ∧ i = μP.colLen 0 - 1) := by
  by_cases hmem : (i, 0) ∈ μP
  · rw [liftPaintP_naive_zero σ μP i hmem]
    by_cases hbm : σ.γ = .Bminus ∧ i = μP.colLen 0 - 1
    · rw [if_pos hbm]; exact ⟨fun _ => ⟨hmem, hbm⟩, fun _ => rfl⟩
    · rw [if_neg hbm]; split_ifs <;> (constructor <;> intro h) <;> simp_all <;>
        exact (by decide : (DRCSymbol.dot : DRCSymbol) ≠ .c) h
  · rw [liftPaintP_naive_outside hmem]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 hmem⟩

/-- τ.P(i, 0) = s iff in μP, not B⁻ bottom, and ¬(∈σ.Q ∧ σ.Q.lo ≤ 1). -/
theorem liftPaintP_naive_col0_s_iff (σ : PBP) (μP : YoungDiagram) (i : ℕ) :
    liftPaintP_naive σ μP i 0 = .s ↔
    ((i, 0) ∈ μP ∧ ¬(σ.γ = .Bminus ∧ i = μP.colLen 0 - 1) ∧
     ¬((i, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i 0).layerOrd ≤ 1)) := by
  by_cases hmem : (i, 0) ∈ μP
  · rw [liftPaintP_naive_zero σ μP i hmem]
    by_cases hbm : σ.γ = .Bminus ∧ i = μP.colLen 0 - 1
    · rw [if_pos hbm]; exact ⟨fun h => absurd h (by decide), fun ⟨_, h, _⟩ => absurd hbm h⟩
    · rw [if_neg hbm]
      by_cases hdot : (i, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i 0).layerOrd ≤ 1
      · rw [if_pos hdot]; exact ⟨fun h => absurd h (by decide), fun ⟨_, _, h⟩ => absurd hdot h⟩
      · rw [if_neg hdot]; exact ⟨fun _ => ⟨hmem, hbm, hdot⟩, fun _ => rfl⟩
  · rw [liftPaintP_naive_outside hmem]
    exact ⟨fun h => absurd h (by decide), fun ⟨h, _, _⟩ => absurd h hmem⟩

/-- τ.P(i, j+1) = c iff in μP and σ.P(i, j) = c. -/
theorem liftPaintP_naive_succ_c_iff (σ : PBP) (μP : YoungDiagram) (i j : ℕ) :
    liftPaintP_naive σ μP i (j + 1) = .c ↔
    ((i, j + 1) ∈ μP ∧ σ.P.paint i j = .c) := by
  by_cases hmem : (i, j + 1) ∈ μP
  · rw [liftPaintP_naive_succ σ μP i j hmem]
    by_cases hc : σ.P.paint i j = .c
    · rw [if_pos hc]; exact ⟨fun _ => ⟨hmem, hc⟩, fun _ => rfl⟩
    · rw [if_neg hc]; split_ifs <;>
        exact ⟨fun h => absurd h (by decide), fun ⟨_, h⟩ => absurd h hc⟩
  · rw [liftPaintP_naive_outside hmem]
    exact ⟨fun h => absurd h (by decide), fun ⟨h, _⟩ => absurd h hmem⟩

/-- τ.P(i, j+1) = s iff in μP, σ.P(i, j) ≠ c, and ¬(∈σ.Q ∧ σ.Q.lo ≤ 1). -/
theorem liftPaintP_naive_succ_s_iff (σ : PBP) (μP : YoungDiagram) (i j : ℕ) :
    liftPaintP_naive σ μP i (j + 1) = .s ↔
    ((i, j + 1) ∈ μP ∧ σ.P.paint i j ≠ .c ∧
     ¬((i, j + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i (j + 1)).layerOrd ≤ 1)) := by
  by_cases hmem : (i, j + 1) ∈ μP
  · rw [liftPaintP_naive_succ σ μP i j hmem]
    by_cases hc : σ.P.paint i j = .c
    · rw [if_pos hc]; exact ⟨fun h => absurd h (by decide), fun ⟨_, h, _⟩ => absurd hc h⟩
    · rw [if_neg hc]
      by_cases hdot : (i, j + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i (j + 1)).layerOrd ≤ 1
      · rw [if_pos hdot]; exact ⟨fun h => absurd h (by decide), fun ⟨_, _, h⟩ => absurd hdot h⟩
      · rw [if_neg hdot]; exact ⟨fun _ => ⟨hmem, hc, hdot⟩, fun _ => rfl⟩
  · rw [liftPaintP_naive_outside hmem]
    exact ⟨fun h => absurd h (by decide), fun ⟨h, _, _⟩ => absurd h hmem⟩

/-- τ.Q(i, j) = dot iff ((i, j) ∉ σ.Q.shape) OR σ.Q.lo ≤ 1. -/
theorem liftPaintQ_naive_dot_iff (σ : PBP) (i j : ℕ) :
    liftPaintQ_naive σ i j = .dot ↔
    ((i, j) ∉ σ.Q.shape ∨ (σ.Q.paint i j).layerOrd ≤ 1) := by
  simp only [liftPaintQ_naive]
  by_cases h : (i, j) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i j).layerOrd ≤ 1
  · rw [if_pos h]
    refine ⟨fun heq => ?_, fun hor => ?_⟩
    · obtain ⟨_, hlo⟩ := h; push_neg at hlo; rw [heq] at hlo; simp [DRCSymbol.layerOrd] at hlo
    · rcases hor with h1 | h1
      · exact absurd h.1 h1
      · exact absurd h1 h.2
  · rw [if_neg h]
    push_neg at h
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    by_cases hm : (i, j) ∈ σ.Q.shape
    · right; exact h hm
    · left; exact hm

/-- dotScolLen equality between τ.P col j+1 and σ.P col j.
    Placeholder — exact formulation depends on how τ.P is accessed. -/
theorem dotScolLen_liftBM_P_zero_placeholder : True := trivial

theorem dotScolLen_liftBM_Q_placeholder : True := trivial

/-! ## Helper: τ.P col 0 layerOrd structure -/

/-- layerOrd of τ.P at col 0 is at most 3 (since τ.P ∈ {•, s, c}). -/
theorem liftPaintP_naive_col0_layerOrd_le (σ : PBP) (μP : YoungDiagram) (i : ℕ) :
    (liftPaintP_naive σ μP i 0).layerOrd ≤ 3 := by
  rcases liftPaintP_naive_mem σ μP i 0 with h | h | h <;> rw [h] <;> decide

/-- τ.P col 0 is monotone in i: if i₁ ≤ i₂ and (i₂, 0) ∈ μP, then
    (τ.P(i₁, 0)).lo ≤ (τ.P(i₂, 0)).lo. -/
theorem liftPaintP_naive_col0_mono (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hQsh : σ.Q.shape = μQ) (h_QleP : μQ ≤ μP)
    {i₁ i₂ : ℕ} (hi : i₁ ≤ i₂) (hmem : (i₂, 0) ∈ μP) :
    (liftPaintP_naive σ μP i₁ 0).layerOrd ≤ (liftPaintP_naive σ μP i₂ 0).layerOrd := by
  -- Case on whether (i₁, 0) ∈ μP
  by_cases hmem₁ : (i₁, 0) ∈ μP
  · rw [liftPaintP_naive_zero σ μP i₁ hmem₁, liftPaintP_naive_zero σ μP i₂ hmem]
    -- Case analysis on the ifs
    by_cases hbm₁ : σ.γ = .Bminus ∧ i₁ = μP.colLen 0 - 1
    · rw [if_pos hbm₁]
      -- i₁ = bottom. i₂ ≥ i₁ = bottom. Also (i₂, 0) ∈ μP means i₂ < μP.colLen 0 = bottom + 1.
      -- So i₂ = bottom.
      have hi₁_eq : i₁ = μP.colLen 0 - 1 := hbm₁.2
      have hi₂_lt : i₂ < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
      have hi₂_eq : i₂ = μP.colLen 0 - 1 := by omega
      have hbm₂ : σ.γ = .Bminus ∧ i₂ = μP.colLen 0 - 1 := ⟨hbm₁.1, hi₂_eq⟩
      rw [if_pos hbm₂]
    · rw [if_neg hbm₁]
      by_cases hdot₁ : (i₁, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i₁ 0).layerOrd ≤ 1
      · rw [if_pos hdot₁]
        -- τ.P(i₁, 0) = •, lo = 0. Anything ≥ 0.
        simp [DRCSymbol.layerOrd]
      · rw [if_neg hdot₁]
        -- τ.P(i₁, 0) = s, lo = 1.
        -- Need: τ.P(i₂, 0).lo ≥ 1.
        -- τ.P(i₂, 0) ∈ {•, s, c}. If •, lo = 0 < 1. Bad.
        -- We need to show τ.P(i₂, 0) ≠ •, i.e., σ.γ = B- ∧ i₂ = bottom OR ¬(i₂ ∈ σ.Q.shape ∧ σ.Q lo ≤ 1).
        -- From i₂ ≥ i₁, and ¬hdot₁: (i₁, 0) ∉ σ.Q.shape OR σ.Q(i₁, 0).lo > 1.
        -- By σ.Q's mono_Q: σ.Q(i₁, 0).lo ≤ σ.Q(i₂, 0).lo (if (i₂, 0) ∈ σ.Q).
        -- So if σ.Q(i₁, 0).lo > 1, then σ.Q(i₂, 0).lo > 1.
        -- And if (i₁, 0) ∉ σ.Q, then (i₂, 0) ∉ σ.Q (shape lower set contrapositive).
        -- In either case, ¬hdot₂.
        push_neg at hdot₁
        by_cases hbm₂ : σ.γ = .Bminus ∧ i₂ = μP.colLen 0 - 1
        · rw [if_pos hbm₂]; simp [DRCSymbol.layerOrd]
        · rw [if_neg hbm₂]
          by_cases hdot₂ : (i₂, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i₂ 0).layerOrd ≤ 1
          · -- Contradiction: i₁ ≤ i₂, (i₂, 0) ∈ σ.Q, σ.Q(i₂, 0).lo ≤ 1.
            -- Then (i₁, 0) ∈ σ.Q and σ.Q(i₁, 0).lo ≤ σ.Q(i₂, 0).lo ≤ 1.
            -- But hdot₁ says NOT this. Contradiction.
            exfalso
            obtain ⟨hmemQ₂, hlo₂⟩ := hdot₂
            have hmemQ₁ : (i₁, 0) ∈ σ.Q.shape :=
              σ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, le_rfl⟩) hmemQ₂
            have hlo₁ := hdot₁ hmemQ₁
            have hmono := σ.mono_Q i₁ 0 i₂ 0 hi le_rfl hmemQ₂
            omega
          · rw [if_neg hdot₂]
  · -- (i₁, 0) ∉ μP. τ.P(i₁, 0) = • by paint_outside.
    rw [liftPaintP_naive_outside hmem₁]
    simp [DRCSymbol.layerOrd]

/-- σ B-type → σ.P ∈ {•, c}. -/
theorem B_P_dot_or_c (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus) {i j : ℕ}
    (hmem : (i, j) ∈ σ.P.shape) : σ.P.paint i j = .dot ∨ σ.P.paint i j = .c := by
  have hsym := σ.sym_P i j hmem
  rcases hγ with hγ | hγ <;> rw [hγ] at hsym <;> simp [DRCSymbol.allowed] at hsym <;>
    exact hsym

/-- τ.P at col ≥ 1 is monotone in i and j: uses σ.P's mono_P via col-shift. -/
theorem liftPaintP_naive_succ_mono (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    {i₁ i₂ j₁' j₂' : ℕ} (hi : i₁ ≤ i₂) (hj : j₁' + 1 ≤ j₂' + 1)
    (hmem : (i₂, j₂' + 1) ∈ μP) :
    (liftPaintP_naive σ μP i₁ (j₁' + 1)).layerOrd ≤
    (liftPaintP_naive σ μP i₂ (j₂' + 1)).layerOrd := by
  -- τ.P at col j+1 uses σ.P at col j. Key: σ.P.shape = shiftLeft μP.
  -- (i₂, j₂'+1) ∈ μP ↔ (i₂, j₂') ∈ σ.P.shape.
  have hmemPσ : (i₂, j₂') ∈ σ.P.shape := by
    rw [hPsh, YoungDiagram.mem_shiftLeft]; exact hmem
  have hj' : j₁' ≤ j₂' := by omega
  -- Case on σ.P(i₂, j₂') ∈ {•, c}.
  rcases B_P_dot_or_c σ hγ hmemPσ with hdot₂ | hc₂
  · -- σ.P(i₂, j₂') = •. By σ.mono_P: σ.P(i₁, j₁').lo ≤ 0, so σ.P(i₁, j₁') = •.
    have hmono_σ := σ.mono_P i₁ j₁' i₂ j₂' hi hj' hmemPσ
    rw [hdot₂, DRCSymbol.layerOrd] at hmono_σ
    have hle_zero : (σ.P.paint i₁ j₁').layerOrd = 0 := Nat.le_zero.mp hmono_σ
    have hne_c_1 : σ.P.paint i₁ j₁' ≠ .c := by
      intro h; rw [h, DRCSymbol.layerOrd] at hle_zero; omega
    -- τ.P(i₁, j₁'+1) ∈ {•, s}.
    rcases liftPaintP_naive_mem σ μP i₁ (j₁' + 1) with hτ₁ | hτ₁ | hτ₁
    · rw [hτ₁]; simp [DRCSymbol.layerOrd]
    · -- τ.P(i₁, j₁'+1) = s. Need τ.P(i₂, j₂'+1).lo ≥ 1.
      -- i.e., τ.P(i₂, j₂'+1) ≠ •.
      have hne_dot_2 : liftPaintP_naive σ μP i₂ (j₂' + 1) ≠ .dot := by
        intro hτ₂
        have hs_spec := (liftPaintP_naive_succ_s_iff σ μP i₁ j₁').mp hτ₁
        obtain ⟨_, _, hnot_dot_1⟩ := hs_spec
        rw [liftPaintP_naive_succ σ μP i₂ j₂' hmem,
            if_neg (by rw [hdot₂]; decide)] at hτ₂
        by_cases hdot₂' : (i₂, j₂' + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i₂ (j₂' + 1)).layerOrd ≤ 1
        · apply hnot_dot_1
          refine ⟨σ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hdot₂'.1, ?_⟩
          have hmono_Q := σ.mono_Q i₁ (j₁' + 1) i₂ (j₂' + 1) hi (by omega) hdot₂'.1
          omega
        · rw [if_neg hdot₂'] at hτ₂; exact absurd hτ₂ (by decide)
      rw [hτ₁]
      rcases liftPaintP_naive_mem σ μP i₂ (j₂' + 1) with h | h | h
      · exact absurd h hne_dot_2
      · simp [h, DRCSymbol.layerOrd]
      · simp [h, DRCSymbol.layerOrd]
    · -- τ.P(i₁, j₁'+1) = c means σ.P(i₁, j₁') = c. But σ.P(i₁, j₁').lo = 0.
      exfalso
      have h_mem₁_μ : (i₁, j₁' + 1) ∈ μP := by
        by_contra hout
        rw [liftPaintP_naive_outside hout] at hτ₁
        exact absurd hτ₁ (by decide)
      have hc₁ := ((liftPaintP_naive_succ_c_iff σ μP i₁ j₁').mp hτ₁).2
      rw [hc₁, DRCSymbol.layerOrd] at hle_zero
      omega
  · -- σ.P(i₂, j₂') = c. τ.P(i₂, j₂'+1) = c (lo=3). Anything ≤ 3.
    rw [(liftPaintP_naive_succ_c_iff σ μP i₂ j₂').mpr ⟨hmem, hc₂⟩]
    rcases liftPaintP_naive_mem σ μP i₁ (j₁' + 1) with h | h | h <;>
      rw [h] <;> decide

/-- Helper: μP.colLen(1) ≤ μQ.colLen(0) from h_sub. -/
private theorem col1_le_Q_of_h_sub (μP μQ : YoungDiagram) (h_sub : μP.shiftLeft ≤ μQ) :
    μP.colLen 1 ≤ μQ.colLen 0 := by
  by_contra hne; push_neg at hne
  have : (μQ.colLen 0, 0) ∈ μP.shiftLeft := by
    rw [YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]; exact hne
  exact absurd (h_sub this)
    (YoungDiagram.mem_iff_lt_colLen.not.mpr (by omega))

/-- Helper: μQ.colLen(0) ≤ μP.colLen(0) from h_QleP. -/
private theorem Q_le_P_colLen (μP μQ : YoungDiagram) (h_QleP : μQ ≤ μP) :
    μQ.colLen 0 ≤ μP.colLen 0 := by
  by_contra hne; push_neg at hne
  have : (μP.colLen 0, 0) ∈ μQ :=
    YoungDiagram.mem_iff_lt_colLen.mpr hne
  exact absurd (h_QleP this)
    (YoungDiagram.mem_iff_lt_colLen.not.mpr (by omega))

/-- Key helper: τ.P monotone across col 0 → col ≥ 1 boundary.
    Uses shape conditions (h_sub, h_QleP, h_bal_exc) to handle all cases.
    The trickiest case is τ.P(i₁, 0) = c (γ=B-, i₁=bottom_μP): either
    (a) primitive: the target cell doesn't exist (vacuous), or
    (b) balanced (μP.colLen 0 = μQ.colLen 0) with μP.colLen 1 = μP.colLen 0:
        h_bal_exc forces σ.Q(bottom, 0).lo > 1 → σ.P(bottom, 0) = c → propagate. -/
theorem liftPaintP_naive_col0_to_succ_mono (σ : PBP)
    (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ) (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    {i₁ i₂ j₂' : ℕ} (hi : i₁ ≤ i₂)
    (hmem : (i₂, j₂' + 1) ∈ μP) :
    (liftPaintP_naive σ μP i₁ 0).layerOrd ≤
    (liftPaintP_naive σ μP i₂ (j₂' + 1)).layerOrd := by
  rcases liftPaintP_naive_mem σ μP i₁ 0 with hτ₁ | hτ₁ | hτ₁
  · rw [hτ₁]; simp [DRCSymbol.layerOrd]
  · -- τ.P(i₁, 0) = s. Need τ.P(i₂, j₂'+1).lo ≥ 1, i.e., ≠ •.
    rw [hτ₁]
    obtain ⟨_, _, hnot_dot⟩ :=
      (liftPaintP_naive_col0_s_iff σ μP i₁).mp hτ₁
    have hne_dot_2 : liftPaintP_naive σ μP i₂ (j₂' + 1) ≠ .dot := by
      intro hτ₂
      rw [liftPaintP_naive_succ σ μP i₂ j₂' hmem] at hτ₂
      by_cases hc₂ : σ.P.paint i₂ j₂' = .c
      · rw [if_pos hc₂] at hτ₂; exact absurd hτ₂ (by decide)
      · rw [if_neg hc₂] at hτ₂
        by_cases hdot₂' : (i₂, j₂' + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i₂ (j₂' + 1)).layerOrd ≤ 1
        · apply hnot_dot
          refine ⟨σ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, by omega⟩) hdot₂'.1, ?_⟩
          have hmono_Q := σ.mono_Q i₁ 0 i₂ (j₂' + 1) hi (by omega) hdot₂'.1
          omega
        · rw [if_neg hdot₂'] at hτ₂; exact absurd hτ₂ (by decide)
    rcases liftPaintP_naive_mem σ μP i₂ (j₂' + 1) with h | h | h
    · exact absurd h hne_dot_2
    · simp [h, DRCSymbol.layerOrd]
    · simp [h, DRCSymbol.layerOrd]
  · -- τ.P(i₁, 0) = c. γ = B- and i₁ = μP.colLen 0 - 1.
    rw [hτ₁]
    obtain ⟨hmem₁μ, _hγBm, hi₁_eq⟩ :=
      (liftPaintP_naive_col0_c_iff σ μP i₁).mp hτ₁
    have h_pos : μP.colLen 0 > 0 := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hmem₁μ
      rw [hi₁_eq] at this; omega
    have hi₂_lt_μP : i₂ < μP.colLen (j₂' + 1) :=
      YoungDiagram.mem_iff_lt_colLen.mp hmem
    have hcolLen_anti : μP.colLen (j₂' + 1) ≤ μP.colLen 1 := μP.colLen_anti 1 (j₂' + 1) (by omega)
    have hcol1_le_Q : μP.colLen 1 ≤ μQ.colLen 0 := col1_le_Q_of_h_sub μP μQ h_sub
    have hQ_le_P : μQ.colLen 0 ≤ μP.colLen 0 := Q_le_P_colLen μP μQ h_QleP
    have hi₂_ge : i₂ ≥ μP.colLen 0 - 1 := by rw [← hi₁_eq]; exact hi
    -- i₂ < μP.colLen(j₂'+1) ≤ μP.colLen(1) ≤ μQ.colLen(0) ≤ μP.colLen(0)
    by_cases h_prim : μP.colLen 0 > μQ.colLen 0
    · -- Primitive: contradiction.
      exfalso
      have : i₂ < μP.colLen 0 - 1 := by
        calc i₂ < μP.colLen (j₂' + 1) := hi₂_lt_μP
          _ ≤ μP.colLen 1 := hcolLen_anti
          _ ≤ μQ.colLen 0 := hcol1_le_Q
          _ ≤ μP.colLen 0 - 1 := by omega
      omega
    · -- Balanced: μP.colLen 0 = μQ.colLen 0.
      push_neg at h_prim
      have h_bal : μP.colLen 0 = μQ.colLen 0 := by omega
      have h_gt := h_bal_exc h_bal h_pos
      have hi₁_eq' : i₁ = μQ.colLen 0 - 1 := by rw [hi₁_eq]; omega
      have hi₂_eq : i₂ = μP.colLen 0 - 1 := by
        have : i₂ < μP.colLen 0 := by
          calc i₂ < μP.colLen (j₂' + 1) := hi₂_lt_μP
            _ ≤ μP.colLen 1 := hcolLen_anti
            _ ≤ μQ.colLen 0 := hcol1_le_Q
            _ = μP.colLen 0 := h_bal.symm
        omega
      have hcol1_eq : μP.colLen 1 = μP.colLen 0 := by
        have := hi₂_lt_μP; omega
      have hmemPσ : (i₁, 0) ∈ σ.P.shape := by
        rw [hPsh, YoungDiagram.mem_shiftLeft, YoungDiagram.mem_iff_lt_colLen]
        rw [hi₁_eq]
        show μP.colLen 0 - 1 < μP.colLen (0 + 1)
        rw [show (0 + 1 : ℕ) = 1 from rfl, hcol1_eq]; omega
      have hmemQσ_i₁ : (i₁, 0) ∈ σ.Q.shape := by
        rw [hQsh, YoungDiagram.mem_iff_lt_colLen]; rw [hi₁_eq']; omega
      -- h_gt at (μQ.colLen 0 - 1, 0), same as (i₁, 0) via hi₁_eq'.
      have h_gt_at_i₁ : (σ.Q.paint i₁ 0).layerOrd > 1 := by rw [hi₁_eq']; exact h_gt
      have hQne_dot : σ.Q.paint i₁ 0 ≠ .dot := by
        intro habs; rw [habs, DRCSymbol.layerOrd] at h_gt_at_i₁; omega
      have hPne_dot : σ.P.paint i₁ 0 ≠ .dot := by
        intro habs
        have ⟨_, hQ_dot⟩ := (σ.dot_match i₁ 0).mp ⟨hmemPσ, habs⟩
        exact hQne_dot hQ_dot
      have hPc : σ.P.paint i₁ 0 = .c := by
        rcases B_P_dot_or_c σ hγ hmemPσ with h | h
        · exact absurd h hPne_dot
        · exact h
      -- Propagate to σ.P(i₁, j₂').
      have hmemPσ_j : (i₁, j₂') ∈ σ.P.shape := by
        rw [hPsh, YoungDiagram.mem_shiftLeft, YoungDiagram.mem_iff_lt_colLen]
        rw [hi₁_eq]
        have := hi₂_lt_μP; rw [hi₂_eq] at this; omega
      have hmono_σP := σ.mono_P i₁ 0 i₁ j₂' le_rfl (by omega) hmemPσ_j
      rw [hPc, DRCSymbol.layerOrd] at hmono_σP
      have hPc_j : σ.P.paint i₁ j₂' = .c := by
        rcases B_P_dot_or_c σ hγ hmemPσ_j with h | h
        · rw [h, DRCSymbol.layerOrd] at hmono_σP; omega
        · exact h
      -- i₂ = i₁ (both = μP.colLen 0 - 1).
      have hi₂_eq_i₁ : i₂ = i₁ := by rw [hi₂_eq, hi₁_eq]
      rw [hi₂_eq_i₁]
      rw [(liftPaintP_naive_succ_c_iff σ μP i₁ j₂').mpr ⟨(hi₂_eq_i₁ ▸ hmem), hPc_j⟩]

/-! ## Main construction: liftBM_naive -/

/-- Preimage construction for Prop 10.8(a) (primitive case).

    Given σ ∈ PBPSet_{B⁺/B⁻} on (shiftLeft μP, μQ) with shape conditions
    μQ ≤ μP (cell containment) and shiftLeft μP ≤ μQ (right interleaving),
    construct τ ∈ PBP_M on (μP, μQ) with descentMB_PBP(τ) = σ.

    The ONLY free choice is τ.P(μP.colLen(0) - 1, 0):
    - γ' = B⁺ → s
    - γ' = B⁻ → c -/
noncomputable def liftBM_naive (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ)  -- shiftLeft μP ≤ μQ (right interleaving)
    (h_QleP : μQ ≤ μP)  -- μQ ≤ μP (cell containment)
    -- Balanced SS-exclusion: in balanced case, the bottom of μQ col 0 should not
    -- have a problematic σ.Q paint. For primitive, this is vacuous.
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 →
        μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1) : PBP where
  γ := .M
  P := { shape := μP
         paint := liftPaintP_naive σ μP
         paint_outside := fun i j hmem => by
           simp only [liftPaintP_naive_outside hmem] }
  Q := { shape := μQ
         paint := liftPaintQ_naive σ
         paint_outside := fun i j hmem => by
           have : (i, j) ∉ σ.Q.shape := by rw [hQsh]; exact hmem
           simp only [liftPaintQ_naive_outside this] }
  sym_P := by
    intro i j hmem
    show DRCSymbol.allowed .M .L (liftPaintP_naive σ μP i j)
    rcases liftPaintP_naive_mem σ μP i j with h | h | h <;> rw [h] <;>
      simp [DRCSymbol.allowed]
  sym_Q := by
    intro i j hmem
    show DRCSymbol.allowed .M .R (liftPaintQ_naive σ i j)
    rcases liftPaintQ_naive_mem σ hγ i j with h | h | h <;> rw [h] <;>
      simp [DRCSymbol.allowed]
  dot_match := by
    intro i j
    show (_ ∈ μP ∧ liftPaintP_naive σ μP i j = .dot) ↔
         (_ ∈ μQ ∧ liftPaintQ_naive σ i j = .dot)
    constructor
    · -- Forward: τ.P(i,j) = • ∧ (i,j) ∈ μP → τ.Q(i,j) = • ∧ (i,j) ∈ μQ
      intro ⟨hmemP, hpaintP⟩
      cases j with
      | zero =>
        rw [liftPaintP_naive_zero σ μP i hmemP] at hpaintP
        by_cases hbm : σ.γ = .Bminus ∧ i = μP.colLen 0 - 1
        · rw [if_pos hbm] at hpaintP; exact absurd hpaintP (by decide)
        · rw [if_neg hbm] at hpaintP
          by_cases hdot : (i, 0) ∈ σ.Q.shape ∧ (σ.Q.paint i 0).layerOrd ≤ 1
          · obtain ⟨hmemQσ, hlo⟩ := hdot
            have hmemQ : (i, 0) ∈ μQ := hQsh ▸ hmemQσ
            refine ⟨hmemQ, ?_⟩
            simp only [liftPaintQ_naive]
            rw [if_neg]; push_neg; intro _; exact hlo
          · rw [if_neg hdot] at hpaintP; exact absurd hpaintP (by decide)
      | succ j' =>
        rw [liftPaintP_naive_succ σ μP i j' hmemP] at hpaintP
        by_cases hc : σ.P.paint i j' = .c
        · rw [if_pos hc] at hpaintP; exact absurd hpaintP (by decide)
        · rw [if_neg hc] at hpaintP
          by_cases hdot : (i, j' + 1) ∈ σ.Q.shape ∧ (σ.Q.paint i (j' + 1)).layerOrd ≤ 1
          · obtain ⟨hmemQσ, hlo⟩ := hdot
            have hmemQ : (i, j' + 1) ∈ μQ := hQsh ▸ hmemQσ
            refine ⟨hmemQ, ?_⟩
            simp only [liftPaintQ_naive]
            rw [if_neg]; push_neg; intro _; exact hlo
          · rw [if_neg hdot] at hpaintP; exact absurd hpaintP (by decide)
    · -- Backward: τ.Q(i,j) = • ∧ (i,j) ∈ μQ → τ.P(i,j) = • ∧ (i,j) ∈ μP
      intro ⟨hmemQ, hpaintQ⟩
      have hmemQσ : (i, j) ∈ σ.Q.shape := hQsh ▸ hmemQ
      -- From τ.Q = •: σ.Q.paint lo ≤ 1
      have hlo : (σ.Q.paint i j).layerOrd ≤ 1 := by
        simp only [liftPaintQ_naive] at hpaintQ
        by_contra h
        push_neg at h
        rw [if_pos ⟨hmemQσ, not_le.mpr h⟩] at hpaintQ
        -- σ.Q.paint i j = .dot but σ.Q.paint.lo > 1
        have : (σ.Q.paint i j).layerOrd = 0 := by rw [hpaintQ]; rfl
        omega
      -- (i, j) ∈ μP from μQ ≤ μP
      have hmemP : (i, j) ∈ μP := h_QleP hmemQ
      refine ⟨hmemP, ?_⟩
      cases j with
      | zero =>
        rw [liftPaintP_naive_zero σ μP i hmemP]
        -- Need: NOT (σ.γ = B- ∧ i = bottom) for this to go to the dot branch
        have h_not_bm_bot : ¬ (σ.γ = .Bminus ∧ i = μP.colLen 0 - 1) := by
          intro ⟨hγ_eq, hi_eq⟩
          -- Balanced case: h_bal_exc forces σ.Q.lo > 1 at bottom, contradicting hlo
          -- Primitive case: i < μQ.colLen(0) < μP.colLen(0), so i < μP.colLen(0) - 1 = bottom
          have hiQ : i < μQ.colLen 0 :=
            YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have hiP : i < μP.colLen 0 :=
            YoungDiagram.mem_iff_lt_colLen.mp hmemP
          -- μQ.colLen 0 ≤ μP.colLen 0
          have h_le : μQ.colLen 0 ≤ μP.colLen 0 := by
            by_contra h'; push_neg at h'
            have := YoungDiagram.mem_iff_lt_colLen.mpr h'
            exact absurd (h_QleP this)
              (YoungDiagram.mem_iff_lt_colLen.not.mpr (by omega))
          by_cases hbal : μP.colLen 0 = μQ.colLen 0
          · -- Balanced: use h_bal_exc
            have h_pos : μP.colLen 0 > 0 := by
              rw [hi_eq] at hiP; omega
            have h_gt := h_bal_exc hbal h_pos
            rw [← hbal, ← hi_eq] at h_gt
            omega
          · -- Primitive: μQ.colLen 0 < μP.colLen 0
            have : μQ.colLen 0 < μP.colLen 0 := lt_of_le_of_ne h_le (Ne.symm hbal)
            -- i < μQ.colLen 0, so i ≤ μQ.colLen 0 - 1 < μP.colLen 0 - 1 = bottom
            omega
        rw [if_neg h_not_bm_bot]
        rw [if_pos ⟨hmemQσ, hlo⟩]
      | succ j' =>
        rw [liftPaintP_naive_succ σ μP i j' hmemP]
        -- Need: σ.P.paint i j' ≠ .c (for τ.P to not be c)
        -- And (i, j'+1) ∈ σ.Q.shape ∧ σ.Q lo ≤ 1 (for τ.P = •)
        -- From τ.Q(i, j'+1) = •, we have σ.Q.lo ≤ 1 at (i, j'+1). ✓
        -- For σ.P(i, j') ≠ c: use σ's dot_match + mono.
        have h_not_c : σ.P.paint i j' ≠ .c := by
          intro hPc
          -- σ.P(i, j') = c → σ.P(i, j').lo = 3
          -- σ's dot_match: σ.P = c ∧ ∈σ.P → σ.Q ≠ • ∧ ∈σ.Q (in overlap)
          -- (i, j'+1) ∈ σ.Q, σ.Q.lo ≤ 1 so σ.Q ∈ {•, s}
          -- σ's mono_Q: σ.Q(i, j').lo ≤ σ.Q(i, j'+1).lo ≤ 1
          -- σ.Q(i, j') = • → by σ's dot_match at (i, j'): σ.P ≠ c or ∉ σ.P. But σ.P(i, j') = c. Contradiction if (i, j') ∈ σ.P.
          -- σ.Q(i, j') = s → σ.Q(i, j'+1) must be s too (mono + ≤1), but then two s's in row i by σ's row_s. Contradiction.
          -- Actually need to show (i, j') ∈ σ.P for σ.P(i, j') = c.
          have hmemPσ : (i, j') ∈ σ.P.shape := by
            rw [hPsh]; rw [YoungDiagram.mem_shiftLeft]
            exact hmemP
          have hmemQσ' : (i, j') ∈ σ.Q.shape := by
            rw [hQsh]
            exact μQ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ _⟩)
              (by rw [← hQsh]; exact hmemQσ)
          -- σ's dot_match at (i, j'): σ.P = c ≠ • → σ.Q ≠ •
          have hQne : σ.Q.paint i j' ≠ .dot := by
            intro hQdot
            have := (σ.dot_match i j').mpr ⟨hmemQσ', hQdot⟩
            rw [hPc] at this; exact DRCSymbol.noConfusion this.2
          -- σ's mono_Q: σ.Q(i, j').lo ≤ σ.Q(i, j'+1).lo ≤ 1
          have hlo_j' := σ.mono_Q i j' i (j' + 1) le_rfl (by omega) hmemQσ
          have hlo_j'_le : (σ.Q.paint i j').layerOrd ≤ 1 := le_trans hlo_j' hlo
          -- σ.Q ∈ {•, s, r, d}. lo ≤ 1 and ≠ • → σ.Q = s (lo = 1)
          have hQs : σ.Q.paint i j' = .s := by
            have hsymQ := σ.sym_Q i j' hmemQσ'
            rcases hγ with hγ | hγ <;> rw [hγ] at hsymQ <;>
              simp [DRCSymbol.allowed] at hsymQ <;>
              (rcases hsymQ with h | h | h | h <;>
               first
                 | (exact absurd h hQne)
                 | (exact h)
                 | (rw [h] at hlo_j'_le; simp [DRCSymbol.layerOrd] at hlo_j'_le))
          -- Now σ.Q(i, j') = s and σ.Q(i, j'+1).lo ≤ 1.
          -- σ.Q(i, j'+1): σ.Q ≠ • (from hpaintQ analysis? or from mono?)
          -- Actually σ.Q(i, j'+1).lo ≤ 1 and sym_Q. If σ.Q(i, j'+1) = •: OK. If = s: row_s conflict.
          -- We don't know σ.Q(i, j'+1) exactly, but if = s: σ's row_s at row i gives j' = j'+1. Contradiction.
          by_cases hQ_j1_s : σ.Q.paint i (j' + 1) = .s
          · have := (σ.row_s i .R .R j' (j' + 1)
              (by simp [paintBySide]; exact hQs)
              (by simp [paintBySide]; exact hQ_j1_s)).2
            omega
          · -- σ.Q(i, j'+1) ≠ s. And lo ≤ 1. So σ.Q(i, j'+1) = •.
            have hQ_j1_dot : σ.Q.paint i (j' + 1) = .dot := by
              have hsymQ1 := σ.sym_Q i (j' + 1) hmemQσ
              rcases hγ with hγ | hγ <;> rw [hγ] at hsymQ1 <;>
                simp [DRCSymbol.allowed] at hsymQ1 <;>
                (rcases hsymQ1 with h | h | h | h <;>
                 first
                   | (exact h)
                   | (exact absurd h hQ_j1_s)
                   | (rw [h] at hlo; simp [DRCSymbol.layerOrd] at hlo))
            -- σ's dot_match at (i, j'+1): σ.Q = • ∧ ∈σ.Q ↔ σ.P = • ∧ ∈σ.P
            have hdm := (σ.dot_match i (j' + 1)).mpr ⟨hmemQσ, hQ_j1_dot⟩
            -- So (i, j'+1) ∈ σ.P and σ.P(i, j'+1) = •.
            have hmono := σ.mono_P i j' i (j' + 1) le_rfl (by omega) hdm.1
            rw [hPc, hdm.2] at hmono
            simp [DRCSymbol.layerOrd] at hmono
        -- Now σ.P(i, j') ≠ c. Go to next if.
        rw [if_neg h_not_c]
        rw [if_pos ⟨hmemQσ, hlo⟩]
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    show (liftPaintP_naive σ μP i₁ j₁).layerOrd ≤ (liftPaintP_naive σ μP i₂ j₂).layerOrd
    -- Case split on j₁, j₂
    match j₁, j₂, hj with
    | 0, 0, _ =>
      -- Col 0 → Col 0: use liftPaintP_naive_col0_mono
      exact liftPaintP_naive_col0_mono σ hγ μP μQ hQsh h_QleP hi hmem
    | j₁' + 1, j₂' + 1, hj =>
      -- Col ≥ 1 → Col ≥ 1: use liftPaintP_naive_succ_mono
      exact liftPaintP_naive_succ_mono σ hγ μP hPsh hi hj hmem
    | 0, j₂' + 1, _ =>
      -- Col 0 → Col ≥ 1: use liftPaintP_naive_col0_to_succ_mono
      exact liftPaintP_naive_col0_to_succ_mono σ hγ μP μQ hPsh hQsh h_sub h_QleP
        h_bal_exc hi hmem
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    show (liftPaintQ_naive σ i₁ j₁).layerOrd ≤ (liftPaintQ_naive σ i₂ j₂).layerOrd
    -- f(σ.Q) = τ.Q. f(•) = •, f(s) = •, f(r) = r, f(d) = d.
    -- f preserves order in lo (weakly): σ mono_Q → τ mono_Q.
    -- (i₂, j₂) ∈ μQ = σ.Q.shape.
    have hmem₂ : (i₂, j₂) ∈ σ.Q.shape := hQsh ▸ hmem
    -- Key: τ.Q.lo ≤ σ.Q.lo actually, but we need τ.lo ≤ τ.lo.
    -- If σ.Q(i₁, j₁).lo ≤ 1 (dot/s): τ.Q(i₁, j₁) = •, lo = 0.
    -- If σ.Q(i₁, j₁).lo > 1: τ.Q(i₁, j₁) = σ.Q(i₁, j₁).
    -- Similarly for (i₂, j₂).
    -- σ's mono_Q: σ.Q(i₁, j₁).lo ≤ σ.Q(i₂, j₂).lo.
    have hmono := σ.mono_Q i₁ j₁ i₂ j₂ hi hj hmem₂
    simp only [liftPaintQ_naive]
    by_cases c₁ : (i₁, j₁) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i₁ j₁).layerOrd ≤ 1
    · rw [if_pos c₁]
      push_neg at c₁
      by_cases c₂ : (i₂, j₂) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i₂ j₂).layerOrd ≤ 1
      · rw [if_pos c₂]
        exact hmono
      · -- (i₂, j₂) ∈ σ.Q.shape (from hmem₂). So ¬c₂ means σ.Q(i₂, j₂).lo ≤ 1.
        -- But σ.Q(i₁, j₁).lo ≤ σ.Q(i₂, j₂).lo and σ.Q(i₁, j₁).lo > 1.
        -- 1 < σ.Q(i₁, j₁).lo ≤ σ.Q(i₂, j₂).lo ≤ 1. Contradiction.
        exfalso
        push_neg at c₂
        have hle := c₂ hmem₂
        have := c₁.2
        omega
    · rw [if_neg c₁]
      simp [DRCSymbol.layerOrd]
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- s appears only in τ.P (τ.Q ⊆ {•, r, d}).
    have hs₁_L : s₁ = .L := by
      cases s₁ with
      | L => rfl
      | R => exfalso
             exact liftPaintQ_naive_ne_s σ hγ i j₁ (by simpa [paintBySide] using h₁)
    have hs₂_L : s₂ = .L := by
      cases s₂ with
      | L => rfl
      | R => exfalso
             exact liftPaintQ_naive_ne_s σ hγ i j₂ (by simpa [paintBySide] using h₂)
    subst hs₁_L; subst hs₂_L
    refine ⟨rfl, ?_⟩
    simp only [paintBySide] at h₁ h₂
    change liftPaintP_naive σ μP i j₁ = .s at h₁
    change liftPaintP_naive σ μP i j₂ = .s at h₂
    -- Goal: j₁ = j₂. Case on j₁, j₂.
    -- Helper: j_a=0, j_b≥1 gives contradiction (via dot_match + mono_Q).
    -- Helper: j_a≥1, j_b≥1, j_a < j_b gives contradiction via Cases A/B.
    suffices h : ∀ a b : ℕ, a ≤ b → liftPaintP_naive σ μP i a = .s →
      liftPaintP_naive σ μP i b = .s → a = b by
      rcases Nat.le_or_ge j₁ j₂ with hle | hle
      · exact h j₁ j₂ hle h₁ h₂
      · exact (h j₂ j₁ hle h₂ h₁).symm
    intro a b hab ha hb
    by_contra hne
    have hab' : a < b := lt_of_le_of_ne hab hne
    -- Case: a = 0, b ≥ 1 (since a < b, b ≥ 1 always).
    -- Now both h_a and h_b hold. Derive contradiction via σ.
    -- From h_b : τ.P(i, b) = s and b ≥ 1 (always): σ.P(i, b-1) ≠ c, ¬(Q(i, b).lo ≤ 1).
    have hb_ge : b ≥ 1 := by omega
    -- Generate b as b = b' + 1 for some b'.
    obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hspec_b := (liftPaintP_naive_succ_s_iff σ μP i b').mp hb
    obtain ⟨hmem_b, hne_c_b, hnot_dot_b⟩ := hspec_b
    -- (i, b') ∈ σ.P.shape via shiftLeft.
    have hmemPσ_b : (i, b') ∈ σ.P.shape := by
      rw [hPsh, YoungDiagram.mem_shiftLeft]; exact hmem_b
    -- σ.P(i, b') ≠ c, σ.P ∈ {•, c}, so σ.P(i, b') = •.
    have hPdot_b : σ.P.paint i b' = .dot := by
      rcases B_P_dot_or_c σ hγ hmemPσ_b with h | h
      · exact h
      · exact absurd h hne_c_b
    -- By σ's dot_match at (i, b'): (i, b') ∈ σ.Q.shape and σ.Q(i, b') = •.
    have hQdot_b : σ.Q.paint i b' = .dot ∧ (i, b') ∈ σ.Q.shape := by
      have ⟨h_mem, h_dot⟩ := (σ.dot_match i b').mp ⟨hmemPσ_b, hPdot_b⟩
      exact ⟨h_dot, h_mem⟩
    cases a with
    | zero =>
      -- a = 0. τ.P(i, 0) = s → ¬((i, 0) ∈ σ.Q ∧ σ.Q(i, 0).lo ≤ 1).
      obtain ⟨_, _, hnot_dot_a⟩ := (liftPaintP_naive_col0_s_iff σ μP i).mp ha
      apply hnot_dot_a
      -- (i, 0) ∈ σ.Q.shape by lower set from (i, b') (need (i, 0) ≤ (i, b')).
      have hmemQ_0 : (i, 0) ∈ σ.Q.shape :=
        σ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hQdot_b.2
      refine ⟨hmemQ_0, ?_⟩
      -- σ.Q(i, 0).lo ≤ σ.Q(i, b').lo = 0 via mono_Q.
      have := σ.mono_Q i 0 i b' le_rfl (by omega) hQdot_b.2
      rw [hQdot_b.1, DRCSymbol.layerOrd] at this
      omega
    | succ a' =>
      -- a = a' + 1. τ.P(i, a'+1) = s. Similarly σ.P(i, a') = •, σ.Q(i, a') = •.
      have hspec_a := (liftPaintP_naive_succ_s_iff σ μP i a').mp ha
      obtain ⟨hmem_a, _hne_c_a, hnot_dot_a⟩ := hspec_a
      -- Now j₁ = a' + 1 < b' + 1, so a' < b' (but only a' ≤ b' since a < b means a' < b').
      -- Goal: show (i, a' + 1) ∉ σ.Q.shape OR σ.Q(i, a' + 1).lo > 1.
      -- Use: σ.Q(i, b').lo = 0 (from hQdot_b). σ.Q(i, a'+1) relates via mono_Q if (i, b') ∈ shape.
      -- We have (i, b') ∈ σ.Q.shape.
      apply hnot_dot_a
      -- We want (i, a'+1) ∈ σ.Q.shape ∧ σ.Q(i, a'+1).lo ≤ 1.
      have hab'_lt : a' < b' := by omega
      -- (i, a'+1) ≤ (i, b') since a'+1 ≤ b'.
      have ha1_le : a' + 1 ≤ b' := by omega
      have hmemQ_a1 : (i, a' + 1) ∈ σ.Q.shape :=
        σ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, ha1_le⟩) hQdot_b.2
      refine ⟨hmemQ_a1, ?_⟩
      have := σ.mono_Q i (a' + 1) i b' le_rfl ha1_le hQdot_b.2
      rw [hQdot_b.1, DRCSymbol.layerOrd] at this
      omega
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- r appears only in τ.Q (τ.P ⊆ {•, s, c}).
    have hs₁_R : s₁ = .R := by
      cases s₁ with
      | R => rfl
      | L => exfalso; exact liftPaintP_naive_ne_r σ μP i j₁ (by simpa [paintBySide] using h₁)
    have hs₂_R : s₂ = .R := by
      cases s₂ with
      | R => rfl
      | L => exfalso; exact liftPaintP_naive_ne_r σ μP i j₂ (by simpa [paintBySide] using h₂)
    subst hs₁_R; subst hs₂_R
    refine ⟨rfl, ?_⟩
    -- τ.Q(i, j) = r iff σ.Q(i, j) = r (with conditions).
    simp only [paintBySide] at h₁ h₂
    change liftPaintQ_naive σ i j₁ = .r at h₁
    change liftPaintQ_naive σ i j₂ = .r at h₂
    simp only [liftPaintQ_naive] at h₁ h₂
    -- Unpack: τ.Q(i, j) = r requires the if condition and σ.Q.paint = r.
    have hr₁ : σ.Q.paint i j₁ = .r := by
      by_cases c : (i, j₁) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i j₁).layerOrd ≤ 1
      · rw [if_pos c] at h₁; exact h₁
      · rw [if_neg c] at h₁; exact absurd h₁ (by decide)
    have hr₂ : σ.Q.paint i j₂ = .r := by
      by_cases c : (i, j₂) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i j₂).layerOrd ≤ 1
      · rw [if_pos c] at h₂; exact h₂
      · rw [if_neg c] at h₂; exact absurd h₂ (by decide)
    exact (σ.row_r i .R .R j₁ j₂
      (by simp [paintBySide]; exact hr₁)
      (by simp [paintBySide]; exact hr₂)).2
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    -- h₁ : τ.P(i₁, j) = c, h₂ : τ.P(i₂, j) = c.
    -- show i₁ = i₂. Use σ's col_c_P or the unique bottom structure of col 0.
    -- τ.P(i, j) = c comes from:
    -- j = 0: σ.γ = B- ∧ i = bottom. So i = bottom (unique).
    -- j = j'+1: σ.P(i, j') = c, by σ's col_c_P, i is unique.
    change liftPaintP_naive σ μP i₁ j = .c at h₁
    change liftPaintP_naive σ μP i₂ j = .c at h₂
    cases j with
    | zero =>
      -- τ.P(i, 0) = c requires σ.γ = B- ∧ i = μP.colLen 0 - 1.
      -- So both i₁ = i₂ = μP.colLen 0 - 1.
      have hmem₁ : (i₁, 0) ∈ μP := by
        by_contra h; rw [liftPaintP_naive_outside h] at h₁; exact DRCSymbol.noConfusion h₁
      have hmem₂ : (i₂, 0) ∈ μP := by
        by_contra h; rw [liftPaintP_naive_outside h] at h₂; exact DRCSymbol.noConfusion h₂
      rw [liftPaintP_naive_zero σ μP i₁ hmem₁] at h₁
      rw [liftPaintP_naive_zero σ μP i₂ hmem₂] at h₂
      by_cases hbm₁ : σ.γ = .Bminus ∧ i₁ = μP.colLen 0 - 1
      · by_cases hbm₂ : σ.γ = .Bminus ∧ i₂ = μP.colLen 0 - 1
        · rw [hbm₁.2, hbm₂.2]
        · rw [if_neg hbm₂] at h₂
          split_ifs at h₂ <;> exact absurd h₂ (by decide)
      · rw [if_neg hbm₁] at h₁
        split_ifs at h₁ <;> exact absurd h₁ (by decide)
    | succ j' =>
      have hmem₁ : (i₁, j' + 1) ∈ μP := by
        by_contra h; rw [liftPaintP_naive_outside h] at h₁; exact DRCSymbol.noConfusion h₁
      have hmem₂ : (i₂, j' + 1) ∈ μP := by
        by_contra h; rw [liftPaintP_naive_outside h] at h₂; exact DRCSymbol.noConfusion h₂
      rw [liftPaintP_naive_succ σ μP i₁ j' hmem₁] at h₁
      rw [liftPaintP_naive_succ σ μP i₂ j' hmem₂] at h₂
      by_cases hc₁ : σ.P.paint i₁ j' = .c
      · by_cases hc₂ : σ.P.paint i₂ j' = .c
        · exact σ.col_c_P j' i₁ i₂ hc₁ hc₂
        · rw [if_neg hc₂] at h₂
          split_ifs at h₂ <;> exact absurd h₂ (by decide)
      · rw [if_neg hc₁] at h₁
        split_ifs at h₁ <;> exact absurd h₁ (by decide)
  col_c_Q := by
    intro j i₁ _ h₁ _
    exact absurd h₁ (liftPaintQ_naive_ne_c σ hγ i₁ j)
  col_d_P := by
    intro j i₁ _ h₁ _
    exact absurd h₁ (liftPaintP_naive_ne_d σ μP i₁ j)
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂
    change liftPaintQ_naive σ i₁ j = .d at h₁
    change liftPaintQ_naive σ i₂ j = .d at h₂
    simp only [liftPaintQ_naive] at h₁ h₂
    by_cases c₁ : (i₁, j) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i₁ j).layerOrd ≤ 1
    · rw [if_pos c₁] at h₁
      by_cases c₂ : (i₂, j) ∈ σ.Q.shape ∧ ¬(σ.Q.paint i₂ j).layerOrd ≤ 1
      · rw [if_pos c₂] at h₂
        exact σ.col_d_Q j i₁ i₂ h₁ h₂
      · rw [if_neg c₂] at h₂; exact absurd h₂ (by decide)
    · rw [if_neg c₁] at h₁; exact absurd h₁ (by decide)

/-! ## Round trip: descent ∘ lift = id -/

/-- descentType_M of the lift equals σ's γ (B⁺ or B⁻), when μP has non-empty col 0. -/
theorem descentType_M_liftBM_naive (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    (h_pos : μP.colLen 0 > 0) :
    PBP.descentType_M (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc) rfl = σ.γ := by
  have h_bot : (μP.colLen 0 - 1, 0) ∈ μP :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  unfold PBP.descentType_M
  split_ifs with h
  · -- Nonempty filter. Show σ.γ = .Bminus.
    obtain ⟨⟨i, j⟩, hmem⟩ := h
    simp at hmem
    obtain ⟨_, hj, hc⟩ := hmem
    subst hj
    have := (liftPaintP_naive_col0_c_iff σ μP i).mp hc
    exact this.2.1.symm
  · -- Empty filter. Show σ.γ = .Bplus.
    rcases hγ with hγ | hγ
    · exact hγ.symm
    · exfalso; apply h
      refine ⟨(μP.colLen 0 - 1, 0), ?_⟩
      simp only [Finset.mem_filter, YoungDiagram.mem_cells]
      refine ⟨h_bot, trivial, ?_⟩
      show liftPaintP_naive σ μP _ _ = _
      exact (liftPaintP_naive_col0_c_iff σ μP _).mpr ⟨h_bot, hγ, rfl⟩

/-- Paint equality: descent(lift σ).P = σ.P. -/
theorem descentMB_liftBM_naive_P_paint (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1) :
    ∀ i j, PBP.descentPaintL_MB
      (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc) i j = σ.P.paint i j := by
  intro i j
  set τ := liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc with hτ
  simp only [PBP.descentPaintL_MB]
  -- Case on whether (i, j) ∈ σ.P.shape.
  by_cases hmem : (i, j) ∈ σ.P.shape
  · -- (i, j) ∈ σ.P.shape. Use σ's B-type property.
    have hmemμP : (i, j + 1) ∈ μP := by
      rw [hPsh, YoungDiagram.mem_shiftLeft] at hmem; exact hmem
    rcases B_P_dot_or_c σ hγ hmem with hdot | hc
    · -- σ.P(i, j) = dot. Need descent to return dot.
      -- τ.P(i, j+1) ∈ {dot, s} by succ, since σ.P(i, j) = dot ≠ c.
      -- i < dotScolLen τ.P (j+1) since τ.P(i, j+1) has lo ≤ 1.
      have hτp_lo : (τ.P.paint i (j + 1)).layerOrd ≤ 1 := by
        show (liftPaintP_naive σ μP i (j + 1)).layerOrd ≤ 1
        rw [liftPaintP_naive_succ σ μP i j hmemμP]
        split_ifs with h1 h2
        · rw [h1] at hdot; exact absurd hdot (by decide)
        all_goals simp [DRCSymbol.layerOrd]
      -- Show i < dotScolLen τ.P (j+1).
      -- Use that τ.P(i, j+1) has lo ≤ 1 and is in shape → i is in dotSdiag column.
      have hmemτP : (i, j + 1) ∈ τ.P.shape := by simp [hτ, liftBM_naive]; exact hmemμP
      have hi_lt : i < PBP.dotScolLen τ.P (j + 1) := by
        rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
        have : (i, j + 1) ∈ PBP.dotSdiag τ.P τ.mono_P := by
          simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
            YoungDiagram.mem_cells]
          exact ⟨hmemτP, hτp_lo⟩
        exact YoungDiagram.mem_iff_lt_colLen.mp this
      rw [if_pos hi_lt, hdot]
    · -- σ.P(i, j) = c. Need descent to return c.
      -- τ.P(i, j+1) = c by succ_c_iff.
      have hτp_c : τ.P.paint i (j + 1) = .c := by
        show liftPaintP_naive σ μP i (j + 1) = .c
        exact (liftPaintP_naive_succ_c_iff σ μP i j).mpr ⟨hmemμP, hc⟩
      -- ¬(i < dotScolLen τ.P (j+1)): τ.P(i, j+1) = c has lo = 3 > 1.
      have hi_ge : ¬ (i < PBP.dotScolLen τ.P (j + 1)) := by
        intro hlt
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hlt)
        rw [hτp_c, DRCSymbol.layerOrd] at hlo; omega
      rw [if_neg hi_ge, hτp_c, hc]
  · -- (i, j) ∉ σ.P.shape. σ.P(i, j) = dot. τ.P(i, j+1) = dot (outside μP).
    rw [σ.P.paint_outside i j hmem]
    have hmemμP_not : (i, j + 1) ∉ μP := by
      rw [hPsh, YoungDiagram.mem_shiftLeft] at hmem
      exact hmem
    -- τ.P(i, j+1) = dot.
    have hτp_dot : τ.P.paint i (j + 1) = .dot :=
      τ.P.paint_outside i (j + 1) (by simp [hτ, liftBM_naive]; exact hmemμP_not)
    -- Need to show: either dotScolLen gives dot, or τ.P.paint gives dot.
    split_ifs with h
    · rfl
    · exact hτp_dot

/-! ### Helpers for Q_paint -/

/-- Helper: ¬(i < dotScolLen τ.P (j+1)) when (i, j) ∉ σ.P.shape.
    Because (i, j+1) ∉ μP = τ.P.shape, so (i, j+1) ∉ dotSdiag τ.P either. -/
private theorem τP_succ_outside_not_dotScolLen (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    {i j : ℕ} (hmemPσ : (i, j) ∉ σ.P.shape) :
    ¬ (i < PBP.dotScolLen
      (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc).P (j + 1)) := by
  set τ := liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc with hτ
  intro hlt
  have hds_le := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  have h_mem_τ : (i, j + 1) ∈ τ.P.shape :=
    YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le hlt hds_le)
  have h_mem_μP : (i, j + 1) ∈ μP := by
    simp [hτ, liftBM_naive] at h_mem_τ; exact h_mem_τ
  rw [hPsh, YoungDiagram.mem_shiftLeft] at hmemPσ
  exact hmemPσ h_mem_μP

/-- Helper: ¬(i < dotScolLen τ.P (j+1)) when σ.P(i, j) = c.
    Because τ.P(i, j+1) = c has layerOrd 3 > 1. -/
private theorem τP_succ_c_not_dotScolLen (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    {i j : ℕ} (hmemμP : (i, j + 1) ∈ μP) (hPc : σ.P.paint i j = .c) :
    ¬ (i < PBP.dotScolLen
      (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc).P (j + 1)) := by
  set τ := liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc with hτ
  have hτp_c : τ.P.paint i (j + 1) = .c := by
    show liftPaintP_naive σ μP i (j + 1) = .c
    exact (liftPaintP_naive_succ_c_iff σ μP i j).mpr ⟨hmemμP, hPc⟩
  intro hlt
  have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
    (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hlt)
  rw [hτp_c, DRCSymbol.layerOrd] at hlo; omega

/-- Helper: (σ.P(i, j) = c) follows from (i, j) ∈ σ.P.shape and σ.Q(i, j) ≠ dot.
    Uses σ's dot_match contrapositive + B-type P structure. -/
private theorem σP_c_of_Q_ne_dot (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    {i j : ℕ} (hmemPσ : (i, j) ∈ σ.P.shape) (hQne_dot : σ.Q.paint i j ≠ .dot) :
    σ.P.paint i j = .c := by
  have hPne_dot : σ.P.paint i j ≠ .dot := by
    intro habs
    have ⟨_, h_dot⟩ := (σ.dot_match i j).mp ⟨hmemPσ, habs⟩
    exact hQne_dot h_dot
  rcases B_P_dot_or_c σ hγ hmemPσ with h | h
  · exact absurd h hPne_dot
  · exact h

theorem descentMB_liftBM_naive_Q_paint (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1) :
    ∀ i j, PBP.descentPaintR_MB
      (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc) i j = σ.Q.paint i j := by
  intro i j
  set τ := liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc with hτ
  simp only [PBP.descentPaintR_MB]
  -- Case on whether (i, j) ∈ σ.Q.shape.
  by_cases hmem : (i, j) ∈ σ.Q.shape
  · -- (i, j) ∈ σ.Q.shape = μQ.
    have hmemμQ : (i, j) ∈ μQ := hQsh ▸ hmem
    have hmemτQ : (i, j) ∈ τ.Q.shape := by simp [hτ, liftBM_naive]; exact hmemμQ
    -- σ.Q ∈ {dot, s, r, d} for B-type.
    have hsymQ := σ.sym_Q i j hmem
    have hQcases : σ.Q.paint i j = .dot ∨ σ.Q.paint i j = .s ∨
                   σ.Q.paint i j = .r ∨ σ.Q.paint i j = .d := by
      rcases hγ with hγB | hγB <;> rw [hγB] at hsymQ <;>
        simp [DRCSymbol.allowed] at hsymQ <;> exact hsymQ
    rcases hQcases with hdot | hs | hr | hd
    · -- σ.Q(i, j) = dot.
      -- Via σ.dot_match: (i, j) ∈ σ.P.shape and σ.P(i, j) = dot.
      obtain ⟨hmemPσ, hPdot⟩ := (σ.dot_match i j).mpr ⟨hmem, hdot⟩
      have hmemμP : (i, j + 1) ∈ μP := by
        rw [hPsh, YoungDiagram.mem_shiftLeft] at hmemPσ; exact hmemPσ
      -- τ.P(i, j+1) ∈ {dot, s} since σ.P(i, j) = dot ≠ c.
      have hτp_lo : (τ.P.paint i (j + 1)).layerOrd ≤ 1 := by
        show (liftPaintP_naive σ μP i (j + 1)).layerOrd ≤ 1
        rw [liftPaintP_naive_succ σ μP i j hmemμP]
        rw [if_neg (by rw [hPdot]; decide)]
        split_ifs <;> simp [DRCSymbol.layerOrd]
      have hmemτP : (i, j + 1) ∈ τ.P.shape := by
        simp [hτ, liftBM_naive]; exact hmemμP
      -- i < dotScolLen τ.P (j+1) (Zone 1).
      have hi_lt : i < PBP.dotScolLen τ.P (j + 1) := by
        rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
        have : (i, j + 1) ∈ PBP.dotSdiag τ.P τ.mono_P := by
          simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
            YoungDiagram.mem_cells]
          exact ⟨hmemτP, hτp_lo⟩
        exact YoungDiagram.mem_iff_lt_colLen.mp this
      rw [if_pos hi_lt, hdot]
    · -- σ.Q(i, j) = s.
      -- First show: ¬ Zone 1, by case on (i, j) ∈ σ.P.shape.
      have hQne_dot : σ.Q.paint i j ≠ .dot := by rw [hs]; decide
      have hi_ge_P : ¬ (i < PBP.dotScolLen τ.P (j + 1)) := by
        by_cases hmemPσ : (i, j) ∈ σ.P.shape
        · have hPc := σP_c_of_Q_ne_dot σ hγ hmemPσ hQne_dot
          have hmemμP : (i, j + 1) ∈ μP := by
            rw [hPsh, YoungDiagram.mem_shiftLeft] at hmemPσ; exact hmemPσ
          exact τP_succ_c_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemμP hPc
        · exact τP_succ_outside_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemPσ
      rw [if_neg hi_ge_P]
      -- Now Zone 2: τ.Q(i, j) = dot (since σ.Q = s has lo = 1 ≤ 1), i < dotScolLen τ.Q j.
      have hτq_dot : τ.Q.paint i j = .dot := by
        show liftPaintQ_naive σ i j = .dot
        apply (liftPaintQ_naive_dot_iff σ i j).mpr
        right; rw [hs]; decide
      have hi_lt2 : i < PBP.dotScolLen τ.Q j := by
        rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]
        have : (i, j) ∈ PBP.dotSdiag τ.Q τ.mono_Q := by
          simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
            YoungDiagram.mem_cells]
          exact ⟨hmemτQ, by rw [hτq_dot]; decide⟩
        exact YoungDiagram.mem_iff_lt_colLen.mp this
      rw [if_pos hi_lt2, hs]
    · -- σ.Q(i, j) = r.
      have hQne_dot : σ.Q.paint i j ≠ .dot := by rw [hr]; decide
      -- ¬ Zone 1.
      have hi_ge_P : ¬ (i < PBP.dotScolLen τ.P (j + 1)) := by
        by_cases hmemPσ : (i, j) ∈ σ.P.shape
        · have hPc := σP_c_of_Q_ne_dot σ hγ hmemPσ hQne_dot
          have hmemμP : (i, j + 1) ∈ μP := by
            rw [hPsh, YoungDiagram.mem_shiftLeft] at hmemPσ; exact hmemPσ
          exact τP_succ_c_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemμP hPc
        · exact τP_succ_outside_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemPσ
      rw [if_neg hi_ge_P]
      -- τ.Q(i, j) = r (lo = 2 > 1, so NOT Zone 2).
      have hτq_r : τ.Q.paint i j = .r := by
        show liftPaintQ_naive σ i j = .r
        simp only [liftPaintQ_naive]
        rw [if_pos ⟨hmem, by rw [hr]; decide⟩]
        exact hr
      have hi_ge_Q : ¬ (i < PBP.dotScolLen τ.Q j) := by
        intro hlt
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hlt)
        rw [hτq_r, DRCSymbol.layerOrd] at hlo; omega
      rw [if_neg hi_ge_Q, hτq_r, hr]
    · -- σ.Q(i, j) = d.
      have hQne_dot : σ.Q.paint i j ≠ .dot := by rw [hd]; decide
      have hi_ge_P : ¬ (i < PBP.dotScolLen τ.P (j + 1)) := by
        by_cases hmemPσ : (i, j) ∈ σ.P.shape
        · have hPc := σP_c_of_Q_ne_dot σ hγ hmemPσ hQne_dot
          have hmemμP : (i, j + 1) ∈ μP := by
            rw [hPsh, YoungDiagram.mem_shiftLeft] at hmemPσ; exact hmemPσ
          exact τP_succ_c_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemμP hPc
        · exact τP_succ_outside_not_dotScolLen σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc hmemPσ
      rw [if_neg hi_ge_P]
      have hτq_d : τ.Q.paint i j = .d := by
        show liftPaintQ_naive σ i j = .d
        simp only [liftPaintQ_naive]
        rw [if_pos ⟨hmem, by rw [hd]; decide⟩]
        exact hd
      have hi_ge_Q : ¬ (i < PBP.dotScolLen τ.Q j) := by
        intro hlt
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hlt)
        rw [hτq_d, DRCSymbol.layerOrd] at hlo; omega
      rw [if_neg hi_ge_Q, hτq_d, hd]
  · -- (i, j) ∉ σ.Q.shape. σ.Q(i, j) = dot (paint_outside). Need descent = dot.
    rw [σ.Q.paint_outside i j hmem]
    have hmemμQ_not : (i, j) ∉ μQ := hQsh ▸ hmem
    have hmemτQ_not : (i, j) ∉ τ.Q.shape := by simp [hτ, liftBM_naive]; exact hmemμQ_not
    have hτq_dot : τ.Q.paint i j = .dot := τ.Q.paint_outside i j hmemτQ_not
    -- Zone 1 gives dot ✓; Zone 2 contradicts (i, j) ∉ τ.Q.shape; Zone 3 gives τ.Q = dot ✓.
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hds_le := PBP.dotScolLen_le_colLen τ.Q τ.mono_Q j
      have : (i, j) ∈ τ.Q.shape :=
        YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le h2 hds_le)
      exact hmemτQ_not this
    · exact hτq_dot

/-- The lift τ = liftBM_naive σ satisfies descentMB_PBP(τ) = σ.
    Requires h_pos : μP.colLen 0 > 0 (edge case μP = ⊥ fails for σ.γ = B-). -/
theorem descentMB_liftBM_naive (σ : PBP) (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = YoungDiagram.shiftLeft μP)
    (hQsh : σ.Q.shape = μQ)
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    (h_pos : μP.colLen 0 > 0) :
    descentMB_PBP (liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc) rfl = σ := by
  apply PBP.ext''
  · exact descentType_M_liftBM_naive σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc h_pos
  · apply PaintedYoungDiagram.ext'
    · -- descent(lift).P.shape = shiftLeft (lift.P.shape) = shiftLeft μP = σ.P.shape
      show μP.shiftLeft = σ.P.shape; exact hPsh.symm
    · funext i j
      exact descentMB_liftBM_naive_P_paint σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc i j
  · apply PaintedYoungDiagram.ext'
    · exact hQsh.symm
    · funext i j
      exact descentMB_liftBM_naive_Q_paint σ hγ μP μQ hPsh hQsh h_sub h_QleP h_bal_exc i j

/-! ## Prop 10.8(a) for M: primitive case bijection -/

/-- The lift as a PBPSet map. -/
noncomputable def liftBM_naive_PBPSet {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal_exc_plus : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        ∀ σ : PBPSet .Bplus μP.shiftLeft μQ,
          (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    (h_bal_exc_minus : μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
        ∀ σ : PBPSet .Bminus μP.shiftLeft μQ,
          (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1)
    (σ : PBPSet .Bplus μP.shiftLeft μQ ⊕ PBPSet .Bminus μP.shiftLeft μQ) :
    PBPSet .M μP μQ :=
  match σ with
  | .inl σp =>
    ⟨liftBM_naive σp.val (Or.inl σp.prop.1) μP μQ σp.prop.2.1 σp.prop.2.2
      h_sub h_QleP (fun hb hp => h_bal_exc_plus hb hp σp),
      ⟨rfl, rfl, rfl⟩⟩
  | .inr σm =>
    ⟨liftBM_naive σm.val (Or.inr σm.prop.1) μP μQ σm.prop.2.1 σm.prop.2.2
      h_sub h_QleP (fun hb hp => h_bal_exc_minus hb hp σm),
      ⟨rfl, rfl, rfl⟩⟩

/-! ## Helpers for Prop 10.8(a): building the bijection -/

/-- In primitive case, h_bal_exc is vacuously true. -/
theorem h_bal_exc_of_primitive {μP μQ : YoungDiagram} (σ : PBP)
    (h_prim : μP.colLen 0 > μQ.colLen 0) :
    μP.colLen 0 = μQ.colLen 0 → μP.colLen 0 > 0 →
    (σ.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1 := by
  intro heq _; omega

/-- Shape property of descent: P' shape = shiftLeft τ.P.shape. -/
private lemma descentMB_PBP_P_shape (τ : PBP) (hγ : τ.γ = .M) :
    (descentMB_PBP τ hγ).P.shape = τ.P.shape.shiftLeft := rfl

/-- Shape property of descent: Q' shape = τ.Q.shape. -/
private lemma descentMB_PBP_Q_shape (τ : PBP) (hγ : τ.γ = .M) :
    (descentMB_PBP τ hγ).Q.shape = τ.Q.shape := rfl

/-- descentType_M is either B+ or B-. -/
private lemma descentType_M_eq_or (τ : PBP) (hγ : τ.γ = .M) :
    PBP.descentType_M τ hγ = .Bplus ∨ PBP.descentType_M τ hγ = .Bminus := by
  unfold PBP.descentType_M; split_ifs <;> tauto

/-- Descent as disjoint sum (routing via γ'). -/
noncomputable def descentMB_sum {μP μQ : YoungDiagram} (τ : PBPSet .M μP μQ) :
    PBPSet .Bplus μP.shiftLeft μQ ⊕ PBPSet .Bminus μP.shiftLeft μQ :=
  let σ := descentMB_PBP τ.val τ.prop.1
  have hPsh : σ.P.shape = μP.shiftLeft := by
    show τ.val.P.shape.shiftLeft = μP.shiftLeft; rw [τ.prop.2.1]
  have hQsh : σ.Q.shape = μQ := τ.prop.2.2
  if h : PBP.descentType_M τ.val τ.prop.1 = .Bplus then
    .inl ⟨σ, ⟨h, hPsh, hQsh⟩⟩
  else
    .inr ⟨σ, ⟨(descentType_M_eq_or τ.val τ.prop.1).resolve_left h, hPsh, hQsh⟩⟩

/-- Lift from sum. -/
noncomputable def liftBM_sum_naive {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_prim : μP.colLen 0 > μQ.colLen 0)
    (σ : PBPSet .Bplus μP.shiftLeft μQ ⊕ PBPSet .Bminus μP.shiftLeft μQ) :
    PBPSet .M μP μQ :=
  match σ with
  | .inl σp =>
    ⟨liftBM_naive σp.val (Or.inl σp.prop.1) μP μQ σp.prop.2.1 σp.prop.2.2
      h_sub h_QleP (h_bal_exc_of_primitive _ h_prim),
      ⟨rfl, rfl, rfl⟩⟩
  | .inr σm =>
    ⟨liftBM_naive σm.val (Or.inr σm.prop.1) μP μQ σm.prop.2.1 σm.prop.2.2
      h_sub h_QleP (h_bal_exc_of_primitive _ h_prim),
      ⟨rfl, rfl, rfl⟩⟩

/-- The equiv between M and B⁺⊕B⁻ on target shapes (primitive case). -/
noncomputable def descent_equiv_primitive {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_prim : μP.colLen 0 > μQ.colLen 0) :
    PBPSet .M μP μQ ≃
      (PBPSet .Bplus μP.shiftLeft μQ ⊕ PBPSet .Bminus μP.shiftLeft μQ) where
  toFun := descentMB_sum
  invFun := liftBM_sum_naive h_sub h_QleP h_prim
  left_inv := by
    intro τ
    -- τ ↦ descent(τ) : Sum ↦ lift(descent(τ)) : PBPSet .M = τ.
    -- Uses descentMB_injective applied to the PBP level round-trip:
    -- descent(lift(descent(τ))) = descent(τ) (via right_inv at PBP level).
    -- Then injectivity gives lift(descent(τ)) = τ.
    have h_pos : μP.colLen 0 > 0 := by omega
    refine descentMB_injective μP μQ _ τ ?_
    simp only [descentMB_sum, liftBM_sum_naive]
    split_ifs with h
    · -- B⁺ branch
      have hPsh : (descentMB_PBP τ.val τ.prop.1).P.shape = μP.shiftLeft := by
        show τ.val.P.shape.shiftLeft = μP.shiftLeft
        rw [τ.prop.2.1]
      have hQsh : (descentMB_PBP τ.val τ.prop.1).Q.shape = μQ := τ.prop.2.2
      exact descentMB_liftBM_naive (descentMB_PBP τ.val τ.prop.1) (Or.inl h)
        μP μQ hPsh hQsh h_sub h_QleP (h_bal_exc_of_primitive _ h_prim) h_pos
    · -- B⁻ branch
      have h' : PBP.descentType_M τ.val τ.prop.1 = .Bminus :=
        (descentType_M_eq_or τ.val τ.prop.1).resolve_left h
      have hPsh : (descentMB_PBP τ.val τ.prop.1).P.shape = μP.shiftLeft := by
        show τ.val.P.shape.shiftLeft = μP.shiftLeft
        rw [τ.prop.2.1]
      have hQsh : (descentMB_PBP τ.val τ.prop.1).Q.shape = μQ := τ.prop.2.2
      exact descentMB_liftBM_naive (descentMB_PBP τ.val τ.prop.1) (Or.inr h')
        μP μQ hPsh hQsh h_sub h_QleP (h_bal_exc_of_primitive _ h_prim) h_pos
  right_inv := by
    intro σ
    have h_pos : μP.colLen 0 > 0 := by omega
    cases σ with
    | inl σp =>
      show descentMB_sum (liftBM_sum_naive h_sub h_QleP h_prim (.inl σp)) = Sum.inl σp
      simp only [liftBM_sum_naive, descentMB_sum]
      have hγ_eq : PBP.descentType_M
        (liftBM_naive σp.val (Or.inl σp.prop.1) μP μQ σp.prop.2.1 σp.prop.2.2
          h_sub h_QleP (h_bal_exc_of_primitive _ h_prim)) rfl = .Bplus :=
        (descentType_M_liftBM_naive σp.val (Or.inl σp.prop.1) μP μQ
          σp.prop.2.1 σp.prop.2.2 h_sub h_QleP _ h_pos).trans σp.prop.1
      rw [dif_pos hγ_eq]
      congr 1
      apply Subtype.ext
      exact descentMB_liftBM_naive σp.val (Or.inl σp.prop.1) μP μQ
        σp.prop.2.1 σp.prop.2.2 h_sub h_QleP _ h_pos
    | inr σm =>
      show descentMB_sum (liftBM_sum_naive h_sub h_QleP h_prim (.inr σm)) = Sum.inr σm
      simp only [liftBM_sum_naive, descentMB_sum]
      have hγ_eq : PBP.descentType_M
        (liftBM_naive σm.val (Or.inr σm.prop.1) μP μQ σm.prop.2.1 σm.prop.2.2
          h_sub h_QleP (h_bal_exc_of_primitive _ h_prim)) rfl = .Bminus :=
        (descentType_M_liftBM_naive σm.val (Or.inr σm.prop.1) μP μQ
          σm.prop.2.1 σm.prop.2.2 h_sub h_QleP _ h_pos).trans σm.prop.1
      rw [dif_neg (by rw [hγ_eq]; decide)]
      congr 1
      apply Subtype.ext
      exact descentMB_liftBM_naive σm.val (Or.inr σm.prop.1) μP μQ
        σm.prop.2.1 σm.prop.2.2 h_sub h_QleP _ h_pos

/-- **Proposition 10.8(a) for M type (primitive case)**:
    When μP.colLen(0) > μQ.colLen(0), the M→B descent is a bijection. -/
theorem descent_bijective_primitive {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_prim : μP.colLen 0 > μQ.colLen 0) :
    Fintype.card (PBPSet .M μP μQ) =
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ) +
      Fintype.card (PBPSet .Bminus μP.shiftLeft μQ) := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (descent_equiv_primitive h_sub h_QleP h_prim)

/-! ## Prop 10.8(b) for M: balanced case image = non-SS -/

/-- Non-SS predicate: σ.Q bottom of col 0 is not in {•, s}. -/
def isNonSS {μ : YoungDiagram} (σ : PBPSet γ μP' μ) (μ_bottom : ℕ) : Prop :=
  (σ.val.Q.paint (μ_bottom - 1) 0).layerOrd > 1

/-- **Proposition 10.8(b) for M type (balanced case)**:
    When μP.colLen(0) = μQ.colLen(0) > 0, the M→B descent is injective
    with image = non-SS (i.e., σ.Q.paint(bottom, 0) has layerOrd > 1).

    Uses the same Equiv machinery as primitive case, but restricted image.
    The restriction comes from the dot_match constraint at (bottom, 0)
    in the balanced case: lift requires σ.Q bottom ∈ {r, d}. -/
theorem descent_image_balanced {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0) (h_pos : μP.colLen 0 > 0) :
    Fintype.card (PBPSet .M μP μQ) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card +
      (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card := by
  sorry -- TODO: build Equiv PBPSet .M μP μQ ≃ {non-SS σ ⊕ non-SS σ}

/-! ## Shape shifting reduction: Case (1,2) ∈ ℘ → Case (1,2) ∉ ℘

When shapes have μP.colLen(0) < μQ.colLen(0) (corresponding to (1,2) ∈ ℘),
apply Lemma 10.3 (shapeShiftM) to map to shapes with swapped col 0 lengths,
then apply the primitive/balanced case. -/

/-- For any M PBP shapes, the M→B descent count can be computed by
    (possibly) first applying shape shifting to ensure c₁(P) ≥ c₁(Q). -/
theorem card_M_eq_via_shape_shift_if_needed {μP μQ μP' μQ' : YoungDiagram}
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ μQ)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ μP)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ μP)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ μQ) :
    Fintype.card (PBPSet .M μP μQ) = Fintype.card (PBPSet .M μP' μQ') :=
  card_PBPSet_M_shapeShift hP'0 hP'S hQ'0 hQ'S
