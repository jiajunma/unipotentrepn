/-
# Tail of a Painted Bipartition and Proposition 10.9

Reference: [BMSZb] Section 10.5; [BMSZ] Section 11.2.
-/
import CombUnipotent.Signature
import CombUnipotent.Descent

namespace PBP

/-! ## D type: column 0 structure -/

theorem col0_dot_below_Q_D (τ : PBP) (hγ : τ.γ = .D)
    {i : ℕ} (hi : i < τ.Q.shape.colLen 0) :
    τ.P.paint i 0 = .dot := by
  have hmem_Q : (i, 0) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr hi
  exact ((τ.dot_match i 0).mpr ⟨hmem_Q, τ.Q_all_dot_of_D hγ i 0 hmem_Q⟩).2

theorem col0_nonDot_tail_D (τ : PBP) (hγ : τ.γ = .D)
    {i : ℕ} (hi_ge : τ.Q.shape.colLen 0 ≤ i) (hi_lt : i < τ.P.shape.colLen 0) :
    τ.P.paint i 0 ≠ .dot := by
  intro heq
  have : (i, 0) ∉ τ.Q.shape := by rw [YoungDiagram.mem_iff_lt_colLen]; omega
  exact this ((τ.dot_match i 0).mp
    ⟨YoungDiagram.mem_iff_lt_colLen.mpr hi_lt, heq⟩).1

theorem col0_dot_above_P (τ : PBP)
    {i : ℕ} (hi : τ.P.shape.colLen 0 ≤ i) :
    τ.P.paint i 0 = .dot :=
  τ.P.paint_outside i 0 (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

theorem col0_layerOrd_mono (τ : PBP) {i₁ i₂ : ℕ}
    (h : i₁ ≤ i₂) (hmem : (i₂, 0) ∈ τ.P.shape) :
    (τ.P.paint i₁ 0).layerOrd ≤ (τ.P.paint i₂ 0).layerOrd :=
  τ.mono_P i₁ 0 i₂ 0 h le_rfl hmem

theorem Q_colLen0_le_P_colLen0_D (τ : PBP) (hγ : τ.γ = .D) :
    τ.Q.shape.colLen 0 ≤ τ.P.shape.colLen 0 := by
  by_contra h; push_neg at h
  have : (τ.P.shape.colLen 0, 0) ∈ τ.Q.shape :=
    YoungDiagram.mem_iff_lt_colLen.mpr h
  have := Q_le_P_of_D τ hγ this
  rw [YoungDiagram.mem_iff_lt_colLen] at this; omega

/-! ## Part D: Monotone sequence unique

If two non-decreasing (layerOrd) paint functions on a range agree on
counts of each symbol, they agree pointwise.

Proof: pick the first disagreement i₀. One has strictly smaller layerOrd
at i₀. By monotonicity, that symbol can't appear at ≥ i₀ in the other.
Since they agree before i₀, total counts differ. Contradiction. -/

/-- Count of symbol σ in paint's column 0 at rows in [a, a+n). -/
def countCol0 (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ) : ℕ :=
  ((List.range n).filter fun k => paint (a + k) 0 = σ).length

theorem countCol0_zero (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a : ℕ) :
    countCol0 paint σ a 0 = 0 := by
  simp [countCol0]

/-- Splitting: count over n = count over m + count over (n - m) shifted. -/
-- The following four are pure List.range/filter/length lemmas.
-- Mathematically trivial; proof requires Lean 4 List API details.

@[simp] theorem countCol0_split (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol)
    (a m n : ℕ) (hmn : m ≤ n) :
    countCol0 paint σ a n = countCol0 paint σ a m + countCol0 paint σ (a + m) (n - m) := by
  simp only [countCol0]
  have hn : n = m + (n - m) := by omega
  conv_lhs => rw [hn, List.range_add, List.filter_append, List.length_append]
  congr 1
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro k _
  simp only [Function.comp, Nat.add_assoc]

theorem countCol0_congr (f g : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (h : ∀ k, k < n → f (a + k) 0 = g (a + k) 0) :
    countCol0 f σ a n = countCol0 g σ a n := by
  simp only [countCol0]
  congr 1
  apply List.filter_congr
  intro k hk
  rw [List.mem_range] at hk
  rw [h k hk]

theorem countCol0_eq_zero_of_ne (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (h : ∀ k, k < n → paint (a + k) 0 ≠ σ) :
    countCol0 paint σ a n = 0 := by
  simp only [countCol0, List.length_eq_zero_iff]
  rw [List.filter_eq_nil_iff]
  intro k hk
  rw [List.mem_range] at hk
  simp [h k hk]

theorem countCol0_pos (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (hn : 0 < n) (h : paint a 0 = σ) :
    1 ≤ countCol0 paint σ a n := by
  unfold countCol0
  apply List.length_pos_of_mem
  rw [List.mem_filter, List.mem_range]
  exact ⟨hn, by simp [h]⟩

/-- layerOrd injective: same layerOrd ⟹ same symbol. -/
theorem DRCSymbol.eq_of_layerOrd_eq {σ₁ σ₂ : DRCSymbol}
    (h : σ₁.layerOrd = σ₂.layerOrd) : σ₁ = σ₂ := by
  cases σ₁ <;> cases σ₂ <;> simp [DRCSymbol.layerOrd] at h ⊢

/-- Main Part D theorem. -/
theorem monotone_col_unique
    (f g : ℕ → ℕ → DRCSymbol) (a n colLen : ℕ)
    (hcol : a + n ≤ colLen)
    (hf_mono : ∀ i₁ i₂, i₁ ≤ i₂ → i₂ < colLen → (f i₁ 0).layerOrd ≤ (f i₂ 0).layerOrd)
    (hg_mono : ∀ i₁ i₂, i₁ ≤ i₂ → i₂ < colLen → (g i₁ 0).layerOrd ≤ (g i₂ 0).layerOrd)
    (h_counts : ∀ σ, countCol0 f σ a n = countCol0 g σ a n) :
    ∀ k, k < n → f (a + k) 0 = g (a + k) 0 := by
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨k₀, hk₀_lt, hk₀_ne⟩ := h_neg
  -- Pick the minimal k₀
  have ⟨k₀, ⟨hk₀_lt, hk₀_ne⟩, hk₀_min⟩ :=
    Nat.lt_wfRel.wf.has_min {k | k < n ∧ f (a + k) 0 ≠ g (a + k) 0} ⟨k₀, hk₀_lt, hk₀_ne⟩
  -- All k < k₀ agree
  have h_agree : ∀ k, k < k₀ → f (a + k) 0 = g (a + k) 0 := by
    intro k hk; by_contra h; exact hk₀_min k ⟨by omega, h⟩ hk
  -- layerOrd are different (since layerOrd is injective)
  have h_lo_ne : (f (a + k₀) 0).layerOrd ≠ (g (a + k₀) 0).layerOrd := by
    intro h; exact hk₀_ne (DRCSymbol.eq_of_layerOrd_eq h)
  rcases Nat.lt_or_gt_of_ne h_lo_ne with h_lt | h_gt
  · -- f has smaller layerOrd at k₀
    set σ := f (a + k₀) 0
    -- g has no σ at positions ≥ k₀ (layerOrd too high by monotonicity)
    have hg_no_σ : ∀ j, k₀ ≤ j → j < n → g (a + j) 0 ≠ σ := by
      intro j hj hjn heq
      have := hg_mono (a + k₀) (a + j) (by omega) (by omega)
      rw [heq] at this; omega
    -- Split counts at k₀
    have hf_split := countCol0_split f σ a k₀ n (by omega)
    have hg_split := countCol0_split g σ a k₀ n (by omega)
    -- Counts on [a, a+k₀) agree (paint agrees there)
    have h_pre := countCol0_congr f g σ a k₀ h_agree
    -- g count on [a+k₀, a+n) is 0
    have hg_tail := countCol0_eq_zero_of_ne g σ (a + k₀) (n - k₀) (by
      intro j hj heq; exact hg_no_σ (k₀ + j) (by omega) (by omega) (by rwa [show a + (k₀ + j) = a + k₀ + j from by omega]))
    -- f count on [a+k₀, a+n) ≥ 1 (f(a+k₀) = σ)
    have hf_tail : countCol0 f σ (a + k₀) (n - k₀) ≥ 1 :=
      countCol0_pos f σ (a + k₀) (n - k₀) (by omega) rfl
    -- Total counts differ
    have := h_counts σ; omega
  · -- symmetric: g has smaller layerOrd
    set σ := g (a + k₀) 0
    have hf_no_σ : ∀ j, k₀ ≤ j → j < n → f (a + j) 0 ≠ σ := by
      intro j hj hjn heq
      have := hf_mono (a + k₀) (a + j) (by omega) (by omega)
      rw [heq] at this; omega
    have hf_split := countCol0_split f σ a k₀ n (by omega)
    have hg_split := countCol0_split g σ a k₀ n (by omega)
    have h_pre := countCol0_congr f g σ a k₀ h_agree
    have hf_tail := countCol0_eq_zero_of_ne f σ (a + k₀) (n - k₀) (by
      intro j hj heq; exact hf_no_σ (k₀ + j) (by omega) (by omega) (by rwa [show a + (k₀ + j) = a + k₀ + j from by omega]))
    have hg_tail : countCol0 g σ (a + k₀) (n - k₀) ≥ 1 :=
      countCol0_pos g σ (a + k₀) (n - k₀) (by omega) rfl
    have := h_counts σ; omega

/-! ## Parts A + B -/

theorem prop_10_9_partA (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    {i : ℕ} (hi : i < τ₁.Q.shape.colLen 0) :
    τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  rw [col0_dot_below_Q_D τ₁ hγ₁ hi, col0_dot_below_Q_D τ₂ hγ₂ (hshapeQ ▸ hi)]

theorem prop_10_9_partB (τ₁ τ₂ : PBP)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    {i : ℕ} (hi : τ₁.P.shape.colLen 0 ≤ i) :
    τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  rw [col0_dot_above_P τ₁ hi, col0_dot_above_P τ₂ (hshapeP ▸ hi)]

/-! ## Auxiliary: total count and column uniqueness -/

/-- The total count over all 5 symbols in [a, a+n) equals n.
    Every position k < n has exactly one symbol. -/
theorem countCol0_total (paint : ℕ → ℕ → DRCSymbol) (a n : ℕ) :
    countCol0 paint .dot a n + countCol0 paint .s a n +
    countCol0 paint .r a n + countCol0 paint .c a n +
    countCol0 paint .d a n = n := by
  induction n with
  | zero => simp [countCol0]
  | succ n ih =>
    simp only [countCol0, List.range_succ, List.filter_append, List.filter_cons,
      List.length_append, List.length_cons, List.length_nil]
    -- The last element (n) contributes 1 to exactly one symbol's count
    have ih' := ih
    simp only [countCol0] at ih'
    cases paint (a + n) 0 <;> simp_all <;> omega

/-- If at most one row has symbol σ in column 0 (column uniqueness),
    then countCol0 ≤ 1 in any sub-range. -/
theorem countCol0_le_one_of_unique (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (h : ∀ i₁ i₂, paint i₁ 0 = σ → paint i₂ 0 = σ → i₁ = i₂) :
    countCol0 paint σ a n ≤ 1 := by
  -- Prove by induction: once we find one matching element, no more can exist.
  induction n with
  | zero => simp [countCol0]
  | succ n ih =>
    simp only [countCol0, List.range_succ, List.filter_append, List.length_append]
    simp only [List.filter_cons, List.length_nil]
    simp only [countCol0] at ih
    by_cases heq : paint (a + n) 0 = σ
    · -- paint(a+n) = σ. By h, no other position can have σ.
      -- So the count in [0, n) is 0, and count in [0, n+1) = 1.
      have h_zero : countCol0 paint σ a n = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk hpk =>
          absurd (h (a + k) (a + n) hpk heq) (by omega)
      simp only [countCol0] at h_zero ⊢
      rw [h_zero]; simp [List.filter_cons, heq]
    · -- paint(a+n) ≠ σ. Count in [0, n+1) = count in [0, n) ≤ 1.
      sorry -- countCol0 n+1 = countCol0 n when last element doesn't match

/-! ## Part C: Tail counts determined

Split into:
- Part C1 (arithmetic): the system of equations from signature + column
  uniqueness determines all tail counts uniquely.
- Part C2 (decomposition): the signature difference reduces to weighted
  sums on the tail (Finset decomposition). -/

/-- **Part C1 (arithmetic core)**: if two tuples (n_s, n_r, n_c, n_d) in ℕ satisfy:
    - same total: n_s₁ + n_r₁ + n_c₁ + n_d₁ = n_s₂ + n_r₂ + n_c₂ + n_d₂
    - same weighted r-sum: 2·n_r₁ + n_c₁ + n_d₁ = 2·n_r₂ + n_c₂ + n_d₂
    - same n_d: n_d₁ = n_d₂
    - n_c bounded: n_c₁ ≤ 1 and n_c₂ ≤ 1
    then all components are equal. -/
theorem tail_counts_arith
    {ns₁ nr₁ nc₁ nd₁ ns₂ nr₂ nc₂ nd₂ : ℕ}
    (htot : ns₁ + nr₁ + nc₁ + nd₁ = ns₂ + nr₂ + nc₂ + nd₂)
    (hwr : 2 * nr₁ + nc₁ + nd₁ = 2 * nr₂ + nc₂ + nd₂)
    (hnd : nd₁ = nd₂)
    (hc1 : nc₁ ≤ 1) (hc2 : nc₂ ≤ 1) :
    ns₁ = ns₂ ∧ nr₁ = nr₂ ∧ nc₁ = nc₂ := by
  -- From hwr and hnd: 2·nr₁ + nc₁ = 2·nr₂ + nc₂
  have hwr' : 2 * nr₁ + nc₁ = 2 * nr₂ + nc₂ := by omega
  -- If nr₁ > nr₂, then nc₂ - nc₁ = 2(nr₁ - nr₂) ≥ 2, but nc₂ ≤ 1. Contradiction.
  -- If nr₂ > nr₁, symmetric. So nr₁ = nr₂, hence nc₁ = nc₂.
  have hnr : nr₁ = nr₂ := by
    by_contra h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · -- nr₁ < nr₂: then 2nr₂ > 2nr₁, so nc₁ > nc₂ + 2(nr₂-nr₁-1) + 2 > nc₂ + 1
      -- but nc₁ ≤ 1. So nc₂ + 2 ≤ 2nr₂ - 2nr₁ + nc₂ = nc₁ ≤ 1
      omega
    · omega
  have hnc : nc₁ = nc₂ := by omega
  have hns : ns₁ = ns₂ := by omega
  exact ⟨hns, hnr, hnc⟩

/-- **Part C2 (Finset decomposition)**: the signature difference for D type
    reduces to weighted sums on the tail counts.
    This requires decomposing PaintedYoungDiagram.countSym into
    column 0 (dot part + tail) + columns ≥ 1.

    The conclusion: the "weighted r-sum" 2·n_r_tail + n_c_tail + n_d_tail
    is determined by (signature, shapes, columns ≥ 1). -/
theorem tail_weighted_sums_eq (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (a : ℕ) (ha : a = τ₁.Q.shape.colLen 0) (n : ℕ) (hn : a + n = τ₁.P.shape.colLen 0) :
    -- Weighted r-sum
    2 * countCol0 τ₁.P.paint .r a n + countCol0 τ₁.P.paint .c a n + countCol0 τ₁.P.paint .d a n =
    2 * countCol0 τ₂.P.paint .r a n + countCol0 τ₂.P.paint .c a n + countCol0 τ₂.P.paint .d a n := by
  sorry -- Finset decomposition of signature

/-- D type epsilon determines n_d in tail. -/
theorem tail_nd_eq (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂)
    (a : ℕ) (ha : a = τ₁.Q.shape.colLen 0) (n : ℕ) (hn : a + n = τ₁.P.shape.colLen 0) :
    countCol0 τ₁.P.paint .d a n = countCol0 τ₂.P.paint .d a n := by
  sorry -- From epsilon + column uniqueness (n_d ∈ {0,1}) + monotonicity

theorem prop_10_9_partC (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂)
    (a : ℕ) (ha : a = τ₁.Q.shape.colLen 0)
    (n : ℕ) (hn : a + n = τ₁.P.shape.colLen 0) :
    ∀ σ, countCol0 τ₁.P.paint σ a n = countCol0 τ₂.P.paint σ a n := by
  -- n_dot in tail = 0 for both (by col0_nonDot_tail_D)
  have hnd_dot : countCol0 τ₁.P.paint .dot a n = countCol0 τ₂.P.paint .dot a n := by
    rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk => col0_nonDot_tail_D τ₁ hγ₁ (by omega) (by omega)),
        countCol0_eq_zero_of_ne _ _ _ _ (fun k hk => col0_nonDot_tail_D τ₂ hγ₂
          (by rw [← hshapeQ]; omega) (by rw [← hshapeP]; omega))]
  -- n_d in tail: determined by epsilon
  have hnd_d := tail_nd_eq τ₁ τ₂ hγ₁ hγ₂ hshapeP heps a ha n hn
  -- Weighted r-sum: from signature decomposition
  have hwr := tail_weighted_sums_eq τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdescent_P hsig a ha n hn
  -- Total tail cells: non-dot counts sum to n (since dot count = 0 in tail)
  have htot : countCol0 τ₁.P.paint .s a n + countCol0 τ₁.P.paint .r a n +
              countCol0 τ₁.P.paint .c a n + countCol0 τ₁.P.paint .d a n =
              countCol0 τ₂.P.paint .s a n + countCol0 τ₂.P.paint .r a n +
              countCol0 τ₂.P.paint .c a n + countCol0 τ₂.P.paint .d a n := by
    -- Both sides = n (total) - dot_count (= 0 in tail)
    have h1 := countCol0_total τ₁.P.paint a n
    have h2 := countCol0_total τ₂.P.paint a n
    rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
      col0_nonDot_tail_D τ₁ hγ₁ (by omega) (by omega))] at h1
    rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
      col0_nonDot_tail_D τ₂ hγ₂ (by rw [← hshapeQ]; omega) (by rw [← hshapeP]; omega))] at h2
    omega
  -- Column uniqueness: n_c ≤ 1 in column 0 of P
  have hc1 : countCol0 τ₁.P.paint .c a n ≤ 1 :=
    countCol0_le_one_of_unique _ _ _ _ (τ₁.col_c_P 0)
  have hc2 : countCol0 τ₂.P.paint .c a n ≤ 1 :=
    countCol0_le_one_of_unique _ _ _ _ (τ₂.col_c_P 0)
  -- Apply arithmetic core
  have ⟨hns, hnr, hnc⟩ := tail_counts_arith htot hwr hnd_d hc1 hc2
  -- Now handle each symbol
  intro σ
  cases σ with
  | dot => exact hnd_dot
  | s => exact hns
  | r => exact hnr
  | c => exact hnc
  | d => exact hnd_d

/-! ## Proposition 10.9 assembly -/

theorem prop_10_9_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (hdescent_Q : ∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    ∀ i, τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  intro i
  set a := τ₁.Q.shape.colLen 0
  set b := τ₁.P.shape.colLen 0
  have hQ_le := Q_colLen0_le_P_colLen0_D τ₁ hγ₁
  by_cases h1 : i < a
  · exact prop_10_9_partA τ₁ τ₂ hγ₁ hγ₂ hshapeQ h1
  · by_cases h2 : i < b
    · push_neg at h1
      have hcounts := prop_10_9_partC τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdescent_P
        hsig heps a rfl (b - a) (by omega)
      have hk : i - a < b - a := by omega
      have heq := monotone_col_unique τ₁.P.paint τ₂.P.paint a (b - a) b
        (by omega)
        (fun i₁ i₂ h hlt => col0_layerOrd_mono τ₁ h
          (YoungDiagram.mem_iff_lt_colLen.mpr hlt))
        (fun i₁ i₂ h hlt => col0_layerOrd_mono τ₂ h
          (YoungDiagram.mem_iff_lt_colLen.mpr (hshapeP ▸ hlt)))
        hcounts (i - a) hk
      simp only [Nat.add_sub_cancel' h1] at heq
      exact heq
    · push_neg at h2
      exact prop_10_9_partB τ₁ τ₂ hshapeP h2

end PBP
