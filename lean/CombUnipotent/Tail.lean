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
theorem countCol0_split (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol)
    (a m n : ℕ) (hmn : m ≤ n) :
    countCol0 paint σ a n = countCol0 paint σ a m + countCol0 paint σ (a + m) (n - m) := by
  sorry

/-- If paint agrees on [a, a+n), counts agree. -/
theorem countCol0_congr (f g : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (h : ∀ k, k < n → f (a + k) 0 = g (a + k) 0) :
    countCol0 f σ a n = countCol0 g σ a n := by
  sorry

/-- If paint never equals σ on [a, a+n), count is 0. -/
theorem countCol0_eq_zero_of_ne (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol) (a n : ℕ)
    (h : ∀ k, k < n → paint (a + k) 0 ≠ σ) :
    countCol0 paint σ a n = 0 := by
  sorry

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
    have hf_tail : countCol0 f σ (a + k₀) (n - k₀) ≥ 1 := by
      sorry -- countCol0 contains the element at k=0 where f(a+k₀) = σ
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
    have hg_tail : countCol0 g σ (a + k₀) (n - k₀) ≥ 1 := by
      sorry -- symmetric to above
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

/-! ## Part C: Tail counts determined -/

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
  sorry

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
