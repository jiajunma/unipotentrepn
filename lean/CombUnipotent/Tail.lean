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
      simp [heq]; omega

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

/-- Count of symbol σ in column 0 of a PaintedYoungDiagram,
    computed via Finset (cells in column 0 with paint = σ). -/
noncomputable def countSymCol0 (D : PaintedYoungDiagram) (σ : DRCSymbol) : ℕ :=
  (D.shape.cells.filter (fun c => c.2 = 0 ∧ D.paint c.1 c.2 = σ)).card

/-- Count of symbol σ in columns ≥ 1 of a PaintedYoungDiagram. -/
noncomputable def countSymColGe1 (D : PaintedYoungDiagram) (σ : DRCSymbol) : ℕ :=
  (D.shape.cells.filter (fun c => 1 ≤ c.2 ∧ D.paint c.1 c.2 = σ)).card

/-- Decomposition: countSym = countSymCol0 + countSymColGe1. -/
theorem countSym_split (D : PaintedYoungDiagram) (σ : DRCSymbol) :
    D.countSym σ = countSymCol0 D σ + countSymColGe1 D σ := by
  unfold PaintedYoungDiagram.countSym countSymCol0 countSymColGe1
  set S := D.shape.cells.filter (fun c => D.paint c.1 c.2 = σ)
  -- Split S into col=0 and col≥1 parts
  have hcol0 : D.shape.cells.filter (fun c => c.2 = 0 ∧ D.paint c.1 c.2 = σ) =
    S.filter (fun c => c.2 = 0) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, S]
    tauto
  have hcolge1 : D.shape.cells.filter (fun c => 1 ≤ c.2 ∧ D.paint c.1 c.2 = σ) =
    S.filter (fun c => ¬(c.2 = 0)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, S]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h2⟩
  rw [hcol0, hcolge1]
  exact (Finset.card_filter_add_card_filter_not (p := fun c => c.2 = 0) (s := S)).symm

/-- Bridge: countSymCol0 = countCol0 over the full column. -/
theorem countSymCol0_eq_countCol0 (D : PaintedYoungDiagram) (σ : DRCSymbol) :
    countSymCol0 D σ = countCol0 D.paint σ 0 (D.shape.colLen 0) := by
  -- LHS = card of {(i,0) ∈ D.shape.cells | paint i 0 = σ}
  -- RHS = length of (List.range (colLen 0)).filter(k => paint k 0 = σ)
  -- Bijection: (i, 0) ↦ i. Uses: (i, 0) ∈ shape ↔ i < colLen 0.
  simp only [countSymCol0, countCol0, Nat.zero_add]
  -- Rewrite LHS Finset as image of a filtered Finset.range
  have h_eq : D.shape.cells.filter (fun c => c.2 = 0 ∧ D.paint c.1 c.2 = σ) =
    (Finset.range (D.shape.colLen 0) |>.filter (fun k => D.paint k 0 = σ)).image (fun k => (k, 0)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_image, Finset.mem_range,
      YoungDiagram.mem_iff_lt_colLen]
    constructor
    · rintro ⟨hmem, rfl, hpaint⟩; exact ⟨i, ⟨hmem, hpaint⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hpaint⟩, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨hk, rfl, hpaint⟩
  rw [h_eq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  -- Now: card of Finset.range(n).filter(p) = length of List.range(n).filter(p)
  -- Finset.range is the same as List.range.toFinset, and List.range has no dups
  rfl

/-- For D type, Q has no non-dot symbols. -/
theorem Q_countSym_eq_zero_of_D (τ : PBP) (hγ : τ.γ = .D)
    (σ : DRCSymbol) (hσ : σ ≠ .dot) :
    τ.Q.countSym σ = 0 := by
  simp only [PaintedYoungDiagram.countSym, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨i, j⟩ hmem
  simp only [YoungDiagram.mem_cells] at hmem
  exact fun h => hσ ((τ.Q_all_dot_of_D hγ i j hmem) ▸ h.symm)

/-- Columns ≥ 1 agree when paint agrees on columns ≥ 1. -/
theorem countSymColGe1_eq (D₁ D₂ : PaintedYoungDiagram)
    (hshape : D₁.shape = D₂.shape)
    (hpaint : ∀ i j, 1 ≤ j → D₁.paint i j = D₂.paint i j) (σ : DRCSymbol) :
    countSymColGe1 D₁ σ = countSymColGe1 D₂ σ := by
  simp only [countSymColGe1]; congr 1; rw [hshape]
  ext ⟨i, j⟩; simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨hm, hj, hp⟩; exact ⟨hm, hj, by rwa [← hpaint i j hj]⟩
  · rintro ⟨hm, hj, hp⟩; exact ⟨hm, hj, by rwa [hpaint i j hj]⟩

/-- Columns ≥ 1 count agrees when descent agrees. -/
theorem countSym_cols_ge1_eq (τ₁ τ₂ : PBP)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (σ : DRCSymbol) :
    (τ₁.P.shape.cells.filter (fun c => 1 ≤ c.2 ∧ τ₁.P.paint c.1 c.2 = σ)).card =
    (τ₂.P.shape.cells.filter (fun c => 1 ≤ c.2 ∧ τ₂.P.paint c.1 c.2 = σ)).card := by
  congr 1
  rw [hshapeP]
  ext ⟨i, j⟩
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hm, hj, hp⟩; exact ⟨hm, hj, by rwa [← hdescent_P i j hj]⟩
  · rintro ⟨hm, hj, hp⟩; exact ⟨hm, hj, by rwa [hdescent_P i j hj]⟩

/-- For D type, Q.countSym σ = 0 for non-dot σ (Q is all dots). -/
theorem Q_countSym_zero_of_D (τ : PBP) (hγ : τ.γ = .D) (σ : DRCSymbol) (hσ : σ ≠ .dot) :
    τ.Q.countSym σ = 0 := by
  simp only [PaintedYoungDiagram.countSym, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨i, j⟩ hm
  exact fun h => hσ ((Q_all_dot_of_D τ hγ i j hm) ▸ h.symm)

/-- **Part C2**: the weighted r-sum in the tail is determined. -/
theorem tail_weighted_sums_eq (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (a : ℕ) (ha : a = τ₁.Q.shape.colLen 0) (n : ℕ) (hn : a + n = τ₁.P.shape.colLen 0) :
    2 * countCol0 τ₁.P.paint .r a n + countCol0 τ₁.P.paint .c a n + countCol0 τ₁.P.paint .d a n =
    2 * countCol0 τ₂.P.paint .r a n + countCol0 τ₂.P.paint .c a n + countCol0 τ₂.P.paint .d a n := by
  -- Key: for σ ≠ dot, P.countSym σ = countCol0 σ a n + countSymColGe1 P σ
  -- This is because col0 contribution = countCol0 0 (a+n), and the [0,a) part is 0 (dots).
  suffices h : ∀ σ : DRCSymbol, σ ≠ .dot →
      ∀ (τ : PBP), τ.γ = .D → a = τ.Q.shape.colLen 0 → a + n = τ.P.shape.colLen 0 →
      τ.P.countSym σ = countCol0 τ.P.paint σ a n + countSymColGe1 τ.P σ by
    -- Signature for D: p = (P.countSym .dot + Q.card) + 2*P.countSym .r + P.countSym .c + P.countSym .d
    -- The dot and Q parts are determined by shapes. The colGe1 parts agree.
    -- So: 2*countCol0 .r + countCol0 .c + countCol0 .d must agree.
    have hr₁ := h .r (by decide) τ₁ hγ₁ ha hn
    have hc₁ := h .c (by decide) τ₁ hγ₁ ha hn
    have hd₁ := h .d (by decide) τ₁ hγ₁ ha hn
    have ha₂ : a = τ₂.Q.shape.colLen 0 := by rw [ha, hshapeQ]
    have hn₂ : a + n = τ₂.P.shape.colLen 0 := by rw [hn, hshapeP]
    have hr₂ := h .r (by decide) τ₂ hγ₂ ha₂ hn₂
    have hc₂ := h .c (by decide) τ₂ hγ₂ ha₂ hn₂
    have hd₂ := h .d (by decide) τ₂ hγ₂ ha₂ hn₂
    have hge1_r := countSymColGe1_eq τ₁.P τ₂.P hshapeP hdescent_P .r
    have hge1_c := countSymColGe1_eq τ₁.P τ₂.P hshapeP hdescent_P .c
    have hge1_d := countSymColGe1_eq τ₁.P τ₂.P hshapeP hdescent_P .d
    -- Extract signature.1 equation for D type
    have hsig1 := congr_arg Prod.fst hsig
    -- Unfold signature for D type
    simp only [PBP.signature, hγ₁, hγ₂] at hsig1
    -- hsig1 : nDot₁ + 2*nR₁ + nC₁ + nD₁ = nDot₂ + 2*nR₂ + nC₂ + nD₂
    -- where nR = P.countSym .r + Q.countSym .r, etc.
    -- For D type: Q.countSym .r/c/d = 0 (Q is all dots)
    rw [Q_countSym_zero_of_D τ₁ hγ₁ .r (by decide),
        Q_countSym_zero_of_D τ₁ hγ₁ .c (by decide),
        Q_countSym_zero_of_D τ₁ hγ₁ .d (by decide),
        Q_countSym_zero_of_D τ₂ hγ₂ .r (by decide),
        Q_countSym_zero_of_D τ₂ hγ₂ .c (by decide),
        Q_countSym_zero_of_D τ₂ hγ₂ .d (by decide)] at hsig1
    -- Now hsig1 involves P.countSym and Q.countSym .dot only
    -- Rewrite P.countSym .r/.c/.d using decomposition
    rw [hr₁, hr₂, hc₁, hc₂, hd₁, hd₂] at hsig1
    -- Cancel equal colGe1 parts
    rw [hge1_r, hge1_c, hge1_d] at hsig1
    -- Q.countSym .dot: for D type, Q is all dots, so countSym .dot = Q.card
    -- Q.card is determined by shape
    have hQ_dot : τ₁.Q.countSym .dot = τ₂.Q.countSym .dot := by
      simp only [PaintedYoungDiagram.countSym]
      congr 1; rw [hshapeQ]
      ext ⟨i, j⟩; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hm, hp⟩; exact ⟨hm, Q_all_dot_of_D τ₂ hγ₂ i j hm⟩
      · rintro ⟨hm, hp⟩; exact ⟨hm, Q_all_dot_of_D τ₁ hγ₁ i j (hshapeQ ▸ hm)⟩
    rw [hQ_dot] at hsig1
    -- P.countSym .dot decomposes: countSym_split + countSymColGe1 agrees
    rw [countSym_split τ₁.P .dot, countSym_split τ₂.P .dot] at hsig1
    have hP_dot_ge1 := countSymColGe1_eq τ₁.P τ₂.P hshapeP hdescent_P .dot
    -- countSymCol0 .dot agrees (by shapes + dot_match)
    have hcol0_dot : countSymCol0 τ₁.P .dot = countSymCol0 τ₂.P .dot := by
      -- Use bridge: countSymCol0 = countCol0, then both equal a (=Q.colLen 0)
      rw [countSymCol0_eq_countCol0, countSymCol0_eq_countCol0]
      rw [show τ₂.P.shape.colLen 0 = τ₁.P.shape.colLen 0 from by rw [hshapeP]]
      -- Both count dots in P's column 0 over [0, P.colLen(0))
      -- In the dot region [0, a), paint = dot for both. In the tail [a, P.colLen), paint ≠ dot.
      -- So both counts = a.
      have hle := Q_colLen0_le_P_colLen0_D τ₁ hγ₁
      -- Split at a
      conv_lhs => rw [countCol0_split _ _ 0 a _ (by omega)]
      conv_rhs => rw [countCol0_split _ _ 0 a _ (by omega)]
      simp only [Nat.zero_add, show τ₁.P.shape.colLen 0 - a = n from by omega]
      -- Tail part: 0 dots
      rw [countCol0_eq_zero_of_ne _ _ a n (fun k hk => col0_nonDot_tail_D τ₁ hγ₁ (by omega) (by omega))]
      rw [countCol0_eq_zero_of_ne _ _ a n (fun k hk => col0_nonDot_tail_D τ₂ hγ₂
            (by rw [← hshapeQ]; omega) (by rw [← hshapeP]; omega))]
      -- Dot region: both paint dot, so same count
      congr 1
      exact countCol0_congr _ _ .dot 0 a (fun k hk => by
        rw [col0_dot_below_Q_D τ₁ hγ₁ (by omega)]
        rw [col0_dot_below_Q_D τ₂ hγ₂ (by rw [← hshapeQ]; omega)])
    rw [hcol0_dot, hP_dot_ge1] at hsig1
    omega
  -- Proof of the decomposition: countSym = tail + colGe1
  intro σ hσ τ hγ ha' hn'
  rw [countSym_split τ.P σ, countSymCol0_eq_countCol0]
  rw [countCol0_split _ _ 0 a (τ.P.shape.colLen 0) (by subst ha'; exact Q_colLen0_le_P_colLen0_D τ hγ)]
  simp only [Nat.zero_add, show τ.P.shape.colLen 0 - a = n from by omega]
  -- countCol0 σ 0 a = 0 (dot region: cells [0, a) are all dots, so no σ ≠ dot)
  rw [countCol0_eq_zero_of_ne _ _ 0 a (by
    intro k hk hpaint
    have := col0_dot_below_Q_D τ hγ (by subst ha'; omega)
    simp only [Nat.zero_add] at hpaint
    rw [this] at hpaint; exact hσ hpaint.symm)]
  omega

/-- Bridge: hasDInCol0(P) iff countCol0(.d, 0, colLen) > 0.
    Both count the same thing (cells in column 0 with paint = d)
    but use different data structures (Finset vs List). -/
theorem hasDInCol0_iff_countCol0_pos (D : PaintedYoungDiagram) :
    D.hasDInCol0 = true ↔ 0 < countCol0 D.paint .d 0 (D.shape.colLen 0) := by
  unfold PaintedYoungDiagram.hasDInCol0 countCol0
  simp only [Nat.zero_add]
  rw [decide_eq_true_eq]
  constructor
  · -- Forward: Finset.Nonempty → List.length > 0
    rintro ⟨⟨i, j⟩, hmem⟩
    rw [Finset.mem_filter] at hmem
    rw [YoungDiagram.mem_cells] at hmem
    obtain ⟨hmem_shape, hj, hpaint⟩ := hmem
    subst hj
    apply List.length_pos_of_mem
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨YoungDiagram.mem_iff_lt_colLen.mp hmem_shape, hpaint⟩
  · -- Backward: List.length > 0 → Finset.Nonempty
    intro hpos
    obtain ⟨k, hk⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    exact ⟨⟨k, 0⟩, by
      rw [Finset.mem_filter, YoungDiagram.mem_cells]
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hk.1, rfl, hk.2⟩⟩

/-- D type epsilon determines n_d in tail.
    Proof: epsilon = 0 iff d in P's column 0 (for D, Q has no d).
    By dot region having no d, d is only in the tail.
    Column uniqueness: n_d ∈ {0,1}. So epsilon determines n_d. -/
theorem tail_nd_eq (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂)
    (a : ℕ) (ha : a = τ₁.Q.shape.colLen 0) (n : ℕ) (hn : a + n = τ₁.P.shape.colLen 0) :
    countCol0 τ₁.P.paint .d a n = countCol0 τ₂.P.paint .d a n := by
  -- Both n_d ∈ {0, 1} (column uniqueness)
  have hle₁ := countCol0_le_one_of_unique τ₁.P.paint .d a n (τ₁.col_d_P 0)
  have hle₂ := countCol0_le_one_of_unique τ₂.P.paint .d a n (τ₂.col_d_P 0)
  -- epsilon determines whether n_d = 0 or 1
  -- For D type: epsilon = 0 iff hasDInCol0(P) (Q is all dots, no d in Q)
  -- hasDInCol0(P) iff countCol0(.d, 0, P.colLen(0)) > 0
  -- countCol0(.d, 0, P.colLen(0)) = countCol0(.d, 0, a) + countCol0(.d, a, n)
  -- countCol0(.d, 0, a) = 0 (dot region has no d)
  -- So: hasDInCol0(P) iff countCol0(.d, a, n) > 0 iff n_d = 1
  -- For D type, Q is all dots, so Q.hasDInCol0 = false
  have hQ_no_d₁ : τ₁.Q.hasDInCol0 = false := by
    simp only [PaintedYoungDiagram.hasDInCol0, Bool.not_eq_true, decide_eq_false_iff_not,
      Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
    intro ⟨i, j⟩ hmem
    rw [YoungDiagram.mem_cells] at hmem
    simp [τ₁.Q_all_dot_of_D hγ₁ i j hmem]
  have hQ_no_d₂ : τ₂.Q.hasDInCol0 = false := by
    simp only [PaintedYoungDiagram.hasDInCol0, Bool.not_eq_true, decide_eq_false_iff_not,
      Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
    intro ⟨i, j⟩ hmem
    rw [YoungDiagram.mem_cells] at hmem
    simp [τ₂.Q_all_dot_of_D hγ₂ i j hmem]
  -- epsilon τ = 0 iff P.hasDInCol0 (since Q.hasDInCol0 = false)
  have heps_iff₁ : (PBP.epsilon τ₁ = 0) ↔ τ₁.P.hasDInCol0 = true := by
    simp [PBP.epsilon, hQ_no_d₁]
  have heps_iff₂ : (PBP.epsilon τ₂ = 0) ↔ τ₂.P.hasDInCol0 = true := by
    simp [PBP.epsilon, hQ_no_d₂]
  -- hasDInCol0(P) ↔ countCol0(.d, 0, P.colLen(0)) > 0
  have hbridge₁ := hasDInCol0_iff_countCol0_pos τ₁.P
  have hbridge₂ := hasDInCol0_iff_countCol0_pos τ₂.P
  -- countCol0(.d, 0, P.colLen(0)) = countCol0(.d, 0, a) + countCol0(.d, a, n)
  have hsplit₁ := countCol0_split τ₁.P.paint .d 0 a (τ₁.P.shape.colLen 0) (by omega)
  have hsplit₂ := countCol0_split τ₂.P.paint .d 0 a (τ₂.P.shape.colLen 0)
    (by rw [← hshapeP]; omega)
  -- Dot region [0, a) has no d (paint = dot there)
  have hdot₁ : countCol0 τ₁.P.paint .d 0 a = 0 :=
    countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
      simp only [Nat.zero_add]
      have : k < τ₁.Q.shape.colLen 0 := ha ▸ hk
      rw [col0_dot_below_Q_D τ₁ hγ₁ this]
      exact DRCSymbol.noConfusion
  have hdot₂ : countCol0 τ₂.P.paint .d 0 a = 0 :=
    countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
      simp only [Nat.zero_add]
      have : k < τ₂.Q.shape.colLen 0 := by rw [← hshapeQ]; exact ha ▸ hk
      rw [col0_dot_below_Q_D τ₂ hγ₂ this]
      exact DRCSymbol.noConfusion
  -- So: countCol0(.d, 0, colLen) = countCol0(.d, a, n)
  have hn_sub₁ : τ₁.P.shape.colLen 0 - a = n := by omega
  have hn_sub₂ : τ₂.P.shape.colLen 0 - a = n := by rw [← hshapeP]; omega
  simp only [hdot₁, Nat.zero_add, hn_sub₁] at hsplit₁
  simp only [hdot₂, Nat.zero_add, hn_sub₂] at hsplit₂
  -- Now: hasDInCol0(P₁) ↔ countCol0(.d, a, n) for τ₁ > 0, similarly for τ₂
  rw [hsplit₁] at hbridge₁
  rw [hsplit₂] at hbridge₂
  -- epsilon equal means hasDInCol0 agree
  -- epsilon = if P.hasDInCol0 || Q.hasDInCol0 then 0 else 1
  -- For D type, Q.hasDInCol0 = false, so epsilon = if P.hasDInCol0 then 0 else 1
  have hd_agree : τ₁.P.hasDInCol0 = τ₂.P.hasDInCol0 := by
    simp only [PBP.epsilon, hQ_no_d₁, hQ_no_d₂, Bool.or_false] at heps
    -- heps : (if τ₁.P.hasDInCol0 then 0 else 1) = (if τ₂.P.hasDInCol0 then 0 else 1) : Fin 2
    revert heps
    cases τ₁.P.hasDInCol0 <;> cases τ₂.P.hasDInCol0 <;> simp
  -- Both n_d ∈ {0, 1} and agree on positivity
  -- Positivity equivalence: countCol0 > 0 ↔ hasDInCol0 = true
  have hpos₁ : 0 < countCol0 τ₁.P.paint .d a n ↔ τ₁.P.hasDInCol0 = true := hbridge₁.symm
  have hpos₂ : 0 < countCol0 τ₂.P.paint .d a n ↔ τ₂.P.hasDInCol0 = true := hbridge₂.symm
  rw [hd_agree] at hpos₁
  -- Both counts ∈ {0, 1} and are positive iff the same condition holds
  -- Since both ∈ {0,1} and positive iff same condition, they're equal
  rcases Nat.eq_zero_or_pos (countCol0 τ₁.P.paint .d a n) with h1 | h1
  · -- n_d₁ = 0, show n_d₂ = 0
    have : ¬(0 < countCol0 τ₂.P.paint .d a n) := by
      intro h2
      have := hpos₁.mpr (hpos₂.mp h2)
      omega
    omega
  · -- n_d₁ > 0, so n_d₂ > 0, and both ≤ 1
    have h2 : 0 < countCol0 τ₂.P.paint .d a n := hpos₂.mpr (hpos₁.mp h1)
    omega

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
  have hnd_d := tail_nd_eq τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ heps a ha n hn
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
