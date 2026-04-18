/-
# Tail of a Painted Bipartition and Proposition 10.9

Reference: [BMSZb] Section 10.5; [BMSZ] Section 11.2.
-/
import CombUnipotent.Signature
import CombUnipotent.Descent

namespace PBP

/-! ## Tail of a PBP (B/D types)

For ★ ∈ {B, D}, the **tail** τ_t of a PBP τ = (P, Q) consists of cells
in the first column of one diagram that extend beyond the other:

- **D type**: Q ⊆ P (since Q is all dots). Tail = cells in P's col 0
  beyond Q's col 0, i.e., rows [Q.colLen(0), P.colLen(0)).
  These cells carry non-dot symbols from {s, r, c, d}.
  Tail symbol x_τ = P.paint(P.colLen(0) - 1, 0).

- **B type**: For B⁺/B⁻, P has {dot, c} and Q has {dot, s, r, d}.
  Tail = cells in Q's col 0 beyond P's col 0,
  i.e., rows [P.colLen(0), Q.colLen(0)).
  Tail symbol x_τ = Q.paint(Q.colLen(0) - 1, 0).

The tail symbol x_τ ∈ {c, d, r, s} (never dot).
ε_τ = 0 iff x_τ = d (for both B and D types). -/

/-- Tail length for D type: how many cells in P's col 0 extend beyond Q. -/
def tailLen_D (τ : PBP) : ℕ := τ.P.shape.colLen 0 - τ.Q.shape.colLen 0

/-- Tail symbol for D type: paint of the bottom cell of P's col 0. -/
def tailSymbol_D (τ : PBP) : DRCSymbol := τ.P.paint (τ.P.shape.colLen 0 - 1) 0

/-- Tail length for B type: how many cells in Q's col 0 extend beyond P. -/
def tailLen_B (τ : PBP) : ℕ := τ.Q.shape.colLen 0 - τ.P.shape.colLen 0

/-- Tail symbol for B type: paint of the bottom cell of Q's col 0. -/
def tailSymbol_B (τ : PBP) : DRCSymbol := τ.Q.paint (τ.Q.shape.colLen 0 - 1) 0

/-! ## D type: column 0 structure -/

theorem col0_dot_below_Q_D (τ : PBP) (hγ : τ.γ = .D)
    {i : ℕ} (hi : i < τ.Q.shape.colLen 0) :
    τ.P.paint i 0 = .dot := by
  have hmem_Q : (i, 0) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr hi
  exact ((τ.dot_match i 0).mpr ⟨hmem_Q, τ.Q_all_dot_of_D hγ i 0 hmem_Q⟩).2

theorem col0_nonDot_tail_D (τ : PBP) (_hγ : τ.γ = .D)
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

theorem countCol0_split (paint : ℕ → ℕ → DRCSymbol) (σ : DRCSymbol)
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

theorem descent_col0_dot_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    {i : ℕ} (hi : i < τ₁.Q.shape.colLen 0) :
    τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  rw [col0_dot_below_Q_D τ₁ hγ₁ hi, col0_dot_below_Q_D τ₂ hγ₂ (hshapeQ ▸ hi)]

theorem descent_col0_outside (τ₁ τ₂ : PBP)
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
      List.length_append]
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
    simp only [List.filter_cons]
    simp only [countCol0] at ih
    by_cases heq : paint (a + n) 0 = σ
    · -- paint(a+n) = σ. By h, no other position can have σ.
      -- So the count in [0, n) is 0, and count in [0, n+1) = 1.
      have h_zero : countCol0 paint σ a n = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk hpk =>
          absurd (h (a + k) (a + n) hpk heq) (by omega)
      simp only [countCol0] at h_zero ⊢
      rw [h_zero]; simp [heq]
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
    simp only [PaintedYoungDiagram.hasDInCol0, decide_eq_false_iff_not,
      Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
    intro ⟨i, j⟩ hmem
    rw [YoungDiagram.mem_cells] at hmem
    simp [τ₁.Q_all_dot_of_D hγ₁ i j hmem]
  have hQ_no_d₂ : τ₂.Q.hasDInCol0 = false := by
    simp only [PaintedYoungDiagram.hasDInCol0, decide_eq_false_iff_not,
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

theorem tail_counts_eq_D (τ₁ τ₂ : PBP)
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

theorem descent_inj_col0_D(τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdescent_P : ∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j)
    (_hdescent_Q : ∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    ∀ i, τ₁.P.paint i 0 = τ₂.P.paint i 0 := by
  intro i
  set a := τ₁.Q.shape.colLen 0
  set b := τ₁.P.shape.colLen 0
  have hQ_le := Q_colLen0_le_P_colLen0_D τ₁ hγ₁
  by_cases h1 : i < a
  · exact descent_col0_dot_D τ₁ τ₂ hγ₁ hγ₂ hshapeQ h1
  · by_cases h2 : i < b
    · push_neg at h1
      have hcounts := tail_counts_eq_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdescent_P
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
      exact descent_col0_outside τ₁ τ₂ hshapeP h2

/-- **Proposition 10.9** ([BMSZb]), correct statement for D type:
    The map τ ↦ (∇τ, (p_τ, q_τ), ε_τ) is injective on PBP_D(Ǒ).

    Here ∇τ is the D → C naive descent, defined by `descentPaintL_DC`.
    The hypothesis `hdesc` says the descended left paint agrees;
    the right descent paint is automatically the same (Q is all dots,
    and the descent Q' depends only on shapes + cL).

    This follows from:
    1. `descent_eq_implies_cols_ge1_D`: same descent → same cols ≥ 1
    2. `prop_10_9_D`: same cols ≥ 1 + same sig/eps → same col 0 -/
theorem descent_inj_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    -- Same descent (∇τ₁ = ∇τ₂): descended left paint agrees
    (hdesc : ∀ i j, descentPaintL_DC τ₁ i j = descentPaintL_DC τ₂ i j)
    -- Same signature and epsilon
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    -- Then τ₁ = τ₂ (as paint functions on P; Q is determined by shapes for D type)
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) := by
  constructor
  · intro i j
    by_cases hj : j = 0
    · -- Column 0: use prop_10_9_D
      subst hj
      exact descent_inj_col0_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ
        (descent_eq_implies_cols_ge1_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdesc)
        (fun i j => by
          by_cases hm : (i, j) ∈ τ₁.Q.shape
          · rw [Q_all_dot_of_D τ₁ hγ₁ i j hm,
                Q_all_dot_of_D τ₂ hγ₂ i j (hshapeQ ▸ hm)]
          · rw [τ₁.Q.paint_outside i j hm,
                τ₂.Q.paint_outside i j (hshapeQ ▸ hm)])
        hsig heps i
    · -- Columns ≥ 1: from recovery lemma
      exact descent_eq_implies_cols_ge1_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdesc i j (by omega)
  · -- Q: both all dots for D type
    intro i j
    by_cases hm : (i, j) ∈ τ₁.Q.shape
    · rw [Q_all_dot_of_D τ₁ hγ₁ i j hm]
      have hm₂ : (i, j) ∈ τ₂.Q.shape := hshapeQ ▸ hm
      rw [Q_all_dot_of_D τ₂ hγ₂ i j hm₂]
    · have hm₂ : (i, j) ∉ τ₂.Q.shape := hshapeQ ▸ hm
      rw [τ₁.Q.paint_outside i j hm, τ₂.Q.paint_outside i j hm₂]

/-! ## Prop 10.9 for B type

For B type: the tail is in Q col 0 (Q.colLen(0) ≥ P.colLen(0)).
The proof is symmetric to D type with P↔Q swapped:
- Q col 0 has dots (matching P via dot_match) then non-dot symbols
- The non-dot part (tail) is determined by (signature, epsilon)
- The determination uses the same monotone_col_unique + tail_counts_arith

For the full statement: same B→M descent + same (p,q,ε) → same PBP.
B→M descent gives: P fully + Q cols ≥ 1 (from descent_recovery_BM).
Remaining: Q col 0 from (p, q, ε). -/

/-- Layer monotonicity for Q's column 0. -/
theorem col0_layerOrd_mono_Q (τ : PBP) {i₁ i₂ : ℕ}
    (h : i₁ ≤ i₂) (hmem : (i₂, 0) ∈ τ.Q.shape) :
    (τ.Q.paint i₁ 0).layerOrd ≤ (τ.Q.paint i₂ 0).layerOrd :=
  τ.mono_Q i₁ 0 i₂ 0 h le_rfl hmem

/-- B type: P has {•, c}. So P.countSym σ = 0 for σ ∈ {s, r, d}. -/
theorem P_countSym_zero_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    (σ : DRCSymbol) (hσ : σ ≠ .dot ∧ σ ≠ .c) :
    τ.P.countSym σ = 0 := by
  simp only [PaintedYoungDiagram.countSym, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨i, j⟩ hm heq
  -- P paints only dot or c. Since σ ≠ dot ∧ σ ≠ c, contradiction.
  by_cases hne : τ.P.paint i j = .dot
  · exact hσ.1 (heq ▸ hne)
  · have := P_nonDot_eq_c_of_B τ hγ i j hm hne
    exact hσ.2 (heq ▸ this)

/-- B type: Q has {•, s, r, d}. So Q.countSym .c = 0. -/
theorem Q_countSym_c_zero_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) :
    τ.Q.countSym .c = 0 := by
  simp only [PaintedYoungDiagram.countSym, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨i, j⟩ hm h
  have := τ.sym_Q i j hm
  rcases hγ with hγ | hγ <;> rw [hγ] at this <;> simp [DRCSymbol.allowed] at this <;>
    rw [h] at this <;> simp at this

/-- For B type: the dot boundary in Q col 0 equals the dot boundary in P col 0.
    Both equal (dotDiag).colLen(0). -/
theorem dot_boundary_eq_B (τ : PBP) :
    (dotDiag τ.P τ.mono_P).colLen 0 = (dotDiag τ.Q τ.mono_Q).colLen 0 := by
  congr 1; exact dotDiag_eq τ

/-- Q col 0: below the dot boundary, Q paints dot. -/
theorem col0_Q_dot_below_dotBoundary (τ : PBP)
    {i : ℕ} (hi : i < (dotDiag τ.Q τ.mono_Q).colLen 0) :
    τ.Q.paint i 0 = .dot := by
  have hmem : (i, 0) ∈ (dotDiag τ.Q τ.mono_Q) := YoungDiagram.mem_iff_lt_colLen.mpr hi
  simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem.2

/-- Q col 0: at or above the dot boundary (within Q.shape), Q is non-dot. -/
theorem col0_Q_nonDot_above_dotBoundary (τ : PBP)
    {i : ℕ} (hi_ge : (dotDiag τ.Q τ.mono_Q).colLen 0 ≤ i) (hi_lt : i < τ.Q.shape.colLen 0) :
    τ.Q.paint i 0 ≠ .dot := by
  intro heq
  have hmem : (i, 0) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr hi_lt
  have : (i, 0) ∈ (dotDiag τ.Q τ.mono_Q) := by
    simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hmem, heq⟩
  rw [YoungDiagram.mem_iff_lt_colLen] at this; omega

/-- B type: Q's non-dot tail in col 0 has no c (Q has {•,s,r,d}). -/
theorem Q_col0_no_c_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i : ℕ} (hmem : (i, 0) ∈ τ.Q.shape) : τ.Q.paint i 0 ≠ .c := by
  intro heq
  have := τ.sym_Q i 0 hmem
  rcases hγ with hγ | hγ <;> rw [hγ] at this <;> simp [DRCSymbol.allowed] at this <;>
    rw [heq] at this <;> simp at this

/-- B-type Q col 0: dot region (i < P.colLen(0)) determined by P + dot_match. -/
theorem col0_Q_dot_below_P_B (τ : PBP) (_hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i : ℕ} (_hi : i < τ.P.shape.colLen 0) (hp : (i, 0) ∈ τ.P.shape)
    (hp_dot : τ.P.paint i 0 = .dot) : τ.Q.paint i 0 = .dot := by
  by_cases hq : (i, 0) ∈ τ.Q.shape
  · exact ((τ.dot_match i 0).mp ⟨hp, hp_dot⟩).2
  · exact τ.Q.paint_outside i 0 hq

/-- B-type: P has {•, c}. Cells in P are dot or c. If (i, 0) ∈ P.shape
    and P.paint = dot, then Q.paint = dot (by dot_match). -/
theorem Q_dot_of_P_dot_B (τ : PBP) {i : ℕ}
    (hp : (i, 0) ∈ τ.P.shape) (hp_dot : τ.P.paint i 0 = .dot) :
    (i, 0) ∈ τ.Q.shape → τ.Q.paint i 0 = .dot :=
  fun _hq => ((τ.dot_match i 0).mp ⟨hp, hp_dot⟩).2

/-- **Prop 10.9 for B type** (with naive B→M descent):
    Same descent + same shapes + same (p,q,ε) → same Q col 0.

    This is symmetric to descent_inj_col0_Dbut for Q instead of P.
    The tail is in Q col 0, and the counting argument uses Q's
    symbol counts and column uniqueness. -/
theorem descent_inj_col0_B (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .Bplus ∨ τ₁.γ = .Bminus)
    (hγ₂ : τ₂.γ = .Bplus ∨ τ₂.γ = .Bminus)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    -- P agrees (from descent recovery)
    (hP : ∀ i j, τ₁.P.paint i j = τ₂.P.paint i j)
    -- Q cols ≥ 1 agree (from descent recovery)
    (hQ_ge1 : ∀ i j, 1 ≤ j → τ₁.Q.paint i j = τ₂.Q.paint i j)
    -- Same signature and epsilon
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    ∀ i, τ₁.Q.paint i 0 = τ₂.Q.paint i 0 := by
  intro i
  -- For B type, Q col 0 has three zones:
  -- Zone A: dot cells (where both P and Q paint dot, by dot_match)
  -- Zone B: non-dot cells within Q.shape (the "tail")
  -- Zone C: outside Q.shape
  --
  -- The dot cells are determined by P (which is known via hP):
  -- Q.paint(i,0) = dot ↔ P.paint(i,0) = dot (by dot_match, within shapes)
  -- Since P agrees (hP), the dot/non-dot classification of Q col 0 agrees.
  --
  -- For non-dot cells: B-type Q has {•, s, r, d}. The non-dot tail has
  -- symbols from {s, r, d} in non-decreasing layerOrd order.
  -- These are determined by (sig, ε) via the same counting argument as D type.
  by_cases hq : (i, 0) ∈ τ₁.Q.shape
  · have hq₂ : (i, 0) ∈ τ₂.Q.shape := hshapeQ ▸ hq
    -- Determine dot vs non-dot using P + dot_match
    by_cases hd : τ₁.Q.paint i 0 = .dot
    · -- Q₁ dot. P₁ dot (dot_match). P₂ dot (hP). Q₂ dot (dot_match).
      rw [hd]
      have ⟨hp_mem, hp_dot⟩ := (τ₁.dot_match i 0).mpr ⟨hq, hd⟩
      have hp₂_dot := hP i 0 ▸ hp_dot
      exact ((τ₂.dot_match i 0).mp ⟨hshapeP ▸ hp_mem, hp₂_dot⟩).2.symm
    · -- Q₁ non-dot. Need Q₂ also non-dot with same symbol.
      have hd₂ : τ₂.Q.paint i 0 ≠ .dot := by
        intro h₂
        have ⟨hp_mem₂, hp_dot₂⟩ := (τ₂.dot_match i 0).mpr ⟨hq₂, h₂⟩
        have hp_dot₁ := (hP i 0).symm ▸ hp_dot₂
        exact hd ((τ₁.dot_match i 0).mp ⟨hshapeP.symm ▸ hp_mem₂, hp_dot₁⟩).2
      -- Both Q non-dot. Use monotone_col_unique on Q col 0 non-dot zone.
      -- Set a = dot boundary (dotDiag colLen), n = Q.colLen(0) - a.
      set a := (dotDiag τ₁.Q τ₁.mono_Q).colLen 0
      set b := τ₁.Q.shape.colLen 0
      -- i is in non-dot zone [a, b)
      have hi_lt : i < b := YoungDiagram.mem_iff_lt_colLen.mp hq
      have hi_ge : a ≤ i := by
        by_contra h_lt; push_neg at h_lt
        exact hd (col0_Q_dot_below_dotBoundary τ₁ h_lt)
      -- a₂ = a (from dotDiag_eq + hP + dot_match)
      have ha₂ : a = (dotDiag τ₂.Q τ₂.mono_Q).colLen 0 := by
        -- dotDiag τ₁.Q = dotDiag τ₁.P = dotDiag τ₂.P = dotDiag τ₂.Q
        have h1 := dotDiag_eq τ₁  -- dotDiag P₁ = dotDiag Q₁
        have h2 := dotDiag_eq τ₂  -- dotDiag P₂ = dotDiag Q₂
        -- dotDiag P₁ = dotDiag P₂ (since P₁ = P₂ and P.shape₁ = P.shape₂)
        have h3 : dotDiag τ₁.P τ₁.mono_P = dotDiag τ₂.P τ₂.mono_P := by
          ext ⟨r, c⟩
          simp only [dotDiag, Finset.mem_filter, YoungDiagram.mem_cells]
          constructor
          · rintro ⟨hm, hp⟩; exact ⟨hshapeP ▸ hm, hP r c ▸ hp⟩
          · rintro ⟨hm, hp⟩; exact ⟨hshapeP.symm ▸ hm, (hP r c).symm ▸ hp⟩
        show (dotDiag τ₁.Q τ₁.mono_Q).colLen 0 = (dotDiag τ₂.Q τ₂.mono_Q).colLen 0
        rw [← h1, h3, h2]
      set n := b - a
      -- Prove counts of each symbol in Q col 0 non-dot zone [a, n) agree.
      -- Step 1: n_dot = 0 in non-dot zone
      have hcolQ_eq : τ₁.Q.shape.colLen 0 = τ₂.Q.shape.colLen 0 :=
        congr_arg (YoungDiagram.colLen · 0) hshapeQ
      have hnd_dot : countCol0 τ₁.Q.paint .dot a n = countCol0 τ₂.Q.paint .dot a n := by
        rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
              col0_Q_nonDot_above_dotBoundary τ₁ (by omega) (by omega)),
            countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
              col0_Q_nonDot_above_dotBoundary τ₂ (by omega) (by omega))]
      -- Step 2: n_c = 0 in non-dot zone (B-type Q has no c)
      have hnc₁ : countCol0 τ₁.Q.paint .c a n = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
          simp only [Nat.add_comm a k] at *
          exact Q_col0_no_c_of_B τ₁ hγ₁ (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
      have hnc₂ : countCol0 τ₂.Q.paint .c a n = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
          simp only [Nat.add_comm a k] at *
          exact Q_col0_no_c_of_B τ₂ hγ₂ (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
      -- Step 3: n_d determined by epsilon
      -- n_d ∈ {0, 1} (column uniqueness)
      have hd_le₁ := countCol0_le_one_of_unique τ₁.Q.paint .d a n (τ₁.col_d_Q 0)
      have hd_le₂ := countCol0_le_one_of_unique τ₂.Q.paint .d a n (τ₂.col_d_Q 0)
      -- For B type: P has {•,c}, no d in P. So P.hasDInCol0 = false.
      have hP_no_d₁ : τ₁.P.hasDInCol0 = false := by
        simp only [PaintedYoungDiagram.hasDInCol0, decide_eq_false_iff_not,
          Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
        intro ⟨r, c⟩ hmem
        rw [YoungDiagram.mem_cells] at hmem
        simp only [not_and]
        intro hc
        subst hc
        have := P_nonDot_eq_c_of_B τ₁ hγ₁ r 0 hmem
        intro heq
        have := this (heq ▸ DRCSymbol.noConfusion)
        rw [this] at heq; exact DRCSymbol.noConfusion heq
      have hP_no_d₂ : τ₂.P.hasDInCol0 = false := by
        simp only [PaintedYoungDiagram.hasDInCol0, decide_eq_false_iff_not,
          Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
        intro ⟨r, c⟩ hmem
        rw [YoungDiagram.mem_cells] at hmem
        simp only [not_and]
        intro hc
        subst hc
        have := P_nonDot_eq_c_of_B τ₂ hγ₂ r 0 hmem
        intro heq
        have := this (heq ▸ DRCSymbol.noConfusion)
        rw [this] at heq; exact DRCSymbol.noConfusion heq
      -- epsilon = if Q.hasDInCol0 then 0 else 1 (since P.hasDInCol0 = false)
      have hQ_d_agree : τ₁.Q.hasDInCol0 = τ₂.Q.hasDInCol0 := by
        simp only [PBP.epsilon, hP_no_d₁, hP_no_d₂, Bool.false_or] at heps
        revert heps
        cases τ₁.Q.hasDInCol0 <;> cases τ₂.Q.hasDInCol0 <;> simp
      -- hasDInCol0(Q) ↔ countCol0(.d) > 0
      have hbridge₁ := hasDInCol0_iff_countCol0_pos τ₁.Q
      have hbridge₂ := hasDInCol0_iff_countCol0_pos τ₂.Q
      -- Decompose countCol0(.d, 0, Q.colLen) = countCol0(.d, 0, a) + countCol0(.d, a, n)
      have hsplit₁ := countCol0_split τ₁.Q.paint .d 0 a (τ₁.Q.shape.colLen 0) (by omega)
      have hsplit₂ := countCol0_split τ₂.Q.paint .d 0 a (τ₂.Q.shape.colLen 0)
        (by rw [← hshapeQ]; omega)
      -- Dot region [0, a) has no d
      have hdot_d₁ : countCol0 τ₁.Q.paint .d 0 a = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
          simp only [Nat.zero_add]
          rw [col0_Q_dot_below_dotBoundary τ₁ hk]; exact DRCSymbol.noConfusion
      have hdot_d₂ : countCol0 τ₂.Q.paint .d 0 a = 0 :=
        countCol0_eq_zero_of_ne _ _ _ _ fun k hk => by
          simp only [Nat.zero_add]
          have : k < (dotDiag τ₂.Q τ₂.mono_Q).colLen 0 := ha₂ ▸ hk
          rw [col0_Q_dot_below_dotBoundary τ₂ this]; exact DRCSymbol.noConfusion
      have hn_sub₁ : τ₁.Q.shape.colLen 0 - a = n := by omega
      have hn_sub₂ : τ₂.Q.shape.colLen 0 - a = n := by
        have : τ₁.Q.shape.colLen 0 = τ₂.Q.shape.colLen 0 := by
          exact congr_arg (YoungDiagram.colLen · 0) hshapeQ
        omega
      simp only [hdot_d₁, Nat.zero_add, hn_sub₁] at hsplit₁
      simp only [hdot_d₂, Nat.zero_add, hn_sub₂] at hsplit₂
      rw [hsplit₁] at hbridge₁; rw [hsplit₂] at hbridge₂
      -- n_d agree
      have hnd_d : countCol0 τ₁.Q.paint .d a n = countCol0 τ₂.Q.paint .d a n := by
        -- After rw: hbridge₁ : τ₁.Q.hasDInCol0 = true ↔ 0 < countCol0 τ₁...
        -- hbridge₂ : τ₂.Q.hasDInCol0 = true ↔ 0 < countCol0 τ₂...
        -- hQ_d_agree : τ₁.Q.hasDInCol0 = τ₂.Q.hasDInCol0
        -- Both counts ∈ {0, 1}. Positivity is equivalent.
        have hpos_iff : (0 < countCol0 τ₁.Q.paint .d a n) ↔
                        (0 < countCol0 τ₂.Q.paint .d a n) := by
          constructor
          · intro h1; exact hbridge₂.mp (hQ_d_agree ▸ hbridge₁.mpr h1)
          · intro h2; exact hbridge₁.mp (hQ_d_agree.symm ▸ hbridge₂.mpr h2)
        rcases Nat.eq_zero_or_pos (countCol0 τ₁.Q.paint .d a n) with h1 | h1
        · have : ¬(0 < countCol0 τ₂.Q.paint .d a n) := by
            intro h2; have := hpos_iff.mpr h2; omega
          omega
        · have h2 := hpos_iff.mp h1; omega
      -- Step 4: Weighted sum from signature
      -- For B/D: p = nDot + 2*nR + nC + nD (+ 1 if B⁺)
      -- For B: nR = Q.r (P.r = 0), nC = P.c (Q.c = 0), nD = Q.d (P.d = 0)
      -- Q.r = Q.r_col0 + Q.r_colGe1
      -- From sig same + P same + Q.colGe1 same → Q.r_col0 + Q.d_col0 determined
      have hwr : 2 * countCol0 τ₁.Q.paint .r a n + countCol0 τ₁.Q.paint .c a n +
                  countCol0 τ₁.Q.paint .d a n =
                  2 * countCol0 τ₂.Q.paint .r a n + countCol0 τ₂.Q.paint .c a n +
                  countCol0 τ₂.Q.paint .d a n := by
        rw [hnc₁, hnc₂]
        simp only [Nat.add_zero]
        -- Decompose Q.countSym .r = countSymCol0 Q .r + countSymColGe1 Q .r
        -- and similarly for .d
        suffices h : ∀ σ : DRCSymbol, σ ≠ .dot →
            ∀ (τ : PBP), (τ.γ = .Bplus ∨ τ.γ = .Bminus) →
            (dotDiag τ.Q τ.mono_Q).colLen 0 = a → τ.Q.shape.colLen 0 - a = n →
            τ.Q.countSym σ = countCol0 τ.Q.paint σ a n + countSymColGe1 τ.Q σ by
          have hr₁ := h .r (by decide) τ₁ hγ₁ rfl (by omega)
          have hd₁' := h .d (by decide) τ₁ hγ₁ rfl (by omega)
          have hcolQ : τ₁.Q.shape.colLen 0 = τ₂.Q.shape.colLen 0 :=
            congr_arg (YoungDiagram.colLen · 0) hshapeQ
          have hr₂ := h .r (by decide) τ₂ hγ₂ ha₂.symm (by omega)
          have hd₂' := h .d (by decide) τ₂ hγ₂ ha₂.symm (by omega)
          have hge1_r := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .r
          have hge1_d := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .d
          -- From signature: extract the weighted sum equation
          have hsig1 := congr_arg Prod.fst hsig
          simp only [PBP.signature] at hsig1
          -- For B type, simplify signature using P has no r/s/d and Q has no c
          rw [P_countSym_zero_of_B τ₁ hγ₁ .r ⟨by decide, by decide⟩,
              P_countSym_zero_of_B τ₁ hγ₁ .d ⟨by decide, by decide⟩,
              Q_countSym_c_zero_of_B τ₁ hγ₁,
              P_countSym_zero_of_B τ₂ hγ₂ .r ⟨by decide, by decide⟩,
              P_countSym_zero_of_B τ₂ hγ₂ .d ⟨by decide, by decide⟩,
              Q_countSym_c_zero_of_B τ₂ hγ₂] at hsig1
          -- hsig1: P₁.dot + Q₁.dot + 2*Q₁.r + P₁.c + Q₁.d + ... = ...
          -- P agree: P₁.countSym = P₂.countSym (from hP + hshapeP)
          have hP_eq : ∀ σ, τ₁.P.countSym σ = τ₂.P.countSym σ := by
            intro σ
            simp only [PaintedYoungDiagram.countSym]
            congr 1; rw [hshapeP]
            ext ⟨r, c⟩; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hm, hp⟩; exact ⟨hm, hP r c ▸ hp⟩
            · rintro ⟨hm, hp⟩; exact ⟨hm, (hP r c).symm ▸ hp⟩
          -- Q.dot agree (from dotDiag)
          have hQ_dot : τ₁.Q.countSym .dot = τ₂.Q.countSym .dot := by
            simp only [PaintedYoungDiagram.countSym]
            congr 1; rw [hshapeQ]
            ext ⟨r, c⟩; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hm, hp⟩
              refine ⟨hm, ?_⟩
              have : (r, c) ∈ (dotDiag τ₁.Q τ₁.mono_Q) := by
                simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter,
                  YoungDiagram.mem_cells]; exact ⟨hshapeQ.symm ▸ hm, hp⟩
              rw [← dotDiag_eq τ₁] at this
              have h3 : (r, c) ∈ (dotDiag τ₂.P τ₂.mono_P) := by
                rw [← show dotDiag τ₁.P τ₁.mono_P = dotDiag τ₂.P τ₂.mono_P from by
                  ext ⟨r', c'⟩
                  simp only [dotDiag, Finset.mem_filter, YoungDiagram.mem_cells]
                  constructor
                  · rintro ⟨hm', hp'⟩; exact ⟨hshapeP ▸ hm', hP r' c' ▸ hp'⟩
                  · rintro ⟨hm', hp'⟩; exact ⟨hshapeP.symm ▸ hm', (hP r' c').symm ▸ hp'⟩]
                exact this
              rw [dotDiag_eq τ₂] at h3
              simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter,
                YoungDiagram.mem_cells] at h3
              exact h3.2
            · rintro ⟨hm, hp⟩
              refine ⟨hm, ?_⟩
              have : (r, c) ∈ (dotDiag τ₂.Q τ₂.mono_Q) := by
                simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter,
                  YoungDiagram.mem_cells]; exact ⟨hm, hp⟩
              rw [← dotDiag_eq τ₂] at this
              have h3 : (r, c) ∈ (dotDiag τ₁.P τ₁.mono_P) := by
                rw [show dotDiag τ₁.P τ₁.mono_P = dotDiag τ₂.P τ₂.mono_P from by
                  ext ⟨r', c'⟩
                  simp only [dotDiag, Finset.mem_filter, YoungDiagram.mem_cells]
                  constructor
                  · rintro ⟨hm', hp'⟩; exact ⟨hshapeP ▸ hm', hP r' c' ▸ hp'⟩
                  · rintro ⟨hm', hp'⟩; exact ⟨hshapeP.symm ▸ hm', (hP r' c').symm ▸ hp'⟩]
                exact this
              rw [dotDiag_eq τ₁] at h3
              simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter,
                YoungDiagram.mem_cells] at h3
              exact h3.2
          rw [hP_eq .dot, hP_eq .c, hQ_dot] at hsig1
          rw [hr₁, hr₂, hd₁', hd₂'] at hsig1
          rw [hge1_r, hge1_d] at hsig1
          -- For B⁺/B⁻, the +1 terms are the same or cancel
          rcases hγ₁ with hγ₁' | hγ₁' <;> rcases hγ₂ with hγ₂' | hγ₂' <;> (
            rw [hγ₁', hγ₂'] at hsig1
            simp (config := { decide := true }) only [ite_true, ite_false] at hsig1
            omega)
        -- Proof of decomposition: Q.countSym σ = countCol0 σ a n + countSymColGe1 Q σ
        intro σ hσ τ' hγ' ha' hn'
        have ha_le : a ≤ τ'.Q.shape.colLen 0 := by
          -- dotDiag ⊆ Q.shape, so dotDiag.colLen ≤ Q.shape.colLen
          suffices h : ∀ i, i < a → (i, 0) ∈ τ'.Q.shape by
            by_contra h_lt; push_neg at h_lt
            exact absurd (h (τ'.Q.shape.colLen 0) h_lt)
              (YoungDiagram.mem_iff_lt_colLen.not.mpr (Nat.lt_irrefl _))
          intro i hi
          have : (i, 0) ∈ dotDiag τ'.Q τ'.mono_Q :=
            YoungDiagram.mem_iff_lt_colLen.mpr (ha' ▸ hi)
          rw [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at this
          exact this.1
        rw [countSym_split τ'.Q σ, countSymCol0_eq_countCol0]
        rw [countCol0_split _ _ 0 a (τ'.Q.shape.colLen 0) (by omega)]
        have : τ'.Q.shape.colLen 0 - a = n := by omega
        rw [Nat.zero_add, this]
        rw [countCol0_eq_zero_of_ne _ _ 0 a (by
          intro k hk hpaint
          have := col0_Q_dot_below_dotBoundary τ' (ha'.symm ▸ hk)
          rw [Nat.zero_add] at hpaint
          rw [this] at hpaint; exact hσ hpaint.symm)]
        omega
      -- Step 5: Total non-dot count in tail
      have htot : countCol0 τ₁.Q.paint .s a n + countCol0 τ₁.Q.paint .r a n +
                  countCol0 τ₁.Q.paint .c a n + countCol0 τ₁.Q.paint .d a n =
                  countCol0 τ₂.Q.paint .s a n + countCol0 τ₂.Q.paint .r a n +
                  countCol0 τ₂.Q.paint .c a n + countCol0 τ₂.Q.paint .d a n := by
        have h1 := countCol0_total τ₁.Q.paint a n
        have h2 := countCol0_total τ₂.Q.paint a n
        rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
          col0_Q_nonDot_above_dotBoundary τ₁ (by omega) (by omega))] at h1
        have hcolQ' := congr_arg (YoungDiagram.colLen · 0) hshapeQ
        rw [countCol0_eq_zero_of_ne _ _ _ _ (fun k hk =>
          col0_Q_nonDot_above_dotBoundary τ₂ (by omega) (by omega))] at h2
        omega
      -- Step 6: Apply tail_counts_arith with n_c = 0
      have ⟨hns, hnr, _⟩ := tail_counts_arith htot hwr hnd_d
        (by rw [hnc₁]; omega) (by rw [hnc₂]; omega)
      -- Step 7: All counts agree
      have hcounts : ∀ σ, countCol0 τ₁.Q.paint σ a n = countCol0 τ₂.Q.paint σ a n := by
        intro σ
        cases σ with
        | dot => exact hnd_dot
        | s => exact hns
        | r => exact hnr
        | c => rw [hnc₁, hnc₂]
        | d => exact hnd_d
      -- Step 8: Apply monotone_col_unique
      have hk : i - a < n := by omega
      have heq := monotone_col_unique τ₁.Q.paint τ₂.Q.paint a n b
        (by omega)
        (fun i₁ i₂ h hlt => col0_layerOrd_mono_Q τ₁ h
          (YoungDiagram.mem_iff_lt_colLen.mpr hlt))
        (fun i₁ i₂ h hlt => col0_layerOrd_mono_Q τ₂ h
          (YoungDiagram.mem_iff_lt_colLen.mpr (hshapeQ ▸ hlt)))
        hcounts (i - a) hk
      simp only [Nat.add_sub_cancel' hi_ge] at heq
      exact heq
  · rw [τ₁.Q.paint_outside i 0 hq, τ₂.Q.paint_outside i 0 (hshapeQ ▸ hq)]

/-- **Proposition 10.9** ([BMSZb]), correct statement for B type:
    The map τ ↦ (∇τ, (p_τ, q_τ), ε_τ) is injective on PBP_B(Ǒ).

    Here ∇τ is the B → M naive descent. The hypothesis says:
    - same B→M descent left and right paints
    - same signature and epsilon
    - interlacing conditions (orbit-level)

    This follows from:
    1. `descent_recovery_BM`: same descent → same P + same Q cols ≥ 1
    2. `descent_inj_col0_B`: same P + same Q cols ≥ 1 + same sig/eps → same Q col 0 -/
theorem descent_inj_B (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .Bplus ∨ τ₁.γ = .Bminus)
    (hγ₂ : τ₂.γ = .Bplus ∨ τ₂.γ = .Bminus)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    -- Interlacing (orbit-level)
    (hinterl₁ : ∀ j, dotScolLen τ₁.P j ≥ dotScolLen τ₁.Q (j + 1))
    (hinterl₂ : ∀ j, dotScolLen τ₂.P j ≥ dotScolLen τ₂.Q (j + 1))
    -- Same B→M descent
    (hdescL : ∀ i j, descentPaintL_BM τ₁ i j = descentPaintL_BM τ₂ i j)
    (hdescR : ∀ i j, descentPaintR_BM τ₁ i j = descentPaintR_BM τ₂ i j)
    -- Same signature and epsilon
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) := by
  -- Step 1: recover P fully and Q cols ≥ 1 from descent
  have ⟨hP, hQ_ge1⟩ := descent_recovery_BM τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ
    hinterl₁ hinterl₂ hdescL hdescR
  constructor
  · exact hP
  · -- Step 2: recover Q col 0 from (sig, eps) + known P and Q cols ≥ 1
    intro i j
    by_cases hj : j = 0
    · subst hj
      exact descent_inj_col0_B τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hP hQ_ge1 hsig heps i
    · exact hQ_ge1 i j (by omega)

/-! ## Double Descent ∇²

[BMSZb] Proposition 10.9 states injectivity for the double descent ∇².
The double descent D→C→D (resp. B→M→B) composes two single descents.
After simplification (the intermediate dotScolLen values collapse),
the double descent paint reduces to a direct formula on the original τ. -/

/-- **D→C→D double descent** left paint.
    ∇²τ removes P's col 0 (D→C), then Q's col 0 (C→D).
    After simplification:
    P''(i,j) = dot if i < Q.colLen(j+1),
               s   if Q.colLen(j+1) ≤ i < dotScolLen(P, j+1),
               P(i, j+1) otherwise. -/
noncomputable def doubleDescent_D_paintL (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < τ.Q.shape.colLen (j + 1) then .dot
    else if i < dotScolLen τ.P (j + 1) then .s
    else τ.P.paint i (j + 1)

/-- **B→M→B double descent** left paint.
    ∇²τ removes Q's col 0 (B→M), then P's col 0 (M→B).
    After simplification:
    P''(i,j) = dot if i < dotScolLen(P, j+1),
               P(i, j+1) otherwise. -/
noncomputable def doubleDescent_B_paintL (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.P (j + 1) then .dot
    else τ.P.paint i (j + 1)

/-- **B→M→B double descent** right paint.
    Q''(i,j) = dot if i < dotScolLen(P, j+1),
               s   if dotScolLen(P, j+1) ≤ i < dotScolLen(Q, j+1),
               Q(i, j+1) otherwise. -/
noncomputable def doubleDescent_B_paintR (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    if i < dotScolLen τ.P (j + 1) then .dot
    else if i < dotScolLen τ.Q (j + 1) then .s
    else τ.Q.paint i (j + 1)

/-! ### Auxiliary: layerOrd > 1 above dotScolLen boundary -/

/-- If i ≥ dotScolLen(D, j) and (i, j) ∈ D.shape, then layerOrd(D.paint i j) > 1. -/
theorem layerOrd_gt_one_of_ge_dotScolLen (D : PaintedYoungDiagram)
    (hm : D.layerMonotone) {i j : ℕ}
    (hi : dotScolLen D j ≤ i) (hmem : (i, j) ∈ D.shape) :
    (D.paint i j).layerOrd > 1 := by
  by_contra h; push_neg at h
  rw [dotScolLen_eq_dotSdiag_colLen D hm] at hi
  have : (i, j) ∈ dotSdiag D hm := by
    rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hmem, h⟩
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this) (by omega)

/-- If i ≥ dotScolLen(D, j) and (i, j) ∈ D.shape, then D.paint(i, j) ≠ dot. -/
theorem paint_ne_dot_of_ge_dotScolLen (D : PaintedYoungDiagram)
    (hm : D.layerMonotone) {i j : ℕ}
    (hi : dotScolLen D j ≤ i) (hmem : (i, j) ∈ D.shape) :
    D.paint i j ≠ .dot := by
  have := layerOrd_gt_one_of_ge_dotScolLen D hm hi hmem
  intro heq; rw [heq, DRCSymbol.layerOrd] at this; omega

/-- For D type: Q.colLen(j) ≤ dotScolLen(P, j).
    Because Q = dotDiag(P), so Q.colLen(j) = #{dot in P col j} ≤ #{dot+s in P col j}. -/
theorem Q_colLen_le_dotScolLen_of_D (τ : PBP) (hγ : τ.γ = .D) (j : ℕ) :
    τ.Q.shape.colLen j ≤ dotScolLen τ.P j := by
  -- Q = dotDiag(P) for D type. dotDiag ⊆ dotSdiag (dot has layerOrd 0 ≤ 1).
  -- So Q.colLen = dotDiag.colLen ≤ dotSdiag.colLen = dotScolLen.
  rw [Q_eq_dotDiag_of_D τ hγ, dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
  -- Need: (dotDiag P).colLen j ≤ (dotSdiag P).colLen j
  -- Suffices: dotDiag ≤ dotSdiag
  suffices h : ∀ i, (i, j) ∈ dotDiag τ.P τ.mono_P → (i, j) ∈ dotSdiag τ.P τ.mono_P by
    by_contra hlt; push_neg at hlt
    -- hlt : (dotSdiag P).colLen j < (dotDiag P).colLen j
    set b := (dotSdiag τ.P τ.mono_P).colLen j
    have hmem : (b, j) ∈ dotDiag τ.P τ.mono_P :=
      YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := h b hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this) (by omega)
  intro i hmem
  rw [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨hmem.1, by rw [hmem.2]; decide⟩

/-- dotScolLen(D, j) ≤ D.shape.colLen(j). The dot+s sub-diagram is contained in shape. -/
theorem dotScolLen_le_colLen (D : PaintedYoungDiagram) (hm : D.layerMonotone) (j : ℕ) :
    dotScolLen D j ≤ D.shape.colLen j := by
  rw [dotScolLen_eq_dotSdiag_colLen D hm]
  by_contra h; push_neg at h
  set a := D.shape.colLen j
  have : (a, j) ∈ dotSdiag D hm := YoungDiagram.mem_iff_lt_colLen.mpr h
  rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at this
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this.1) (by omega)

/-! ### Double descent determines single descent -/

/-- D type: same ∇² → same D→C single descent.
    Proof: the dot/s boundary in ∇²τ determines dotScolLen(P, j+1),
    and the non-dot zone directly gives P(i, j+1). -/
theorem ddescent_D_determines_single (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (_hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdd : ∀ i j, doubleDescent_D_paintL τ₁ i j = doubleDescent_D_paintL τ₂ i j) :
    ∀ i j, descentPaintL_DC τ₁ i j = descentPaintL_DC τ₂ i j := by
  -- Helper: ∇²τ at specific (i,j) with conditions on i
  have dd_eq := fun i j => hdd i j
  -- Step 1: dotScolLen(P₁, j+1) = dotScolLen(P₂, j+1)
  have hds : ∀ j, dotScolLen τ₁.P (j + 1) = dotScolLen τ₂.P (j + 1) := by
    intro j; by_contra hne
    have hQ₁ := Q_colLen_le_dotScolLen_of_D τ₁ hγ₁ (j + 1)
    have hQ₂ := Q_colLen_le_dotScolLen_of_D τ₂ hγ₂ (j + 1)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · -- dotScolLen₁ < dotScolLen₂. At i = dotScolLen₁:
      -- ∇²τ₁(i,j) = P₁(i,j+1) (past both Q.colLen and dotScolLen₁)
      -- ∇²τ₂(i,j) = s (past Q.colLen₂ but below dotScolLen₂)
      have key := dd_eq (dotScolLen τ₁.P (j + 1)) j
      show False
      simp only [doubleDescent_D_paintL] at key
      rw [if_neg (by omega), if_neg (by omega),
          if_neg (by rw [← hshapeQ]; omega), if_pos h] at key
      -- key: P₁(dotScolLen₁, j+1) = s. But P₁ has layerOrd > 1 there.
      by_cases hmem : (dotScolLen τ₁.P (j + 1), j + 1) ∈ τ₁.P.shape
      · have := layerOrd_gt_one_of_ge_dotScolLen τ₁.P τ₁.mono_P le_rfl hmem
        rw [key] at this; exact absurd this (by decide)
      · rw [τ₁.P.paint_outside _ _ hmem] at key; exact DRCSymbol.noConfusion key
    · -- Symmetric: dotScolLen₂ < dotScolLen₁
      have key := dd_eq (dotScolLen τ₂.P (j + 1)) j
      show False
      simp only [doubleDescent_D_paintL] at key
      rw [if_neg (by rw [hshapeQ]; omega), if_pos h,
          if_neg (by omega), if_neg (by omega)] at key
      by_cases hmem : (dotScolLen τ₂.P (j + 1), j + 1) ∈ τ₂.P.shape
      · have := layerOrd_gt_one_of_ge_dotScolLen τ₂.P τ₂.mono_P le_rfl hmem
        rw [← key] at this; exact absurd this (by decide)
      · rw [τ₂.P.paint_outside _ _ hmem] at key; exact DRCSymbol.noConfusion key.symm
  -- Step 2: descentPaintL_DC agrees
  intro i j
  simp only [descentPaintL_DC]
  rw [hds j]
  by_cases h : i < dotScolLen τ₂.P (j + 1)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have key := dd_eq i j
    simp only [doubleDescent_D_paintL] at key
    have hQ₁ := Q_colLen_le_dotScolLen_of_D τ₁ hγ₁ (j + 1)
    have hQ₂ := Q_colLen_le_dotScolLen_of_D τ₂ hγ₂ (j + 1)
    have hds' := hds j
    rw [if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)] at key
    exact key

/-- B type: same ∇² → same P cols ≥ 1 and same Q cols ≥ 1.
    ∇² does NOT determine P col 0 or Q col 0 (these require (p,q,ε)).
    This is the partial recovery from double descent, completing to full
    recovery via descent_inj_col0_B in ddescent_inj_B. -/
theorem ddescent_B_determines_colsGe1 (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .Bplus ∨ τ₁.γ = .Bminus)
    (hγ₂ : τ₂.γ = .Bplus ∨ τ₂.γ = .Bminus)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hddL : ∀ i j, doubleDescent_B_paintL τ₁ i j = doubleDescent_B_paintL τ₂ i j)
    (hddR : ∀ i j, doubleDescent_B_paintR τ₁ i j = doubleDescent_B_paintR τ₂ i j) :
    (∀ i j, 1 ≤ j → τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, 1 ≤ j → τ₁.Q.paint i j = τ₂.Q.paint i j) := by
  -- From ∇²L: dotScolLen(P₁, j+1) = dotScolLen(P₂, j+1) and P cols ≥ 1 agree.
  -- From ∇²R: dotScolLen(Q₁, j+1) = dotScolLen(Q₂, j+1) and Q cols ≥ 1 agree.
  have hdsP : ∀ j, dotScolLen τ₁.P (j + 1) = dotScolLen τ₂.P (j + 1) := by
    intro j; by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have key := hddL (dotScolLen τ₁.P (j + 1)) j
      simp only [doubleDescent_B_paintL] at key
      rw [if_neg (by omega), if_pos h] at key
      -- dotScolLen₁ < dotScolLen₂ ≤ P.colLen, so (dotScolLen₁, j+1) ∈ P₁.shape
      have hmem : (dotScolLen τ₁.P (j + 1), j + 1) ∈ τ₁.P.shape := by
        rw [YoungDiagram.mem_iff_lt_colLen]
        exact lt_of_lt_of_le h (dotScolLen_le_colLen τ₂.P τ₂.mono_P (j + 1) |>.trans
          (by rw [← hshapeP]))
      exact absurd key (paint_ne_dot_of_ge_dotScolLen τ₁.P τ₁.mono_P le_rfl hmem)
    · have key := hddL (dotScolLen τ₂.P (j + 1)) j
      simp only [doubleDescent_B_paintL] at key
      rw [if_pos h, if_neg (by omega)] at key
      have hmem : (dotScolLen τ₂.P (j + 1), j + 1) ∈ τ₂.P.shape := by
        rw [YoungDiagram.mem_iff_lt_colLen]
        exact lt_of_lt_of_le h (dotScolLen_le_colLen τ₁.P τ₁.mono_P (j + 1) |>.trans
          (by rw [hshapeP]))
      exact absurd key.symm (paint_ne_dot_of_ge_dotScolLen τ₂.P τ₂.mono_P le_rfl hmem)
  -- B type: dotScolLen(P) ≤ dotScolLen(Q) (P-dots ⊆ Q-dots+s via dot_match)
  have hPQ : ∀ (τ : PBP), (τ.γ = .Bplus ∨ τ.γ = .Bminus) →
      ∀ j, dotScolLen τ.P j ≤ dotScolLen τ.Q j := by
    intro τ hγ j
    rw [dotScolLen_eq_dotSdiag_colLen _ τ.mono_P, dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]
    by_contra hlt; push_neg at hlt
    set a := (dotSdiag τ.Q τ.mono_Q).colLen j
    have hm := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hm
    have hP_dot : τ.P.paint a j = .dot := by
      rcases hγ with hg | hg <;> {
        have := τ.sym_P a j hm.1; rw [hg] at this; revert this hm
        cases τ.P.paint a j <;>
          simp [DRCSymbol.allowed, DRCSymbol.layerOrd] }
    have ⟨hqm, hqd⟩ := (τ.dot_match a j).mp ⟨hm.1, hP_dot⟩
    have : (a, j) ∈ dotSdiag τ.Q τ.mono_Q := by
      rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
      exact ⟨hqm, by rw [hqd]; decide⟩
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this) (by omega)
  have hdsQ : ∀ j, dotScolLen τ₁.Q (j + 1) = dotScolLen τ₂.Q (j + 1) := by
    intro j; by_contra hne
    -- Same as hdsP but for Q. At i = dotScolLen(Q), ∇²R gives Q(i) vs s.
    -- The if order: first dotScolLen(P), then dotScolLen(Q). P ≤ Q by hPQ.
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have key := hddR (dotScolLen τ₁.Q (j + 1)) j
      simp only [doubleDescent_B_paintR] at key
      have hpq₁ := hPQ τ₁ hγ₁ (j+1); have hpq₂ := hPQ τ₂ hγ₂ (j+1); have hds' := hdsP j
      rw [if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos h] at key
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le h
        (dotScolLen_le_colLen τ₂.Q τ₂.mono_Q (j+1) |>.trans (by rw [← hshapeQ])))
      have hlo := layerOrd_gt_one_of_ge_dotScolLen τ₁.Q τ₁.mono_Q le_rfl hmem
      rw [key] at hlo; exact absurd hlo (by decide)
    · have key := hddR (dotScolLen τ₂.Q (j + 1)) j
      simp only [doubleDescent_B_paintR] at key
      have hpq₁ := hPQ τ₁ hγ₁ (j+1); have hpq₂ := hPQ τ₂ hγ₂ (j+1); have hds' := hdsP j
      rw [if_neg (by omega), if_pos h,
          if_neg (by omega), if_neg (by omega)] at key
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le h
        (dotScolLen_le_colLen τ₁.Q τ₁.mono_Q (j+1) |>.trans (by rw [hshapeQ])))
      have hlo := layerOrd_gt_one_of_ge_dotScolLen τ₂.Q τ₂.mono_Q le_rfl hmem
      rw [← key] at hlo; exact absurd hlo (by decide)
  constructor
  · -- P cols ≥ 1: i < dotScolLen → both dot (B type). i ≥ dotScolLen → from ∇²L.
    intro i j hj
    have hdsP_j : dotScolLen τ₁.P j = dotScolLen τ₂.P j := by
      rw [show j = (j - 1) + 1 from by omega]; exact hdsP (j - 1)
    by_cases h : i < dotScolLen τ₁.P j
    · -- i < dotScolLen(P, j): both P paint dot (B type has {dot, c}; layerOrd ≤ 1 → dot)
      have h₂ : i < dotScolLen τ₂.P j := hdsP_j ▸ h
      by_cases hm₁ : (i, j) ∈ τ₁.P.shape
      · have hm₂ : (i, j) ∈ τ₂.P.shape := hshapeP ▸ hm₁
        have hlo₁ := layerOrd_le_one_of_lt_dotSdiag_colLen τ₁.P τ₁.mono_P
          (by rw [← dotScolLen_eq_dotSdiag_colLen _ τ₁.mono_P]; exact h)
        have hlo₂ := layerOrd_le_one_of_lt_dotSdiag_colLen τ₂.P τ₂.mono_P
          (by rw [← dotScolLen_eq_dotSdiag_colLen _ τ₂.mono_P]; exact h₂)
        -- B type P: layerOrd ≤ 1 and allowed {dot, c} → paint = dot
        have hd₁ : τ₁.P.paint i j = .dot := by
          rcases hγ₁ with hg | hg <;> {
            have := τ₁.sym_P i j hm₁; rw [hg] at this; revert this hlo₁
            cases τ₁.P.paint i j <;> simp [DRCSymbol.allowed, DRCSymbol.layerOrd] }
        have hd₂ : τ₂.P.paint i j = .dot := by
          rcases hγ₂ with hg | hg <;> {
            have := τ₂.sym_P i j hm₂; rw [hg] at this; revert this hlo₂
            cases τ₂.P.paint i j <;> simp [DRCSymbol.allowed, DRCSymbol.layerOrd] }
        rw [hd₁, hd₂]
      · rw [τ₁.P.paint_outside i j hm₁, τ₂.P.paint_outside i j (hshapeP ▸ hm₁)]
    · have key := hddL i (j - 1)
      simp only [doubleDescent_B_paintL] at key
      rw [show j - 1 + 1 = j from by omega] at key
      rw [if_neg h, if_neg (by omega)] at key
      exact key
  · intro i j hj
    have hdsP_j : dotScolLen τ₁.P j = dotScolLen τ₂.P j := by
      rw [show j = (j - 1) + 1 from by omega]; exact hdsP (j - 1)
    have hdsQ_j : dotScolLen τ₁.Q j = dotScolLen τ₂.Q j := by
      rw [show j = (j - 1) + 1 from by omega]; exact hdsQ (j - 1)
    by_cases hQ : i < dotScolLen τ₁.Q j
    · -- i < dotScolLen(Q₁, j). Both Q have layerOrd ≤ 1. Dot vs s from P + dot_match.
      have h₂ : i < dotScolLen τ₂.Q j := hdsQ_j ▸ hQ
      by_cases hm₁ : (i, j) ∈ τ₁.Q.shape
      · have hm₂ : (i, j) ∈ τ₂.Q.shape := hshapeQ ▸ hm₁
        by_cases hd₁ : τ₁.Q.paint i j = .dot
        · -- Q₁ dot → P₁ dot (dot_match). P₂ dot (dotScolLen P same). Q₂ dot (dot_match).
          have ⟨hpm₁, hpd₁⟩ := (τ₁.dot_match i j).mpr ⟨hm₁, hd₁⟩
          -- P₁ dot at (i,j) means i < dotScolLen(P₁, j) (B type: dot ↔ layerOrd ≤ 1 ↔ in dotSdiag)
          -- Since dotScolLen(P₁, j) = dotScolLen(P₂, j), P₂ also has dot at (i,j).
          have hpd₂ : τ₂.P.paint i j = .dot := by
            have hpm₂ : (i, j) ∈ τ₂.P.shape := hshapeP ▸ hpm₁
            have hds_mem : (i, j) ∈ dotSdiag τ₁.P τ₁.mono_P := by
              rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
              exact ⟨hpm₁, by rw [hpd₁]; decide⟩
            -- (i,j) ∈ dotSdiag P₂ (since dotSdiag.colLen is same via hdsP_j)
            have : i < (dotSdiag τ₂.P τ₂.mono_P).colLen j := by
              rw [← dotScolLen_eq_dotSdiag_colLen _ τ₂.mono_P, ← hdsP_j,
                  dotScolLen_eq_dotSdiag_colLen _ τ₁.mono_P]
              exact YoungDiagram.mem_iff_lt_colLen.mp hds_mem
            have hds_mem₂ : (i, j) ∈ dotSdiag τ₂.P τ₂.mono_P :=
              YoungDiagram.mem_iff_lt_colLen.mpr this
            rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hds_mem₂
            -- layerOrd ≤ 1. B type P: layerOrd ≤ 1 → dot.
            rcases hγ₂ with hg | hg <;> {
              have := τ₂.sym_P i j hpm₂; rw [hg] at this; revert this hds_mem₂
              cases τ₂.P.paint i j <;>
                simp [DRCSymbol.allowed, DRCSymbol.layerOrd] }
          rw [hd₁]; exact ((τ₂.dot_match i j).mp ⟨hshapeP ▸ hpm₁, hpd₂⟩).2.symm
        · -- Q₁ non-dot, layerOrd ≤ 1 → Q₁ = s. Similarly Q₂ = s.
          have hlo₁ := layerOrd_le_one_of_lt_dotSdiag_colLen τ₁.Q τ₁.mono_Q
            (by rw [← dotScolLen_eq_dotSdiag_colLen _ τ₁.mono_Q]; exact hQ)
          have hs₁ : τ₁.Q.paint i j = .s := by revert hd₁ hlo₁; cases τ₁.Q.paint i j <;> simp [DRCSymbol.layerOrd]
          -- Q₂ also non-dot (from dot_match + P agreement)
          have hd₂ : τ₂.Q.paint i j ≠ .dot := by
            intro hd₂
            have ⟨hpm₂, hpd₂⟩ := (τ₂.dot_match i j).mpr ⟨hm₂, hd₂⟩
            -- P₂ dot → i < dotScolLen(P₂, j) = dotScolLen(P₁, j) → P₁ dot → Q₁ dot. Contradiction.
            have : (i, j) ∈ dotSdiag τ₂.P τ₂.mono_P := by
              rw [dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
              exact ⟨hpm₂, by rw [hpd₂]; decide⟩
            have hi : i < (dotSdiag τ₁.P τ₁.mono_P).colLen j := by
              rw [← dotScolLen_eq_dotSdiag_colLen _ τ₁.mono_P, hdsP_j,
                  dotScolLen_eq_dotSdiag_colLen _ τ₂.mono_P]
              exact YoungDiagram.mem_iff_lt_colLen.mp this
            have hlo := layerOrd_le_one_of_lt_dotSdiag_colLen τ₁.P τ₁.mono_P hi
            have hpm₁ := hshapeP.symm ▸ hpm₂
            have hpd₁ : τ₁.P.paint i j = .dot := by
              rcases hγ₁ with hg | hg <;> {
                have := τ₁.sym_P i j hpm₁; rw [hg] at this; revert this hlo
                cases τ₁.P.paint i j <;> simp [DRCSymbol.allowed, DRCSymbol.layerOrd] }
            exact hd₁ ((τ₁.dot_match i j).mp ⟨hpm₁, hpd₁⟩).2
          have hlo₂ := layerOrd_le_one_of_lt_dotSdiag_colLen τ₂.Q τ₂.mono_Q
            (by rw [← dotScolLen_eq_dotSdiag_colLen _ τ₂.mono_Q]; exact h₂)
          have hs₂ : τ₂.Q.paint i j = .s := by revert hd₂ hlo₂; cases τ₂.Q.paint i j <;> simp [DRCSymbol.layerOrd]
          rw [hs₁, hs₂]
      · rw [τ₁.Q.paint_outside i j hm₁, τ₂.Q.paint_outside i j (hshapeQ ▸ hm₁)]
    · have key := hddR i (j - 1)
      simp only [doubleDescent_B_paintR] at key
      rw [show j - 1 + 1 = j from by omega] at key
      have h1 : ¬i < dotScolLen τ₁.P j := by
        have := hPQ τ₁ hγ₁ j; omega
      have h2 : ¬i < dotScolLen τ₁.Q j := hQ
      have h3 : ¬i < dotScolLen τ₂.P j := hdsP_j ▸ h1
      have h4 : ¬i < dotScolLen τ₂.Q j := by omega
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4] at key
      exact key

/-! ### Prop 10.9 with double descent -/

/-- **Proposition 10.9** ([BMSZb]) for D type, double descent version:
    τ ↦ (∇²τ, (p_τ, q_τ), ε_τ) is injective on PBP_D(Ǒ).

    ∇²τ is the D→C→D double descent (doubleDescent_D_paintL).
    Same ∇² + same (p,q,ε) → same τ. -/
theorem ddescent_inj_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdd : ∀ i j, doubleDescent_D_paintL τ₁ i j = doubleDescent_D_paintL τ₂ i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) :=
  descent_inj_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ
    (ddescent_D_determines_single τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdd)
    hsig heps

/-- **Proposition 10.9** ([BMSZb]) for B type, double descent version:
    τ ↦ (∇²τ, (p_τ, q_τ), ε_τ) is injective on PBP_B(Ǒ) for fixed γ.

    ∇²τ is the B→M→B double descent (doubleDescent_B_paintL, doubleDescent_B_paintR).
    Same γ + same ∇² + same (p,q,ε) → same τ.
    The hypothesis γ₁ = γ₂ is necessary: B⁺ vs B⁻ introduces a ±1 offset
    in the signature that cannot be recovered from (p,q,ε) alone.

    **Informal proof sketch**:
    Step 0: ∇² determines P and Q on columns ≥ 1 (ddescent_B_determines_colsGe1).
    Step 1: P col 0 agrees. B-type P has {•,c}. Let nc = #c in P col 0 ∈ {0,1}.
      From dotDiag_eq (P.dot = Q.dot) + countSym decomposition + ge1 agreement:
        (*) nc₁ + bq₁ = nc₂ + bq₂  where bq = #• in Q col 0.
      From signature p-equation + P col 0 total (dot + c = colLen) + ge1 cancellation:
        (**) bq₁ + 2·nr₁ = bq₂ + 2·nr₂  where nr = #r in Q col 0.
      Subtracting: 2·nr₁ + nc₂ = 2·nr₂ + nc₁, i.e. 2·δ_r = δ_c.
      Since |δ_c| ≤ 1 (nc ∈ {0,1}) and 2|δ_r| = |δ_c|, we get δ_c = 0, δ_r = 0.
      Then monotone_col_unique gives P col 0 pointwise.
    Step 2: Q col 0 from descent_inj_col0_B (which needs P fully determined). -/
theorem ddescent_inj_B (τ₁ τ₂ : PBP)
    (hγ : τ₁.γ = .Bplus ∨ τ₁.γ = .Bminus)
    (hγ_eq : τ₁.γ = τ₂.γ)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (_hinterl₁ : ∀ j, dotScolLen τ₁.P j ≥ dotScolLen τ₁.Q (j + 1))
    (_hinterl₂ : ∀ j, dotScolLen τ₂.P j ≥ dotScolLen τ₂.Q (j + 1))
    (hddL : ∀ i j, doubleDescent_B_paintL τ₁ i j = doubleDescent_B_paintL τ₂ i j)
    (hddR : ∀ i j, doubleDescent_B_paintR τ₁ i j = doubleDescent_B_paintR τ₂ i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) := by
  -- Derive hγ₂ from hγ and hγ_eq
  have hγ₁ := hγ
  have hγ₂ : τ₂.γ = .Bplus ∨ τ₂.γ = .Bminus := hγ_eq ▸ hγ
  -- ∇² gives P cols ≥ 1 and Q cols ≥ 1.
  have ⟨hP_ge1, hQ_ge1⟩ := ddescent_B_determines_colsGe1 τ₁ τ₂ hγ₁ hγ₂
    hshapeP hshapeQ hddL hddR
  -- P col 0 for B type: {dot, c}. Use tail_counts_arith on joint P+Q col 0 system.
  -- From sig: 2*δ_r + δ_d - δ_c = 0 where δ_c = P.c_col0₁ - P.c_col0₂ ∈ {-1,0,1}.
  -- Since |δ_c| ≤ 1 and 2|δ_r| = |δ_c|: δ_r = 0, δ_c = 0.
  -- Then P col 0 determined, and descent_inj_col0_B gives Q col 0.
  -- Step 1: P col 0 agreement. B type P has {dot, c} in col 0.
  -- Both non-dot cells are c (P_nonDot_eq_c_of_B). Layer monotonicity: dots first, then c.
  -- P₁ and P₂ col 0 agree iff they have the same number of c's (0 or 1).
  -- The number of c's is determined by parity of signature residual.
  -- For now we use a direct argument via countCol0.
  -- P col 0: B type P has {dot, c}. Layer monotone: dots [0, a), c at a (if any).
  -- a = P.colLen(0) - P.c_col0_count. Since col_c_P: at most one c.
  -- Use monotone_col_unique on P col 0 with the known P cols ≥ 1 + sig + eps.
  -- Concretely: both P₁ and P₂ have the same signature residual for col 0,
  -- and tail_counts_arith (with n_c playing the central role, |δ_c| ≤ 1,
  -- and 2*δ_r = δ_c from the weighted sum) gives all counts equal.
  -- Then monotone_col_unique gives pointwise agreement.
  -- We inline this as: P(i,0) ∈ {dot, c}. Layer mono + same c-count → same paint.
  -- The c-count in col 0 is determined because col_c_P gives at most 1.
  -- The c-count agreement follows from tail_counts_arith on the combined P+Q col 0.
  -- For simplicity, we prove P col 0 using the D-type Prop 10.9 infrastructure
  -- applied to P (with the roles reversed: P has a simple 2-symbol col 0).
  --
  -- Actually the SIMPLEST approach: P col 0 has {dot, c}. monotone_col_unique on
  -- P col 0 with a = 0 (all of col 0). Need same count of each symbol.
  -- n_dot + n_c = P.colLen(0) (same from shapes). n_c ∈ {0, 1}.
  -- n_dot₁ = n_dot₂ iff n_c₁ = n_c₂. And n_c is determined by P.countSym(.c):
  -- P.countSym(.c) = P.c_col0 + P.c_ge1. P.c_ge1 known (P cols ≥ 1).
  -- P.countSym(.c) = P.card - P.countSym(.dot) (B type: only dot and c).
  -- P.card is shape-determined. P.countSym(.dot) = dotDiag(P).card = dotDiag(Q).card.
  -- dotDiag(Q).card = Q.countSym(.dot) depends on Q col 0 (unknown).
  -- Circular! So we CAN'T determine P.c_col0 from shapes alone.
  -- We NEED signature. Use the Finset decomposition approach from tail_counts_eq_D.
  -- For the proof: extract the signature equation, decompose into col0 + colsGe1,
  -- show col0 contribution determines n_c via parity (tail_counts_arith).
  -- This requires ~30 lines. Apply tail_counts_arith with:
  -- htot: ns₁+nr₁+nc₁+nd₁ = ns₂+nr₂+nc₂+nd₂ (total non-dot in P+Q col 0)
  -- hwr: 2nr₁+nc₁+nd₁ = 2nr₂+nc₂+nd₂ (from p-equation col0 residual)
  -- hnd: nd₁ = nd₂ (from epsilon)
  -- hc1, hc2: nc ≤ 1 (col_c_P)
  -- Here ns = Q.s_col0, nr = Q.r_col0, nc = P.c_col0, nd = Q.d_col0.
  -- This gives ns₁=ns₂, nr₁=nr₂, nc₁=nc₂. Then P col 0 and Q col 0 agree.
  -- For full formalization we would need the Finset decomposition of signature
  -- into col 0 and cols ≥ 1 contributions for BOTH P and Q.
  -- This is substantial but follows the exact same pattern as tail_counts_eq_D.
  -- We defer to descent_inj_col0_B by first establishing P col 0 agreement
  -- through the n_c determination, then using the existing Q col 0 theorem.
  --
  -- P col 0 determination via the monotone + counting argument:
  have hP : ∀ i j, τ₁.P.paint i j = τ₂.P.paint i j := by
    intro i j
    by_cases hj : 1 ≤ j
    · exact hP_ge1 i j hj
    · push_neg at hj
      have hj0 : j = 0 := by omega
      subst hj0
      -- j = 0: P col 0 for B type has {dot, c}, monotone, at most one c.
      -- Derive nc₁ = nc₂ from signature parity, then monotone_col_unique.
      set b := τ₁.P.shape.colLen 0 with hb_def
      have hb_eq : τ₂.P.shape.colLen 0 = b := congr_arg (YoungDiagram.colLen · 0) hshapeP.symm
      by_cases hi : i < b
      · -- Inside P.shape: derive countCol0 agreement then monotone_col_unique
        -- s, r, d counts are 0 in B-type P col 0
        have hzero : ∀ (τ : PBP), (τ.γ = .Bplus ∨ τ.γ = .Bminus) →
            ∀ σ : DRCSymbol, σ ≠ .dot → σ ≠ .c →
            countCol0 τ.P.paint σ 0 (τ.P.shape.colLen 0) = 0 :=
          fun τ hγ σ hσ₁ hσ₂ => countCol0_eq_zero_of_ne _ _ _ _ fun k hk hpk => by
            simp only [Nat.zero_add] at hpk
            have hmem : (k, 0) ∈ τ.P.shape := YoungDiagram.mem_iff_lt_colLen.mpr hk
            by_cases hd : τ.P.paint k 0 = .dot
            · exact hσ₁ (hpk ▸ hd)
            · exact hσ₂ (hpk ▸ P_nonDot_eq_c_of_B τ hγ k 0 hmem hd)
        -- P.countSym .dot = Q.countSym .dot (dotDiag_eq)
        have hPQ_dot (τ : PBP) : τ.P.countSym .dot = τ.Q.countSym .dot := by
          show (dotDiag τ.P τ.mono_P).cells.card = (dotDiag τ.Q τ.mono_Q).cells.card
          rw [dotDiag_eq]
        -- Collect equalities for the parity argument
        -- P.countSym σ agrees for cols ≥ 1
        have hPc_ge1 := countSymColGe1_eq τ₁.P τ₂.P hshapeP hP_ge1 .c
        have hQd_ge1 := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .dot
        have hQr_ge1 := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .r
        have hQdd_ge1 := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .d
        -- Decomposition: countSym = col0 + colGe1
        have hPc1 := countSym_split τ₁.P .c
        have hPc2 := countSym_split τ₂.P .c
        have hQd1 := countSym_split τ₁.Q .dot
        have hQd2 := countSym_split τ₂.Q .dot
        have hQr1 := countSym_split τ₁.Q .r
        have hQr2 := countSym_split τ₂.Q .r
        have hQdd1 := countSym_split τ₁.Q .d
        have hQdd2 := countSym_split τ₂.Q .d
        -- B-type zeros
        have hPr1 := P_countSym_zero_of_B τ₁ hγ₁ .r ⟨by decide, by decide⟩
        have hPd1 := P_countSym_zero_of_B τ₁ hγ₁ .d ⟨by decide, by decide⟩
        have hQc1 := Q_countSym_c_zero_of_B τ₁ hγ₁
        have hPr2 := P_countSym_zero_of_B τ₂ hγ₂ .r ⟨by decide, by decide⟩
        have hPd2 := P_countSym_zero_of_B τ₂ hγ₂ .d ⟨by decide, by decide⟩
        have hQc2 := Q_countSym_c_zero_of_B τ₂ hγ₂
        -- P.dot = Q.dot
        have hPQd1 := hPQ_dot τ₁
        have hPQd2 := hPQ_dot τ₂
        -- Extract signature
        have hsig1 := congr_arg Prod.fst hsig
        simp only [PBP.signature] at hsig1
        -- countSymCol0(Q, .d) agrees (from epsilon)
        have hP_no_d (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) :
            τ.P.hasDInCol0 = false := by
          simp only [PaintedYoungDiagram.hasDInCol0, decide_eq_false_iff_not,
            Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
          intro ⟨r, c⟩ hmem
          rw [YoungDiagram.mem_cells] at hmem
          simp only [not_and]
          intro hc; subst hc
          have := P_nonDot_eq_c_of_B τ hγ r 0 hmem
          intro heq
          have := this (heq ▸ DRCSymbol.noConfusion)
          rw [this] at heq; exact DRCSymbol.noConfusion heq
        have hQd_agree : τ₁.Q.hasDInCol0 = τ₂.Q.hasDInCol0 := by
          simp only [PBP.epsilon, hP_no_d τ₁ hγ₁, hP_no_d τ₂ hγ₂, Bool.false_or] at heps
          revert heps; cases τ₁.Q.hasDInCol0 <;> cases τ₂.Q.hasDInCol0 <;> simp
        have hQd_col0 : countSymCol0 τ₁.Q .d = countSymCol0 τ₂.Q .d := by
          -- countSymCol0 Q .d ∈ {0, 1} and hasDInCol0 agrees
          rw [countSymCol0_eq_countCol0, countSymCol0_eq_countCol0]
          have hle1 := countCol0_le_one_of_unique τ₁.Q.paint .d 0 (τ₁.Q.shape.colLen 0) (τ₁.col_d_Q 0)
          have hle2 := countCol0_le_one_of_unique τ₂.Q.paint .d 0 (τ₂.Q.shape.colLen 0) (τ₂.col_d_Q 0)
          have hbr1 := hasDInCol0_iff_countCol0_pos τ₁.Q
          have hbr2 := hasDInCol0_iff_countCol0_pos τ₂.Q
          have hpos_iff : (0 < countCol0 τ₁.Q.paint .d 0 (τ₁.Q.shape.colLen 0)) ↔
                          (0 < countCol0 τ₂.Q.paint .d 0 (τ₂.Q.shape.colLen 0)) := by
            constructor
            · intro h1; exact hbr2.mp (hQd_agree ▸ hbr1.mpr h1)
            · intro h2; exact hbr1.mp (hQd_agree.symm ▸ hbr2.mpr h2)
          rcases Nat.eq_zero_or_pos (countCol0 τ₁.Q.paint .d 0 (τ₁.Q.shape.colLen 0)) with h1 | h1
          · have : ¬(0 < countCol0 τ₂.Q.paint .d 0 (τ₂.Q.shape.colLen 0)) := by
              intro h2; have := hpos_iff.mpr h2; omega
            omega
          · have h2 := hpos_iff.mp h1; omega
        -- nc ≤ 1
        have hc1 : countSymCol0 τ₁.P .c ≤ 1 := by
          rw [countSymCol0_eq_countCol0]
          exact countCol0_le_one_of_unique _ _ _ _ (τ₁.col_c_P 0)
        have hc2 : countSymCol0 τ₂.P .c ≤ 1 := by
          rw [countSymCol0_eq_countCol0]
          exact countCol0_le_one_of_unique _ _ _ _ (τ₂.col_c_P 0)
        -- Parity argument: 2·δ_r = δ_c with |δ_c| ≤ 1 forces δ_c = 0.
        -- Step (i): P col 0 total for B type: dot_col0 + c_col0 = colLen
        have hPtot₁ : countSymCol0 τ₁.P .dot + countSymCol0 τ₁.P .c = b := by
          have h1 := countSymCol0_eq_countCol0 τ₁.P .dot
          have h2 := countSymCol0_eq_countCol0 τ₁.P .c
          have hb' : τ₁.P.shape.colLen 0 = b := hb_def.symm
          rw [hb'] at h1 h2
          have h3 := countCol0_total τ₁.P.paint 0 b
          rw [hzero τ₁ hγ₁ .s (by decide) (by decide),
              hzero τ₁ hγ₁ .r (by decide) (by decide),
              hzero τ₁ hγ₁ .d (by decide) (by decide)] at h3
          omega
        have hPtot₂ : countSymCol0 τ₂.P .dot + countSymCol0 τ₂.P .c = b := by
          have h1 := countSymCol0_eq_countCol0 τ₂.P .dot
          have h2 := countSymCol0_eq_countCol0 τ₂.P .c
          rw [hb_eq] at h1 h2
          have h3 := countCol0_total τ₂.P.paint 0 (τ₂.P.shape.colLen 0)
          rw [hzero τ₂ hγ₂ .s (by decide) (by decide),
              hzero τ₂ hγ₂ .r (by decide) (by decide),
              hzero τ₂ hγ₂ .d (by decide) (by decide)] at h3
          rw [hb_eq] at h3; omega
        -- Step (ii): P.dot decomposition + ge1 agreement
        have hPdot1 := countSym_split τ₁.P .dot
        have hPdot2 := countSym_split τ₂.P .dot
        have hPdge1 := countSymColGe1_eq τ₁.P τ₂.P hshapeP hP_ge1 .dot
        -- Step (iii): equation (*): nc₁ + bq₁ = nc₂ + bq₂
        --   from P.dot = Q.dot (dotDiag_eq) + P col 0 total + ge1 agreement
        have h_star : countSymCol0 τ₁.P .c + countSymCol0 τ₁.Q .dot =
            countSymCol0 τ₂.P .c + countSymCol0 τ₂.Q .dot := by
          have hQdot1 := countSym_split τ₁.Q .dot
          have hQdot2 := countSym_split τ₂.Q .dot
          have hQdge1 := countSymColGe1_eq τ₁.Q τ₂.Q hshapeQ hQ_ge1 .dot
          omega
        -- Step (iv): equation (**): bq₁ + 2·nr₁ = bq₂ + 2·nr₂
        --   from signature p-equation + P col 0 total + ge1 cancellation
        have h_starstar : countSymCol0 τ₁.Q .dot + 2 * countSymCol0 τ₁.Q .r =
            countSymCol0 τ₂.Q .dot + 2 * countSymCol0 τ₂.Q .r := by
          -- Case-split on γ to resolve the match in signature
          rcases hγ₁ with hg | hg <;> (
            have hg₂ := show τ₂.γ = _ from hγ_eq ▸ hg
            simp only [hg, hg₂] at hsig1
            simp (config := { decide := true }) only [ite_true, ite_false] at hsig1
            rw [hPr1, hPd1, hQc1, hPr2, hPd2, hQc2] at hsig1
            simp only [Nat.zero_add, Nat.add_zero] at hsig1
            rw [hPc1, hPc2, hQd1, hQd2, hQr1, hQr2, hQdd1, hQdd2,
                hPdot1, hPdot2] at hsig1
            omega)
        -- Step (v): from (*) and (**): 2·nr₁ + nc₂ = 2·nr₂ + nc₁
        -- with nc ≤ 1: nc₁ = nc₂ (LHS-RHS parity forces equality)
        have hnc : countSymCol0 τ₁.P .c = countSymCol0 τ₂.P .c := by omega
        -- Convert to countCol0 agreement
        have hnc' : countCol0 τ₁.P.paint .c 0 b = countCol0 τ₂.P.paint .c 0 b := by
          have h1 := countSymCol0_eq_countCol0 τ₁.P .c
          have h2 := countSymCol0_eq_countCol0 τ₂.P .c
          rw [hb_eq] at h2; rw [← h1, ← h2]; exact hnc
        -- All 5 symbol counts agree in [0, b)
        have hzero₁ : ∀ σ : DRCSymbol, σ ≠ .dot → σ ≠ .c →
            countCol0 τ₁.P.paint σ 0 b = 0 := fun σ hσ₁ hσ₂ => hzero τ₁ hγ₁ σ hσ₁ hσ₂
        have hzero₂ : ∀ σ : DRCSymbol, σ ≠ .dot → σ ≠ .c →
            countCol0 τ₂.P.paint σ 0 b = 0 := fun σ hσ₁ hσ₂ =>
          hb_eq ▸ hzero τ₂ hγ₂ σ hσ₁ hσ₂
        have hcounts : ∀ σ, countCol0 τ₁.P.paint σ 0 b = countCol0 τ₂.P.paint σ 0 b := by
          intro σ; cases σ with
          | c => exact hnc'
          | s => rw [hzero₁ .s (by decide) (by decide), hzero₂ .s (by decide) (by decide)]
          | r => rw [hzero₁ .r (by decide) (by decide), hzero₂ .r (by decide) (by decide)]
          | d => rw [hzero₁ .d (by decide) (by decide), hzero₂ .d (by decide) (by decide)]
          | dot =>
            have h1 := countCol0_total τ₁.P.paint 0 b
            have h2 := countCol0_total τ₂.P.paint 0 b
            rw [hzero₁ .s (by decide) (by decide), hzero₁ .r (by decide) (by decide),
                hzero₁ .d (by decide) (by decide)] at h1
            rw [hzero₂ .s (by decide) (by decide), hzero₂ .r (by decide) (by decide),
                hzero₂ .d (by decide) (by decide)] at h2
            omega
        -- Apply monotone_col_unique
        have heq := monotone_col_unique τ₁.P.paint τ₂.P.paint 0 b b (by omega)
          (fun i₁ i₂ h hlt => col0_layerOrd_mono τ₁ h
            (YoungDiagram.mem_iff_lt_colLen.mpr hlt))
          (fun i₁ i₂ h hlt => col0_layerOrd_mono τ₂ h
            (YoungDiagram.mem_iff_lt_colLen.mpr (hshapeP ▸ hlt)))
          hcounts i (by omega)
        simp only [Nat.zero_add] at heq
        exact heq
      · -- Outside P.shape
        push_neg at hi
        exact descent_col0_outside τ₁ τ₂ hshapeP hi
  -- Step 2: Q col 0 from descent_inj_col0_B (which needs P fully)
  constructor
  · exact hP
  · intro i j
    by_cases hj : j = 0
    · subst hj; exact descent_inj_col0_B τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hP hQ_ge1 hsig heps i
    · exact hQ_ge1 i j (by omega)

end PBP
