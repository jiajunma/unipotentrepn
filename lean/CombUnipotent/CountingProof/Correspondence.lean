/-
# DualPart ↔ YoungDiagram correspondence for D-type

The key lemma `colLens_shiftLeft` connects `shiftLeft` to `List.tail`, and the
top-level theorem `card_PBPSet_D_eq_countPBP_D` states that for any (μP, μQ)
whose colLens match the dp-derived colLens, the fiber count equals `countPBP_D dp`.
-/
import CombUnipotent.CountingProof.LiftRC
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

open Classical

/-! ## `shiftLeft` as `tail` on `colLens` -/

namespace YoungDiagram

/-- `(shiftLeft μ).rowLen 0 = μ.rowLen 0 - 1`. -/
lemma rowLen_zero_shiftLeft (μ : YoungDiagram) :
    μ.shiftLeft.rowLen 0 = μ.rowLen 0 - 1 := by
  by_cases h : μ.rowLen 0 = 0
  · rw [h]
    simp only [Nat.zero_sub]
    by_contra hne
    have hp : 0 < μ.shiftLeft.rowLen 0 := Nat.pos_of_ne_zero hne
    have hmem : (0, 0) ∈ μ.shiftLeft := mem_iff_lt_rowLen.mpr hp
    rw [mem_shiftLeft] at hmem
    have hr : 0 + 1 < μ.rowLen 0 := mem_iff_lt_rowLen.mp hmem
    omega
  · have h_pos : 0 < μ.rowLen 0 := Nat.pos_of_ne_zero h
    apply le_antisymm
    · by_contra hc
      push_neg at hc
      have hge : μ.shiftLeft.rowLen 0 ≥ μ.rowLen 0 := by omega
      have hmem : (0, μ.rowLen 0 - 1) ∈ μ.shiftLeft := by
        apply mem_iff_lt_rowLen.mpr
        omega
      rw [mem_shiftLeft] at hmem
      have : μ.rowLen 0 - 1 + 1 < μ.rowLen 0 := mem_iff_lt_rowLen.mp hmem
      omega
    · by_contra hc
      push_neg at hc
      by_cases hge2 : μ.rowLen 0 ≥ 2
      · have hmem_orig : (0, μ.rowLen 0 - 1) ∈ μ :=
          mem_iff_lt_rowLen.mpr (by omega)
        have hmem_shift : (0, μ.rowLen 0 - 2) ∈ μ.shiftLeft := by
          rw [mem_shiftLeft]
          have : μ.rowLen 0 - 2 + 1 = μ.rowLen 0 - 1 := by omega
          rw [this]
          exact hmem_orig
        have : μ.rowLen 0 - 2 < μ.shiftLeft.rowLen 0 := mem_iff_lt_rowLen.mp hmem_shift
        omega
      · have : μ.rowLen 0 = 1 := by omega
        rw [this] at hc
        omega

/-- `(shiftLeft μ).colLens = μ.colLens.tail`. -/
lemma colLens_shiftLeft (μ : YoungDiagram) :
    μ.shiftLeft.colLens = μ.colLens.tail := by
  apply List.ext_getElem
  · rw [length_colLens, rowLen_zero_shiftLeft, List.length_tail, length_colLens]
  · intro j h1 h2
    rw [getElem_colLens h1, colLen_shiftLeft]
    rw [List.getElem_tail]
    rw [getElem_colLens]

end YoungDiagram

/-! ## dp-recursion lemmas

We use a custom well-founded recursion on `dp.length` to avoid complex pattern
matching on dp structure. -/

/-- Helper: when dp = `r₁ :: r₂ :: rest`, `dpartColLensP_D dp = (r₁+1)/2 :: dpartColLensP_D rest`. -/
lemma dpartColLensP_D_cons₂_eq (r₁ r₂ : ℕ) (rest : DualPart) :
    dpartColLensP_D (r₁ :: r₂ :: rest) = (r₁ + 1) / 2 :: dpartColLensP_D rest := rfl

lemma dpartColLensQ_D_cons₂_pos (r₁ r₂ : ℕ) (rest : DualPart) (h : r₂ > 1) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = (r₂ - 1) / 2 :: dpartColLensQ_D rest := by
  simp [dpartColLensQ_D, h]

lemma dpartColLensQ_D_cons₂_neg (r₁ r₂ : ℕ) (rest : DualPart) (h : ¬ r₂ > 1) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = dpartColLensQ_D rest := by
  simp [dpartColLensQ_D, h]

/-! ## Top-level D theorem in dp form

We prove the final correspondence: for any (μP, μQ) matching the dp-derived colLens,
`Fintype.card (PBPSet .D μP μQ) = countPBP_D dp` sum.

The proof works by induction on `μP.rowLen 0` (which equals `dp.length / 2` rounded up
for dp-derived shapes), using the step theorems at each level. -/

/-- The sum of a triple. -/
def tripleSum (t : ℕ × ℕ × ℕ) : ℕ := t.1 + t.2.1 + t.2.2

/-- `countPBP_D [] = (1, 0, 0)` ⇒ sum is 1. -/
lemma tripleSum_countPBP_D_nil : tripleSum (countPBP_D []) = 1 := by
  simp [tripleSum, countPBP_D]


/-- Base case: `countPBP_D []` has sum 1. -/
lemma tripleSum_countPBP_D_empty : tripleSum (countPBP_D []) = 1 := rfl

/-- `μ.colLens = []` implies `μ.rowLen 0 = 0`, which implies `μ = ⊥`. -/
lemma yd_of_colLens_nil {μ : YoungDiagram} (h : μ.colLens = []) : μ = ⊥ := by
  have h_row : μ.rowLen 0 = 0 := by
    have hlen : μ.colLens.length = μ.rowLen 0 := YoungDiagram.length_colLens μ
    rw [h] at hlen; simpa using hlen.symm
  -- From μ.rowLen 0 = 0, (0, 0) ∉ μ (since rowLen 0 = 0 means row 0 is empty).
  -- By isLowerSet, every cell is ≤ (0, j) for some j, but row 0 has no cells.
  -- Conclude μ is empty.
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  constructor
  · intro hmem
    exfalso
    have h_lower : (0, j) ∈ μ := by
      apply μ.isLowerSet (show ((0, j) : ℕ × ℕ) ≤ (i, j) from ?_) hmem
      exact ⟨Nat.zero_le _, le_refl _⟩
    have : j < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp h_lower
    omega
  · intro hmem; exact absurd hmem (YoungDiagram.notMem_bot _)

/-- When both colLens are nil, both YDs are ⊥. -/
lemma card_PBPSet_D_bot_case {μP μQ : YoungDiagram}
    (hP : μP.colLens = []) (hQ : μQ.colLens = []) :
    Fintype.card (PBPSet .D μP μQ) = 1 := by
  rw [yd_of_colLens_nil hP, yd_of_colLens_nil hQ, card_PBPSet_bot]

/-! ## Main correspondence theorem

For a sorted DualPart `dp` with all entries ≥ 3 (ensuring `dpartColLensQ_D` always
adds an entry per pair), and YDs `(μP, μQ)` with matching `colLens`, the fiber count
equals `countPBP_D dp` sum.

The restriction `r ≥ 3` avoids the edge case `r₂ = 1` where `dpartColLensQ_D` drops
the Q column, causing shiftLeft mismatch. For standard D-type partitions where all
parts are ≥ 3, the theorem gives the full correspondence. -/

/-- The key correspondence: μP matches dp's P colLens ⇒ shiftLeft μP matches rest. -/
lemma colLens_eq_tail {μP : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (hP : μP.colLens = dpartColLensP_D (r₁ :: r₂ :: rest)) :
    μP.shiftLeft.colLens = dpartColLensP_D rest := by
  rw [YoungDiagram.colLens_shiftLeft, hP, dpartColLensP_D_cons₂_eq]
  rfl

/-- Similar for μQ when r₂ > 1. -/
lemma colLens_eq_tail_Q {μQ : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (h : r₂ > 1) (hQ : μQ.colLens = dpartColLensQ_D (r₁ :: r₂ :: rest)) :
    μQ.shiftLeft.colLens = dpartColLensQ_D rest := by
  rw [YoungDiagram.colLens_shiftLeft, hQ, dpartColLensQ_D_cons₂_pos _ _ _ h]
  rfl

/-- `colLens = []` from a non-empty `dpartColLensP_D` list is impossible. -/
lemma dpartColLensP_D_singleton (r : ℕ) :
    dpartColLensP_D [r] = [(r + 1) / 2] := rfl

/-- `dpartColLensQ_D [r] = []`. -/
lemma dpartColLensQ_D_singleton (r : ℕ) : dpartColLensQ_D [r] = [] := rfl

/-- `μP.rowLen 0` equals `dp.length / 2 + dp.length % 2` for dp-derived shapes.
    For dp of length `2m + r` (r ∈ {0, 1}), μP has `m + r` columns. -/
lemma rowLen_zero_eq_length_P {μP : YoungDiagram} {dp : DualPart}
    (hP : μP.colLens = dpartColLensP_D dp) :
    μP.rowLen 0 = (dpartColLensP_D dp).length := by
  rw [← YoungDiagram.length_colLens μP, hP]

/-- Length of `dpartColLensP_D` for a 2-cons: adds 1. -/
lemma dpartColLensP_D_length_cons₂ (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensP_D (r₁ :: r₂ :: rest)).length = (dpartColLensP_D rest).length + 1 := by
  rw [dpartColLensP_D_cons₂_eq]
  rfl

/-! ## `card_D_aux` ↔ `countPBP_D` matching

We prove that for dp-derived (μP, μQ), `card_D_aux n μP μQ` equals `tripleSum (countPBP_D dp)`
by strong induction on dp length. -/

/-- Helper: `dpartColLensP_D` length for a dp with at least 2 elements. -/
lemma dpartColLensP_D_length_cons₂_mem (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensP_D (r₁ :: r₂ :: rest)).length = 1 + (dpartColLensP_D rest).length := by
  rw [dpartColLensP_D_length_cons₂]; omega



/-- If μ.colLens starts with `a`, then `μ.colLen 0 = a`. -/
lemma colLen_0_eq_of_colLens_cons {μ : YoungDiagram} {a : ℕ} {tail : List ℕ}
    (h : μ.colLens = a :: tail) : μ.colLen 0 = a := by
  have h_len : 0 < μ.colLens.length := by rw [h]; simp
  have h_get : μ.colLens[0]'h_len = μ.colLen 0 := YoungDiagram.getElem_colLens h_len
  have h_first : μ.colLens[0]'h_len = a := by
    -- Use List.getElem_cons_zero with a cast through h
    have h' : μ.colLens[0]?.getD 0 = a := by rw [h]; rfl
    have h_some : μ.colLens[0]? = some (μ.colLens[0]'h_len) := by
      exact List.getElem?_eq_getElem h_len
    rw [h_some] at h'
    simpa using h'
  omega

/-- Helper: `μP.colLen 0 = (r₁ + 1) / 2` when μP.colLens matches dp's P with cons₂. -/
lemma colLen_0_of_dp_cons₂ {μP : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (hP : μP.colLens = dpartColLensP_D (r₁ :: r₂ :: rest)) :
    μP.colLen 0 = (r₁ + 1) / 2 :=
  colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)

/-- Helper: `μQ.colLen 0 = (r₂ - 1) / 2` when μQ.colLens matches dp's Q with r₂ > 1. -/
lemma colLen_0_of_dp_cons₂_Q {μQ : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (h : r₂ > 1) (hQ : μQ.colLens = dpartColLensQ_D (r₁ :: r₂ :: rest)) :
    μQ.colLen 0 = (r₂ - 1) / 2 :=
  colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_D_cons₂_pos _ _ _ h])

/-! ## Main theorem: card matches countPBP_D

Under the assumption that all entries of dp are ≥ 3 (avoiding the r₂ = 1 edge case),
we prove the complete correspondence. -/

/-- When all dp entries are ≥ 3, dpartColLensQ_D always uses the positive branch. -/
lemma dpartColLensQ_D_cons₂_ge3 (r₁ r₂ : ℕ) (rest : DualPart) (h : r₂ ≥ 3) :
    dpartColLensQ_D (r₁ :: r₂ :: rest) = (r₂ - 1) / 2 :: dpartColLensQ_D rest := by
  rw [dpartColLensQ_D_cons₂_pos]; omega

/-- For sorted dp with all entries ≥ 3, taking `rest` preserves ≥ 3. -/
lemma all_ge3_tail₂ {r₁ r₂ : ℕ} {rest : DualPart} (h : ∀ r ∈ r₁ :: r₂ :: rest, r ≥ 3) :
    ∀ r ∈ rest, r ≥ 3 :=
  fun r hr => h r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

/-- For sorted dp, the tail is sorted. -/
lemma sorted_tail₂ {r₁ r₂ : ℕ} {rest : DualPart}
    (h : (r₁ :: r₂ :: rest).SortedGE) : rest.SortedGE := by
  have hp := h.pairwise
  have h1 : (r₂ :: rest).Pairwise (· ≥ ·) := (List.pairwise_cons.mp hp).2
  exact ((List.pairwise_cons.mp h1).2).sortedGE

/-! ## Triple-valued per-tc step theorems (with sorry for gaps)

The triple `(dd, rc, ss)` from `countPBP_D` matches `(card(PBPSet_tc DD), card(PBPSet_tc RC),
card(PBPSet_tc SS))` at each recursive step. -/

/-- **Gap 1 (technical)**: Primitive per-tc step.
    Proved from `card_PBPSet_D_primitive_step` + IH on total. -/
theorem card_PBPSet_D_primitive_tripleSum {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0)
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0) :
    Fintype.card (PBPSet .D μP μQ) =
      Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft) *
        tripleSum (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).1 := by
  rw [tripleSum]
  exact card_PBPSet_D_primitive_step _ h_prim rfl hQP hk_pos

/-- **Gap 2 (main technical gap)**: Balanced per-tc step.
    Needs: `card(PBPSet_tc DD shifted) = dd'` and `card(PBPSet_tc RC shifted) = rc'`
    from the inductive triple. This requires per-tc fiber analysis for RC_sub σ. -/
theorem card_PBPSet_D_balanced_tripleSum {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0)
    (h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1)
    (dd' rc' ss' : ℕ)
    (h_dd : dd' = Fintype.card (PBPSet_tc .D μP.shiftLeft μQ.shiftLeft .DD))
    (h_rc : rc' = Fintype.card (PBPSet_tc .D μP.shiftLeft μQ.shiftLeft .RC))
    (h_ss : ss' = Fintype.card (PBPSet_tc .D μP.shiftLeft μQ.shiftLeft .SS))
    (h_total : dd' + rc' + ss' =
        Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft)) :
    let k := μP.colLen 0 - μQ.colLen 0
    let ((tDD, tRC, tSS), (scDD, scRC, scSS)) := tailCoeffs k
    Fintype.card (PBPSet .D μP μQ) =
      dd' * (tDD + tRC + tSS) + rc' * (scDD + scRC + scSS) := by
  rw [h_dd, h_rc]
  simp only [PBPSet_tc, Fintype.card_subtype]
  exact card_PBPSet_D_balanced_step _ h_bal rfl hQP hk_pos

/-! ## Main theorem: dp → card matching -/

/-! Main theorem: For sorted dp with all entries ≥ 3,
    `card(PBPSet .D μP μQ) = tripleSum(countPBP_D dp)`.

    Sorries: singleton (arithmetic), pair step (balanced triple match). -/

/-- Base case: dp = []. -/
theorem card_PBPSet_D_eq_tripleSum_nil {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_D [])
    (hQ : μQ.colLens = dpartColLensQ_D []) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D []) := by
  have hP' : μP.colLens = [] := by rw [hP]; rfl
  have hQ' : μQ.colLens = [] := by rw [hQ]; rfl
  rw [yd_of_colLens_nil hP', yd_of_colLens_nil hQ']
  simp [tripleSum, countPBP_D, card_PBPSet_bot]

/-- `⊥.colLen j = 0` for all j. -/
lemma colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 := by
  by_contra h
  have h_pos := Nat.pos_of_ne_zero h
  have := YoungDiagram.mem_iff_lt_colLen.mpr h_pos
  exact YoungDiagram.notMem_bot _ this

/-- `⊥.rowLen j = 0`. -/
lemma rowLen_bot (j : ℕ) : (⊥ : YoungDiagram).rowLen j = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot _ (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))

/-- `⊥.colLens = []`. -/
lemma colLens_bot : (⊥ : YoungDiagram).colLens = [] := by
  have h := YoungDiagram.length_colLens (⊥ : YoungDiagram)
  rw [rowLen_bot] at h
  match (⊥ : YoungDiagram).colLens, h with
  | [], _ => rfl

/-- `⊥.shiftLeft = ⊥`. -/
lemma shiftLeft_bot : (⊥ : YoungDiagram).shiftLeft = ⊥ := by
  apply yd_of_colLens_nil
  rw [YoungDiagram.colLens_shiftLeft, colLens_bot]; rfl

/-- Key arithmetic: for odd n, `(n+1)/2 = n/2 + 1`. -/
lemma odd_div2_succ {n : ℕ} (h : Odd n) : (n + 1) / 2 = n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := h; omega

/-- Singleton case: dp = [r₁], always primitive with shifted = ⊥. -/
theorem card_PBPSet_D_eq_tripleSum_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_D [r₁])
    (hQ : μQ.colLens = dpartColLensQ_D [r₁])
    (hge3 : r₁ ≥ 3) (hodd : Odd r₁) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D [r₁]) := by
  have hμQ_bot : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
  subst hμQ_bot
  have hP_colLen : μP.colLen 0 = (r₁ + 1) / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)
  have h_shifted_P : μP.shiftLeft = ⊥ :=
    yd_of_colLens_nil (by rw [YoungDiagram.colLens_shiftLeft, hP]; rfl)
  have hK_eq : (r₁ + 1) / 2 = r₁ / 2 + 1 := odd_div2_succ hodd
  have hK_pos : 1 ≤ (r₁ + 1) / 2 := by obtain ⟨m, rfl⟩ := hodd; omega
  have h_prim : (⊥ : YoungDiagram).colLen 0 ≥ μP.shiftLeft.colLen 0 := by
    rw [h_shifted_P, colLen_bot]
  have h_card := card_PBPSet_D_primitive_step ((r₁ + 1) / 2) h_prim
      (by rw [hP_colLen, colLen_bot]; omega) (by rw [colLen_bot]; omega) hK_pos
  rw [h_shifted_P, shiftLeft_bot] at h_card
  rw [h_card, card_PBPSet_bot, Nat.one_mul]
  -- Goal: tailCoeffs_total((r₁+1)/2) = tripleSum(countPBP_D [r₁])
  -- countPBP_D [r₁] = (1 * tDD, 1 * tRC, 1 * tSS) with tailCoeffs(r₁/2 + 1)
  -- tripleSum = tDD + tRC + tSS with tailCoeffs(r₁/2 + 1)
  -- by hK_eq: (r₁+1)/2 = r₁/2 + 1, so same tailCoeffs
  dsimp only [countPBP_D, tripleSum]
  rw [hK_eq]; simp [Nat.one_mul, Nat.zero_add]

/-- Key arithmetic: for odd r₁ r₂, `(r₁+1)/2 - (r₂-1)/2 = (r₁-r₂)/2 + 1`. -/
lemma k_eq_of_odd {r₁ r₂ : ℕ} (h₁ : Odd r₁) (h₂ : Odd r₂) (hle : r₂ ≤ r₁) :
    (r₁ + 1) / 2 - (r₂ - 1) / 2 = (r₁ - r₂) / 2 + 1 := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; omega

theorem card_PBPSet_D_eq_tripleSum_cons₂ (r₁ r₂ : ℕ) (rest : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_D (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_D (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE) (hge3 : ∀ r ∈ r₁ :: r₂ :: rest, r ≥ 3)
    (hodd : ∀ r ∈ r₁ :: r₂ :: rest, Odd r)
    (h_ih : Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft) =
        tripleSum (countPBP_D rest))
    (h_ih_dd : rest ≠ [] → (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .DD)).card = (countPBP_D rest).1)
    (h_ih_rc : rest ≠ [] → (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).card = (countPBP_D rest).2.1) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D (r₁ :: r₂ :: rest)) := by
  have hr₁_ge3 := hge3 r₁ (by simp)
  have hr₂_ge3 := hge3 r₂ (by simp)
  have hr₁_odd := hodd r₁ (by simp)
  have hr₂_odd := hodd r₂ (by simp)
  have hr₁_ge_r₂ : r₂ ≤ r₁ := by
    have := hsort.pairwise; rw [List.pairwise_cons] at this; exact this.1 r₂ (by simp)
  have hP_colLen : μP.colLen 0 = (r₁ + 1) / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)
  have hQ_colLen : μQ.colLen 0 = (r₂ - 1) / 2 :=
    colLen_0_eq_of_colLens_cons (by
      rw [hQ, dpartColLensQ_D_cons₂_pos r₁ r₂ rest (by omega)])
  have hQP : μQ.colLen 0 ≤ μP.colLen 0 := by rw [hP_colLen, hQ_colLen]; omega
  have hK : μP.colLen 0 - μQ.colLen 0 = (r₁ - r₂) / 2 + 1 := by
    rw [hP_colLen, hQ_colLen]; exact k_eq_of_odd hr₁_odd hr₂_odd hr₁_ge_r₂
  have hK_pos : 1 ≤ μP.colLen 0 - μQ.colLen 0 := by omega
  -- Unfold countPBP_D for r₁ :: r₂ :: rest
  have h_r₃ := rest.head?.getD 0
  show Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D (r₁ :: r₂ :: rest))
  simp only [countPBP_D, tripleSum]
  -- The countPBP_D branches on r₂ > r₃
  -- We branch correspondingly on primitive vs balanced for the YD step
  by_cases h_prim_dp : r₂ > rest.head?.getD 0
  · -- Primitive case: r₂ > r₃
    rw [if_pos h_prim_dp]
    -- primitive condition on YD: μQ.colLen 0 ≥ shiftLeft μP.colLen 0
    have h_prim : μQ.colLen 0 ≥ μP.shiftLeft.colLen 0 := by
      rw [hQ_colLen]
      have h_sh := colLens_eq_tail hP
      match rest with
      | [] =>
        have h_bot := yd_of_colLens_nil (by rw [h_sh]; rfl)
        rw [h_bot, colLen_bot]; omega
      | [r₃] =>
        rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_singleton])]
        have hr₃_odd := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
        obtain ⟨a, rfl⟩ := hr₂_odd; obtain ⟨b, rfl⟩ := hr₃_odd
        simp at h_prim_dp; omega
      | r₃ :: _ :: _ =>
        rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_cons₂_eq])]
        have hr₃_odd := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
        obtain ⟨a, rfl⟩ := hr₂_odd; obtain ⟨b, rfl⟩ := hr₃_odd
        simp at h_prim_dp; omega
    have h_card := card_PBPSet_D_primitive_step (μP.colLen 0 - μQ.colLen 0)
        h_prim rfl hQP hK_pos
    rw [h_card, h_ih, hK]
    simp only [tripleSum, Nat.add_mul, Nat.mul_add]
  · -- Balanced case: r₂ ≤ r₃ (hence r₂ = r₃ by sortedness)
    rw [if_neg h_prim_dp]
    -- YD balanced condition: shiftLeft μP.colLen 0 = μQ.colLen 0 + 1
    have h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1 := by
      -- r₂ = r₃ (from ¬(r₂ > r₃) + r₂ ≥ r₃ by sortedness)
      push_neg at h_prim_dp
      have hr₂_ge_r₃ : r₂ ≥ rest.head?.getD 0 := by
        match rest with
        | [] => simp
        | r₃ :: _ =>
          simp only [List.head?_cons, Option.getD_some]
          have hp := hsort.pairwise; rw [List.pairwise_cons] at hp
          exact (List.pairwise_cons.mp hp.2).1 r₃ (by simp)
      have hr₂_eq_r₃ : r₂ = rest.head?.getD 0 := Nat.le_antisymm h_prim_dp hr₂_ge_r₃
      -- shiftLeft μP.colLen 0 = first(dpartColLensP_D rest)
      have h_sh := colLens_eq_tail hP
      match rest with
      | [] => exfalso; simp at hr₂_eq_r₃; omega
      | [r₃] =>
        rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_singleton]), hQ_colLen]
        simp at hr₂_eq_r₃
        obtain ⟨a, rfl⟩ := hr₂_odd
        obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
        omega
      | r₃ :: _ :: _ =>
        rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_cons₂_eq]), hQ_colLen]
        simp at hr₂_eq_r₃
        obtain ⟨a, rfl⟩ := hr₂_odd
        obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
        omega
    -- Apply balanced step directly
    have h_step := card_PBPSet_D_balanced_step _ h_bal rfl hQP hK_pos
    -- Need: filter counts = countPBP_D rest components (per-tc IH = Task 25)
    have h_rest_ne : rest ≠ [] := by
      intro h; subst h; simp at h_prim_dp; exact absurd hr₂_ge3 (by omega)
    have h_dd_eq := h_ih_dd h_rest_ne
    have h_rc_eq := h_ih_rc h_rest_ne
    rw [h_step, h_dd_eq, h_rc_eq, hK]; ring

/-- Primitive per-tc step: filter(tc).card = card_shifted × validCol0_tc_count.
    Uses: PBPSet_tc DD = Σ_σ fiber_tc(σ, DD) and fiber_tc constant over σ. -/
theorem card_PBPSet_D_primitive_step_tc {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0)
    (h_prim : μQ.colLen 0 ≥ μP.shiftLeft.colLen 0) (tc : TailClass) :
    Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc} =
      Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft) *
        Fintype.card {v : ValidCol0 μP μQ //
          tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = tc} :=
  card_PBPSet_D_primitive_step_tc' hQP hk_pos h_prim tc

/-- tailClassOfSymbol = DD iff symbol = .d -/
lemma tailClassOfSymbol_DD (sym : DRCSymbol) :
    tailClassOfSymbol sym = .DD ↔ sym = .d := by
  cases sym <;> simp [tailClassOfSymbol]

/-- tailClassOfSymbol = RC iff symbol ∈ {.r, .c} -/
lemma tailClassOfSymbol_RC (sym : DRCSymbol) :
    tailClassOfSymbol sym = .RC ↔ (sym = .r ∨ sym = .c) := by
  cases sym <;> simp [tailClassOfSymbol]

/-! Per-tc matching for dp.length ≥ 1: filter counts match countPBP_D components.
    Note: dp=[] doesn't satisfy per-tc (countPBP_D []=(1,0,0) but actual is (0,0,1)).
    But dp=[] never appears as rest in balanced step. -/

/-- Per-tc for singleton dp = [r₁]. -/
theorem per_tc_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_D [r₁])
    (hQ : μQ.colLens = dpartColLensQ_D [r₁])
    (hge3 : r₁ ≥ 3) (hodd : Odd r₁) :
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .DD)).card = (countPBP_D [r₁]).1 ∧
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .RC)).card = (countPBP_D [r₁]).2.1 := by
  simp only [← Fintype.card_subtype]
  have hμQ_bot := yd_of_colLens_nil (by rw [hQ]; rfl : μQ.colLens = [])
  subst hμQ_bot
  have hP_col : μP.colLen 0 = (r₁ + 1) / 2 := colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)
  have hK_eq := odd_div2_succ hodd
  have hQP_lt : (⊥ : YoungDiagram).colLen 0 < μP.colLen 0 := by rw [colLen_bot, hP_col]; omega
  have h_shifted := yd_of_colLens_nil (by rw [YoungDiagram.colLens_shiftLeft, hP]; rfl)
  have h_prim : (⊥ : YoungDiagram).colLen 0 ≥ μP.shiftLeft.colLen 0 := by
    rw [h_shifted, colLen_bot]
  have h_hQP := (show (⊥ : YoungDiagram).colLen 0 ≤ μP.colLen 0 by rw [colLen_bot]; omega)
  constructor <;>
    rw [card_PBPSet_D_primitive_step_tc h_hQP hQP_lt h_prim,
        h_shifted, shiftLeft_bot, card_PBPSet_bot, Nat.one_mul]
  · -- DD: rewrite tailClassOfSymbol = DD as top = .d
    simp_rw [tailClassOfSymbol_DD]
    rw [validCol0_card_top_d h_hQP hQP_lt, hP_col, colLen_bot]
    obtain ⟨m, rfl⟩ := hodd
    have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    have h3 : (⊥ : YoungDiagram).colLen 0 = 0 := colLen_bot 0
    have hm_ge : m + 1 ≥ 2 := by omega
    simp only [h1, h2, countPBP_D, tailCoeffs, nu, ge_iff_le, hm_ge, ite_true]; omega
  · -- RC: split into .r and .c subtypes
    sorry

/-- Per-tc step for dp = r₁::r₂::rest. -/
theorem per_tc_cons₂ (r₁ r₂ : ℕ) (rest : DualPart) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_D (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_D (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (hge3 : ∀ r ∈ r₁ :: r₂ :: rest, r ≥ 3)
    (hodd : ∀ r ∈ r₁ :: r₂ :: rest, Odd r)
    (h_ih_tc : rest ≠ [] →
      (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
          tailClass_D σ.val = .DD)).card = (countPBP_D rest).1 ∧
      (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
          tailClass_D σ.val = .RC)).card = (countPBP_D rest).2.1) :
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .DD)).card = (countPBP_D (r₁ :: r₂ :: rest)).1 ∧
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .RC)).card = (countPBP_D (r₁ :: r₂ :: rest)).2.1 := by
  sorry

theorem card_PBPSet_D_per_tc (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hge3 : ∀ r ∈ dp, r ≥ 3)
    (hodd : ∀ r ∈ dp, Odd r) (hne : dp ≠ []) :
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .DD)).card = (countPBP_D dp).1 ∧
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .RC)).card = (countPBP_D dp).2.1 := by
  match dp, hP, hQ, hsort, hge3, hodd, hne with
  | [r₁], hP, hQ, _, hge3, hodd, _ =>
    exact per_tc_singleton r₁ hP hQ (hge3 r₁ (by simp)) (hodd r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, hge3, hodd, _ =>
    have hr₂ : r₂ > 1 := by
      have := hge3 r₂ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))); omega
    exact per_tc_cons₂ r₁ r₂ rest hP hQ hsort hge3 hodd (fun hne =>
      card_PBPSet_D_per_tc rest μP.shiftLeft μQ.shiftLeft
          (colLens_eq_tail hP) (colLens_eq_tail_Q hr₂ hQ)
          (sorted_tail₂ hsort) (all_ge3_tail₂ hge3)
          (fun r hr => hodd r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) hne)
termination_by dp.length
decreasing_by simp [List.length_cons]; omega

/-- **Main theorem**: `card(PBPSet .D μP μQ) = tripleSum(countPBP_D dp)`. -/
theorem card_PBPSet_D_eq_tripleSum_countPBP_D (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hge3 : ∀ r ∈ dp, r ≥ 3)
    (hodd : ∀ r ∈ dp, Odd r) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D dp) := by
  match dp, hP, hQ, hsort, hge3, hodd with
  | [], hP, hQ, _, _, _ => exact card_PBPSet_D_eq_tripleSum_nil hP hQ
  | [r₁], hP, hQ, _, hge3, hodd =>
    exact card_PBPSet_D_eq_tripleSum_singleton r₁ hP hQ
      (hge3 r₁ (by simp)) (hodd r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, hge3, hodd =>
    have hr₂ : r₂ > 1 := by
      have := hge3 r₂ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))); omega
    have hP_sh := colLens_eq_tail hP
    have hQ_sh := colLens_eq_tail_Q hr₂ hQ
    have hsort' := sorted_tail₂ hsort
    have hge3' := all_ge3_tail₂ hge3
    have hodd' := fun r hr => hodd r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have h_ih_total := card_PBPSet_D_eq_tripleSum_countPBP_D rest
        μP.shiftLeft μQ.shiftLeft hP_sh hQ_sh hsort' hge3' hodd'
    exact card_PBPSet_D_eq_tripleSum_cons₂ r₁ r₂ rest hP hQ hsort hge3 hodd
        h_ih_total
        (fun hne => (card_PBPSet_D_per_tc rest μP.shiftLeft μQ.shiftLeft
            hP_sh hQ_sh hsort' hge3' hodd' hne).1)
        (fun hne => (card_PBPSet_D_per_tc rest μP.shiftLeft μQ.shiftLeft
            hP_sh hQ_sh hsort' hge3' hodd' hne).2)
termination_by dp.length
decreasing_by simp [List.length_cons]; omega
