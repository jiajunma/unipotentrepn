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

/-- tailCoeffs DD component = 2K-1. -/
lemma tailCoeffs_tDD (K : ℕ) (hK : K ≥ 1) : (tailCoeffs K).1.1 = 2 * K - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  show nu k + (if k + 1 ≥ 2 then nu (k + 1 - 2) else 0) = 2 * (k + 1) - 1
  unfold nu; by_cases h : k + 1 ≥ 2 <;> simp [h] <;> omega

/-- tailCoeffs RC component = 2K. -/
lemma tailCoeffs_tRC (K : ℕ) (hK : K ≥ 1) : (tailCoeffs K).1.2.1 = 2 * K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  show 2 * nu k = 2 * (k + 1)
  unfold nu; omega

/-- tailCoeffs SS component = 1. -/
lemma tailCoeffs_tSS : ∀ K, (tailCoeffs K).1.2.2 = 1 := fun _ => rfl

/-- tailCoeffs scDD component. -/
lemma tailCoeffs_scDD (K : ℕ) : (tailCoeffs K).2.1 = 2 * (if K ≥ 2 then K - 1 else 0) := by
  obtain _ | _ | K := K <;> simp [tailCoeffs, nu] <;> omega

/-- tailCoeffs scRC component. -/
lemma tailCoeffs_scRC (K : ℕ) (hK : K ≥ 1) : (tailCoeffs K).2.2.1 = 2 * K - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  show nu k + (if k + 1 ≥ 2 then nu (k + 1 - 2) else 0) = 2 * (k + 1) - 1
  unfold nu; by_cases h : k + 1 ≥ 2 <;> simp [h] <;> omega

/-- tailCoeffs scSS component = 1. -/
lemma tailCoeffs_scSS : ∀ K, (tailCoeffs K).2.2.2 = 1 := fun _ => rfl

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

/-- R_ValidCol0 with given top symbol = TSeq(K-1) with given last symbol.
    Via equivTSeq + peel_first_s. -/
lemma R_ValidCol0_tc_eq_TSeq_last {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0)
    (hK2 : μP.colLen 0 - μQ.colLen 0 ≥ 2) (sym : DRCSymbol) :
    Fintype.card {v : ValidCol0 μP μQ //
      v.paint (μQ.colLen 0) = .s ∧ v.paint (μP.colLen 0 - 1) = sym} =
    Fintype.card {w : TSeq (μP.colLen 0 - μQ.colLen 0 - 1) //
      w.val ⟨μP.colLen 0 - μQ.colLen 0 - 1 - 1, by omega⟩ = sym} :=
  R_ValidCol0_tc_card hQP hk_pos hK2 sym

/-! RC_sub per-tc aggregate (Task 25 core) -/

/-- Per-tc value for R_sub σ: |{v // compat_R ∧ topTC = tc}|. -/
private noncomputable def R_ValidCol0_tc (μP μQ : YoungDiagram) (tc : TailClass) : ℕ :=
  Fintype.card {v : ValidCol0 μP μQ //
    v.paint (μQ.colLen 0) = .s ∧ tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = tc}

/-- Per-tc value for C_sub σ: |{v // compat_C ∧ topTC = tc}|. -/
private noncomputable def C_ValidCol0_tc (μP μQ : YoungDiagram) (tc : TailClass) : ℕ :=
  Fintype.card {v : ValidCol0 μP μQ //
    (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧ tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = tc}

/-- R_tc(DD) + C_tc(DD) = 2 × scDD. -/
theorem X_r_tc_plus_X_c_tc_DD {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0) :
    R_ValidCol0_tc μP μQ .DD + C_ValidCol0_tc μP μQ .DD =
      2 * (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.1 := by
  simp only [R_ValidCol0_tc, C_ValidCol0_tc, tailClassOfSymbol_DD]
  rcases Nat.lt_or_ge (μP.colLen 0 - μQ.colLen 0) 2 with hK1 | hK2
  · -- K = 1: both R and C are 0 (contradictory conditions)
    have h_top_eq_b : μP.colLen 0 - 1 = μQ.colLen 0 := by omega
    have h_R : Fintype.card {v : ValidCol0 μP μQ //
        v.paint (μQ.colLen 0) = .s ∧ v.paint (μP.colLen 0 - 1) = .d} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, hs, hd⟩ => by
        rw [h_top_eq_b] at hd; rw [hs] at hd; exact DRCSymbol.noConfusion hd⟩
    have h_C : Fintype.card {v : ValidCol0 μP μQ //
        (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧ v.paint (μP.colLen 0 - 1) = .d} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, hlo, hd⟩ => by
        rw [h_top_eq_b] at hd; rw [hd] at hlo; simp [DRCSymbol.layerOrd] at hlo⟩
    rw [h_R, h_C]; simp [tailCoeffs_scDD]; omega
  · -- K ≥ 2: R = 2K-3, C = 2K-1
    -- C_tc(DD): layerOrd ≤ 3 is automatic for top=.d with K≥2 (d_unique)
    have h_C : Fintype.card {v : ValidCol0 μP μQ //
        (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧ v.paint (μP.colLen 0 - 1) = .d} =
        Fintype.card {v : ValidCol0 μP μQ // v.paint (μP.colLen 0 - 1) = .d} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro v; constructor
      · exact fun ⟨_, hd⟩ => hd
      · intro hd; refine ⟨?_, hd⟩
        have h_ne : μQ.colLen 0 ≠ μP.colLen 0 - 1 := by omega
        have hb_ne_d : v.paint (μQ.colLen 0) ≠ .d := fun hbd =>
          h_ne (v.col_d_unique _ _ hbd hd)
        rcases hp : v.paint (μQ.colLen 0) with _ | _ | _ | _ | _
        all_goals (simp [DRCSymbol.layerOrd]; try omega)
        exact absurd hp hb_ne_d
    rw [h_C, validCol0_card_top_d hQP (by omega),
        R_ValidCol0_tc_eq_TSeq_last hQP (by omega) hK2 .d,
        TSeq_card_last_d' _ (by omega), tailCoeffs_scDD, if_pos hK2]; omega

/-- R_tc(RC) + C_tc(RC) = 2 × scRC. -/
theorem X_r_tc_plus_X_c_tc_RC {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0) :
    R_ValidCol0_tc μP μQ .RC + C_ValidCol0_tc μP μQ .RC =
      2 * (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.1 := by
  set K := μP.colLen 0 - μQ.colLen 0 with hK_def
  have hK_pos : K ≥ 1 := by omega
  simp_rw [R_ValidCol0_tc, C_ValidCol0_tc, tailClassOfSymbol_RC]
  rcases Nat.lt_or_ge K 2 with hK1 | hK2
  · -- K = 1
    have hK_eq : K = 1 := by omega
    have h_top_eq_b : μP.colLen 0 - 1 = μQ.colLen 0 := by omega
    -- R: {paint(b)=.s ∧ (top=.r ∨ top=.c)}. K=1: top=b → .s=.r∨.c impossible
    have h_R : Fintype.card {v : ValidCol0 μP μQ //
        v.paint (μQ.colLen 0) = .s ∧
        (v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c)} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun ⟨_, hs, hrc⟩ => by
        rw [h_top_eq_b] at hrc; rcases hrc with hr | hc
        · rw [hs] at hr; exact DRCSymbol.noConfusion hr
        · rw [hs] at hc; exact DRCSymbol.noConfusion hc⟩
    -- C: {layerOrd≤3 ∧ (top=.r ∨ top=.c)}. K=1: top=b. .r.layerOrd=2≤3 and .c.layerOrd=3≤3. So 2 elements.
    have h_C : Fintype.card {v : ValidCol0 μP μQ //
        (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧
        (v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c)} = 2 := by
      -- K=1: {v // layerOrd ≤ 3 ∧ (top=.r ∨ top=.c)}. top = b.
      -- = {v // paint(b) ∈ {.r,.c}} since .r.layerOrd=2≤3, .c.layerOrd=3≤3
      -- = ValidCol0 top=.r + ValidCol0 top=.c = 1 + 1 = 2
      have h_top_eq_b' : μP.colLen 0 - 1 = μQ.colLen 0 := by omega
      -- The compat condition (layerOrd ≤ 3) is auto for .r and .c
      have h_equiv : Fintype.card {v : ValidCol0 μP μQ //
          (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧
          (v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c)} =
        Fintype.card {v : ValidCol0 μP μQ //
          v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c} := by
        apply Fintype.card_congr; apply Equiv.subtypeEquivRight; intro v; constructor
        · exact fun ⟨_, h⟩ => h
        · intro h; refine ⟨?_, h⟩; rw [h_top_eq_b'] at h; rcases h with hr | hc
          · rw [hr]; decide
          · rw [hc]; decide
      rw [h_equiv]
      rw [Fintype.card_subtype_or_disjoint _ _
          (Set.disjoint_iff.2 fun v ⟨hr, hc⟩ => by
            change v.paint _ = .r at hr; change v.paint _ = .c at hc
            rw [hr] at hc; exact DRCSymbol.noConfusion hc),
          validCol0_card_top_r hQP (by omega), validCol0_card_top_c hQP (by omega)]; omega
    rw [h_R, h_C, hK_eq]; simp [tailCoeffs_scRC]
  · -- K ≥ 2
    -- C: layerOrd ≤ 3 is automatic (same as DD case: top ∈ {.r,.c} → no d_unique issue)
    have h_C : Fintype.card {v : ValidCol0 μP μQ //
        (v.paint (μQ.colLen 0)).layerOrd ≤ 3 ∧
        (v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c)} =
        Fintype.card {v : ValidCol0 μP μQ //
        v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c} := by
      apply Fintype.card_congr; apply Equiv.subtypeEquivRight; intro v; constructor
      · exact fun ⟨_, h⟩ => h
      · intro h; refine ⟨?_, h⟩
        -- top ∈ {.r,.c} → paint(b) can be anything except .d requires K≥2
        -- Actually layerOrd ≤ 3 means ≠ .d. For K≥2 with top ∈ {.r,.c}:
        -- by col_c_unique or general argument, paint(b) ≤ top in layerOrd
        -- Since b < top by K≥2, monotonicity gives paint(b).layerOrd ≤ top.layerOrd ≤ 3
        have h_top_lt : μQ.colLen 0 < μP.colLen 0 - 1 := by omega
        have := v.mono (μQ.colLen 0) (μP.colLen 0 - 1) (by omega) (by omega)
        rcases h with hr | hc
        · rw [hr, DRCSymbol.layerOrd] at this; exact Nat.le_trans this (by omega)
        · rw [hc, DRCSymbol.layerOrd] at this; exact this
    rw [h_C]
    -- ValidCol0 top ∈ {.r,.c} = K + K = 2K
    rw [Fintype.card_subtype_or_disjoint _ _
        (Set.disjoint_iff.2 fun v ⟨hr, hc⟩ => by
          change v.paint _ = .r at hr; change v.paint _ = .c at hc
          rw [hr] at hc; exact DRCSymbol.noConfusion hc)]
    rw [validCol0_card_top_r hQP (by omega), validCol0_card_top_c hQP (by omega), hK_def]
    -- R_tc(RC) via TSeq bridge
    have h_R_val : Fintype.card {v : ValidCol0 μP μQ //
        v.paint (μQ.colLen 0) = .s ∧
        (v.paint (μP.colLen 0 - 1) = .r ∨ v.paint (μP.colLen 0 - 1) = .c)} = 2 * (K - 1) := by
      -- Rewrite ∧(∨) as (∧)∨(∧), split, bridge each part
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun v : ValidCol0 μP μQ => and_or_left)),
          Fintype.card_subtype_or_disjoint _ _
            (Set.disjoint_iff.2 fun v hv => by
              obtain ⟨⟨_, hr⟩, ⟨_, hc⟩⟩ := hv
              rw [hr] at hc; exact DRCSymbol.noConfusion hc),
          R_ValidCol0_tc_eq_TSeq_last hQP (by omega) hK2 .r, TSeq_card_last_r' _ (by omega),
          R_ValidCol0_tc_eq_TSeq_last hQP (by omega) hK2 .c, TSeq_card_last_c' _ (by omega)]
      omega
    rw [h_R_val, tailCoeffs_scRC K hK_pos]; omega

/-- Helper: for R_sub σ, compat_with_RC σ v ↔ v.paint(b) = .s. -/
private lemma compat_R_iff {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP.shiftLeft μQ.shiftLeft)
    (h_r : σ.val.P.paint (μQ.colLen 0) 0 = .r)
    (v : ValidCol0 μP μQ) (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0) :
    v.compat_with_RC σ ↔ v.paint (μQ.colLen 0) = .s := by
  constructor
  · intro ⟨h1, h2⟩
    rw [h_r, DRCSymbol.layerOrd] at h1
    have h_nd := v.nondot_tail (μQ.colLen 0) (le_refl _) hk_pos
    have h_ne_r := h2 h_r
    rcases hp : v.paint (μQ.colLen 0) with _ | _ | _ | _ | _
    · exact absurd hp h_nd
    · rfl
    · exact absurd hp h_ne_r
    all_goals (rw [hp, DRCSymbol.layerOrd] at h1; omega)
  · intro h; exact ⟨by rw [h, h_r]; decide, fun _ => by rw [h]; decide⟩

/-- Helper: for C_sub σ, compat_with_RC σ v ↔ v.paint(b).layerOrd ≤ 2. -/
private lemma compat_C_iff {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP.shiftLeft μQ.shiftLeft)
    (h_c : σ.val.P.paint (μQ.colLen 0) 0 = .c)
    (v : ValidCol0 μP μQ) :
    v.compat_with_RC σ ↔ (v.paint (μQ.colLen 0)).layerOrd ≤ 3 := by
  constructor
  · intro ⟨h1, _⟩; rw [h_c, DRCSymbol.layerOrd] at h1; exact h1
  · intro h; exact ⟨by rw [h_c, DRCSymbol.layerOrd]; exact h,
      fun hr => by rw [h_c] at hr; exact DRCSymbol.noConfusion hr⟩

/-- Balanced RC aggregate for DD (and RC) per-tc.
    Follows fiber_card_balanced_RC_aggregate structure with per-tc restriction. -/
theorem balanced_RC_aggregate_tc {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0)
    (h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1) (tc : TailClass)
    (h_sum : R_ValidCol0_tc μP μQ tc + C_ValidCol0_tc μP μQ tc =
      2 * (match tc with | .DD => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.1
                         | .RC => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.1
                         | .SS => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.2)) :
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).sum
      (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc}) =
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).card *
      (match tc with | .DD => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.1
                     | .RC => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.1
                     | .SS => (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.2) := by
  -- Follow fiber_card_balanced_RC_aggregate: split RC into R ∪ C
  have hfilter_eq : Finset.univ.filter
      (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft => tailClass_D σ.val = .RC) =
    Finset.univ.filter (fun σ => σ.val.P.paint (μQ.colLen 0) 0 = .r ∨
      σ.val.P.paint (μQ.colLen 0) 0 = .c) := by
    apply Finset.filter_congr; intros σ _; exact tailClass_RC_iff_paint_rc σ h_bal
  have hfilter_or := Finset.filter_or
    (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft => σ.val.P.paint (μQ.colLen 0) 0 = .r)
    (fun σ => σ.val.P.paint (μQ.colLen 0) 0 = .c)
  have hdisj : Disjoint
      (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        σ.val.P.paint (μQ.colLen 0) 0 = .r))
      (Finset.univ.filter (fun σ => σ.val.P.paint (μQ.colLen 0) 0 = .c)) := by
    rw [Finset.disjoint_filter]; intros σ _ hr hc; rw [hr] at hc; exact absurd hc (by decide)
  rw [hfilter_eq, hfilter_or, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj]
  -- R sum: each R_sub σ gives fiber_tc = R_ValidCol0_tc via fiber_card_balanced_RC_tc + compat_R_iff
  have h_R_sum : (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
      σ.val.P.paint (μQ.colLen 0) 0 = .r)).sum
      (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc}) =
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
      σ.val.P.paint (μQ.colLen 0) 0 = .r)).card * R_ValidCol0_tc μP μQ tc := by
    rw [Finset.sum_congr rfl (fun σ hσ => ?_)]; · rw [Finset.sum_const]; rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [fiber_card_balanced_RC_tc σ h_bal hQP hk_pos
        ((tailClass_RC_iff_paint_rc σ h_bal).mpr (Or.inl hσ)) tc]
    simp only [R_ValidCol0_tc]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v =>
      ⟨fun ⟨hc, ht⟩ => ⟨(compat_R_iff σ hσ v hQP hk_pos).mp hc, ht⟩,
       fun ⟨hs, ht⟩ => ⟨(compat_R_iff σ hσ v hQP hk_pos).mpr hs, ht⟩⟩))
  -- C sum: similarly
  have h_C_sum : (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
      σ.val.P.paint (μQ.colLen 0) 0 = .c)).sum
      (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc}) =
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
      σ.val.P.paint (μQ.colLen 0) 0 = .c)).card * C_ValidCol0_tc μP μQ tc := by
    rw [Finset.sum_congr rfl (fun σ hσ => ?_)]; · rw [Finset.sum_const]; rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [fiber_card_balanced_RC_tc σ h_bal hQP hk_pos
        ((tailClass_RC_iff_paint_rc σ h_bal).mpr (Or.inr hσ)) tc]
    simp only [C_ValidCol0_tc]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v =>
      ⟨fun ⟨hc, ht⟩ => ⟨(compat_C_iff σ hσ v).mp hc, ht⟩,
       fun ⟨hs, ht⟩ => ⟨(compat_C_iff σ hσ v).mpr hs, ht⟩⟩))
  rw [h_R_sum, h_C_sum]
  -- |R| = |C| + h_sum
  set n := (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
    σ.val.P.paint (μQ.colLen 0) 0 = .r)).card
  have h_eq_n : (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
      σ.val.P.paint (μQ.colLen 0) 0 = .c)).card = n :=
    (r_sub_card_eq_c_sub_card h_bal).symm
  rw [h_eq_n, ← Nat.mul_add, h_sum, ← Nat.mul_assoc, ← Nat.two_mul, Nat.mul_comm 2 n]
  cases tc <;> simp [Nat.mul_comm]

theorem balanced_RC_aggregate_DD {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0)
    (h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1) :
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).sum
      (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .DD}) =
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).card *
      (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.1 :=
  balanced_RC_aggregate_tc hQP hk_pos h_bal .DD (X_r_tc_plus_X_c_tc_DD hQP hk_pos)

theorem balanced_RC_aggregate_RC {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (hk_pos : μQ.colLen 0 < μP.colLen 0)
    (h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1) :
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).sum
      (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .RC}) =
    (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
        tailClass_D σ.val = .RC)).card *
      (tailCoeffs (μP.colLen 0 - μQ.colLen 0)).2.2.1 :=
  balanced_RC_aggregate_tc hQP hk_pos h_bal .RC (X_r_tc_plus_X_c_tc_RC hQP hk_pos)

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
  obtain ⟨m, rfl⟩ := hodd
  have h_div : (2 * m + 1) / 2 = m := by omega
  have hm1 : m + 1 ≥ 2 := by omega
  simp only [← Fintype.card_subtype]
  have hμQ_bot := yd_of_colLens_nil (by rw [hQ]; rfl : μQ.colLens = [])
  subst hμQ_bot
  have hP_col : μP.colLen 0 = m + 1 := by
    rw [colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)]; omega
  have hQP_lt : (⊥ : YoungDiagram).colLen 0 < μP.colLen 0 := by rw [colLen_bot]; omega
  have h_shifted := yd_of_colLens_nil (by rw [YoungDiagram.colLens_shiftLeft, hP]; rfl)
  have h_prim : (⊥ : YoungDiagram).colLen 0 ≥ μP.shiftLeft.colLen 0 := by
    rw [h_shifted, colLen_bot]
  have h_hQP : (⊥ : YoungDiagram).colLen 0 ≤ μP.colLen 0 := by rw [colLen_bot]; omega
  -- DD
  have h_dd : Fintype.card {τ : PBPSet .D μP ⊥ // tailClass_D τ.val = .DD} =
      2 * (m + 1) - 1 := by
    rw [card_PBPSet_D_primitive_step_tc h_hQP hQP_lt h_prim,
        h_shifted, shiftLeft_bot, card_PBPSet_bot, Nat.one_mul]
    simp_rw [tailClassOfSymbol_DD]
    rw [validCol0_card_top_d h_hQP hQP_lt, hP_col, colLen_bot]; omega
  -- RC via total - DD - SS
  have h_rc : Fintype.card {τ : PBPSet .D μP ⊥ // tailClass_D τ.val = .RC} =
      2 * (m + 1) := by
    -- SS value
    have h_ss : Fintype.card {τ : PBPSet .D μP ⊥ // tailClass_D τ.val = .SS} = 1 := by
      rw [card_PBPSet_D_primitive_step_tc h_hQP hQP_lt h_prim,
          h_shifted, shiftLeft_bot, card_PBPSet_bot, Nat.one_mul]
      have : ∀ v : ValidCol0 μP ⊥,
          tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .SS ↔
            v.paint (μP.colLen 0 - 1) = .s := by
        intro v
        have h_nd := v.nondot_tail (μP.colLen 0 - 1) (by rw [colLen_bot]; omega) (by omega)
        rcases hv : v.paint (μP.colLen 0 - 1) with _ | _ | _ | _ | _
        · exact absurd hv h_nd
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
        all_goals exact ⟨fun h => by simp [tailClassOfSymbol] at h, fun h => by simp at h⟩
      simp_rw [this]; exact validCol0_card_top_s h_hQP hQP_lt
    -- Total
    have h_total : Fintype.card (PBPSet .D μP ⊥) = 4 * (m + 1) := by
      rw [card_PBPSet_D_eq_tripleSum_singleton (2*m+1) hP hQ hge3 ⟨m, rfl⟩]
      simp only [countPBP_D, tailCoeffs, nu, ge_iff_le, hm1, ite_true, h_div, tripleSum]; omega
    -- Partition via card_PBPSet_eq_sum_tc
    have h_sum := card_PBPSet_eq_sum_tc μP ⊥
    -- PBPSet_tc and subtype have same card
    have h_conv : ∀ tc, Fintype.card (PBPSet_tc .D μP ⊥ tc) =
        Fintype.card {τ : PBPSet .D μP ⊥ // tailClass_D τ.val = tc} :=
      fun _ => Fintype.card_congr (Equiv.refl _)
    rw [h_conv, h_conv, h_conv] at h_sum
    omega
  constructor
  · rw [h_dd]; simp only [countPBP_D, tailCoeffs, nu, ge_iff_le, hm1, ite_true, h_div]; omega
  · rw [h_rc]; simp only [countPBP_D, tailCoeffs, nu, ge_iff_le, hm1, ite_true, h_div]; omega

/-- Combined: total + per-tc matching. Proved by induction. -/
theorem card_PBPSet_D_combined (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hge3 : ∀ r ∈ dp, r ≥ 3)
    (hodd : ∀ r ∈ dp, Odd r) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D dp) ∧
    (dp ≠ [] →
      (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
          tailClass_D σ.val = .DD)).card = (countPBP_D dp).1 ∧
      (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
          tailClass_D σ.val = .RC)).card = (countPBP_D dp).2.1) := by
  match dp, hP, hQ, hsort, hge3, hodd with
  | [], hP, hQ, _, _, _ =>
    exact ⟨card_PBPSet_D_eq_tripleSum_nil hP hQ, fun h => absurd rfl h⟩
  | [r₁], hP, hQ, _, hge3, hodd =>
    exact ⟨card_PBPSet_D_eq_tripleSum_singleton r₁ hP hQ (hge3 r₁ (by simp)) (hodd r₁ (by simp)),
           fun _ => per_tc_singleton r₁ hP hQ (hge3 r₁ (by simp)) (hodd r₁ (by simp))⟩
  | r₁ :: r₂ :: rest, hP, hQ, hsort, hge3, hodd =>
    have hr₂ : r₂ > 1 := by
      have := hge3 r₂ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))); omega
    have hP_sh := colLens_eq_tail hP
    have hQ_sh := colLens_eq_tail_Q hr₂ hQ
    have hsort' := sorted_tail₂ hsort
    have hge3' := all_ge3_tail₂ hge3
    have hodd' := fun r hr => hodd r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have h_ih := card_PBPSet_D_combined rest μP.shiftLeft μQ.shiftLeft
        hP_sh hQ_sh hsort' hge3' hodd'
    refine ⟨?_, fun _ => ?_⟩
    · exact card_PBPSet_D_eq_tripleSum_cons₂ r₁ r₂ rest hP hQ hsort hge3 hodd
          h_ih.1
          (fun hne => (h_ih.2 hne).1)
          (fun hne => (h_ih.2 hne).2)
    · -- Per-tc for r₁::r₂::rest
      -- Setup
      have hr₁_ge3 := hge3 r₁ (by simp)
      have hr₂_ge3 := hge3 r₂ (by simp)
      have hr₁_odd := hodd r₁ (by simp)
      have hr₂_odd := hodd r₂ (by simp)
      have hr₁_ge_r₂ : r₂ ≤ r₁ := by
        have := hsort.pairwise; rw [List.pairwise_cons] at this; exact this.1 r₂ (by simp)
      have hP_colLen : μP.colLen 0 = (r₁ + 1) / 2 :=
        colLen_0_eq_of_colLens_cons (by rw [hP]; rfl)
      have hQ_colLen : μQ.colLen 0 = (r₂ - 1) / 2 :=
        colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_D_cons₂_pos r₁ r₂ rest (by omega)])
      have hQP : μQ.colLen 0 ≤ μP.colLen 0 := by
        rw [hP_colLen, hQ_colLen]
        obtain ⟨a, rfl⟩ := hr₁_odd; obtain ⟨b, rfl⟩ := hr₂_odd; omega
      have hQP_lt : μQ.colLen 0 < μP.colLen 0 := by
        rw [hP_colLen, hQ_colLen]
        obtain ⟨a, rfl⟩ := hr₁_odd; obtain ⟨b, rfl⟩ := hr₂_odd; omega
      simp only [← Fintype.card_subtype]
      by_cases h_prim_dp : r₂ > rest.head?.getD 0
      · -- Primitive per-tc via total-DD-SS
        have h_prim : μQ.colLen 0 ≥ μP.shiftLeft.colLen 0 := by
          rw [hQ_colLen]; have h_sh := colLens_eq_tail hP
          match rest with
          | [] =>
            have hbot := yd_of_colLens_nil (by rw [h_sh]; rfl)
            rw [hbot, colLen_bot]; omega
          | [r₃] =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_singleton])]
            obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            simp at h_prim_dp; omega
          | r₃ :: _ :: _ =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_cons₂_eq])]
            obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            simp at h_prim_dp; omega
        -- DD
        have h_dd := card_PBPSet_D_primitive_step_tc hQP hQP_lt h_prim .DD
        simp_rw [tailClassOfSymbol_DD] at h_dd
        rw [validCol0_card_top_d hQP hQP_lt, h_ih.1] at h_dd
        -- SS
        have h_ss := card_PBPSet_D_primitive_step_tc hQP hQP_lt h_prim .SS
        have h_ss_iff : ∀ v : ValidCol0 μP μQ,
            tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .SS ↔
              v.paint (μP.colLen 0 - 1) = .s := by
          intro v
          have h_nd := v.nondot_tail (μP.colLen 0 - 1) (by omega) (by omega)
          rcases hv : v.paint (μP.colLen 0 - 1) with _ | _ | _ | _ | _
          · exact absurd hv h_nd
          · exact ⟨fun _ => rfl, fun _ => rfl⟩
          all_goals exact ⟨fun h => by simp [tailClassOfSymbol] at h, fun h => by simp at h⟩
        simp_rw [h_ss_iff] at h_ss
        rw [validCol0_card_top_s hQP hQP_lt, h_ih.1] at h_ss
        -- Total (already proved)
        have h_total := card_PBPSet_eq_sum_tc μP μQ
        have h_conv : ∀ tc, Fintype.card (PBPSet_tc .D μP μQ tc) =
            Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc} :=
          fun _ => Fintype.card_congr (Equiv.refl _)
        rw [h_conv, h_conv, h_conv] at h_total
        have h_total_val := card_PBPSet_D_eq_tripleSum_cons₂ r₁ r₂ rest hP hQ hsort hge3 hodd
            h_ih.1 (fun hne => (h_ih.2 hne).1) (fun hne => (h_ih.2 hne).2)
        -- Arithmetic: DD + RC + SS = total, all expressed via countPBP_D
        -- Primitive countPBP_D: .1 = total × tDD, .2.1 = total × tRC
        have h_prim : μQ.colLen 0 ≥ μP.shiftLeft.colLen 0 := by
          rw [hQ_colLen]; have h_sh := colLens_eq_tail hP
          match rest with
          | [] =>
            have hbot := yd_of_colLens_nil (by rw [h_sh]; rfl)
            rw [hbot, colLen_bot]; omega
          | [r₃] =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_singleton])]
            obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            simp at h_prim_dp; omega
          | r₃ :: _ :: _ =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_cons₂_eq])]
            obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            simp at h_prim_dp; omega
        set K := μP.colLen 0 - μQ.colLen 0 with hK_def
        have hK_pos' : K ≥ 1 := by omega
        have hK_dp : K = (r₁ - r₂) / 2 + 1 := by
          rw [hK_def, hP_colLen, hQ_colLen]; exact k_eq_of_odd hr₁_odd hr₂_odd hr₁_ge_r₂
        -- DD via calc
        have h_cpd₁ : (countPBP_D (r₁ :: r₂ :: rest)).1 =
            tripleSum (countPBP_D rest) * (tailCoeffs K).1.1 := by
          simp [countPBP_D, tripleSum, if_pos h_prim_dp, hK_dp]
        have h_dd_tc := card_PBPSet_D_primitive_step_tc hQP hQP_lt h_prim .DD
        simp_rw [tailClassOfSymbol_DD] at h_dd_tc
        have h_dd : Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = .DD} =
            (countPBP_D (r₁ :: r₂ :: rest)).1 :=
          calc Fintype.card _
              = Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft) *
                  Fintype.card {v : ValidCol0 μP μQ // v.paint (μP.colLen 0 - 1) = .d} := h_dd_tc
            _ = tripleSum (countPBP_D rest) * (2 * K - 1) := by
                rw [h_ih.1, validCol0_card_top_d hQP hQP_lt]
            _ = tripleSum (countPBP_D rest) * (tailCoeffs K).1.1 := by
                rw [tailCoeffs_tDD K hK_pos']
            _ = _ := h_cpd₁.symm
        -- SS
        have h_ss_tc := card_PBPSet_D_primitive_step_tc hQP hQP_lt h_prim .SS
        have h_ss_iff : ∀ v : ValidCol0 μP μQ,
            tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .SS ↔
              v.paint (μP.colLen 0 - 1) = .s := by
          intro v
          have h_nd := v.nondot_tail (μP.colLen 0 - 1) (by omega) (by omega)
          rcases hv : v.paint (μP.colLen 0 - 1) with _ | _ | _ | _ | _
          · exact absurd hv h_nd
          · exact ⟨fun _ => rfl, fun _ => rfl⟩
          all_goals exact ⟨fun h => by simp [tailClassOfSymbol] at h, fun h => by simp at h⟩
        simp_rw [h_ss_iff] at h_ss_tc
        rw [validCol0_card_top_s hQP hQP_lt, h_ih.1] at h_ss_tc
        -- Total
        have h_total := card_PBPSet_eq_sum_tc μP μQ
        have h_conv : ∀ tc, Fintype.card (PBPSet_tc .D μP μQ tc) =
            Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc} :=
          fun _ => Fintype.card_congr (Equiv.refl _)
        rw [h_conv, h_conv, h_conv] at h_total
        have h_total_val := card_PBPSet_D_eq_tripleSum_cons₂ r₁ r₂ rest hP hQ hsort hge3 hodd
            h_ih.1 (fun hne => (h_ih.2 hne).1) (fun hne => (h_ih.2 hne).2)
        -- RC = total - DD - SS
        have h_cpd₂ : (countPBP_D (r₁ :: r₂ :: rest)).2.1 =
            tripleSum (countPBP_D rest) * (tailCoeffs K).1.2.1 := by
          simp [countPBP_D, tripleSum, if_pos h_prim_dp, hK_dp]
        rw [h_total, h_dd, h_ss_tc] at h_total_val
        -- RC: from DD + RC + SS = cpd.1 + cpd.2.1 + cpd.2.2
        -- with DD = cpd.1 and SS = cpd.2.2 → RC = cpd.2.1 (additive)
        have h_cpd₃ : (countPBP_D (r₁ :: r₂ :: rest)).2.2 =
            tripleSum (countPBP_D rest) := by
          simp only [countPBP_D, tripleSum, if_pos h_prim_dp]
          rw [tailCoeffs_tSS, Nat.mul_one]
        have h_ss_eq : Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = .SS} =
            (countPBP_D (r₁ :: r₂ :: rest)).2.2 := by
          rw [h_ss_tc, h_cpd₃, Nat.mul_one]
        -- RC via calc: card(PBPSet_tc RC) = card_shifted × ValidCol0_tc(RC) = total × tRC = cpd.2.1
        have h_cpd₂ : (countPBP_D (r₁ :: r₂ :: rest)).2.1 =
            tripleSum (countPBP_D rest) * (tailCoeffs K).1.2.1 := by
          simp [countPBP_D, tripleSum, if_pos h_prim_dp, hK_dp]
        have h_rc_tc := card_PBPSet_D_primitive_step_tc hQP hQP_lt h_prim .RC
        -- Need: ValidCol0_tc(RC) = tRC = 2K
        -- ValidCol0_tc(RC) = validCol0_total - DD - SS = 4K - (2K-1) - 1 = 2K at ValidCol0 level
        have h_vc_total : Fintype.card (ValidCol0 μP μQ) = 4 * K := by
          rw [validCol0_card K (by rw [hK_def]) hQP hK_pos']
          rw [tailCoeffs_tDD K hK_pos', tailCoeffs_tRC K hK_pos', tailCoeffs_tSS K]; omega
        have h_vc_dd : Fintype.card {v : ValidCol0 μP μQ //
            tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .DD} = 2 * K - 1 := by
          simp_rw [tailClassOfSymbol_DD]
          rw [validCol0_card_top_d hQP hQP_lt, hK_def]
        have h_vc_ss : Fintype.card {v : ValidCol0 μP μQ //
            tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .SS} = 1 := by
          have h_iff : ∀ v : ValidCol0 μP μQ,
              tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .SS ↔
                v.paint (μP.colLen 0 - 1) = .s := by
            intro v
            have h_nd := v.nondot_tail (μP.colLen 0 - 1) (by omega) (by omega)
            rcases hv : v.paint (μP.colLen 0 - 1) with _ | _ | _ | _ | _
            · exact absurd hv h_nd
            · exact ⟨fun _ => rfl, fun _ => rfl⟩
            all_goals exact ⟨fun h => by simp [tailClassOfSymbol] at h, fun h => by simp at h⟩
          simp_rw [h_iff]; exact validCol0_card_top_s hQP hQP_lt
        -- ValidCol0 partition: total = DD + RC + SS
        -- All are Subtype.fintype instances (consistent!)
        have h_vc_rc : Fintype.card {v : ValidCol0 μP μQ //
            tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .RC} = 2 * K := by
          simp_rw [tailClassOfSymbol_RC]
          rw [Fintype.card_subtype_or_disjoint _ _
              (Set.disjoint_iff.2 fun v ⟨hr, hc⟩ => by
                change v.paint _ = .r at hr; change v.paint _ = .c at hc
                rw [hr] at hc; exact DRCSymbol.noConfusion hc),
              validCol0_card_top_r hQP hQP_lt, validCol0_card_top_c hQP hQP_lt, hK_def]; omega
        have h_rc : Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = .RC} =
            (countPBP_D (r₁ :: r₂ :: rest)).2.1 :=
          calc Fintype.card _
              = Fintype.card (PBPSet .D μP.shiftLeft μQ.shiftLeft) *
                  Fintype.card {v : ValidCol0 μP μQ //
                    tailClassOfSymbol (v.paint (μP.colLen 0 - 1)) = .RC} := h_rc_tc
            _ = tripleSum (countPBP_D rest) * (2 * K) := by rw [h_ih.1, h_vc_rc]
            _ = tripleSum (countPBP_D rest) * (tailCoeffs K).1.2.1 := by
                  rw [tailCoeffs_tRC K hK_pos']
            _ = _ := h_cpd₂.symm
        exact ⟨h_dd, h_rc⟩
      · -- Balanced per-tc
        push_neg at h_prim_dp
        have h_bal : μP.shiftLeft.colLen 0 = μQ.colLen 0 + 1 := by
          have hr₂_ge_r₃ : r₂ ≥ rest.head?.getD 0 := by
            match rest with
            | [] => simp
            | r₃ :: _ =>
              simp only [List.head?_cons, Option.getD_some]
              have hp := hsort.pairwise; rw [List.pairwise_cons] at hp
              exact (List.pairwise_cons.mp hp.2).1 r₃ (by simp)
          have hr₂_eq_r₃ : r₂ = rest.head?.getD 0 := Nat.le_antisymm h_prim_dp hr₂_ge_r₃
          have h_sh := colLens_eq_tail hP
          match rest with
          | [] => exfalso; simp at hr₂_eq_r₃; omega
          | [r₃] =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_singleton]), hQ_colLen]
            simp at hr₂_eq_r₃; obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            omega
          | r₃ :: _ :: _ =>
            rw [colLen_0_eq_of_colLens_cons (by rw [h_sh, dpartColLensP_D_cons₂_eq]), hQ_colLen]
            simp at hr₂_eq_r₃; obtain ⟨a, rfl⟩ := hr₂_odd
            obtain ⟨b, rfl⟩ := hodd r₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simp)))
            omega
        set K := μP.colLen 0 - μQ.colLen 0 with hK_def
        have hK_pos' : K ≥ 1 := by omega
        have hK_dp : K = (r₁ - r₂) / 2 + 1 := by
          rw [hK_def, hP_colLen, hQ_colLen]; exact k_eq_of_odd hr₁_odd hr₂_odd hr₁_ge_r₂
        have h_rest_ne : rest ≠ [] := by
          intro h; subst h; simp at h_prim_dp; exact absurd hr₂_ge3 (by omega)
        have h_ih_tc' := h_ih.2 h_rest_ne
        -- Balanced step: card = subDD × tSum + subRC × scSum
        have h_step := card_PBPSet_D_balanced_step K h_bal (by rw [hK_def]) hQP hK_pos'
        -- Balanced countPBP_D components
        have h_cpd₁ : (countPBP_D (r₁ :: r₂ :: rest)).1 =
            (countPBP_D rest).1 * (tailCoeffs K).1.1 +
            (countPBP_D rest).2.1 * (tailCoeffs K).2.1 := by
          simp [countPBP_D, tripleSum, show ¬(r₂ > (List.head? rest).getD 0) from by omega, hK_dp]
        have h_cpd₂ : (countPBP_D (r₁ :: r₂ :: rest)).2.1 =
            (countPBP_D rest).1 * (tailCoeffs K).1.2.1 +
            (countPBP_D rest).2.1 * (tailCoeffs K).2.2.1 := by
          simp [countPBP_D, tripleSum, show ¬(r₂ > (List.head? rest).getD 0) from by omega, hK_dp]
        -- cpd.1 = dd' × tDD + rc' × scDD where dd' = filter(DD), rc' = filter(RC) by IH
        -- cpd.2.1 = dd' × tRC + rc' × scRC
        rw [← h_ih_tc'.1, ← h_ih_tc'.2] at h_cpd₁ h_cpd₂
        -- Now h_cpd₁ : cpd.1 = filter(DD) × tDD + filter(RC) × scDD
        -- Need: filter(DD new) = cpd.1 ∧ filter(RC new) = cpd.2.1
        -- Use total - DD_tc - SS_tc = card, with per-tc decomposition
        -- DD per-tc via balanced step:
        -- filter(DD new) = Σ_{σ:DD} fib_tc(DD) + Σ_{σ:RC} fib_tc(DD) + 0
        --               = subDD × tDD + subRC × scDD   [by DD_tc + RC_aggregate]
        --               = cpd.1  [by h_cpd₁]
        -- Similarly for RC.
        -- But assembling the Finset.sum decomposition is the same pattern as balanced_step.
        -- Use total - SS approach:
        -- Per-tc fiber sum: card(PBPSet_tc tc) = Σ_σ card(fiber_tc(σ, tc))
        -- via sigma-subtype exchange on sigmaFiberEquiv
        -- Per-tc fiber sum: proved by sandwich (lower bound injection) + total consistency
        have card_tc_sum : ∀ tc' : TailClass,
            Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc'} =
            Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) := by
          -- Lower bound for ALL tc'
          have h_ge : ∀ tc', Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) ≤
              Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc'} := by
            intro tc'; rw [← Fintype.card_sigma]
            apply Fintype.card_le_of_injective
              (fun (p : (σ : _) × {τ : doubleDescent_D_fiber σ // _}) =>
                (⟨p.2.val.val, p.2.prop⟩ : {τ : PBPSet .D μP μQ // tailClass_D τ.val = tc'}))
            intro ⟨σ₁, ⟨⟨τ₁, h₁⟩, _⟩⟩ ⟨σ₂, ⟨⟨τ₂, h₂⟩, _⟩⟩ h
            simp only [Subtype.mk.injEq] at h; subst h
            have : σ₁ = σ₂ := h₁.symm.trans h₂; subst this; rfl
          -- Total consistency
          have h_total := card_PBPSet_eq_sum_fiber (μP := μP) (μQ := μQ)
          have h_sum_tc := card_PBPSet_eq_sum_tc μP μQ
          have h_conv : ∀ t, Fintype.card (PBPSet_tc .D μP μQ t) =
              Fintype.card {τ : PBPSet .D μP μQ // tailClass_D τ.val = t} :=
            fun _ => Fintype.card_congr (Equiv.refl _)
          rw [h_conv, h_conv, h_conv] at h_sum_tc
          have h_S_total : Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .DD}) +
            Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .RC}) +
            Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .SS}) =
            Fintype.card (PBPSet .D μP μQ) := by
            trans (Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
                Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .DD} +
                Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .RC} +
                Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = .SS}))
            · simp only [Finset.sum_add_distrib]
            · rw [Finset.sum_congr rfl (fun σ _ => (card_fiber_eq_sum_tc σ).symm), h_total]
          -- S(tc) ≤ C(tc) for all tc, and Σ S = Σ C → S = C for each
          have hgDD := h_ge .DD; have hgRC := h_ge .RC; have hgSS := h_ge .SS
          intro tc'; rcases tc' with _ | _ | _ <;> omega
        -- Use card_tc_sum + split + compute each part
        -- For DD: card_tc_sum DD = Σ_σ fib_tc(σ,DD)
        -- Split: Σ_{σ:DD} fib_tc(DD) + Σ_{σ:RC} fib_tc(DD) + Σ_{σ:SS} fib_tc(DD)
        -- DD_sub: Σ = subDD × tDD (fiber_card_balanced_DD_tc + validCol0_tc(DD))
        -- RC_sub: Σ = subRC × scDD (balanced_RC_aggregate_DD)
        -- SS_sub: Σ = 0 (fiber=0)
        -- Total: subDD × tDD + subRC × scDD = cpd.1 [h_cpd₁]
        -- Similarly for RC.
        -- Use card_tc_sum + Finset.sum split + known sub-sums
        -- card_tc(DD) = Σ_σ fib_tc(σ,DD) [by card_tc_sum]
        --            = Σ_{σ:DD} + Σ_{σ:RC} + Σ_{σ:SS} [by balanced_step split]
        -- Σ_{σ:DD} = subDD × tDD [fiber_card_balanced_DD_tc]
        -- Σ_{σ:RC} = subRC × scDD [balanced_RC_aggregate_DD]
        -- Σ_{σ:SS} = 0 [fiber_card_balanced_SS → fiber_tc ≤ fiber = 0]
        -- Sum = subDD × tDD + subRC × scDD = cpd.1 [h_cpd₁]
        -- Similarly for RC.
        -- These facts are all proved; assembly needs balanced_step split (Finset.sum over tc partition)
        -- Use h_step (total balanced step) + h_sum_tc + card_tc_sum for all tc to derive:
        have h_card_DD := card_tc_sum .DD
        have h_card_RC := card_tc_sum .RC
        have h_card_SS := card_tc_sum .SS
        -- h_card_DD : card_tc(DD) = Σ fib_tc(DD), etc.
        -- h_step : card = subDD × tSum + subRC × scSum
        -- h_sum_tc (via h_conv) : card = card_tc(DD) + card_tc(RC) + card_tc(SS)
        -- h_cpd₁ : cpd.1 = subDD × tDD + subRC × scDD (with subDD/RC = IH filter)
        -- h_cpd₂ : cpd.2.1 = subDD × tRC + subRC × scRC
        -- From balanced_RC_aggregate_DD/RC:
        have h_agg_DD := balanced_RC_aggregate_DD hQP hQP_lt h_bal
        have h_agg_RC := balanced_RC_aggregate_RC hQP hQP_lt h_bal
        -- Split Σ_σ fib_tc(σ, tc) into DD_sub + RC_sub + SS_sub
        -- using Finset.sum_filter_add_sum_filter_not
        have h_split_sum : ∀ tc' : TailClass,
            Finset.univ.sum (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) =
            (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              tailClass_D σ.val = .DD)).sum (fun σ =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) +
            (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              tailClass_D σ.val = .RC)).sum (fun σ =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) +
            (Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              tailClass_D σ.val = .SS)).sum (fun σ =>
              Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'}) := by
          intro tc'
          have step1 := (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft => tailClass_D σ.val = .DD)
            (fun σ => Fintype.card {τ : doubleDescent_D_fiber σ // tailClass_D τ.val.val = tc'})).symm
          have h_tri : ∀ σ : PBPSet .D μP.shiftLeft μQ.shiftLeft,
              tailClass_D σ.val = .DD ∨ tailClass_D σ.val = .RC ∨ tailClass_D σ.val = .SS := by
            intro σ; simp only [tailClass_D]; split_ifs
            · right; right; rfl
            · cases PBP.tailSymbol_D σ.val <;> simp
          have hf_eq : Finset.univ.filter (fun σ : PBPSet .D μP.shiftLeft μQ.shiftLeft =>
              ¬tailClass_D σ.val = .DD) =
            Finset.univ.filter (fun σ => tailClass_D σ.val = .RC ∨ tailClass_D σ.val = .SS) := by
            apply Finset.filter_congr; intro σ _
            exact ⟨fun h => (h_tri σ).elim (absurd · h) id,
                   fun h => h.elim (· ▸ by decide) (· ▸ by decide)⟩
          rw [step1, hf_eq, Finset.filter_or,
              Finset.sum_union (by rw [Finset.disjoint_filter]; intro σ _ hr hs
                                   rw [hr] at hs; exact absurd hs (by decide))]
          ring
        -- Assembly: use card_tc_sum + h_split_sum + sub-sum computations
        -- DD_sub sum = subDD × validCol0_tc via fiber_card_balanced_DD_tc (constant)
        -- RC_sub sum = from balanced_RC_aggregate_DD/RC
        -- SS_sub sum = 0 (fiber = 0)
        -- Total = cpd.1 / cpd.2.1 via h_cpd₁/h_cpd₂
        -- All ingredients proved. Finset.sum mechanics needed.
        sorry
termination_by dp.length
decreasing_by simp [List.length_cons]; omega


theorem card_PBPSet_D_per_tc (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hge3 : ∀ r ∈ dp, r ≥ 3)
    (hodd : ∀ r ∈ dp, Odd r) (hne : dp ≠ []) :
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .DD)).card = (countPBP_D dp).1 ∧
    (Finset.univ.filter (fun σ : PBPSet .D μP μQ =>
        tailClass_D σ.val = .RC)).card = (countPBP_D dp).2.1 :=
  (card_PBPSet_D_combined dp μP μQ hP hQ hsort hge3 hodd).2 hne

/-- **Main theorem**: `card(PBPSet .D μP μQ) = tripleSum(countPBP_D dp)`. -/
theorem card_PBPSet_D_eq_tripleSum_countPBP_D (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hge3 : ∀ r ∈ dp, r ≥ 3)
    (hodd : ∀ r ∈ dp, Odd r) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D dp) :=
  (card_PBPSet_D_combined dp μP μQ hP hQ hsort hge3 hodd).1
