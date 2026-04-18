/-
# Lemma 11.1(b): Concrete PBPExt at r₁(Ǒ) = 1 with cardinality match

Reference: [BMSZ] Lemma 11.1(b) — bijection between
`PBP^ext_★(Ǒ) × ℤ/2ℤ` and `{(a, b) ∈ ℤ × ℤ : |a| + |b| = |O|}` when `r₁(Ǒ) ≤ 1`.

This file constructs the **PBP side** at the meaningful stratum `r₁(Ǒ) = 1`
for `★ = D` (the case where the cardinality match is non-trivial), and shows
the cardinality matches `SignTargetSet N` so that
`lemma_11_1_b_bijection_concrete` can be applied.

## Setup

For `★ = D` with `r₁(Ǒ) = 1`, the dual partition `Ǒ` is the all-ones list
`List.replicate (2*m+2) 1` (length `2(m+1) ≥ 2`, all entries `= 1`).
The orbit `O = BV-dual(Ǒ)` is a single column of height `N = 2(m+1)`.

`PBP^ext_D(Ǒ) = PBPSet .D μP μQ` where `μP, μQ` are the column-length-derived
Young diagrams from `Ǒ` (no PP fanout, since the all-ones dp has no admissible
primitive pairs at the descent level: tail symbols are only `s` or `dot`).

## Main results

- `countPBP_D_replicate_2_succ_succ`: the recursive formula evaluates to
  `(1, 2m+2, 2m+1)` on `List.replicate (2m+2) 1`.
- `tripleSum_countPBP_D_replicate_2_succ_succ`: total count is `4m + 4 = 4(m+1)`.
- `PBPExt_at_r1_eq_1_D_card`: `Fintype.card (PBPSet .D μP μQ) = 4m + 4`.
- `PBPExt_at_r1_eq_1_D_card_match_concrete`: the form
  `card (PBPSet .D μP μQ × Fin 2) = if N = 0 then 1 else 4*N` for `N = 2(m+1)`.
  This is exactly the cardinality hypothesis `lemma_11_1_b_bijection_concrete`
  consumes.

For `★ ∈ {B+, B-}` at `r₁(Ǒ) = 1`: the constraint forces `Ǒ = []` (since
B-type requires all even parts), so the bijection is trivial / degenerate.
Only the D-type case carries content here.
-/
import CombUnipotent.MYD
import CombUnipotent.CountingProof.Correspondence

open Classical

/-! ## Recursive formula for `countPBP_D` on `List.replicate (2m+2) 1` -/

/-- The cons₂ rewrite for `List.replicate (2*(n+1)+2) 1`. -/
private lemma replicate_2_succ_succ_cons (n : ℕ) :
    List.replicate (2 * (n + 1) + 2) 1 =
      (1 : ℕ) :: 1 :: List.replicate (2 * n + 2) 1 := by
  rw [show 2 * (n + 1) + 2 = (2 * n + 2).succ.succ from by omega]
  rfl

/-- For `n ≥ 0`, the head of `List.replicate (2n+2) 1` is `1`. -/
private lemma replicate_2_succ_succ_head (n : ℕ) :
    (List.replicate (2 * n + 2) 1).head?.getD 0 = 1 := by
  rw [show 2 * n + 2 = (2 * n + 1).succ from rfl]
  rfl

/-- **Key recursion**: `countPBP_D` evaluated on the all-ones dual partition
    `[1, 1, …, 1]` of length `2(m+1)` equals `(1, 2(m+1), 2m+1)`.

    Proof by induction on `m`. The structural shape of the recursion:
    - Base `m = 0`: dp = `[1, 1]`. Singleton-tail primitive case. `decide`.
    - Step `m + 1`: dp = `1 :: 1 :: rest` where `rest = replicate (2m+2) 1`.
      The pair `(r₂, r₃) = (1, 1)` is **balanced** (since `r₂ = r₃`), so
      `countPBP_D` uses the matrix-multiply branch with
      `tailCoeffs 1 = ((1, 2, 1), (0, 1, 1))`. Combined with the IH
      `(1, 2m+2, 2m+1)` for `rest`, the formula closes by `ring`. -/
lemma countPBP_D_replicate_2_succ_succ (m : ℕ) :
    countPBP_D (List.replicate (2 * m + 2) 1) = (1, 2 * m + 2, 2 * m + 1) := by
  induction m with
  | zero => decide
  | succ n ih =>
    rw [replicate_2_succ_succ_cons]
    show countPBP_D (1 :: 1 :: List.replicate (2 * n + 2) 1) = _
    rw [countPBP_D]
    simp only [replicate_2_succ_succ_head]
    rw [if_neg (by omega)]
    rw [ih]
    show (1 * 1 + (2 * n + 2) * 0,
          1 * 2 + (2 * n + 2) * 1,
          1 * 1 + (2 * n + 2) * 1) =
         (1, 2 * (n + 1) + 2, 2 * (n + 1) + 1)
    ext
    all_goals ring

/-- The triple-sum of `countPBP_D (replicate (2m+2) 1)` equals `4(m+1)`. -/
lemma tripleSum_countPBP_D_replicate_2_succ_succ (m : ℕ) :
    tripleSum (countPBP_D (List.replicate (2 * m + 2) 1)) = 4 * m + 4 := by
  rw [countPBP_D_replicate_2_succ_succ]
  simp [tripleSum]; ring

/-! ## Sortedness and oddness for `List.replicate k 1` -/

/-- `List.replicate k 1` is sorted in decreasing order (vacuously, all elements
    equal). -/
lemma replicate_one_sortedGE (k : ℕ) : (List.replicate k 1).SortedGE := by
  unfold List.SortedGE
  intro i j _
  simp [List.getElem_replicate]

/-- All entries of `List.replicate k 1` are odd (they are all `1`). -/
lemma replicate_one_all_odd (k : ℕ) : ∀ r ∈ List.replicate k 1, Odd r := by
  intro r hr
  rw [List.mem_replicate] at hr
  rcases hr with ⟨_, rfl⟩
  decide

/-! ## PBP^ext at r₁(Ǒ) = 1 for D type

The PBP^ext at this stratum is the disjoint union of `PBP_D(Ǒ, ℘)` over
`℘ ⊆ PP(Ǒ)`. Since `Ǒ = [1, 1, …, 1]` has no admissible primitive pairs
at the descent level (all pairs `(r₂, r₃) = (1, 1)` have equal heights),
the union collapses to the single term `PBP_D(Ǒ, ∅) = PBPSet .D μP μQ`.

We define the type as a transparent `abbrev` for `PBPSet .D μP μQ`. -/

/-- **PBP^ext_D at r₁(Ǒ) = 1**, with `|Ǒ| = 2(m+1)` (so the orbit `O` has
    `N = 2(m+1)` cells in a single column).

    Concretely this is `PBPSet .D μP μQ` where `μP, μQ` have column lengths
    matching `dpartColLensP_D / dpartColLensQ_D` of `List.replicate (2m+2) 1`. -/
abbrev PBPExt_at_r1_eq_1_D (μP μQ : YoungDiagram) : Type := PBPSet .D μP μQ

/-- **Cardinality of `PBPExt_at_r1_eq_1_D` for the all-ones Ǒ of size `2(m+1)`.**

    By `card_PBPSet_D_combined` plus the closed-form `tripleSum = 4(m+1)`. -/
theorem PBPExt_at_r1_eq_1_D_card (m : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D (List.replicate (2 * m + 2) 1))
    (hQ : μQ.colLens = dpartColLensQ_D (List.replicate (2 * m + 2) 1)) :
    Fintype.card (PBPExt_at_r1_eq_1_D μP μQ) = 4 * m + 4 := by
  show Fintype.card (PBPSet .D μP μQ) = 4 * m + 4
  have h_combined := card_PBPSet_D_combined (List.replicate (2 * m + 2) 1) μP μQ
    hP hQ (replicate_one_sortedGE _) (replicate_one_all_odd _)
  rw [h_combined.1, tripleSum_countPBP_D_replicate_2_succ_succ]

/-- **Cardinality of `PBPExt × Fin 2`** matches `SignTargetSet (2(m+1))`.

    `card (PBPExt × Fin 2) = (4m + 4) * 2 = 8m + 8 = 4 * (2m + 2)`. -/
theorem PBPExt_at_r1_eq_1_D_times_Fin2_card (m : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D (List.replicate (2 * m + 2) 1))
    (hQ : μQ.colLens = dpartColLensQ_D (List.replicate (2 * m + 2) 1)) :
    Fintype.card (PBPExt_at_r1_eq_1_D μP μQ × Fin 2) =
      Fintype.card (SignTargetSet (2 * m + 2)) := by
  rw [Fintype.card_prod, PBPExt_at_r1_eq_1_D_card m μP μQ hP hQ,
      Fintype.card_fin,
      SignTargetSet_card_pos (by omega : (0 : ℕ) < 2 * m + 2)]
  ring

/-- **Cardinality match in the form consumed by `lemma_11_1_b_bijection_concrete`:**
    `card (PBPExt × Fin 2) = if N = 0 then 1 else 4 * N` for `N = 2(m+1) > 0`. -/
theorem PBPExt_at_r1_eq_1_D_card_match_concrete (m : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D (List.replicate (2 * m + 2) 1))
    (hQ : μQ.colLens = dpartColLensQ_D (List.replicate (2 * m + 2) 1)) :
    Fintype.card (PBPExt_at_r1_eq_1_D μP μQ × Fin 2) =
      (if (2 * m + 2) = 0 then 1 else 4 * (2 * m + 2)) := by
  rw [Fintype.card_prod, PBPExt_at_r1_eq_1_D_card m μP μQ hP hQ,
      Fintype.card_fin]
  simp only [show (2 * m + 2 : ℕ) ≠ 0 from by omega, if_false]
  ring

/-! ## Application skeleton: `lemma_11_1_b_bijection_concrete` consumer

Given an injective map
  `f : PBPExt_at_r1_eq_1_D μP μQ × Fin 2 → SignTargetSet (2*m+2)`
(coming from the signed-first-entry construction), the cardinality match
above plus `lemma_11_1_b_bijection_concrete` immediately yields bijectivity. -/

/-- **Lemma 11.1(b) bijection (D type, r₁(Ǒ) = 1):** any injective map from
    `PBPExt_at_r1_eq_1_D × Fin 2` to `SignTargetSet (2*m+2)` is bijective.

    The injective map is built from `lemma_11_1_signed_first_entry` applied
    to each PBP (via Lemma 11.1(a)); injectivity on the `(p, q)` part is
    `lemma_11_1_signed_injective_pq`. The cardinality side is closed here. -/
theorem lemma_11_1_b_bijection_D (m : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D (List.replicate (2 * m + 2) 1))
    (hQ : μQ.colLens = dpartColLensQ_D (List.replicate (2 * m + 2) 1))
    (f : PBPExt_at_r1_eq_1_D μP μQ × Fin 2 → SignTargetSet (2 * m + 2))
    (hf : Function.Injective f) :
    Function.Bijective f :=
  lemma_11_1_b_bijection_concrete
    (PBPExt_at_r1_eq_1_D_card_match_concrete m μP μQ hP hQ) f hf

/-! ## Sanity checks via `decide` -/

/-- Sanity: `m = 0` (Ǒ = `[1, 1]`) gives `(1, 2, 1)`. -/
example : countPBP_D (List.replicate 2 1) = (1, 2, 1) := by decide

/-- Sanity: `m = 1` (Ǒ = `[1, 1, 1, 1]`) gives `(1, 4, 3)`. -/
example : countPBP_D (List.replicate 4 1) = (1, 4, 3) := by decide

/-- Sanity: `m = 2` (Ǒ = `[1, 1, 1, 1, 1, 1]`) gives `(1, 6, 5)`. -/
example : countPBP_D (List.replicate 6 1) = (1, 6, 5) := by decide

/-- Sanity: tripleSum at `m = 3` is `4 * 3 + 4 = 16`. -/
example : tripleSum (countPBP_D (List.replicate 8 1)) = 16 := by decide
