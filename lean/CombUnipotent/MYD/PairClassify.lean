/-
# Relationships among γ-pair categories (paper Def 3.5, 4.8)

Reference: [BMSZ] arXiv:1712.05552, Definitions 3.5 and 4.8.

This file establishes:
1. **Exclusivity**: the four categories vacant / balanced / tailed /
   primitive are mutually exclusive.
2. **Exhaustivity under good parity**: for a partition `dp` satisfying
   the root-type good parity (B/M: all entries even; C/D: all entries
   odd), every γ-pair belongs to exactly one category.
3. **QD characterization**: `IsQuasiDistinguished γ dp` ⟺ every γ-pair
   in `dp` is vacant, tailed, or primitive (i.e., not balanced).

Note: existing counting proofs (`CountingProof/CorrespondenceB.lean`
etc.) use the simplified "primitive iff r₂ > r₃" form under good parity;
paper's Def 3.5 adds the parity condition which is automatic in that
setting. See paper's remark after Def 3.5.
-/
import CombUnipotent.MYD.DPToSYD
import CombUnipotent.MYD

namespace BMSZ

/-! ## Connection to the existing `PPSet` (paper's ℘ vs `PP_★(Ǒ)`)

`PPSet := Finset ℕ` (MYD.lean:252) represents the choice `℘` of primitive
pairs for a PBP. Its indexing convention ("i represents paper pair
(i+1, i+2)") matches our 0-indexed `IsPrimitivePair γ dp k` exactly:
- B/D: k ∈ {1, 3, 5, …} → paper pairs (2, 3), (4, 5), …
- C/M: k ∈ {0, 2, 4, …} → paper pairs (1, 2), (3, 4), …

We now define the universe `PP_★(Ǒ)` = `primitivePPOf γ dp`.
-/

/-- **Paper's `PP_★(Ǒ)`**: the set of all primitive γ-pairs in `dp`.
    Paper [BMSZ] Def 3.5 below. -/
def primitivePPOf (γ : RootType) (dp : DualPart) : PPSet :=
  (Finset.range dp.length).filter (IsPrimitivePair γ dp ·)

theorem mem_primitivePPOf_iff (γ : RootType) (dp : DualPart) (k : ℕ) :
    k ∈ primitivePPOf γ dp ↔ IsPrimitivePair γ dp k := by
  unfold primitivePPOf
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro hprim
    refine ⟨?_, hprim⟩
    -- IsPrimitivePair requires pairEntry dp k > pairEntry dp (k+1) ≥ 0
    -- so pairEntry dp k > 0, forcing k < dp.length
    obtain ⟨_, hlt, _⟩ := hprim
    have hk_pos : 0 < pairEntry dp k := by omega
    by_contra hk
    push_neg at hk
    have : pairEntry dp k = 0 := by
      unfold pairEntry
      simp [List.getElem?_eq_none hk]
    omega

variable (γ : RootType) (dp : DualPart) (k : ℕ)

/-! ## Exclusivity of pair categories

For any γ, dp, k, at most one of the four categories holds.
-/

theorem IsVacantPair_and_IsBalancedPair_iff_False :
    ¬ (IsVacantPair γ dp k ∧ IsBalancedPair γ dp k) := by
  intro ⟨⟨_, hvk, _⟩, ⟨_, hpos, _⟩⟩
  omega

theorem IsVacantPair_and_IsTailedPair_iff_False :
    ¬ (IsVacantPair γ dp k ∧ IsTailedPair γ dp k) := by
  intro ⟨⟨_, hvk, _⟩, ⟨_, hlt, _⟩⟩
  omega

theorem IsVacantPair_and_IsPrimitivePair_iff_False :
    ¬ (IsVacantPair γ dp k ∧ IsPrimitivePair γ dp k) := by
  intro ⟨⟨_, hvk, _⟩, ⟨_, hlt, _⟩⟩
  omega

theorem IsBalancedPair_and_IsTailedPair_iff_False :
    ¬ (IsBalancedPair γ dp k ∧ IsTailedPair γ dp k) := by
  intro ⟨⟨_, _, hbEq⟩, ⟨_, hlt, _⟩⟩
  omega

theorem IsBalancedPair_and_IsPrimitivePair_iff_False :
    ¬ (IsBalancedPair γ dp k ∧ IsPrimitivePair γ dp k) := by
  intro ⟨⟨_, _, hbEq⟩, ⟨_, hlt, _⟩⟩
  omega

theorem IsTailedPair_and_IsPrimitivePair_iff_False :
    ¬ (IsTailedPair γ dp k ∧ IsPrimitivePair γ dp k) := by
  intro ⟨⟨_, _, h_odd⟩, ⟨_, _, h_even⟩⟩
  omega

/-! ## Exhaustivity under the partition property

A ★-pair in a weakly-decreasing partition (`pairEntry k ≥ pairEntry (k+1)`)
belongs to exactly one of vacant, balanced, tailed, primitive, given
`IsPairStart γ k`.
-/

/-- A dp satisfies the partition property up to position `k` if
    `pairEntry dp k ≥ pairEntry dp (k+1)`. -/
def PairMonotone (dp : DualPart) (k : ℕ) : Prop :=
  pairEntry dp (k + 1) ≤ pairEntry dp k

/-- Exhaustivity: given a γ-pair start and partition-monotone at k,
    the pair is exactly one of the four categories. -/
theorem pair_category_exhaustive
    (hstart : IsPairStart γ k) (hmono : PairMonotone dp k) :
    IsVacantPair γ dp k ∨ IsBalancedPair γ dp k ∨
    IsTailedPair γ dp k ∨ IsPrimitivePair γ dp k := by
  unfold IsVacantPair IsBalancedPair IsTailedPair IsPrimitivePair
  unfold PairMonotone at hmono
  by_cases hvk : pairEntry dp k = 0
  · -- pairEntry k = 0 → (hmono) pairEntry (k+1) = 0 → vacant
    left
    have : pairEntry dp (k + 1) = 0 := by omega
    exact ⟨hstart, hvk, this⟩
  · -- pairEntry k > 0
    by_cases hvk1 : pairEntry dp (k + 1) = pairEntry dp k
    · right; left
      exact ⟨hstart, Nat.pos_of_ne_zero hvk, hvk1.symm⟩
    · -- strict decrease
      have hlt : pairEntry dp (k + 1) < pairEntry dp k := by
        rcases lt_or_eq_of_le hmono with h | h
        · exact h
        · exact absurd h hvk1
      -- tailed iff diff odd; primitive iff diff even
      by_cases h_odd : (pairEntry dp k - pairEntry dp (k + 1)) % 2 = 1
      · right; right; left; exact ⟨hstart, hlt, h_odd⟩
      · right; right; right
        refine ⟨hstart, hlt, ?_⟩
        omega

/-! ## Quasi-distinguished characterization

`IsQuasiDistinguished γ dp` means no balanced pair; equivalently, every
γ-pair is vacant, tailed, or primitive.
-/

theorem isQuasiDistinguished_iff_all_non_balanced :
    IsQuasiDistinguished γ dp ↔
    ∀ k, IsPairStart γ k →
      IsVacantPair γ dp k ∨ IsTailedPair γ dp k ∨ IsPrimitivePair γ dp k ∨
      ¬ PairMonotone dp k := by
  constructor
  · intro hqd k hstart
    by_cases hmono : PairMonotone dp k
    · rcases pair_category_exhaustive γ dp k hstart hmono with
        hv | hb | ht | hp
      · exact Or.inl hv
      · exact absurd hb (hqd k)
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr hmono))
  · intro h k hbal
    have hstart := hbal.1
    rcases h k hstart with hv | ht | hp | hnmono
    · exact IsVacantPair_and_IsBalancedPair_iff_False γ dp k ⟨hv, hbal⟩
    · exact IsBalancedPair_and_IsTailedPair_iff_False γ dp k ⟨hbal, ht⟩
    · exact IsBalancedPair_and_IsPrimitivePair_iff_False γ dp k ⟨hbal, hp⟩
    · apply hnmono
      -- In IsBalancedPair, pairEntry k = pairEntry (k+1), so PairMonotone holds.
      obtain ⟨_, _, heq⟩ := hbal
      unfold PairMonotone
      omega

end BMSZ
