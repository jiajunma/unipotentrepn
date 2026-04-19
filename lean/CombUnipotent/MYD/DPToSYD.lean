/-
# Dual partition → Orbit SYD (Def 9.1 via BV duality)

Reference: [BMSZ] arXiv:1712.05552, §9.1–9.8; [BMSZb] §10.

Given a dual partition `dp : DualPart` (row lengths of Ǒ), the orbit
O is the BV dual: its partition is the *transpose* of dp. The SYD of O
pairs each row length with a (p, q) signature splitting the row count.

For the canonical quasi-distinguished orbit we default to:
- at γ-parity-forced rows (B/D: even i; C/M: odd i): split `(n/2, n/2)`
  so `p = q` is trivially satisfied
- at free rows: `(n, 0)` (all positive)

Note: the split-sum `p + q` may differ from `n` (e.g. at odd counts on
parity-forced rows the floor of `n/2` twice sums to `n - 1`). This is
immaterial for the SYD *validity predicate* (which only enforces
parity), but means the resulting SYD does NOT faithfully encode the
orbit's full partition in borderline cases. For the bijection work,
we only care about parity + signature matching, so this is acceptable.
-/
import CombUnipotent.MYD.SYD
import CombUnipotent.Counting

namespace BMSZ

/-- Number of rows of length `ℓ` in partition `λ`. -/
def rowCount (part : List ℕ) (ℓ : ℕ) : ℕ :=
  (part.filter (· = ℓ)).length

/-- Maximum row length in a partition (0 for empty). -/
def rowMax (part : List ℕ) : ℕ :=
  part.foldr max 0

/-- Partition transpose (conjugate): row lengths of λ' are
    `λ'_i = #{j : λ_j ≥ i}`. Returned as a List ℕ with one entry per
    row of λ' (which has `rowMax λ` rows). -/
def partTranspose (part : List ℕ) : List ℕ :=
  (List.range (rowMax part)).map fun i => (part.filter (· ≥ i + 1)).length

/-- Row-length multiplicity list for a partition: entry `j` counts
    the number of rows of length `j + 1`. -/
def rowMultiplicities (part : List ℕ) : List ℕ :=
  (List.range (rowMax part)).map fun j => rowCount part (j + 1)

/-- Build an SYD row `(p, q)` from a count `n` at 1-indexed row length
    `i`, following the γ-parity convention:
    - forced (p = q): `(n / 2, n / 2)`
    - free: `(n, 0)`. -/
def sydRowFromCount (γ : RootType) (i : ℕ) (n : ℕ) : ℕ × ℕ :=
  if SYDParityForced γ i then (n / 2, n / 2) else (n, 0)

theorem sydRowFromCount_valid (γ : RootType) (i n : ℕ) :
    SYDRowValid γ i (sydRowFromCount γ i n) := by
  unfold SYDRowValid sydRowFromCount
  split_ifs with h
  · intro _; rfl
  · intro h_forced; exact absurd h_forced h

/-- Build SYD rows by mapping each `(count, index)` pair to an `(p, q)` entry. -/
def buildRows (γ : RootType) (counts : List ℕ) : List (ℕ × ℕ) :=
  (List.range counts.length).map fun j =>
    sydRowFromCount γ (j + 1) ((counts[j]?).getD 0)

theorem buildRows_length (γ : RootType) (counts : List ℕ) :
    (buildRows γ counts).length = counts.length := by
  unfold buildRows; simp

theorem buildRows_getElem (γ : RootType) (counts : List ℕ)
    (j : ℕ) (h : j < (buildRows γ counts).length) :
    (buildRows γ counts)[j] =
      sydRowFromCount γ (j + 1) ((counts[j]?).getD 0) := by
  unfold buildRows
  rw [List.getElem_map, List.getElem_range]

/-- **Orbit SYD from dual partition**: transpose `dp`, count row lengths,
    apply the γ-parity split. Paper: quasi-distinguished orbit associated
    to Ǒ with partition = transpose(dp). -/
def dpToSYD (γ : RootType) (dp : DualPart) : SYD γ :=
  let O_part := partTranspose dp
  let counts := rowMultiplicities O_part
  { rows := buildRows γ counts
    valid := by
      intro j hj
      rw [buildRows_getElem]
      exact sydRowFromCount_valid γ (j + 1) _ }

/-- Sanity check: empty dp → empty SYD. -/
theorem dpToSYD_empty (γ : RootType) : dpToSYD γ [] = SYD.empty γ := by
  apply SYD.ext
  show buildRows γ (rowMultiplicities (partTranspose [])) = []
  simp [partTranspose, rowMax, rowMultiplicities, buildRows]

/-! ## Quasi-distinguished dual partitions

A dual partition `Ǒ` is **quasi-distinguished** (for root type γ) when
every γ-pair is either **primitive** (strictly decreasing) or **tailed**
(second element is 0) — equivalently, no γ-pair is **balanced**
(both positive and equal).

The γ-pair indexing convention (paper [BMSZb] §10):
- γ ∈ {B⁺, B⁻, D}: pairs `(2i, 2i+1)` for `i ≥ 1` (1-indexed), i.e.
  `(r_2, r_3), (r_4, r_5), (r_6, r_7), ...`
- γ ∈ {C, M}: pairs `(2i-1, 2i)` for `i ≥ 1`, i.e.
  `(r_1, r_2), (r_3, r_4), (r_5, r_6), ...`

A γ-pair `(r_{2i}, r_{2i+1})` (B/D) or `(r_{2i-1}, r_{2i})` (C/M) is:
- **primitive** if first > second (strict inequality, positive first)
- **tailed** if second = 0
- **balanced** if first = second > 0 (both positive, equal)

Since `dp` is a partition (decreasing), `primitive ∨ balanced ∨ tailed`
holds for every pair. Quasi-distinguished excludes the balanced case.

Reference: `docs/recursive_counting.md` §"balanced pair"; [BMSZb] Prop
10.11 (b): "If (2,3) ∉ PP_★(Ǒ) [balanced pair]".

Paper [BMSZ] §11 uses QD to guarantee `L_τ` is a single MYD.
-/

/-- 0-indexed offset of the γ-pairing: pairs start at this offset and
    step by 2. For B/D this is 1 (pairs `(1,2), (3,4), ...`); for C/M
    this is 0 (pairs `(0,1), (2,3), ...`). -/
def pairOffset (γ : RootType) : ℕ :=
  match γ with
  | .Bplus | .Bminus | .D => 1
  | .C | .M => 0

/-- Is the 0-indexed position `k` the start of a γ-pair? I.e., does a
    pair `(k, k+1)` exist in the γ-pairing convention? -/
def IsPairStart (γ : RootType) (k : ℕ) : Prop :=
  k ≥ pairOffset γ ∧ (k - pairOffset γ) % 2 = 0

instance (γ : RootType) (k : ℕ) : Decidable (IsPairStart γ k) := by
  unfold IsPairStart; exact inferInstance

/-- A γ-pair starting at 0-indexed position `k` in `dp` is **balanced**:
    both `dp[k]` and `dp[k+1]` exist, are positive, and equal. -/
def IsBalancedPair (γ : RootType) (dp : DualPart) (k : ℕ) : Prop :=
  IsPairStart γ k ∧ ∃ (h₁ : k < dp.length) (h₂ : k + 1 < dp.length),
    dp[k] = dp[k + 1] ∧ 0 < dp[k]

instance (γ : RootType) (dp : DualPart) (k : ℕ) :
    Decidable (IsBalancedPair γ dp k) := by
  unfold IsBalancedPair; exact inferInstance

/-- **Quasi-distinguished** (paper [BMSZ] §11): the dual partition has
    no balanced γ-pair. Every pair is either primitive (first > second)
    or tailed (second = 0). -/
def IsQuasiDistinguished (γ : RootType) (dp : DualPart) : Prop :=
  ∀ k, ¬ IsBalancedPair γ dp k

instance (γ : RootType) (dp : DualPart) :
    Decidable (IsQuasiDistinguished γ dp) := by
  unfold IsQuasiDistinguished
  -- Only need to check k < dp.length
  refine decidable_of_iff (∀ k ∈ List.range dp.length, ¬ IsBalancedPair γ dp k) ?_
  constructor
  · intro h k
    by_cases hk : k < dp.length
    · exact h k (List.mem_range.mpr hk)
    · intro hbad
      obtain ⟨_, h₁, _⟩ := hbad
      exact hk h₁
  · intro h k _; exact h k

/-- Empty dp is quasi-distinguished (no pairs at all). -/
theorem IsQuasiDistinguished_nil (γ : RootType) :
    IsQuasiDistinguished γ [] := by
  intro k ⟨_, h₁, _⟩
  exact absurd h₁ (by simp)

/-- Single-row dp is quasi-distinguished (no complete pair). -/
theorem IsQuasiDistinguished_singleton (γ : RootType) (r : ℕ) :
    IsQuasiDistinguished γ [r] := by
  intro k ⟨_, _, h₂, _⟩
  simp at h₂

end BMSZ
