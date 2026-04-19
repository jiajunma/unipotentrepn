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

Paper [BMSZ] arXiv:1712.05552:

**Definition 3.5**: A ★-pair is a pair `(i, i+1)` of consecutive positive
integers where:
- i is odd if ★ ∈ {C, C̃, C*}
- i is even if ★ ∈ {B, D, D*}

A ★-pair `(i, i+1)` is:
- **vacant in Ǒ**: `r_i(Ǒ) = r_{i+1}(Ǒ) = 0`
- **balanced in Ǒ**: `r_i(Ǒ) = r_{i+1}(Ǒ) > 0`
- **tailed in Ǒ**: `r_i(Ǒ) - r_{i+1}(Ǒ)` positive and odd
- **primitive in Ǒ**: `r_i(Ǒ) - r_{i+1}(Ǒ)` positive and even

**Definition 4.8**: Ǒ is **quasi-distinguished** iff there is no ★-pair
that is balanced in Ǒ.

In Lean we use 0-indexed positions, so the 1-indexed paper pair `(i, i+1)`
becomes the 0-indexed pair `(i-1, i)`. Pair starts:
- γ ∈ {B⁺, B⁻, D}: 0-indexed pair starts at odd positions (1, 3, 5, …)
  corresponding to 1-indexed (2, 3), (4, 5), …
- γ ∈ {C, M}: 0-indexed pair starts at even positions (0, 2, 4, …)
  corresponding to 1-indexed (1, 2), (3, 4), …

(We omit C*, D* per the project directive skipping those real forms.)
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

/-- Get entry at 0-indexed position `k` in `dp`, defaulting to 0 if out of bounds. -/
def pairEntry (dp : DualPart) (k : ℕ) : ℕ := (dp[k]?).getD 0

/-- A γ-pair starting at 0-indexed position `k` in `dp` is **vacant**
    (paper Def 3.5): both entries are 0. -/
def IsVacantPair (γ : RootType) (dp : DualPart) (k : ℕ) : Prop :=
  IsPairStart γ k ∧ pairEntry dp k = 0 ∧ pairEntry dp (k + 1) = 0

/-- A γ-pair starting at 0-indexed position `k` is **balanced** in `dp`
    (paper Def 3.5): both entries positive and equal. -/
def IsBalancedPair (γ : RootType) (dp : DualPart) (k : ℕ) : Prop :=
  IsPairStart γ k ∧ 0 < pairEntry dp k ∧ pairEntry dp k = pairEntry dp (k + 1)

/-- A γ-pair starting at 0-indexed position `k` is **tailed** in `dp`
    (paper Def 3.5): the difference is positive and odd. -/
def IsTailedPair (γ : RootType) (dp : DualPart) (k : ℕ) : Prop :=
  IsPairStart γ k ∧ pairEntry dp (k + 1) < pairEntry dp k ∧
  (pairEntry dp k - pairEntry dp (k + 1)) % 2 = 1

/-- A γ-pair starting at 0-indexed position `k` is **primitive** in `dp`
    (paper Def 3.5): the difference is positive and even. -/
def IsPrimitivePair (γ : RootType) (dp : DualPart) (k : ℕ) : Prop :=
  IsPairStart γ k ∧ pairEntry dp (k + 1) < pairEntry dp k ∧
  (pairEntry dp k - pairEntry dp (k + 1)) % 2 = 0

instance (γ : RootType) (dp : DualPart) (k : ℕ) :
    Decidable (IsVacantPair γ dp k) := by
  unfold IsVacantPair; exact inferInstance

instance (γ : RootType) (dp : DualPart) (k : ℕ) :
    Decidable (IsBalancedPair γ dp k) := by
  unfold IsBalancedPair; exact inferInstance

instance (γ : RootType) (dp : DualPart) (k : ℕ) :
    Decidable (IsTailedPair γ dp k) := by
  unfold IsTailedPair; exact inferInstance

instance (γ : RootType) (dp : DualPart) (k : ℕ) :
    Decidable (IsPrimitivePair γ dp k) := by
  unfold IsPrimitivePair; exact inferInstance

/-- **Quasi-distinguished** (paper [BMSZ] Def 4.8): the dual partition
    has no balanced γ-pair. Every γ-pair is vacant, tailed, or primitive. -/
def IsQuasiDistinguished (γ : RootType) (dp : DualPart) : Prop :=
  ∀ k, ¬ IsBalancedPair γ dp k

instance (γ : RootType) (dp : DualPart) :
    Decidable (IsQuasiDistinguished γ dp) := by
  unfold IsQuasiDistinguished
  -- Out-of-range k: pairEntry dp k = 0, so 0 < 0 fails and IsBalancedPair is False.
  refine decidable_of_iff (∀ k ∈ List.range dp.length, ¬ IsBalancedPair γ dp k) ?_
  constructor
  · intro h k
    by_cases hk : k < dp.length
    · exact h k (List.mem_range.mpr hk)
    · intro ⟨_, hpos, _⟩
      have : pairEntry dp k = 0 := by
        unfold pairEntry
        simp [List.getElem?_eq_none (Nat.le_of_not_lt hk)]
      omega
  · intro h k _; exact h k

/-- Empty dp is quasi-distinguished (no pairs). -/
theorem IsQuasiDistinguished_nil (γ : RootType) :
    IsQuasiDistinguished γ [] := by
  intro k ⟨_, hpos, _⟩
  simp [pairEntry] at hpos

/-- Single-row dp is quasi-distinguished. -/
theorem IsQuasiDistinguished_singleton (γ : RootType) (r : ℕ) :
    IsQuasiDistinguished γ [r] := by
  intro k ⟨_, hpos, heq⟩
  unfold pairEntry at hpos heq
  match k with
  | 0 => simp at heq; subst heq; exact absurd hpos (by simp)
  | k + 1 => simp at hpos

end BMSZ
