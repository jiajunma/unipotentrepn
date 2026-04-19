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

A dual partition `Ǒ` is **quasi-distinguished** when `r_i > r_{i+1}` for
every `i ≥ 2` (1-indexed), equivalently, all row lengths from position 2
onwards are strictly decreasing. The top two rows may coincide.

Paper [BMSZ] §11 uses this hypothesis to guarantee that `L_τ` is a
single MYD (not a formal sum) and that the descent-induction closes.

Reference: `docs/myd_computation.md` — "quasi-distinguished at top:
r₂(Ǒ) > r₃(Ǒ)". The recursive version (used by Props 11.13–11.17)
propagates to every descent level, giving strict decrease from index 2.
-/

/-- Strict decrease of `dp` from index 1 onwards (0-indexed), i.e.
    `dp[1] > dp[2] > dp[3] > ...`. Top two rows `dp[0], dp[1]` may coincide. -/
def IsQuasiDistinguished (dp : DualPart) : Prop :=
  List.IsChain (· > ·) (dp.drop 1)

instance (dp : DualPart) : Decidable (IsQuasiDistinguished dp) := by
  unfold IsQuasiDistinguished; exact inferInstance

/-- Empty dp is quasi-distinguished. -/
theorem IsQuasiDistinguished_nil : IsQuasiDistinguished [] := by
  unfold IsQuasiDistinguished; simp

/-- Single-row dp is quasi-distinguished. -/
theorem IsQuasiDistinguished_singleton (r : ℕ) :
    IsQuasiDistinguished [r] := by
  unfold IsQuasiDistinguished; simp [List.IsChain]

/-- Two-row dp is always quasi-distinguished (only `r_1, r_2` — no `r_3`). -/
theorem IsQuasiDistinguished_pair (r₁ r₂ : ℕ) :
    IsQuasiDistinguished [r₁, r₂] := by
  unfold IsQuasiDistinguished; simp [List.IsChain]

end BMSZ
