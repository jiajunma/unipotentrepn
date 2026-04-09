/-
# Recursive Counting of Painted Bipartitions

Reference: [BMSZb] Propositions 10.11–10.12.

The recursive formulas count #PBP_★(Ǒ, ∅) by decomposing into
tail-symbol classes {d}, {c,r}, {s} for B/D types, and reducing
C/M to B/D via descent injectivity.
-/
import CombUnipotent.Basic

/-! ## Dual partition (orbit) -/

/-- A dual partition: list of positive naturals (row lengths of orbit Ǒ). -/
abbrev DualPart := List ℕ

/-! ## ν function -/

/-- ν(n) = n + 1 (for ℕ, always ≥ 1). Used in tail polynomial evaluation. -/
@[inline] def nu (n : ℕ) : ℕ := n + 1

/-! ## Helper: tail polynomials at p=q=1 -/

/-- Tail polynomial coefficients for (DD, RC, SS) at p=q=1.
    k = (r₁ - r₂)/2 + 1 (excess half-length + 1). -/
def tailCoeffs (k : ℕ) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  let tDD := nu (k - 1) + (if k ≥ 2 then nu (k - 2) else 0)
  let tRC := 2 * nu (k - 1)
  let tSS := 1
  let scDD := 2 * (if k ≥ 2 then nu (k - 2) else 0)
  let scRC := nu (k - 1) + (if k ≥ 2 then nu (k - 2) else 0)
  let scSS := 1
  ((tDD, tRC, tSS), (scDD, scRC, scSS))

/-! ## Counting for D type (Proposition 10.11) -/

/-- Count PBPs for D type, returning (DD, RC, SS) triple.
    Reference: [BMSZb] Proposition 10.11.

    Recursive on the dual partition, removing two rows at each step.
    Base case: empty → (1, 0, 0).

    k = (r₁ - r₂)/2 + 1.
    Case (a) r₂ > r₃: (DD, RC, SS) = total · (TDD, TRC, TSS)
    Case (b) r₂ = r₃: matrix multiply with (DD', RC') from recursion. -/
def countPBP_D : DualPart → ℕ × ℕ × ℕ
  | [] => (1, 0, 0)
  | [r₁] =>
    let k := r₁ / 2 + 1  -- r₂ = 0, so k = r₁/2 + 1... but r₁ is odd for D type
    -- Actually for D type with single row: r₂ = 0, r₃ = -1 (convention)
    -- k = (r₁ - 0)/2 + 1. (2,3) always primitive (r₂ = 0 > r₃ = -1).
    let ((tDD, tRC, tSS), _) := tailCoeffs k
    let (dd', rc', ss') := (1, 0, 0)  -- countPBP_D []
    let total := dd' + rc' + ss'
    (total * tDD, total * tRC, total * tSS)
  | r₁ :: r₂ :: rest =>
    let k := (r₁ - r₂) / 2 + 1
    let ((tDD, tRC, tSS), (scDD, scRC, scSS)) := tailCoeffs k
    let r₃ := rest.head?.getD 0
    if r₂ > r₃ then
      -- (2,3) primitive
      let (dd', rc', ss') := countPBP_D rest
      let total := dd' + rc' + ss'
      (total * tDD, total * tRC, total * tSS)
    else
      -- (2,3) balanced
      let (dd', rc', ss') := countPBP_D rest
      (dd' * tDD + rc' * scDD,
       dd' * tRC + rc' * scRC,
       dd' * tSS + rc' * scSS)

/-! ## Counting for B type (Proposition 10.11) -/

/-- Count PBPs for B type, returning (DD, RC, SS) triple.
    Reference: [BMSZb] Proposition 10.11. -/
def countPBP_B : DualPart → ℕ × ℕ × ℕ
  | [] => (0, 1, 1)
  | [r₁] =>
    -- Single even row [r₁]. c₁ = r₁/2.
    let c₁ := r₁ / 2
    (2 * (if c₁ ≥ 1 then nu (c₁ - 1) else 0),
     nu c₁ + (if c₁ ≥ 1 then nu (c₁ - 1) else 0),
     1)
  | r₁ :: r₂ :: rest =>
    let k := (r₁ - r₂) / 2 + 1
    let ((tDD, tRC, tSS), (scDD, scRC, scSS)) := tailCoeffs k
    let r₃ := rest.head?.getD 0
    if r₂ > r₃ then
      let (dd', rc', ss') := countPBP_B rest
      let total := dd' + rc' + ss'
      (total * tDD, total * tRC, total * tSS)
    else
      let (dd', rc', ss') := countPBP_B rest
      (dd' * tDD + rc' * scDD,
       dd' * tRC + rc' * scRC,
       dd' * tSS + rc' * scSS)

/-! ## Counting for C type (Proposition 10.12) -/

/-- Count PBPs for C type.
    Reference: [BMSZb] Proposition 10.12.

    C→D descent is injective.
    (a) (1,2) ∈ PP: #PBP_C = DD + RC + SS = total #PBP_D(Ǒ[1:])
    (b) (1,2) ∉ PP: #PBP_C = DD + RC (tail symbol s has no preimage) -/
def countPBP_C : DualPart → ℕ
  | [] => 0
  | [_] => 1
  | r₁ :: r₂ :: rest =>
    let (dd, rc, ss) := countPBP_D (r₂ :: rest)
    if r₁ > r₂ then dd + rc + ss
    else dd + rc

/-! ## Counting for M type (Proposition 10.12) -/

/-- Count PBPs for M type.
    Reference: [BMSZb] Proposition 10.12.
    M→B descent gives recovery.
    Same structure as C type but using B instead of D. -/
def countPBP_M (dp : DualPart) : ℕ :=
  let dp' := dp.filter (· > 0)
  match dp' with
  | [] => 1
  | [r₁] =>
    let (dd, rc, ss) := countPBP_B []
    dd + rc + ss  -- single row: (1,2) always primitive
  | r₁ :: r₂ :: _ =>
    let (dd, rc, ss) := countPBP_B dp'.tail
    if r₁ > r₂ then dd + rc + ss
    else dd + rc

/-! ## Total PBP count -/

/-- Total #PBP_★(Ǒ, ∅).
    Reference: [BMSZb] Propositions 10.11-10.12. -/
def countPBP (dp : DualPart) (γ : RootType) : ℕ :=
  match γ with
  | .C => countPBP_C dp
  | .M => countPBP_M dp
  | .D => let (dd, rc, ss) := countPBP_D dp; dd + rc + ss
  | .Bplus | .Bminus => let (dd, rc, ss) := countPBP_B dp; (dd + rc + ss) / 2

/-! ## Verification -/

-- D empty: (1, 0, 0), total = 1
#eval countPBP_D []
#eval countPBP [] .D

-- D [3,1]: k = (3-1)/2+1 = 2. r₂=1 > r₃=0 (primitive).
-- sub = (1,0,0), total=1. TDD=nu(1)+nu(0)=3, TRC=2*nu(1)=4, TSS=1.
-- Result: (3, 4, 1), total = 8.
#eval countPBP_D [3, 1]
#eval countPBP [3, 1] .D

-- C [3,1]: r₁=3 > r₂=1 → DD+RC+SS from D([1]).
-- D([1]): k=(1-0)/2+1=1. sub=(1,0,0), total=1.
-- TDD=nu(0)+0=1, TRC=2*nu(0)=2, TSS=1. D([1])=(1,2,1). Total=4.
#eval countPBP_C [3, 1]

-- C [3,3]: r₁=3 = r₂=3 → DD+RC from D([3]).
-- D([3]): k=(3-0)/2+1=2. sub=(1,0,0), total=1.
-- TDD=nu(1)+nu(0)=3, TRC=2*nu(1)=4, TSS=1. D([3])=(3,4,1). DD+RC=7.
#eval countPBP_C [3, 3]

-- M empty: 1
#eval countPBP_M []

-- More tests (verified against standalone.py):
-- D [3,3]: DD+RC = 4 (balanced pair)
#eval countPBP [3, 3] .D  -- Python: 4

-- D [5,3,1]: should be 32
#eval countPBP [5, 3, 1] .D  -- Python: 32

-- C [5,3,1]: should be 8
#eval countPBP_C [5, 3, 1]  -- Python: 8

-- M [2]: should be 2
#eval countPBP_M [2]  -- Python: 2

-- M [2,2]: should be 5
#eval countPBP_M [2, 2]  -- Python: 5

-- B [2]: total/2 = 3
#eval countPBP [2] .Bplus  -- Python: 3

-- B [4,2]: total/2 = 8
#eval countPBP [4, 2] .Bplus  -- Python: 8
