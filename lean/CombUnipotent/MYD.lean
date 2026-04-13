/-
# Marked Young Diagrams (MYD) and ILS Operations

Reference:
  [BMSZ] Barbasch–Ma–Sun–Zhu, "Special unipotent representations:
         construction and unitarity", arXiv:1712.05552v6
  Sections 9.1–9.5, 11.1–11.5.

A marked Young diagram E of type ★ is a finite sequence
  E = ((p₁, q₁), (p₂, q₂), ..., (pₖ, qₖ))
of integer pairs, satisfying type-dependent sign constraints.

The code represents an ILS (irreducible local system) as `List (ℤ × ℤ)`,
following the Python `standalone.py` convention where index i (0-based)
corresponds to row length i+1.
-/
import Mathlib.Data.Int.Basic
import CombUnipotent.Basic

open Int

/-! ## ILS: Irreducible Local System -/

/-- An irreducible local system: a finite sequence of (p, q) pairs.
    Index i (0-based) corresponds to row length i+1.
    Reference: [BMSZ] Definition 9.3. -/
abbrev ILS := List (ℤ × ℤ)

namespace ILS

/-! ## Signature: Sign(E) = (p, q) -/

/-- Contribution of row i (0-based) to the signature.
    Let (h, r) = divmod(i+1, 2), then
      p += |pᵢ|·(h + r) + |qᵢ|·h
      q += |qᵢ|·(h + r) + |pᵢ|·h
    Reference: [BMSZ] Equation (9.10). -/
def signRow (i : ℕ) (pq : ℤ × ℤ) : ℤ × ℤ :=
  let h : ℤ := (i + 1) / 2
  let r : ℤ := (i + 1) % 2
  let p := pq.1.natAbs * (h + r) + pq.2.natAbs * h
  let q := pq.2.natAbs * (h + r) + pq.1.natAbs * h
  (p, q)

/-- Signature Sign(E) = (p, q) of an ILS.
    Reference: [BMSZ] Equation (9.10). -/
def sign (E : ILS) : ℤ × ℤ :=
  (E.zipIdx).foldl (fun acc ⟨pq, i⟩ =>
    let s := signRow i pq
    (acc.1 + s.1, acc.2 + s.2)) (0, 0)

/-! ## First-column signature -/

/-- First-column signature contribution of row i (0-based).
    For i even:  p += |pᵢ|, q += |qᵢ|
    For i odd:   p += |qᵢ|, q += |pᵢ|  (swap!)
    Reference: [BMSZ] Equation (9.12). -/
def firstColSignRow (i : ℕ) (pq : ℤ × ℤ) : ℤ × ℤ :=
  if i % 2 = 0 then (pq.1.natAbs, pq.2.natAbs)
  else (pq.2.natAbs, pq.1.natAbs)

/-- First-column signature of an ILS.
    Reference: [BMSZ] Equation (9.12), Lemma 9.2. -/
def firstColSign (E : ILS) : ℤ × ℤ :=
  (E.zipIdx).foldl (fun acc ⟨pq, i⟩ =>
    let s := firstColSignRow i pq
    (acc.1 + s.1, acc.2 + s.2)) (0, 0)

/-! ## Sign twist ⊗ (ε⁺, ε⁻) for B/D types -/

/-- Sign twist on a single row at index i (0-based).
    Acts only on odd-length rows (i even, since length = i+1).
    twist = (tp, tn) where tp, tn ∈ {1, -1}.

    For odd-length ℓ = i+1 (i even):
      let h = ℓ / 2 = i / 2
      tpp = tp^(h+1) · tn^h
      tnn = tn^(h+1) · tp^h
      (pᵢ, qᵢ) ↦ (tpp · pᵢ, tnn · qᵢ)
    Even-length rows (i odd) are unchanged.

    Reference: [BMSZ] Equation (9.15). -/
def twistBDRow (i : ℕ) (tp tn : ℤ) (pq : ℤ × ℤ) : ℤ × ℤ :=
  let ℓ := i + 1
  if ℓ % 2 = 0 then pq  -- even-length row: unchanged
  else
    let h : ℕ := ℓ / 2   -- = i / 2
    let tpp := tp ^ (h + 1) * tn ^ h
    let tnn := tn ^ (h + 1) * tp ^ h
    (tpp * pq.1, tnn * pq.2)

/-- Sign twist ⊗ (ε⁺, ε⁻) on an ILS.
    Reference: [BMSZ] Equation (9.15).

    Common cases:
      (1, -1): sign twist ⊗ 1⁺⁻ (B/D post-twist when ε_τ = 1)
      (-1, -1): det twist (C/M pre-twist when ε_℘ = 1)
      (1, 1): identity -/
def twistBD (E : ILS) (tp tn : ℤ) : ILS :=
  E.mapIdx fun i pq => twistBDRow i tp tn pq

/-! ## Character twist T for C/M types -/

/-- Character twist T^j on a single row at index i (0-based).
    Negates entries at positions where (i+1) ≡ 2 (mod 4), when j is odd.
    T² = identity, so only parity of j matters.
    Reference: [BMSZ] Equation (9.16)–(9.17). -/
def charTwistCMRow (j : ℤ) (i : ℕ) (pq : ℤ × ℤ) : ℤ × ℤ :=
  if j % 2 = 1 ∧ (i + 1) % 4 = 2 then (-pq.1, -pq.2) else pq

/-- Character twist T^j on an ILS.
    Reference: [BMSZ] Equation (9.16)–(9.17). -/
def charTwistCM (E : ILS) (j : ℤ) : ILS :=
  E.mapIdx fun i pq => charTwistCMRow j i pq

/-! ## Augmentation: prepend (p₀, q₀) -/

/-- Augmentation E' ⊗ (p₀, q₀): shift all rows up by 1 and insert (p₀, q₀)
    at position 1 (index 0).
    Reference: [BMSZ] Equation (9.18). -/
def augment (pq : ℤ × ℤ) (E : ILS) : ILS := pq :: E

/-! ## Truncation Λ -/

/-- Containment check: E ⊇ (p₀, q₀).
    Requires the first entry of E to "contain" (p₀, q₀):
      (p₁ ≥ p₀ ≥ 0 or p₁ ≤ p₀ ≤ 0) and similarly for q.
    Reference: [BMSZ] Equation (9.19). -/
def contains (E : ILS) (pq : ℤ × ℤ) : Prop :=
  match E with
  | [] => pq = (0, 0)
  | (p₁, q₁) :: _ =>
    (0 ≤ pq.1 ∧ pq.1 ≤ p₁ ∨ p₁ ≤ pq.1 ∧ pq.1 ≤ 0) ∧
    (0 ≤ pq.2 ∧ pq.2 ≤ q₁ ∨ q₁ ≤ pq.2 ∧ pq.2 ≤ 0)

/-- Truncation Λ_{(p₀, q₀)} E: subtract (p₀, q₀) from the first entry.
    Reference: [BMSZ] Equation (9.19)–(9.20). -/
def truncate (E : ILS) (pq : ℤ × ℤ) : ILS :=
  match E with
  | [] => []
  | (p₁, q₁) :: rest => (p₁ - pq.1, q₁ - pq.2) :: rest

/-! ## Theta lift on ILS -/

/-- Theta lift D → C: target Sp(2n), sig = (n, n).
    Reference: [BMSZ] Equations (9.29)–(9.30), Section 11.1.

    Given E' ∈ MYD_D(O'), compute ϑ̂(E') ∈ MYD_C(O).
    addp = n - ps - fns, addn = n - ns - fps.
    Result: T^γ((addp, addn) :: E')
    where γ = (ps - ns) / 2.

    If addp or addn < 0, the lift may split or vanish. -/
def thetaLift_DC (E : ILS) (n : ℤ) : List ILS :=
  let (ps, ns) := sign E
  let (fps, fns) := firstColSign E
  let addp := n - ps - fns
  let addn := n - ns - fps
  if addp ≥ 0 ∧ addn ≥ 0 then
    [charTwistCM (augment (addp, addn) E) ((ps - ns) / 2)]
  else if (addp, addn) = (-1, -1) ∨ (addp, addn) = (-2, 0) ∨ (addp, addn) = (0, -2) then
    match E with
    | [] => []
    | (pp0, nn0) :: rest =>
      let γ := (ps - ns) / 2
      let r1 := if pp0 > 0 then
        [charTwistCM (augment (0, 0) ((pp0 - 1, nn0) :: rest)) γ] else []
      let r2 := if nn0 > 0 then
        [charTwistCM (augment (0, 0) ((pp0, nn0 - 1) :: rest)) γ] else []
      r1 ++ r2
  else []

/-- Theta lift C → D: target O(p, q), p+q even.
    Reference: [BMSZ] Equations (9.29)–(9.30), Section 11.2. -/
def thetaLift_CD (E : ILS) (p q : ℤ) : List ILS :=
  let (ps, ns) := sign E
  let (fps, fns) := firstColSign E
  let addp := p - ps - fns
  let addn := q - ns - fps
  if addp ≥ 0 ∧ addn ≥ 0 then
    [augment (addp, addn) (charTwistCM E ((p - q) / 2))]
  else []

/-- Theta lift B → M: target Mp(2n), sig = (n, n).
    Reference: [BMSZ] Section 11.3. -/
def thetaLift_BM (E : ILS) (n : ℤ) : List ILS :=
  let (ps, ns) := sign E
  let (fps, fns) := firstColSign E
  let addp := n - ps - fns
  let addn := n - ns - fps
  if addp ≥ 0 ∧ addn ≥ 0 then
    [charTwistCM (augment (addp, addn) E) ((ps - ns - 1) / 2)]
  else if (addp, addn) = (-1, -1) ∨ (addp, addn) = (-2, 0) ∨ (addp, addn) = (0, -2) then
    match E with
    | [] => []
    | (pp0, nn0) :: rest =>
      let γ := (ps - ns - 1) / 2
      let r1 := if pp0 > 0 then
        [charTwistCM (augment (0, 0) ((pp0 - 1, nn0) :: rest)) γ] else []
      let r2 := if nn0 > 0 then
        [charTwistCM (augment (0, 0) ((pp0, nn0 - 1) :: rest)) γ] else []
      r1 ++ r2
  else []

/-- Theta lift M → B: target O(p, q), p+q odd.
    Reference: [BMSZ] Section 11.4. -/
def thetaLift_MB (E : ILS) (p q : ℤ) : List ILS :=
  let (ps, ns) := sign E
  let (fps, fns) := firstColSign E
  let addp := p - ps - fns
  let addn := q - ns - fps
  if addp ≥ 0 ∧ addn ≥ 0 then
    [augment (addp, addn) (charTwistCM E ((p - q + 1) / 2))]
  else []

/-- Theta lift a single ILS to target type ★ with signature (p, q).
    Dispatches to the appropriate lift formula based on target type.
    Reference: [BMSZ] Sections 11.1–11.4. -/
def thetaLift (E : ILS) (target : RootType) (p q : ℤ) : List ILS :=
  match target with
  | .C => thetaLift_DC E p       -- D → C, target Sp(2n), n = p = q
  | .D => thetaLift_CD E p q     -- C → D, target O(p,q)
  | .M => thetaLift_BM E p       -- B → M, target Mp(2n), n = p = q
  | .Bplus | .Bminus => thetaLift_MB E p q  -- M → B, target O(p,q)

end ILS

/-! ## Associated Cycle computation -/

/-- An AC result: list of (multiplicity, ILS) pairs. -/
abbrev ACResult := List (ℤ × ILS)

/-- Theta lift an AC result: lift each component independently. -/
def ACResult.thetaLift (ac : ACResult) (target : RootType) (p q : ℤ) : ACResult :=
  ac.flatMap fun ⟨coeff, ils⟩ =>
    (ILS.thetaLift ils target p q).map fun lifted => (coeff, lifted)

/-- Apply B/D sign twist to each ILS in an AC result. -/
def ACResult.twistBD (ac : ACResult) (tp tn : ℤ) : ACResult :=
  ac.map fun ⟨coeff, ils⟩ => (coeff, ils.twistBD tp tn)

/-! ## Descent of ℘ (primitive pair set) -/

/-- Primitive pair set ℘: a finite set of indices.
    Index i represents the pair (i+1, i+2) in the paper's notation.
    Reference: [BMSZb] Section 10.4. -/
abbrev PPSet := Finset ℕ

/-- ε_℘: whether the first primitive pair (1,2) is in ℘.
    ε_℘ = 1 iff PPidx 0 ∈ ℘.
    Reference: [BMSZ] below Equation (3.16). -/
def PPSet.epsilon (wp : PPSet) : Fin 2 :=
  if 0 ∈ wp then 1 else 0

/-- Descent of ℘: ∇̃(℘) = {(j-1, j) : (j, j+1) ∈ ℘, j ≥ 2}.
    In PPidx encoding for C/M → D/B: shift index down by 1, discard 0.
    Reference: [BMSZ] Equation (3.15); [BMSZb] Section 10.4. -/
def PPSet.descendCM (wp : PPSet) : PPSet :=
  (wp.filter (· > 0)).image (· - 1)

/-- Descent of ℘ for B/D → C/M: PPidx i maps to PPidx i (no shift).
    Reference: [BMSZb] Section 10.4. -/
def PPSet.descendBD (wp : PPSet) : PPSet := wp

/-- Descent of ℘ depending on source type. -/
def PPSet.descend (wp : PPSet) (source : RootType) : PPSet :=
  match source with
  | .C | .M => wp.descendCM
  | .Bplus | .Bminus | .D => wp.descendBD

/-! ## Dual type (descent target) -/

/-- The dual type after one step of descent.
    C → D, D → C, M → B⁺, B⁺ → M, B⁻ → M.
    Reference: [BMSZb] Section 10. -/
def RootType.dualDescent : RootType → RootType
  | .C => .D
  | .D => .C
  | .M => .Bplus  -- M → B (default B⁺; actual choice depends on DRC)
  | .Bplus => .M
  | .Bminus => .M

/-! ## AC recursive computation -/

/-- Base case AC for the trivial group (|Ǒ| = 0).
    Reference: [BMSZ] Section 11, base case. -/
def AC.base (γ : RootType) : ACResult :=
  match γ with
  | .Bplus  => [(1, [(1, 0)])]     -- 1 × MYD with one row marked +
  | .Bminus => [(1, [(0, -1)])]    -- 1 × MYD with one row marked −
  | .C | .D | .M => [(1, [])]      -- 1 × empty MYD

/-- One step of AC recursion: given source AC and current PBP data,
    compute the lifted AC.

    For ★ ∈ {B, D}: AC = ϑ̂(source_AC) ⊗ (0, ε_τ)
    For ★ ∈ {C, M}: AC = ϑ̂(source_AC ⊗ (ε_℘, ε_℘))

    Reference: [BMSZ] Equation (3.16), (11.2). -/
def AC.step (source : ACResult) (γ : RootType) (p q : ℤ)
    (ε_τ : Fin 2) (ε_wp : Fin 2) : ACResult :=
  -- Pre-twist for C/M: ⊗ (ε_℘, ε_℘) on source
  let twisted := if γ = .C ∨ γ = .M then
    if ε_wp = 1 then source.twistBD (-1) (-1) else source
  else source
  -- Theta lift
  let lifted := twisted.thetaLift γ p q
  -- Post-twist for B/D: ⊗ (0, ε_τ)
  if (γ = .Bplus ∨ γ = .Bminus ∨ γ = .D) ∧ ε_τ = 1 then
    lifted.twistBD 1 (-1)
  else lifted

/-! ## Chain-based AC computation -/

/-- Data extracted from one level of the descent chain for AC computation.
    Each entry represents a PBP τ at that level with its type, signature,
    epsilon, and ε_℘. -/
structure ACStepData where
  γ : RootType
  p : ℤ
  q : ℤ
  ε_τ : Fin 2
  ε_wp : Fin 2
  deriving Repr

/-- Compute AC by folding step data from inner (closest to base) to outer (current).
    `baseType` is the type of the fully descended (empty) PBP.
    `chain` is ordered inner-first: chain[0] is the step closest to base.

    At each step, the previous AC is lifted through the current step's data.
    Reference: [BMSZ] Equation (3.16), (11.2). -/
def AC.fold (baseType : RootType) (chain : List ACStepData) : ACResult :=
  chain.foldl (fun ac d => AC.step ac d.γ d.p d.q d.ε_τ d.ε_wp) (AC.base baseType)

/-! ## Key theorem statement: signature matching

The signature of AC(τ) matches the PBP signature (p_τ, q_τ).
This is the main correctness property of the AC computation.
Reference: [BMSZ] Theorem 5.1 (verified computationally for all types up to size 30). -/

/-! ## Verification: #eval tests -/

section Tests

-- Sign of base cases
#eval ILS.sign [(1, 0)]         -- expect (1, 0) for B⁺ base
#eval ILS.sign [(0, -1)]        -- expect (0, 1) for B⁻ base
#eval ILS.sign []                -- expect (0, 0) for trivial

-- Sign of longer ILS: [(2, 1), (1, 1)] has rows of length 1 and 2
-- row 0 (len 1, odd): h=0, r=1 → p += 1*|2| + 0*|1| = 2, q += 1*|1| + 0*|2| = 1
-- row 1 (len 2, even): h=1, r=0 → p += 1*|1| + 1*|1| = 2, q += 1*|1| + 1*|1| = 2
-- total: (4, 3)
#eval ILS.sign [(2, 1), (1, 1)]  -- expect (4, 3)

-- First-column sign
-- row 0 (even): p += |2| = 2, q += |1| = 1
-- row 1 (odd):  p += |1| = 1, q += |1| = 1  (swap!)
-- total: (3, 2)
#eval ILS.firstColSign [(2, 1), (1, 1)]  -- expect (3, 2)

-- Twist: twistBD with (1, -1) on row 0 (odd-length 1, h=0)
-- tpp = 1^1 * (-1)^0 = 1, tnn = (-1)^1 * 1^0 = -1
-- (2, 1) → (2, -1)
-- row 1 (even-length 2): unchanged (1, 1)
#eval ILS.twistBD [(2, 1), (1, 1)] 1 (-1)  -- expect [(2, -1), (1, 1)]

-- Character twist T^1: negate at positions where (i+1) ≡ 2 (mod 4), i.e., i=1
-- row 0: (i+1)=1 ≢ 2 (mod 4), unchanged
-- row 1: (i+1)=2 ≡ 2 (mod 4), negate: (1, 1) → (-1, -1)
#eval ILS.charTwistCM [(2, 1), (1, 1)] 1  -- expect [(2, 1), (-1, -1)]
-- T^2 = identity
#eval ILS.charTwistCM [(2, 1), (1, 1)] 2  -- expect [(2, 1), (1, 1)]

-- Theta lift: D → C with n=1, empty source
#eval ILS.thetaLift_DC [] 1     -- expect [[(1, 1)]]

-- Theta lift: C → D with (p=2, q=0), source = [(1, 1)]
-- sign = (1, 1), firstColSign = (1, 1)
-- addp = 2 - 1 - 1 = 0, addn = 0 - 1 - 1 = -2
-- (addp, addn) = (0, -2): split case
#eval ILS.thetaLift_CD [(1, 1)] 2 0

-- AC base cases
#eval AC.base .D                -- [(1, [])]
#eval AC.base .Bplus            -- [(1, [(1, 0)])]
#eval AC.base .C                -- [(1, [])]

-- AC step: D → C with base D, p=q=1, ε_τ=0, ε_℘=0
-- source = [(1, [])], lift D→C with n=1
-- empty ILS → theta_DC [] 1 = [[(1, 1)]]
-- no post-twist (target is C)
#eval AC.step [(1, [])] .C 1 1 0 0  -- expect [(1, [(1, 1)])]

-- AC.fold cross-validation with Python compute_AC
-- dp=[3,1] type D: chain inner→outer = [C(1,1,ε=1), D(5,3,ε=1)], base=D
-- Python: AC = [(1, ((3, -1), (1, 1)))]
#eval AC.fold .D [
  ⟨.C, 1, 1, 1, 0⟩,   -- innermost: C-type lift
  ⟨.D, 5, 3, 1, 0⟩    -- outermost: D-type lift
]  -- expect [(1, [(3, -1), (1, 1)])]

-- dp=[3,3,1,1] type C: chain inner→outer = [D(1,3,1), C(3,3,1), D(6,8,1), C(10,10,1)], base=C
-- Python: AC = [(1, ((0, 0), (-2, 2), (0, 0), (0, -3)))]
#eval AC.fold .C [
  ⟨.D, 1, 3, 1, 0⟩,
  ⟨.C, 3, 3, 1, 0⟩,
  ⟨.D, 6, 8, 1, 0⟩,
  ⟨.C, 10, 10, 1, 0⟩
]  -- expect [(1, [(0, 0), (-2, 2), (0, 0), (0, -3)])]

-- Verify sign of AC matches outermost signature
#eval
  let ac := AC.fold .D [⟨.C, 1, 1, 1, 0⟩, ⟨.D, 5, 3, 1, 0⟩]
  ac.map fun (c, ils) => (c, ILS.sign ils)
-- expect [(1, (5, 3))], matching D-type sig=(5,3)

#eval
  let ac := AC.fold .C [⟨.D, 1, 3, 1, 0⟩, ⟨.C, 3, 3, 1, 0⟩, ⟨.D, 6, 8, 1, 0⟩, ⟨.C, 10, 10, 1, 0⟩]
  ac.map fun (c, ils) => (c, ILS.sign ils)
-- expect [(1, (10, 10))], matching C-type sig=(10,10)

-- Cross-validation with Python standalone.py
#eval ILS.sign [(3, 0), (0, 2), (1, 1)]           -- expect (8, 5)
#eval ILS.firstColSign [(3, 0), (0, 2), (1, 1)]   -- expect (6, 1)
#eval ILS.twistBD [(2, 1), (1, 1)] (-1) (-1)      -- expect [(-2, -1), (1, 1)]
#eval ILS.charTwistCM [(2, 1), (1, 1), (3, 0)] 1  -- expect [(2, 1), (-1, -1), (3, 0)]
#eval ILS.charTwistCM [(2, 1), (1, 1), (3, 0)] 3  -- expect [(2, 1), (-1, -1), (3, 0)]

-- Theta lifts matching Python
#eval ILS.thetaLift_DC [(1, 0)] 2                  -- expect [[(1, 1), (1, 0)]]
#eval ILS.thetaLift_CD [(1, 1)] 3 1                -- expect []
#eval ILS.thetaLift_BM [(1, 0)] 2                  -- expect [[(1, 1), (1, 0)]]
#eval ILS.thetaLift_MB [(1, 1)] 3 2                -- expect [[(1, 0), (1, 1)]]

end Tests
