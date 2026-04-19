/-
# MYD_γ(O): Marked Young Diagrams of an orbit

Reference: [BMSZ] arXiv:1712.05552, Definitions 9.3, 9.8.

A marked Young diagram (MYD) of type γ and orbit O is an ILS
`E : List (ℤ × ℤ)` such that:

1. **Parity**: at γ-parity-forced row lengths `i` (even for B/D, odd for
   C/M), the entry `(p_i, q_i)` satisfies `p_i = q_i ≥ 0`.
2. **Shape**: the absolute-value projection `V(E) = (|p_i|, |q_i|)_i`
   equals the orbit's SYD rows (paper §9.1, V map).

Notes:
- MYD entries are in `ℤ × ℤ` (signed), unlike SYD which is in `ℕ × ℕ`.
- The V map (absolute values) is the projection MYD_γ → SYD_γ; by
  construction, `V(E) = O.rows` exactly means `E` belongs to orbit O.
- We do not yet enforce signature matching `Sign_MYD(E) = Sign_SYD(O)`
  as a separate condition — it follows from the shape equality plus the
  fact that both signatures share the same `SignRow` formula applied to
  `(|p_i|, |q_i|)`.

Companion blueprint: `lean/docs/blueprints/MYD_type_and_bijection.md`
(section "MYD_γ in the paper vs. in Lean").
-/
import CombUnipotent.MYD.SYD
import CombUnipotent.MYD

namespace BMSZ

/-- Per-row MYD validity: at γ-parity-forced index `i` (1-indexed), the
    pair `(p_i, q_i)` must satisfy `p_i = q_i ≥ 0`. -/
def MYDRowValid (γ : RootType) (i : ℕ) (pq : ℤ × ℤ) : Prop :=
  SYDParityForced γ i → pq.1 = pq.2 ∧ 0 ≤ pq.1

instance (γ : RootType) (i : ℕ) (pq : ℤ × ℤ) :
    Decidable (MYDRowValid γ i pq) := by
  unfold MYDRowValid; exact inferInstance

/-- Absolute-value projection `V : ILS → List (ℕ × ℕ)` (paper §9.1).
    Applied row-wise: `V(E)[j] = (|(E[j]).1|, |(E[j]).2|)`. -/
def absValues (E : ILS) : List (ℕ × ℕ) :=
  E.map (fun pq => (pq.1.natAbs, pq.2.natAbs))

theorem absValues_length (E : ILS) : (absValues E).length = E.length := by
  unfold absValues; simp

/-- `absValues` on a cons: `absValues (pq :: E) = (|pq.1|, |pq.2|) :: absValues E`.
    Trivial unfold. Needed in induction on ILS (e.g., augment results). -/
theorem absValues_cons (pq : ℤ × ℤ) (E : ILS) :
    absValues (pq :: E) = (pq.1.natAbs, pq.2.natAbs) :: absValues E := by
  unfold absValues; simp

/-- `absValues` after `augment (paper Def 9.18 = cons)`. -/
theorem absValues_augment (pq : ℤ × ℤ) (E : ILS) :
    absValues (ILS.augment pq E) = (pq.1.natAbs, pq.2.natAbs) :: absValues E := by
  unfold ILS.augment
  exact absValues_cons pq E

/-- `absValues` is preserved under `charTwistCM`: each row is either
    unchanged or negated, both preserve `.natAbs`. -/
theorem absValues_charTwistCM (E : ILS) (j : ℤ) :
    absValues (ILS.charTwistCM E j) = absValues E := by
  unfold absValues ILS.charTwistCM
  apply List.ext_getElem
  · simp
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_mapIdx]
  unfold ILS.charTwistCMRow
  split_ifs
  · -- Negated case
    simp [Int.natAbs_neg]
  · rfl

/-- **Marked Young Diagram of orbit O** (paper Def 9.3 + §9.8).

    An ILS `E` such that:
    - each row `E[j]` satisfies γ-parity at row length `j + 1`
    - the absolute-value projection `V(E)` equals the SYD's `rows`.

    Decidable equality follows from `ILS` being `List (ℤ × ℤ)`. -/
structure MYD (γ : RootType) (O : SYD γ) where
  E : ILS
  parity : ∀ (j : ℕ) (h : j < E.length), MYDRowValid γ (j + 1) E[j]
  shape : absValues E = O.rows

namespace MYD

variable {γ : RootType} {O : SYD γ}

theorem ext {M₁ M₂ : MYD γ O} (h : M₁.E = M₂.E) : M₁ = M₂ := by
  cases M₁; cases M₂; congr

instance : DecidableEq (MYD γ O) := fun M₁ M₂ =>
  decidable_of_iff (M₁.E = M₂.E)
    ⟨fun h => ext h, fun h => by rw [h]⟩

-- (No canonical constructor yet — the set MYD γ O is non-trivial and we
--  construct elements via the AC chain `L_τ` in a later increment.)

end MYD

end BMSZ
