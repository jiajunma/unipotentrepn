import CombUnipotent.ClassicalGroup.Existence
import CombUnipotent.ClassicalGroup.Uniqueness
import CombUnipotent.ClassicalGroup.Groups

/-!
# Main theorem statements for the ClassicalGroup task

This file re-exports the standalone theorem statements corresponding to
`classicalgroup.md`.
-/

namespace ClassicalGroup

universe u

/-- The core linear-algebra theorem: existence and uniqueness, excluding the
separate group-identification layer. -/
def ClassicalSpaceExistenceAndUniqueness (star : ClassicalStar) (p q : ℕ) : Prop :=
  HasClassicalSpace star p q ∧ UniqueClassicalSpacesFor.{u} star p q

/-- Main core theorem statement from `classicalgroup.md`, with group
identification isolated in `Groups.lean`. -/
theorem classical_space_existence_and_uniqueness (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    ClassicalSpaceExistenceAndUniqueness.{u} star p q := by
  exact ⟨exists_classical_space star p q hsig,
    unique_classical_spaces_by_cases star p q hsig⟩

/-- Main theorem statement including the abstract group-identification layer. -/
def ClassicalGroupTheorem (star : ClassicalStar) (p q : ℕ) : Prop :=
  HasClassicalSpaceWithGroupIdentification star p q ∧
    UniqueClassicalSpacesFor.{u} star p q

/-- Full theorem statement, with property (10) represented by
`HasExpectedGroupIdentification`. -/
theorem classical_group_theorem (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    ClassicalGroupTheorem.{u} star p q := by
  exact ⟨exists_classical_space_with_group_identification star p q hsig,
    unique_classical_spaces_by_cases star p q hsig⟩

end ClassicalGroup
