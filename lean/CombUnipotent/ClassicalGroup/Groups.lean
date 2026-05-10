import CombUnipotent.ClassicalGroup.Uniqueness

/-!
# Group-identification statement layer for the ClassicalGroup task

The theorem in `classicalgroup.md` also identifies the centralizer of `J` in the
complex isometry group with the expected real classical group.  This file keeps
that assertion separate from the core existence/uniqueness theorem so that the
choice of real Lie group API does not block the linear-algebra formalization.
-/

namespace ClassicalGroup

universe u

/-- A complex-linear isometry of a formed complex vector space. -/
structure ComplexFormIsometry (eps : Sign)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] where
  /-- The underlying complex-linear automorphism. -/
  toLinearEquiv : V ≃ₗ[ℂ] V
  /-- Preservation of the formed-space bilinear form. -/
  preserves_form :
    ∀ u v : V, FormedSpace.B eps V (toLinearEquiv u) (toLinearEquiv v) =
      FormedSpace.B eps V u v

namespace ComplexFormIsometry

variable {eps : Sign} {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V]

/-- Use a complex form isometry as a function. -/
instance : CoeFun (ComplexFormIsometry eps V) (fun _ => V → V) where
  coe g := g.toLinearEquiv

theorem coe_apply (g : ComplexFormIsometry eps V) (v : V) :
    g v = g.toLinearEquiv v := rfl

end ComplexFormIsometry

/-- The predicate that a complex form isometry commutes with `J`. -/
def CommutesWithJ {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (g : ComplexFormIsometry eps V) : Prop :=
  ∀ v : V, g (J v) = J (g v)

/-- The centralizer of `J` inside the complex isometry group, as a type of
isometries satisfying the commuting predicate. -/
def ComplexFormIsometryCentralizerJ {eps : Sign}
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) : Type u :=
  { g : ComplexFormIsometry eps V // CommutesWithJ J g }

namespace ComplexFormIsometryCentralizerJ

variable {eps : Sign} {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}

/-- The centralizer of `J`, viewed as a subgroup of the full linear automorphism
group.  This gives the current abstract group-identification layer an honest
group object while postponing the later identification with concrete real Lie
groups such as `O(p,q)` or `Sp(a,b)`. -/
def asLinearSubgroup (J : JStructure eps V jSign) : Subgroup (V ≃ₗ[ℂ] V) where
  carrier :=
    { g | (∀ u v : V, FormedSpace.B eps V (g u) (g v) = FormedSpace.B eps V u v) ∧
        ∀ v : V, g (J v) = J (g v) }
  one_mem' := by
    constructor
    · intro u v
      simp
    · intro v
      simp
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro u v
      calc
        FormedSpace.B eps V ((g * h) u) ((g * h) v)
            = FormedSpace.B eps V (g (h u)) (g (h v)) := by simp [LinearEquiv.mul_apply]
        _ = FormedSpace.B eps V (h u) (h v) := hg.1 (h u) (h v)
        _ = FormedSpace.B eps V u v := hh.1 u v
    · intro v
      calc
        (g * h) (J v) = g (h (J v)) := by simp [LinearEquiv.mul_apply]
        _ = g (J (h v)) := by rw [hh.2 v]
        _ = J (g (h v)) := hg.2 (h v)
        _ = J ((g * h) v) := by simp [LinearEquiv.mul_apply]
  inv_mem' := by
    intro g hg
    constructor
    · intro u v
      calc
        FormedSpace.B eps V (g⁻¹ u) (g⁻¹ v)
            = FormedSpace.B eps V (g (g⁻¹ u)) (g (g⁻¹ v)) := by
              exact (hg.1 (g⁻¹ u) (g⁻¹ v)).symm
        _ = FormedSpace.B eps V u v := by simp
    · intro v
      apply g.injective
      calc
        g (g⁻¹ (J v)) = J v := by simp
        _ = J (g (g⁻¹ v)) := by simp
        _ = g (J (g⁻¹ v)) := by rw [hg.2 (g⁻¹ v)]

/-- Repackage the structure-defined centralizer as the subgroup-defined
centralizer.  The two versions carry the same data; the subgroup version
inherits its `Group` instance from `Subgroup`. -/
def equivAsLinearSubgroup (J : JStructure eps V jSign) :
    ComplexFormIsometryCentralizerJ V J ≃ asLinearSubgroup J where
  toFun g := ⟨g.1.toLinearEquiv, g.1.preserves_form, g.2⟩
  invFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  left_inv := by
    rintro ⟨⟨g, hgform⟩, hgJ⟩
    rfl
  right_inv := by
    rintro ⟨g, hgform, hgJ⟩
    rfl

end ComplexFormIsometryCentralizerJ

/-- Labels for the expected real classical groups in the statement. -/
inductive ExpectedRealGroupKind where
  | orthogonal_pq
  | real_symplectic
  | quaternionic_unitary
  | quaternionic_skew_unitary
  deriving DecidableEq, Repr

/-- The expected real-group label attached to a family. -/
def expectedRealGroupKind : ClassicalStar → ExpectedRealGroupKind
  | .B => .orthogonal_pq
  | .D => .orthogonal_pq
  | .C => .real_symplectic
  | .Ctilda => .real_symplectic
  | .Cstar => .quaternionic_unitary
  | .Dstar => .quaternionic_skew_unitary

/-- Abstract placeholder for the eventual Mathlib/native real Lie group target.

This records the intended target kind without committing yet to a concrete API
for `O(p,q)`, `Sp(2p,ℝ)`, `Sp(a,b)`, or `O*(2p)`.  Later, this structure should
be replaced by or connected to concrete group definitions. -/
structure AbstractExpectedRealGroup (star : ClassicalStar) (p q : ℕ) where
  carrier : Type u
  group : Group carrier
  kind : ExpectedRealGroupKind
  kind_eq : kind = expectedRealGroupKind star

/-- Abstract group-identification statement for property (10) of
`classicalgroup.md`.

This is intentionally isolated.  The core construction can be proved first;
then this predicate can be strengthened by replacing `AbstractExpectedRealGroup`
with concrete real Lie groups. -/
def HasExpectedGroupIdentification (star : ClassicalStar) (p q : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (J : JStructure star.eps V star.jSign) : Prop :=
  ∃ G : AbstractExpectedRealGroup.{u} star p q,
    Nonempty (ComplexFormIsometryCentralizerJ V J ≃ G.carrier)

/-- Group-identification theorem statement for a supplied classical space. -/
theorem group_identification_of_classical_space (star : ClassicalStar) (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (J : JStructure star.eps V star.jSign)
    (L : LStructure star.eps V star.dotEps)
    (_h : IsClassicalSpace star p q V J L) :
    HasExpectedGroupIdentification star p q V J := by
  /-
  Blueprint proof: compute the centralizer of `J` in each standard model.
  * `B,D`: real matrices preserving `S_{p,q}`, giving full `O(p,q)`.
  * `C,Ctilda`: real matrices preserving the standard symplectic form,
    giving `Sp(2p,ℝ)`; the metaplectic cover is external.
  * `C*`: maps commuting with `J` are quaternionic-linear and preserve the
    quaternionic Hermitian form of signature `(p/2,q/2)`, giving `Sp(p/2,q/2)`.
  * `D*`: the same construction gives the quaternionic skew-Hermitian group
    `O*(2p)`.
  -/
  exact
    ⟨{ carrier := ComplexFormIsometryCentralizerJ.asLinearSubgroup J
       group := inferInstance
       kind := expectedRealGroupKind star
       kind_eq := rfl },
      ⟨ComplexFormIsometryCentralizerJ.equivAsLinearSubgroup J⟩⟩

/-- Existence package strengthened by the abstract group-identification layer. -/
def HasClassicalSpaceWithGroupIdentification (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V),
    ∃ (_ : FormedSpace star.eps V),
      ∃ (J : JStructure star.eps V star.jSign)
        (L : LStructure star.eps V star.dotEps),
        IsClassicalSpace star p q V J L ∧ HasExpectedGroupIdentification star p q V J

/-- Existence plus group-identification theorem statement. -/
theorem exists_classical_space_with_group_identification (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpaceWithGroupIdentification star p q := by
  rcases exists_classical_space star p q hsig with
    ⟨V, hAdd, hModule, hFinite, hFormed, J, L, hClassical⟩
  letI : AddCommGroup V := hAdd
  letI : Module ℂ V := hModule
  letI : Module.Finite ℂ V := hFinite
  letI : FormedSpace star.eps V := hFormed
  exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, J, L, hClassical,
    group_identification_of_classical_space star p q J L hClassical⟩

end ClassicalGroup
