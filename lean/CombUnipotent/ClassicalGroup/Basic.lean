import Mathlib

/-!
# Basic definitions for the ClassicalGroup task

Standalone formalization target for
`lean/docs/blueprints/classical_group/problem.md`.

This file contains only the shared definition layer:

* signs and classical signatures;
* formed finite-dimensional complex vector spaces;
* form-preserving conjugate-linear `J` structures;
* form-preserving complex-linear `L` structures;
* the paired compatibility predicate between `J` and `L`;
* the proposition saying that supplied data form a classical space;
* the isomorphism structure used for uniqueness.

It is intentionally independent of `InducedOrbitToy.*`.  Standard models,
case-by-case existence proofs, uniqueness proofs, and group identifications
belong in later files.
-/

namespace ClassicalGroup

universe u v

/-! ## Signs -/

/-- The two signs used for `ε`, `dotε`, and their product. -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

namespace Sign

/-- Interpret a sign as the complex scalar `1` or `-1`. -/
def toComplex : Sign → ℂ
  | pos => 1
  | neg => -1

instance : Mul Sign where
  mul
    | pos, pos => pos
    | pos, neg => neg
    | neg, pos => neg
    | neg, neg => pos

theorem toComplex_pos : Sign.pos.toComplex = (1 : ℂ) := rfl

theorem toComplex_neg : Sign.neg.toComplex = (-1 : ℂ) := rfl

theorem toComplex_mul (a b : Sign) :
    (a * b).toComplex = a.toComplex * b.toComplex := by
  cases a <;> cases b <;> simp [toComplex]

end Sign

/-! ## Classical signatures -/

/-- The six classical families appearing in `classicalgroup.md`. -/
inductive ClassicalStar where
  | B
  | C
  | D
  | Ctilda
  | Cstar
  | Dstar
  deriving DecidableEq, Repr

namespace ClassicalStar

/-- The bilinear-form sign `ε` attached to a classical family. -/
abbrev eps : ClassicalStar → Sign
  | B => Sign.pos
  | D => Sign.pos
  | C => Sign.neg
  | Ctilda => Sign.neg
  | Cstar => Sign.neg
  | Dstar => Sign.pos

/-- The square sign `dotε` of `L` attached to a classical family. -/
abbrev dotEps : ClassicalStar → Sign
  | B => Sign.pos
  | D => Sign.pos
  | C => Sign.neg
  | Ctilda => Sign.neg
  | Cstar => Sign.pos
  | Dstar => Sign.neg

/-- The square sign of `J`, namely `ε * dotε`. -/
abbrev jSign (star : ClassicalStar) : Sign :=
  star.eps * star.dotEps

end ClassicalStar

/-- Raw predicate saying that `(star, p, q)` is a classical signature.

This is the theorem-facing interface used when the star and dimensions are
passed separately. -/
def IsClassicalSignature (star : ClassicalStar) (p q : ℕ) : Prop :=
  match star with
  | .B => Odd (p + q)
  | .D => Even (p + q)
  | .C => p = q
  | .Ctilda => p = q
  | .Cstar => Even p ∧ Even q
  | .Dstar => p = q

/-- Packed version of a classical signature.

The raw `(star, p, q)` interface remains primary, but this packed form is useful
when one wants to carry a signature as one object. -/
structure ClassicalSignature where
  star : ClassicalStar
  p : ℕ
  q : ℕ
  isClassical : IsClassicalSignature star p q

namespace ClassicalSignature

/-- The complex dimension prescribed by a packed signature. -/
abbrev dim (s : ClassicalSignature) : ℕ :=
  s.p + s.q

/-- The bilinear-form sign of a packed signature. -/
abbrev eps (s : ClassicalSignature) : Sign :=
  s.star.eps

/-- The square sign of `L` for a packed signature. -/
abbrev dotEps (s : ClassicalSignature) : Sign :=
  s.star.dotEps

/-- The square sign of `J` for a packed signature. -/
abbrev jSign (s : ClassicalSignature) : Sign :=
  s.star.jSign

end ClassicalSignature

/-! ## Formed vector spaces -/

/-- A finite-dimensional complex vector space with a nondegenerate
`ε`-symmetric complex bilinear form.

The vector space `V` is supplied externally.  This class only records the form
structure on `V`; it does not contain `J` or `L`. -/
class FormedSpace (eps : Sign) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] where
  /-- The complex bilinear form on `V`. -/
  form : LinearMap.BilinForm ℂ V
  /-- Nondegeneracy of the bilinear form. -/
  nondegenerate : form.Nondegenerate
  /-- `ε`-symmetry: symmetric for `ε = +1`, alternating/skew-symmetric for `ε = -1`. -/
  eps_symm : ∀ u v : V, form u v = eps.toComplex * form v u

namespace FormedSpace

variable (eps : Sign) (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V]

/-- The bilinear form of a formed space, as a short abbreviation. -/
abbrev B : LinearMap.BilinForm ℂ V :=
  FormedSpace.form (eps := eps) (V := V)

/-- The complex dimension of a formed space. -/
noncomputable abbrev dim : ℕ :=
  Module.finrank ℂ V

end FormedSpace

/-! ## `J` and `L` structures -/

/-- A conjugate-linear, form-preserving automorphism of a formed complex space.

The square sign is a parameter because in the target theorem
`J² = ε * dotε`.  The form-preservation condition belongs here: it is a
property of `J` itself, not of the paired compatibility with `L`. -/
structure JStructure (eps : Sign) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [FormedSpace eps V] (jSign : Sign) where
  /-- The underlying conjugate-semilinear equivalence. -/
  toSemilinearEquiv : V ≃ₛₗ[starRingEnd ℂ] V
  /-- The square condition `J² = jSign`. -/
  sq : ∀ v : V, toSemilinearEquiv (toSemilinearEquiv v) = jSign.toComplex • v
  /-- `J` preserves the bilinear form up to complex conjugation. -/
  preserves_form :
    ∀ u v : V, FormedSpace.B eps V (toSemilinearEquiv u) (toSemilinearEquiv v) =
      (starRingEnd ℂ) (FormedSpace.B eps V u v)

namespace JStructure

variable {eps : Sign} {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}

/-- The underlying conjugate-semilinear map of a `JStructure`. -/
abbrev toSemilinearMap (J : JStructure eps V jSign) : V →ₛₗ[starRingEnd ℂ] V :=
  J.toSemilinearEquiv

/-- Use a `JStructure` as a function. -/
instance : CoeFun (JStructure eps V jSign) (fun _ => V → V) where
  coe J := J.toSemilinearEquiv

theorem coe_apply (J : JStructure eps V jSign) (v : V) :
    J v = J.toSemilinearEquiv v := rfl

theorem toSemilinearMap_apply (J : JStructure eps V jSign) (v : V) :
    J.toSemilinearMap v = J v := rfl

end JStructure

/-- A complex-linear, form-preserving automorphism of a formed complex space.

The square sign is `dotε` in the target theorem.  The form-preservation
condition belongs here: it is a property of `L` itself, not of paired
compatibility with `J`. -/
structure LStructure (eps : Sign) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [FormedSpace eps V] (lSign : Sign) where
  /-- The underlying complex-linear equivalence. -/
  toLinearEquiv : V ≃ₗ[ℂ] V
  /-- The square condition `L² = lSign`. -/
  sq : ∀ v : V, toLinearEquiv (toLinearEquiv v) = lSign.toComplex • v
  /-- `L` preserves the bilinear form. -/
  preserves_form :
    ∀ u v : V, FormedSpace.B eps V (toLinearEquiv u) (toLinearEquiv v) =
      FormedSpace.B eps V u v

namespace LStructure

variable {eps : Sign} {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}

/-- The underlying complex-linear map of an `LStructure`. -/
abbrev toLinearMap (L : LStructure eps V lSign) : V →ₗ[ℂ] V :=
  L.toLinearEquiv

/-- Use an `LStructure` as a function. -/
instance : CoeFun (LStructure eps V lSign) (fun _ => V → V) where
  coe L := L.toLinearEquiv

theorem coe_apply (L : LStructure eps V lSign) (v : V) :
    L v = L.toLinearEquiv v := rfl

theorem toLinearMap_apply (L : LStructure eps V lSign) (v : V) :
    L.toLinearMap v = L v := rfl

end LStructure

/-! ## Compatibility of `J` and `L` -/

/-- Positive-definiteness of the Hermitian form
`H(u,v) = B(Lu,Jv)`.

The first conjunct records Hermitian symmetry.  The second records positivity
of diagonal real parts.  This is deliberately lightweight; later files may
replace or connect it with Mathlib's Hermitian-form API if useful. -/
def PositiveDefiniteHermitian (eps : Sign) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign) : Prop :=
  (∀ u v : V,
      FormedSpace.B eps V (L v) (J u) =
        (starRingEnd ℂ) (FormedSpace.B eps V (L u) (J v))) ∧
    (∀ v : V, v ≠ 0 → 0 < (FormedSpace.B eps V (L v) (J v)).re)

/-- The paired compatibility conditions between already form-preserving `J` and `L`.

This contains only genuinely paired data: commutation and Cartan positivity.
Individual form preservation is part of `JStructure` and `LStructure`. -/
structure JLCompatible {eps : Sign} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign) : Prop where
  /-- The commuting condition `LJ = JL`. -/
  commute : ∀ v : V, L (J v) = J (L v)
  /-- Positivity of the Hermitian form `H(u,v)=B(Lu,Jv)`. -/
  cartan_positive : PositiveDefiniteHermitian eps V J L

/-! ## Eigenspace conditions for `L` -/

/-- The eigenspace of a complex-linear equivalence at scalar `a`. -/
noncomputable def linearEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V ≃ₗ[ℂ] V) (a : ℂ) : Submodule ℂ V :=
  LinearMap.ker ((T : V →ₗ[ℂ] V) - a • LinearMap.id)

/-- The signature condition imposed on `L`.

For `dotε = +1`, this records the prescribed dimensions of the `+1` and `-1`
eigenspaces.  For `dotε = -1`, this predicate is `True`: the equality of the
`i` and `-i` eigenspace dimensions is a theorem derived from conjugate-linearity
of `J` and `JL` compatibility, not a design axiom. -/
def LSignatureCondition (star : ClassicalStar) (p q : ℕ)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (L : LStructure star.eps V star.dotEps) : Prop :=
  match star.dotEps with
  | Sign.pos =>
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q
  | Sign.neg => True

/-! ## Classical-space predicate -/

/-- Proposition saying that supplied data form a classical space of signature
`(star,p,q)`.

This is intentionally not a bundled object.  The vector space, formed-space
structure, `J`, and `L` are supplied first; this predicate states that they
satisfy the theorem's properties (1)--(9). -/
def IsClassicalSpace (star : ClassicalStar) (p q : ℕ)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (J : JStructure star.eps V star.jSign)
    (L : LStructure star.eps V star.dotEps) : Prop :=
  IsClassicalSignature star p q ∧
    Module.finrank ℂ V = p + q ∧
      JLCompatible J L ∧
        LSignatureCondition star p q V L

/-- Packed-signature version of `IsClassicalSpace`. -/
def IsClassicalSpaceFor (s : ClassicalSignature)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace s.eps V]
    (J : JStructure s.eps V s.jSign)
    (L : LStructure s.eps V s.dotEps) : Prop :=
  IsClassicalSpace s.star s.p s.q V J L

/-! ## Isomorphisms for uniqueness -/

/-- Isomorphism of formed spaces with the same `ε`.

This is the form-preserving part of uniqueness: a complex-linear equivalence
that carries the target bilinear form back to the source bilinear form. -/
structure FormedSpaceIso (eps : Sign)
    (V W : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace eps W] where
  /-- The underlying complex-linear equivalence. -/
  toLinearEquiv : V ≃ₗ[ℂ] W
  /-- Preservation of the bilinear forms. -/
  preserves_form :
    ∀ u v : V, FormedSpace.B eps W (toLinearEquiv u) (toLinearEquiv v) =
      FormedSpace.B eps V u v

/-- Isomorphism of two classical-space data sets for the same raw signature.

This encodes the uniqueness statement from `classicalgroup.md`: uniqueness is
up to a complex-linear form isomorphism intertwining both `J` and `L`, not
literal equality of the underlying types or structures. -/
structure ClassicalSpaceIso (star : ClassicalStar)
    (V W : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace star.eps W]
    (JV : JStructure star.eps V star.jSign)
    (LV : LStructure star.eps V star.dotEps)
    (JW : JStructure star.eps W star.jSign)
    (LW : LStructure star.eps W star.dotEps) where
  /-- The underlying isomorphism of formed spaces. -/
  toFormedSpaceIso : FormedSpaceIso star.eps V W
  /-- The isomorphism intertwines the two `J` structures. -/
  intertwines_J :
    ∀ v : V, toFormedSpaceIso.toLinearEquiv (JV v) =
      JW (toFormedSpaceIso.toLinearEquiv v)
  /-- The isomorphism intertwines the two `L` structures. -/
  intertwines_L :
    ∀ v : V, toFormedSpaceIso.toLinearEquiv (LV v) =
      LW (toFormedSpaceIso.toLinearEquiv v)

namespace FormedSpaceIso

variable {eps : Sign}
variable {U V W : Type*}
variable [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U] [FormedSpace eps U]
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [FormedSpace eps V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [FormedSpace eps W]

/-- Identity isomorphism of a formed space. -/
protected def refl (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] : FormedSpaceIso eps V V where
  toLinearEquiv := LinearEquiv.refl ℂ V
  preserves_form := by intro _ _; rfl

/-- Inverse of an isomorphism of formed spaces. -/
protected def symm (e : FormedSpaceIso eps V W) : FormedSpaceIso eps W V where
  toLinearEquiv := e.toLinearEquiv.symm
  preserves_form := by
    intro u v
    have h := e.preserves_form (e.toLinearEquiv.symm u) (e.toLinearEquiv.symm v)
    simpa using h.symm

/-- Composition of isomorphisms of formed spaces. -/
protected def trans (e₁ : FormedSpaceIso eps U V)
    (e₂ : FormedSpaceIso eps V W) : FormedSpaceIso eps U W where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  preserves_form := by
    intro u v
    calc
      FormedSpace.B eps W (e₂.toLinearEquiv (e₁.toLinearEquiv u))
          (e₂.toLinearEquiv (e₁.toLinearEquiv v))
          = FormedSpace.B eps V (e₁.toLinearEquiv u) (e₁.toLinearEquiv v) :=
            e₂.preserves_form (e₁.toLinearEquiv u) (e₁.toLinearEquiv v)
      _ = FormedSpace.B eps U u v := e₁.preserves_form u v

end FormedSpaceIso

namespace ClassicalSpaceIso

variable {star : ClassicalStar}
variable {U V W : Type*}
variable [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U] [FormedSpace star.eps U]
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [FormedSpace star.eps V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [FormedSpace star.eps W]
variable {JU : JStructure star.eps U star.jSign} {LU : LStructure star.eps U star.dotEps}
variable {JV : JStructure star.eps V star.jSign} {LV : LStructure star.eps V star.dotEps}
variable {JW : JStructure star.eps W star.jSign} {LW : LStructure star.eps W star.dotEps}

/-- Identity isomorphism of classical-space data. -/
protected def refl (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] (J : JStructure star.eps V star.jSign)
    (L : LStructure star.eps V star.dotEps) : ClassicalSpaceIso star V V J L J L where
  toFormedSpaceIso := FormedSpaceIso.refl (eps := star.eps) V
  intertwines_J := by intro _; rfl
  intertwines_L := by intro _; rfl

/-- Inverse of an isomorphism of classical-space data. -/
protected def symm (e : ClassicalSpaceIso star V W JV LV JW LW) :
    ClassicalSpaceIso star W V JW LW JV LV where
  toFormedSpaceIso := e.toFormedSpaceIso.symm
  intertwines_J := by
    intro w
    apply e.toFormedSpaceIso.toLinearEquiv.injective
    calc
      e.toFormedSpaceIso.toLinearEquiv (e.toFormedSpaceIso.toLinearEquiv.symm (JW w))
          = JW w := by simp
      _ = JW (e.toFormedSpaceIso.toLinearEquiv (e.toFormedSpaceIso.toLinearEquiv.symm w)) := by
            simp
      _ = e.toFormedSpaceIso.toLinearEquiv
            (JV (e.toFormedSpaceIso.toLinearEquiv.symm w)) := by
            exact (e.intertwines_J (e.toFormedSpaceIso.toLinearEquiv.symm w)).symm
  intertwines_L := by
    intro w
    apply e.toFormedSpaceIso.toLinearEquiv.injective
    calc
      e.toFormedSpaceIso.toLinearEquiv (e.toFormedSpaceIso.toLinearEquiv.symm (LW w))
          = LW w := by simp
      _ = LW (e.toFormedSpaceIso.toLinearEquiv (e.toFormedSpaceIso.toLinearEquiv.symm w)) := by
            simp
      _ = e.toFormedSpaceIso.toLinearEquiv
            (LV (e.toFormedSpaceIso.toLinearEquiv.symm w)) := by
            exact (e.intertwines_L (e.toFormedSpaceIso.toLinearEquiv.symm w)).symm

/-- Composition of isomorphisms of classical-space data. -/
protected def trans (e₁ : ClassicalSpaceIso star U V JU LU JV LV)
    (e₂ : ClassicalSpaceIso star V W JV LV JW LW) :
    ClassicalSpaceIso star U W JU LU JW LW where
  toFormedSpaceIso := e₁.toFormedSpaceIso.trans e₂.toFormedSpaceIso
  intertwines_J := by
    intro u
    calc
      e₂.toFormedSpaceIso.toLinearEquiv
          (e₁.toFormedSpaceIso.toLinearEquiv (JU u))
          = e₂.toFormedSpaceIso.toLinearEquiv (JV (e₁.toFormedSpaceIso.toLinearEquiv u)) := by
            rw [e₁.intertwines_J]
      _ = JW (e₂.toFormedSpaceIso.toLinearEquiv (e₁.toFormedSpaceIso.toLinearEquiv u)) := by
            rw [e₂.intertwines_J]
  intertwines_L := by
    intro u
    calc
      e₂.toFormedSpaceIso.toLinearEquiv
          (e₁.toFormedSpaceIso.toLinearEquiv (LU u))
          = e₂.toFormedSpaceIso.toLinearEquiv (LV (e₁.toFormedSpaceIso.toLinearEquiv u)) := by
            rw [e₁.intertwines_L]
      _ = LW (e₂.toFormedSpaceIso.toLinearEquiv (e₁.toFormedSpaceIso.toLinearEquiv u)) := by
            rw [e₂.intertwines_L]

end ClassicalSpaceIso

/-- Packed-signature alias for `ClassicalSpaceIso`. -/
abbrev ClassicalSpaceIsoFor (s : ClassicalSignature)
    (V W : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace s.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace s.eps W]
    (JV : JStructure s.eps V s.jSign)
    (LV : LStructure s.eps V s.dotEps)
    (JW : JStructure s.eps W s.jSign)
    (LW : LStructure s.eps W s.dotEps) : Type _ :=
  ClassicalSpaceIso s.star V W JV LV JW LW

end ClassicalGroup
