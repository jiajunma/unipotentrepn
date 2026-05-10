import CombUnipotent.ClassicalGroup.StandardModels

/-!
# Existence theorem statements for the ClassicalGroup task

This file states the existence package and the case-by-case standard-model
existence theorems required by `classicalgroup.md`.  Standard model
constructions will be implemented in the model files later.
-/

namespace ClassicalGroup

universe u

/-- Existence package for a raw signature `(star,p,q)`.

It says there is some finite-dimensional complex vector space, a formed-space
structure, and form-preserving `J` and `L` satisfying `IsClassicalSpace`. -/
def HasClassicalSpace (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V),
    ∃ (_ : FormedSpace star.eps V),
      ∃ (J : JStructure star.eps V star.jSign)
        (L : LStructure star.eps V star.dotEps),
        IsClassicalSpace star p q V J L

/-- Packed-signature version of `HasClassicalSpace`. -/
def HasClassicalSpaceFor (s : ClassicalSignature) : Prop :=
  HasClassicalSpace s.star s.p s.q

/-- Case `B`: existence from the explicit `S_{p,q}` model. -/
theorem exists_B_model (p q : ℕ) (hOdd : Odd (p + q)) :
    HasClassicalSpace ClassicalStar.B p q := by
  /-
  Blueprint model: `V = ℂ^(p+q)`, `B(u,v)=uᵀ S_{p,q} v`, `J=conjugation`,
  and `L=S_{p,q}`.  Direct matrix calculations prove all fields.
  -/
  refine ⟨OrthVec p q, inferInstance, inferInstance, inferInstance, inferInstance,
    orthJ p q, orthL p q, ?_⟩
  exact ⟨hOdd, orth_finrank p q, orth_compatible p q, orth_LSignature p q⟩

/-- Case `D`: existence from the same explicit `S_{p,q}` model. -/
theorem exists_D_model (p q : ℕ) (hEven : Even (p + q)) :
    HasClassicalSpace ClassicalStar.D p q := by
  /-
  Same construction as the `B` case; only the signature parity condition differs.
  -/
  refine ⟨OrthVec p q, inferInstance, inferInstance, inferInstance, inferInstance,
    orthJ p q, orthL p q, ?_⟩
  exact ⟨hEven, orth_finrank p q, orth_compatible p q, by
    simpa [LSignatureCondition] using orth_LSignature p q⟩

/-- Case `C`: existence from the real symplectic model. -/
theorem exists_C_model (r : ℕ) :
    HasClassicalSpace ClassicalStar.C r r := by
  /-
  Blueprint model: `V = ℂ^r ⊕ ℂ^r`, `B((z,w),(z',w')) = zᵀw' - wᵀz'`,
  `J=conjugation`, and `L(z,w)=(w,-z)`.
  -/
  refine ⟨PairVec r, inferInstance, inferInstance, inferInstance, inferInstance,
    sympRealJ r, sympL r, ?_⟩
  exact ⟨rfl, symp_finrank r, symp_compatible r, trivial⟩

/-- Case `Ctilda`: same linear data as the `C` model. -/
theorem exists_Ctilda_model (r : ℕ) :
    HasClassicalSpace ClassicalStar.Ctilda r r := by
  /-
  The metaplectic cover is external; the underlying `J,L` data are the same as
  in the `C` model.
  -/
  refine ⟨PairVec r, inferInstance, inferInstance, inferInstance, inferInstance,
    sympRealJ r, sympL r, ?_⟩
  exact ⟨rfl, symp_finrank r, symp_compatible r, trivial⟩

/-- Case `C*`: existence with `p=2a`, `q=2b`. -/
theorem exists_Cstar_model (a b : ℕ) :
    HasClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) := by
  /-
  Blueprint model: `V = ℂ^(a+b) ⊕ ℂ^(a+b)`, alternating form with matrix
  `S_{a,b}`, `J(z,w)=(-conj w, conj z)`, and `L(z,w)=(S z, S w)`.
  -/
  refine ⟨CstarVec a b, inferInstance, inferInstance, inferInstance, inferInstance,
    cstarJ a b, cstarL a b, ?_⟩
  exact ⟨⟨⟨a, by omega⟩, ⟨b, by omega⟩⟩, cstar_finrank a b,
    cstar_compatible a b, cstar_LSignature a b⟩

/-- Case `D*`: existence with `p=q=r`. -/
theorem exists_Dstar_model (r : ℕ) :
    HasClassicalSpace ClassicalStar.Dstar r r := by
  /-
  Blueprint model: `V = ℂ^r ⊕ ℂ^r`,
  `B((z,w),(z',w')) = -i(zᵀw' + wᵀz')`,
  `J(z,w)=(-conj w,conj z)`, and `L(z,w)=(i z,-i w)`.
  -/
  refine ⟨PairVec r, inferInstance, inferInstance, inferInstance, inferInstance,
    dstarJ r, dstarL r, ?_⟩
  exact ⟨rfl, symp_finrank r, dstar_compatible r, trivial⟩

/-- Existence obtained by dispatching to the four blueprint model cases. -/
theorem exists_classical_space_by_cases (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpace star p q := by
  cases star with
  | B =>
      exact exists_B_model p q hsig
  | C =>
      subst q
      exact exists_C_model p
  | D =>
      exact exists_D_model p q hsig
  | Ctilda =>
      subst q
      exact exists_Ctilda_model p
  | Cstar =>
      rcases hsig with ⟨hp, hq⟩
      rcases hp with ⟨a, ha⟩
      rcases hq with ⟨b, hb⟩
      have hp' : p = 2 * a := by omega
      have hq' : q = 2 * b := by omega
      rw [hp', hq']
      exact exists_Cstar_model a b
  | Dstar =>
      subst q
      exact exists_Dstar_model p

/-- Main existence theorem, raw interface. -/
theorem exists_classical_space (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpace star p q := by
  exact exists_classical_space_by_cases star p q hsig

/-- Main existence theorem, packed-signature interface. -/
theorem exists_classical_space_for (s : ClassicalSignature) :
    HasClassicalSpaceFor s := by
  exact exists_classical_space s.star s.p s.q s.isClassical

end ClassicalGroup
