import CombUnipotent.ClassicalGroup.Existence
import CombUnipotent.ClassicalGroup.NormalForms

/-!
# Uniqueness theorem statements for the ClassicalGroup task

Uniqueness is formalized as existence of a complex-linear isomorphism preserving
the form and intertwining both `J` and `L`, not as equality of structures.
-/

namespace ClassicalGroup

universe u

/-- Pairwise uniqueness for all classical spaces of a fixed raw signature. -/
def UniqueClassicalSpacesFor (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∀ (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace star.eps W]
    (JV : JStructure star.eps V star.jSign)
    (LV : LStructure star.eps V star.dotEps)
    (JW : JStructure star.eps W star.jSign)
    (LW : LStructure star.eps W star.dotEps),
      IsClassicalSpace star p q V JV LV →
        IsClassicalSpace star p q W JW LW →
          Nonempty (ClassicalSpaceIso star V W JV LV JW LW)

/-- Pairwise uniqueness in the `B` case. -/
theorem unique_B_model (p q : ℕ) (hOdd : Odd (p + q)) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.B p q := by
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  rcases normalForm_B p q hOdd V JV LV hV with ⟨eV⟩
  rcases normalForm_B p q hOdd W JW LW hW with ⟨eW⟩
  exact ⟨eV.trans eW.symm⟩

/-- Pairwise uniqueness in the `D` case. -/
theorem unique_D_model (p q : ℕ) (hEven : Even (p + q)) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.D p q := by
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  rcases normalForm_D p q hEven V JV LV hV with ⟨eV⟩
  rcases normalForm_D p q hEven W JW LW hW with ⟨eW⟩
  exact ⟨eV.trans eW.symm⟩

/-- Pairwise uniqueness in the `C` case. -/
theorem unique_C_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.C r r := by
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  rcases normalForm_C r V JV LV hV with ⟨eV⟩
  rcases normalForm_C r W JW LW hW with ⟨eW⟩
  exact ⟨eV.trans eW.symm⟩

/-- Pairwise uniqueness in the `Ctilda` case. -/
theorem unique_Ctilda_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Ctilda r r := by
  /-
  Same linear normal form as in the `C` case.  The metaplectic cover is not part
  of the `J,L` data.
  -/
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  have hVC : IsClassicalSpace ClassicalStar.C r r V JV LV := by
    simpa [IsClassicalSpace, IsClassicalSignature, LSignatureCondition] using hV
  have hWC : IsClassicalSpace ClassicalStar.C r r W JW LW := by
    simpa [IsClassicalSpace, IsClassicalSignature, LSignatureCondition] using hW
  rcases unique_C_model r V W JV LV JW LW hVC hWC with ⟨e⟩
  exact ⟨{ toFormedSpaceIso := e.toFormedSpaceIso
           intertwines_J := e.intertwines_J
           intertwines_L := e.intertwines_L }⟩

/-- Pairwise uniqueness in the `C*` case with `p=2a`, `q=2b`. -/
theorem unique_Cstar_model (a b : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Cstar (2 * a) (2 * b) := by
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  rcases normalForm_Cstar a b V JV LV hV with ⟨eV⟩
  rcases normalForm_Cstar a b W JW LW hW with ⟨eW⟩
  exact ⟨eV.trans eW.symm⟩

/-- Pairwise uniqueness in the `D*` case. -/
theorem unique_Dstar_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Dstar r r := by
  intro V W _ _ _ _ _ _ _ _ JV LV JW LW hV hW
  rcases normalForm_Dstar r V JV LV hV with ⟨eV⟩
  rcases normalForm_Dstar r W JW LW hW with ⟨eW⟩
  exact ⟨eV.trans eW.symm⟩

/-- Uniqueness obtained by dispatching to the blueprint cases. -/
theorem unique_classical_spaces_by_cases (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    UniqueClassicalSpacesFor.{u} star p q := by
  cases star with
  | B =>
      exact unique_B_model p q hsig
  | C =>
      subst q
      exact unique_C_model p
  | D =>
      exact unique_D_model p q hsig
  | Ctilda =>
      subst q
      exact unique_Ctilda_model p
  | Cstar =>
      rcases hsig with ⟨hp, hq⟩
      rcases hp with ⟨a, ha⟩
      rcases hq with ⟨b, hb⟩
      have hp' : p = 2 * a := by omega
      have hq' : q = 2 * b := by omega
      rw [hp', hq']
      exact unique_Cstar_model a b
  | Dstar =>
      subst q
      exact unique_Dstar_model p

/-- Main uniqueness theorem, raw interface. -/
theorem classical_space_unique (star : ClassicalStar) (p q : ℕ)
    (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace star.eps W]
    (JV : JStructure star.eps V star.jSign)
    (LV : LStructure star.eps V star.dotEps)
    (JW : JStructure star.eps W star.jSign)
    (LW : LStructure star.eps W star.dotEps)
    (hV : IsClassicalSpace star p q V JV LV)
    (hW : IsClassicalSpace star p q W JW LW) :
    Nonempty (ClassicalSpaceIso star V W JV LV JW LW) := by
  exact unique_classical_spaces_by_cases star p q (isClassicalSpace_signature hV)
    V W JV LV JW LW hV hW

/-- Main uniqueness theorem, packed-signature interface. -/
theorem classical_space_unique_for (s : ClassicalSignature)
    (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace s.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace s.eps W]
    (JV : JStructure s.eps V s.jSign)
    (LV : LStructure s.eps V s.dotEps)
    (JW : JStructure s.eps W s.jSign)
    (LW : LStructure s.eps W s.dotEps)
    (hV : IsClassicalSpaceFor s V JV LV)
    (hW : IsClassicalSpaceFor s W JW LW) :
    Nonempty (ClassicalSpaceIsoFor s V W JV LV JW LW) := by
  exact classical_space_unique s.star s.p s.q V W JV LV JW LW hV hW

end ClassicalGroup
