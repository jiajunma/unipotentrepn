/-
# AC.fold produces a single-term ACResult with multiplicity 1

Reference: natural-language proof at
`lean/docs/blueprints/AC_fold_singleton.md`.

This file establishes that when the ILS-level theta-lift is singleton at
every step, the full `AC.fold` output is `[(1, L_τ)]` for a unique
`L_τ : ILS`. This is the underpinning for extracting a single MYD from
a PBP's associated-cycle computation.

Scope of this file (M1.2 increment 1):
- `AC.base_singleton`: the base case is singleton.
- `AC.step_singleton`: one step preserves the singleton structure.

Later increments add:
- `AC.ChainValid`: the predicate that each step's ILS.thetaLift is
  singleton.
- `AC.fold_singleton`: full induction over the chain.
- Instantiation for descent chains.
-/
import CombUnipotent.MYD.SYD
import CombUnipotent.MYD.TypeMYD
import CombUnipotent.MYD

namespace BMSZ

/-- The base ILS for γ: paper's leaf AC value. Extracting the single
    payload of `AC.base γ`. -/
def baseILS (γ : RootType) : ILS :=
  match γ with
  | .Bplus  => [(1, 0)]
  | .Bminus => [(0, -1)]
  | .C | .D | .M => []

/-- `AC.base γ = [(1, baseILS γ)]` — immediate by case split. -/
theorem AC_base_singleton (γ : RootType) :
    AC.base γ = [(1, baseILS γ)] := by
  cases γ <;> rfl

/-- `ACResult.twistBD` on a single-term list yields a single-term list
    with the same multiplicity. -/
theorem ACResult_twistBD_singleton (c : ℤ) (E : ILS) (tp tn : ℤ) :
    ACResult.twistBD [(c, E)] tp tn = [(c, ILS.twistBD E tp tn)] := by
  unfold ACResult.twistBD
  simp

/-- `ACResult.thetaLift` on a single-term list with a singleton
    ILS-thetaLift yields a single-term list with the same multiplicity. -/
theorem ACResult_thetaLift_singleton (c : ℤ) (E : ILS)
    (target : RootType) (p q : ℤ)
    (E' : ILS) (h : ILS.thetaLift E target p q = [E']) :
    ACResult.thetaLift [(c, E)] target p q = [(c, E')] := by
  unfold ACResult.thetaLift
  simp [h]

/-- **Single-step singleton preservation**: if source is `[(c, E)]` and
    the internal ILS-thetaLift is a singleton `[E']`, then `AC.step`
    produces `[(c, final_E)]` for some `final_E`.

    The hypothesis `h_theta` is stated on the possibly-twisted input
    that enters `thetaLift`, matching `AC.step`'s pre-twist branching:
    for γ ∈ {C, M} with ε_wp = 1, the pre-twist is `ILS.twistBD (-1) (-1)`.
-/
theorem AC_step_singleton (c : ℤ) (E : ILS) (γ : RootType)
    (p q : ℤ) (ε_τ ε_wp : Fin 2)
    -- Describe the intermediate ILS after pre-twist:
    (pre : ILS)
    (h_pre : pre = (if γ = .C ∨ γ = .M then
                      (if ε_wp = 1 then ILS.twistBD E (-1) (-1) else E)
                    else E))
    (E' : ILS) (h_theta : ILS.thetaLift pre γ p q = [E']) :
    AC.step [(c, E)] γ p q ε_τ ε_wp =
      [(c,
        if (γ = .Bplus ∨ γ = .Bminus ∨ γ = .D) ∧ ε_τ = 1 then
          ILS.twistBD E' 1 (-1)
        else E')] := by
  -- Compute `twisted` explicitly: [(c, pre)]
  have h_tw : (if γ = .C ∨ γ = .M then
                (if ε_wp = 1 then ACResult.twistBD [(c, E)] (-1) (-1)
                 else [(c, E)])
              else [(c, E)]) = [(c, pre)] := by
    subst h_pre
    split_ifs with hCM h1 <;> simp [ACResult.twistBD]
  -- Compute `lifted` from twisted: [(c, E')]
  have h_lift : ACResult.thetaLift [(c, pre)] γ p q = [(c, E')] :=
    ACResult_thetaLift_singleton c pre γ p q E' h_theta
  -- Now unfold AC.step and rewrite
  show (let twisted := if γ = .C ∨ γ = .M then
        if ε_wp = 1 then ACResult.twistBD [(c, E)] (-1) (-1) else [(c, E)]
      else [(c, E)]
    let lifted := twisted.thetaLift γ p q
    if (γ = .Bplus ∨ γ = .Bminus ∨ γ = .D) ∧ ε_τ = 1 then
      lifted.twistBD 1 (-1)
    else lifted) = _
  rw [h_tw]
  simp only
  rw [h_lift]
  split_ifs with hpost
  · simp [ACResult.twistBD]
  · rfl

end BMSZ
