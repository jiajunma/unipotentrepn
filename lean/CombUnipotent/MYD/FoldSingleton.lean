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

/-! ## Full chain singleton preservation

A chain of step data yields a single-term AC output iff every step's
internal `ILS.thetaLift` is a singleton. We capture this via an inductive
predicate `ChainSingleton` that threads the current ILS through the chain.
-/

/-- Pre-twist of E before theta-lift at step `d`. -/
def stepPreTwist (E : ILS) (d : ACStepData) : ILS :=
  if d.γ = .C ∨ d.γ = .M then
    (if d.ε_wp = 1 then ILS.twistBD E (-1) (-1) else E)
  else E

/-- Post-twist of E' after theta-lift at step `d`. -/
def stepPostTwist (E' : ILS) (d : ACStepData) : ILS :=
  if (d.γ = .Bplus ∨ d.γ = .Bminus ∨ d.γ = .D) ∧ d.ε_τ = 1 then
    ILS.twistBD E' 1 (-1)
  else E'

/-- Predicate: folding `chain` starting from ILS `E` yields a final ILS
    `E_final`, with every step's thetaLift being a singleton. -/
inductive ChainSingleton : ILS → List ACStepData → ILS → Prop
  | nil (E : ILS) : ChainSingleton E [] E
  | cons {E : ILS} {d : ACStepData} {rest : List ACStepData} {E_final : ILS}
      (E' : ILS)
      (h_theta : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E'])
      (h_rest : ChainSingleton (stepPostTwist E' d) rest E_final) :
      ChainSingleton E (d :: rest) E_final

/-- **Chain snoc** (chain concatenation with a single step at the end).

    Given a `ChainSingleton E chain E_mid` and one more step `d` whose
    ILS-thetaLift is singleton `[E']`, we get
    `ChainSingleton E (chain ++ [d]) (stepPostTwist E' d)`.

    This is needed because `IsDescentChain_D.step` builds the chain by
    appending outer step, while `ChainSingleton.cons` prepends. Snoc
    reconciles the orientations. -/
theorem ChainSingleton.snoc {E E_mid E' : ILS}
    {chain : List ACStepData} {d : ACStepData}
    (h_rest : ChainSingleton E chain E_mid)
    (h_theta : ILS.thetaLift (stepPreTwist E_mid d) d.γ d.p d.q = [E']) :
    ChainSingleton E (chain ++ [d]) (stepPostTwist E' d) := by
  induction h_rest with
  | nil E =>
    -- base: chain = [], E_mid = E. [] ++ [d] = [d].
    rw [List.nil_append]
    exact ChainSingleton.cons E' h_theta (ChainSingleton.nil _)
  | cons E'' h_theta' _ ih =>
    -- inductive: chain = d_head :: rest. Use IH on rest.
    rw [List.cons_append]
    exact ChainSingleton.cons E'' h_theta' (ih h_theta)

/-- **Main lemma (M1.2)**: When a chain is singleton-valid with witness
    `E_final`, the AC.fold output is `[(1, E_final)]`.

    Proof: induction on `chain`.
    - Base `[]`: `foldl _ init [] = init = AC.base γ = [(1, baseILS γ)]`.
      The predicate `ChainSingleton` forces `E_final = baseILS γ`.
    - Step `d :: rest`: `foldl f init (d :: rest) = foldl f (f init d) rest`.
      By `AC_step_singleton`, `f init d = [(1, stepPostTwist E' d)]`.
      Then apply IH on rest with new starting ILS. -/
theorem AC_fold_singleton (γ : RootType) (chain : List ACStepData)
    (E_final : ILS) (h : ChainSingleton (baseILS γ) chain E_final) :
    AC.fold γ chain = [(1, E_final)] := by
  -- Strengthen for induction: prove it for arbitrary starting ILS.
  suffices h_gen : ∀ (c : ℤ) (E : ILS) (chain : List ACStepData) (E_final : ILS),
      ChainSingleton E chain E_final →
      chain.foldl (fun ac d => AC.step ac d.γ d.p d.q d.ε_τ d.ε_wp) [(c, E)]
        = [(c, E_final)] by
    have := h_gen 1 (baseILS γ) chain E_final h
    unfold AC.fold
    rw [AC_base_singleton γ]
    exact this
  intro c E chain E_final h
  induction h with
  | nil E => rfl
  | cons E' h_theta h_rest ih =>
      rename_i E d rest E_final
      simp only [List.foldl_cons]
      rw [AC_step_singleton c E d.γ d.p d.q d.ε_τ d.ε_wp (stepPreTwist E d) rfl E' h_theta]
      -- After the rewrite, the head is [(c, stepPostTwist E' d)].
      exact ih

end BMSZ
