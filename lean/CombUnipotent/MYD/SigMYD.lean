/-
# `MYD_sig γ signature` — Signature-based MYD (paper Def 9.3 + 9.10)

Reference: `lean/docs/blueprints/dpToSYD_structural_mismatch.md`.

**Motivation**: the previous `MYD γ O` subtype used
`absValues E = O.rows` as the shape constraint, but this doesn't
match paper's Def 9.3 + 9.10 signature-based formulation, and
doesn't decompose under descent. Here we define the paper-faithful
version.

**Structure**:
- `E : ILS`
- `parity`: γ-parity at each row (Def 9.3)
- `sign_match`: `ILS.sign E = signature` (Def 9.10)

The `signature : ℤ × ℤ` parameter replaces the SYD orbit index.
For quasi-distinguished orbits, all PBPs with fixed shape share
the same signature (paper Prop 11.4); this is our intended use case.
-/
import CombUnipotent.MYD.TypeMYD
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.MYD

open PBPInstantiation (toACStepData_D)

namespace BMSZ

/-- **Paper-faithful MYD_γ**: ILS with γ-parity and signature match.
    (Def 9.3 + Eq. 9.10.) -/
structure MYD_sig (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  parity : ∀ (j : ℕ) (h : j < E.length), MYDRowValid γ (j + 1) E[j]
  sign_match : ILS.sign E = signature

namespace MYD_sig

variable {γ : RootType} {signature : ℤ × ℤ}

theorem ext {M₁ M₂ : MYD_sig γ signature} (h : M₁.E = M₂.E) : M₁ = M₂ := by
  cases M₁; cases M₂; congr

instance : DecidableEq (MYD_sig γ signature) := fun M₁ M₂ =>
  decidable_of_iff (M₁.E = M₂.E)
    ⟨fun h => ext h, fun h => by rw [h]⟩

end MYD_sig

/-! ## Signature preservation through descent chain

Using paper's Eq. 9.10 + existing `ACResult.thetaLift_sign` (MYD.lean:821),
we track `ILS.sign E` through the descent chain.
-/

/-- **Signature target** for a D-type PBP τ.

    Note: `twistBD_sign` (MYD.lean:436) shows that `ILS.sign` is
    INVARIANT under `twistBD tp tn` for tp, tn ∈ {1, -1} (sign uses
    natAbs). So the ε_τ post-twist does NOT affect the signature.
    The target is just the PBP's signature cast to ℤ × ℤ. -/
noncomputable def signTarget_D (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))

/-- **Theorem**: along a valid descent chain, the extracted ILS has
    sign matching the τ-derived target (up to ε_τ twist details).

    Proof outline (induction on chain):
    - Base: E = baseILS .D = [], ILS.sign [] = (0, 0). τ has empty shapes,
      so PBP.signature τ = (0, 0) = signTarget_D τ. ✓
    - Step: use `ACResult.thetaLift_sign` (MYD.lean:821) to show sign
      is preserved through the chain's theta-lift + twist operations.

    Deferred: the exact (ε_τ-twisted) formula needs careful alignment
    with `AC.step_sign_D` (MYD.lean:865). Stated as sorry for now. -/
theorem descentChain_sign_match_D {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton (baseILS .D) chain E) :
    ILS.sign E = signTarget_D τ := by
  induction h_chain generalizing E with
  | base τ hγ h_empty =>
    cases h_sing
    -- E = baseILS .D = []; ILS.sign [] = (0, 0)
    show ILS.sign (baseILS .D) = signTarget_D τ
    -- ILS.sign [] = (0, 0) definitionally
    have h_E : ILS.sign (baseILS .D) = (0, 0) := by
      unfold baseILS ILS.sign
      simp
    rw [h_E]
    -- PBP.signature τ = (0, 0) when both shapes are empty (D case)
    unfold signTarget_D
    have h_sig : PBP.signature τ = (0, 0) := by
      unfold PBP.signature
      have hP_empty : ∀ s, τ.P.countSym s = 0 := by
        intro s
        unfold PaintedYoungDiagram.countSym
        rw [h_empty.1]
        simp
      have hQ_empty : ∀ s, τ.Q.countSym s = 0 := by
        intro s
        unfold PaintedYoungDiagram.countSym
        rw [h_empty.2]
        simp
      simp [hγ, hP_empty, hQ_empty]
    rw [h_sig]
    simp
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Key insight: sign E = sign E' (post-twist preserves sign) = (d.p, d.q)
    -- (by thetaLift_CD_sign). Don't even need IH for the sign!
    -- stepPreTwist for D is identity (no pre-twist, d.γ = .D not .C or .M).
    have h_preTwist : stepPreTwist E_mid (toACStepData_D τ_outer hγ) = E_mid := by
      unfold stepPreTwist
      simp [toACStepData_D]
    -- ILS.thetaLift with .D is thetaLift_CD
    have h_tl : ILS.thetaLift E_mid .D (toACStepData_D τ_outer hγ).p
                  (toACStepData_D τ_outer hγ).q = [E'] := by
      rw [← h_preTwist]
      show ILS.thetaLift (stepPreTwist E_mid (toACStepData_D τ_outer hγ))
        (toACStepData_D τ_outer hγ).γ (toACStepData_D τ_outer hγ).p
        (toACStepData_D τ_outer hγ).q = [E']
      exact h_theta
    have h_tl_cd : ILS.thetaLift_CD E_mid (toACStepData_D τ_outer hγ).p
                    (toACStepData_D τ_outer hγ).q = [E'] := by
      simpa [ILS.thetaLift] using h_tl
    have h_sign_E' : ILS.sign E' = ((toACStepData_D τ_outer hγ).p,
                                    (toACStepData_D τ_outer hγ).q) :=
      ILS.thetaLift_CD_sign E_mid _ _ E' (by rw [h_tl_cd]; simp)
    -- Post-twist preserves sign
    have h_sign_E : ILS.sign E = ILS.sign E' := by
      rw [h_E_final]
      unfold stepPostTwist
      split_ifs with hpost
      · -- twistBD 1 (-1) preserves sign
        exact ILS.twistBD_sign E' 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · rfl
    rw [h_sign_E, h_sign_E']
    -- Target: signTarget_D τ_outer = (PBP.signature τ_outer : ℤ × ℤ)
    unfold signTarget_D toACStepData_D
    simp

/-! ## Descendable orbit shape (matches AC chain augment structure)

The standard `dpToSYD` uses `partTranspose + rowMultiplicities`,
which does NOT decompose cleanly under `dp.drop 2`. Here we define
a variant that IS `dp.drop 2`-recursive.

For a descent chain of D-type PBPs at levels
`τ → doubleDescent τ → ... → base`, the AC chain builds
`L_τ = (row_outer) :: L_{τ'}` via augment at each step. So the
"orbit shape" at each level is
`[row_outer, row_{outer-1}, ..., row_inner]` — built one row at a
time by each descent step.

This function computes that structural list:
-/

/-- Descendable SYD row list: recursive on `dp.drop 2`. Each step
    prepends one row derived from the "signature difference" at
    that level. -/
noncomputable def dpToSYDRows_desc_D (dp : DualPart) : List (ℕ × ℕ) := go dp dp.length
where
  /-- Fuel-based recursion to avoid well-founded proof obligation. -/
  go : DualPart → ℕ → List (ℕ × ℕ)
  | _, 0 => []
  | [], _ => []
  | [_], _ => []
  | (r₁ :: r₂ :: rest), n + 1 =>
    -- Outer row: derived from r₁, r₂ (paper's partition descent)
    -- For D: row entry = ((r₁ + 1) / 2 - (r₂ - 1 \?? ... / 2), ...)
    -- This needs paper formula. Placeholder: (0, 0).
    (0, 0) :: go rest n

end BMSZ
