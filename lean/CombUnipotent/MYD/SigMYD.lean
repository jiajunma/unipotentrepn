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

/-- **Natural signature target** for a D-type PBP τ at the end of
    the descent chain. By paper Prop 11.4 + the AC construction,
    this equals `(p_τ, ±q_τ)` depending on `ε_τ` (the outermost step's
    post-twist). For simplicity we state it abstractly for now. -/
noncomputable def signTarget_D (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ
  ((s.1 : ℤ), (s.2 : ℤ))  -- naive; real formula involves ε_τ twist

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
    -- Step: use ACResult.thetaLift_sign + sign-preserving operations
    sorry

end BMSZ
