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
    (_h_chain : IsDescentChain_D τ chain)
    (_h_sing : ChainSingleton (baseILS .D) chain E) :
    ILS.sign E = signTarget_D τ := by
  sorry

end BMSZ
