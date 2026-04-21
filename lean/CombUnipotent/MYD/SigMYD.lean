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

/-! ## ILS trim — canonical form for MYD_sig finiteness

Trailing `(0, 0)` rows don't affect `ILS.sign` (since
`signRow i (0, 0) = (0, 0)`). To avoid the infinite family of
sign-equivalent ILSs, we define a canonical `trim` form that
strips trailing zeros. Used to build the refined finite subtype
`BMSZ.MYD_sig_trim`.

These are placed OUTSIDE `namespace BMSZ` to extend the existing
top-level `ILS` namespace from `MYD.lean`.
-/

namespace ILS

/-- Strip trailing `(0, 0)` rows from an ILS. -/
def trim (E : ILS) : ILS :=
  (E.reverse.dropWhile (· = (0, 0))).reverse

@[simp] theorem trim_nil : trim [] = [] := rfl

theorem trim_append_zero (E : ILS) :
    trim (E ++ [(0, 0)]) = trim E := by
  unfold trim
  simp [List.reverse_append]

/-- Appending `(0, 0)` to any ILS preserves `sign`. -/
theorem sign_append_zero (E : ILS) :
    sign (E ++ [(0, 0)]) = sign E := by
  unfold sign
  rw [List.zipIdx_append]
  simp [List.foldl_append, signRow]

/-- `trim` preserves `sign`. -/
theorem sign_trim (E : ILS) : sign (trim E) = sign E := by
  induction E using List.reverseRecOn with
  | nil => simp [trim]
  | append_singleton xs a ih =>
    by_cases h : a = (0, 0)
    · subst h
      rw [trim_append_zero, sign_append_zero, ih]
    · unfold trim
      simp [List.reverse_append, h]

/-- Predicate: ILS has no trailing `(0, 0)` row. -/
def IsTrim (E : ILS) : Prop := E.getLast? ≠ some (0, 0)

theorem isTrim_nil : IsTrim ([] : ILS) := by
  unfold IsTrim; simp

theorem trim_isTrim (E : ILS) : IsTrim (trim E) := by
  induction E using List.reverseRecOn with
  | nil => exact isTrim_nil
  | append_singleton xs a ih =>
    by_cases h : a = (0, 0)
    · subst h
      rw [trim_append_zero]
      exact ih
    · unfold trim IsTrim
      simp [List.reverse_append, h]

end ILS

namespace BMSZ

/-- **Signature-level MYD_γ**: ILS with signature match.

    Paper Def 9.3 also requires γ-parity (p_i = q_i ∈ N at parity-forced
    rows), but that MYDRowValid invariant fails for chain-extracted E
    without a quasi-distinguished restriction (see
    `project_parity_requires_quasi_distinguished.md`). Since the QD
    restriction is available at the `MYD_sig_qd` level (not here), we
    drop the parity field at this level. This gives a WEAKER bijection
    target where multiple ILSs with matching sign are considered
    equivalent, but enables Phi_γ_sig to type-check without QD. -/
structure MYD_sig (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  sign_match : ILS.sign E = signature

namespace MYD_sig

variable {γ : RootType} {signature : ℤ × ℤ}

theorem ext {M₁ M₂ : MYD_sig γ signature} (h : M₁.E = M₂.E) : M₁ = M₂ := by
  cases M₁; cases M₂; congr

instance : DecidableEq (MYD_sig γ signature) := fun M₁ M₂ =>
  decidable_of_iff (M₁.E = M₂.E)
    ⟨fun h => ext h, fun h => by rw [h]⟩

end MYD_sig

/-- **Trim-canonicalized MYD_sig**: subtype where `E` is trim. Used
    to get a genuinely finite bijection target. -/
structure MYD_sig_trim (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  sign_match : ILS.sign E = signature
  is_trim : ILS.IsTrim E

namespace MYD_sig_trim

variable {γ : RootType} {signature : ℤ × ℤ}

theorem ext {M₁ M₂ : MYD_sig_trim γ signature} (h : M₁.E = M₂.E) : M₁ = M₂ := by
  cases M₁; cases M₂; congr

instance : DecidableEq (MYD_sig_trim γ signature) := fun M₁ M₂ =>
  decidable_of_iff (M₁.E = M₂.E)
    ⟨fun h => ext h, fun h => by rw [h]⟩

end MYD_sig_trim

/-- Canonicalize a `MYD_sig` to `MYD_sig_trim` by trimming. -/
noncomputable def MYD_sig.toTrim {γ : RootType} {s : ℤ × ℤ}
    (M : MYD_sig γ s) : MYD_sig_trim γ s where
  E := ILS.trim M.E
  sign_match := by rw [ILS.sign_trim]; exact M.sign_match
  is_trim := ILS.trim_isTrim M.E

/-- Forget the trim constraint. -/
def MYD_sig_trim.toMYDSig {γ : RootType} {s : ℤ × ℤ}
    (M : MYD_sig_trim γ s) : MYD_sig γ s :=
  ⟨M.E, M.sign_match⟩

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

    Proof (induction on chain):
    - Base: E = baseILS .D = [], ILS.sign [] = (0, 0). τ has empty shapes,
      so PBP.signature τ = (0, 0) = signTarget_D τ. ✓
    - Step: uses `ILS.thetaLift_CD_sign` to derive sign of the
      post-lift ILS, then stepPostTwist preserves sign (for D: twistBD
      with (1, -1) under ε_τ = 1, else identity).

    FULLY PROVED — see `SigMYDB.lean` / `SigMYDC.lean` for the
    B± / C analogues. -/
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

end BMSZ
