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

/-! ### Trim preservation under natAbs-preserving list-index maps -/

/-- A pair is nonzero iff at least one component has nonzero natAbs. -/
theorem pair_ne_zero_iff (a : ℤ × ℤ) :
    a ≠ (0, 0) ↔ a.1.natAbs ≠ 0 ∨ a.2.natAbs ≠ 0 := by
  constructor
  · intro h
    by_contra h_and
    push_neg at h_and
    apply h
    ext
    · exact Int.natAbs_eq_zero.mp h_and.1
    · exact Int.natAbs_eq_zero.mp h_and.2
  · intro h h_eq
    subst h_eq
    simp at h

/-- A natAbs-preserving row map sends nonzero rows to nonzero rows. -/
theorem pair_ne_zero_of_natAbs_preserve {a b : ℤ × ℤ}
    (h_eq : a.1.natAbs = b.1.natAbs ∧ a.2.natAbs = b.2.natAbs)
    (h_ne : a ≠ (0, 0)) : b ≠ (0, 0) := by
  rw [pair_ne_zero_iff] at h_ne ⊢
  rcases h_ne with h | h
  · left; rw [← h_eq.1]; exact h
  · right; rw [← h_eq.2]; exact h

/-- `charTwistCM` preserves trim status (uses natAbs-preservation). -/
theorem charTwistCM_IsTrim (E : ILS) (j : ℤ) (h : IsTrim E) :
    IsTrim (charTwistCM E j) := by
  unfold charTwistCM
  induction E using List.reverseRecOn with
  | nil => unfold IsTrim; simp
  | append_singleton xs a _ih =>
    rw [List.mapIdx_append]
    simp only [List.mapIdx_cons, List.mapIdx_nil]
    -- Now goal is IsTrim (xs.mapIdx ... ++ [charTwistCMRow j xs.length a])
    have h_last : a ≠ (0, 0) := by
      unfold IsTrim at h
      simp at h
      exact h
    have h_na := charTwistCMRow_natAbs j xs.length a
    have h_twist_ne : charTwistCMRow j xs.length a ≠ (0, 0) :=
      pair_ne_zero_of_natAbs_preserve ⟨h_na.1.symm, h_na.2.symm⟩ h_last
    unfold IsTrim
    simp
    exact h_twist_ne

/-- `twistBD` preserves trim status (tp, tn ∈ {1, -1}). -/
theorem twistBD_IsTrim (E : ILS) (tp tn : ℤ)
    (htp : tp = 1 ∨ tp = -1) (htn : tn = 1 ∨ tn = -1) (h : IsTrim E) :
    IsTrim (twistBD E tp tn) := by
  unfold twistBD
  induction E using List.reverseRecOn with
  | nil => unfold IsTrim; simp
  | append_singleton xs a _ih =>
    rw [List.mapIdx_append]
    simp only [List.mapIdx_cons, List.mapIdx_nil]
    have h_last : a ≠ (0, 0) := by
      unfold IsTrim at h
      simp at h
      exact h
    have h_na := twistBDRow_natAbs xs.length tp tn a htp htn
    have h_twist_ne : twistBDRow xs.length tp tn a ≠ (0, 0) :=
      pair_ne_zero_of_natAbs_preserve ⟨h_na.1.symm, h_na.2.symm⟩ h_last
    unfold IsTrim
    simp
    exact h_twist_ne

/-- Augment with a nonzero row: if E' = (addp, addn) :: E and (addp, addn) ≠ (0, 0)
    OR E is trim and nonempty, then E' is trim. -/
theorem augment_IsTrim (E : ILS) (pq : ℤ × ℤ)
    (h : (E = [] ∧ pq ≠ (0, 0)) ∨ (E ≠ [] ∧ IsTrim E)) :
    IsTrim (augment pq E) := by
  unfold augment
  unfold IsTrim
  rcases h with ⟨h_nil, h_ne⟩ | ⟨h_ne, h_trim⟩
  · subst h_nil
    simp
    exact h_ne
  · match E, h_ne, h_trim with
    | q :: rest, _, ht =>
      simp only [List.getLast?_cons]
      unfold IsTrim at ht
      simp only [List.getLast?_cons] at ht
      exact ht

/-- For trim ILS, `trim` is the identity. -/
theorem trim_eq_self_of_IsTrim (E : ILS) (h : IsTrim E) : trim E = E := by
  induction E using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs a _ih =>
    unfold trim IsTrim at *
    by_cases ha : a = (0, 0)
    · subst ha
      simp at h
    · simp [List.reverse_append, ha]

/-- `signRow i pq` produces non-negative components. -/
theorem signRow_fst_nonneg (i : ℕ) (pq : ℤ × ℤ) : 0 ≤ (signRow i pq).1 := by
  show 0 ≤ pq.1.natAbs * (((i : ℤ) + 1) / 2 + ((i : ℤ) + 1) % 2)
            + pq.2.natAbs * (((i : ℤ) + 1) / 2)
  have h1 : 0 ≤ ((i : ℤ) + 1) / 2 :=
    Int.ediv_nonneg (by omega) (by norm_num)
  have h2 : 0 ≤ ((i : ℤ) + 1) % 2 := Int.emod_nonneg _ (by norm_num)
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.add_nonneg h1 h2))
    (Int.mul_nonneg (Int.ofNat_nonneg _) h1)

theorem signRow_snd_nonneg (i : ℕ) (pq : ℤ × ℤ) : 0 ≤ (signRow i pq).2 := by
  show 0 ≤ pq.2.natAbs * (((i : ℤ) + 1) / 2 + ((i : ℤ) + 1) % 2)
            + pq.1.natAbs * (((i : ℤ) + 1) / 2)
  have h1 : 0 ≤ ((i : ℤ) + 1) / 2 :=
    Int.ediv_nonneg (by omega) (by norm_num)
  have h2 : 0 ≤ ((i : ℤ) + 1) % 2 := Int.emod_nonneg _ (by norm_num)
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.add_nonneg h1 h2))
    (Int.mul_nonneg (Int.ofNat_nonneg _) h1)

/-- The sign of any ILS has non-negative first component. -/
theorem sign_fst_nonneg (E : ILS) : 0 ≤ (sign E).1 := by
  unfold sign
  -- foldl over zipIdx, accumulator (0, 0), updates with signRow components.
  -- Generalize the accumulator to any non-negative one.
  suffices h : ∀ (acc : ℤ × ℤ), 0 ≤ acc.1 →
      0 ≤ ((E.zipIdx).foldl
        (fun acc ⟨pq, i⟩ => let s := signRow i pq; (acc.1 + s.1, acc.2 + s.2)) acc).1 by
    exact h (0, 0) (le_refl 0)
  intro acc h_acc
  induction E.zipIdx generalizing acc with
  | nil => exact h_acc
  | cons hd tl ih =>
    apply ih
    simp only
    exact Int.add_nonneg h_acc (signRow_fst_nonneg hd.2 hd.1)

/-- The sign of any ILS has non-negative second component. -/
theorem sign_snd_nonneg (E : ILS) : 0 ≤ (sign E).2 := by
  unfold sign
  suffices h : ∀ (acc : ℤ × ℤ), 0 ≤ acc.2 →
      0 ≤ ((E.zipIdx).foldl
        (fun acc ⟨pq, i⟩ => let s := signRow i pq; (acc.1 + s.1, acc.2 + s.2)) acc).2 by
    exact h (0, 0) (le_refl 0)
  intro acc h_acc
  induction E.zipIdx generalizing acc with
  | nil => exact h_acc
  | cons hd tl ih =>
    apply ih
    simp only
    exact Int.add_nonneg h_acc (signRow_snd_nonneg hd.2 hd.1)

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

/-- Negative-component signatures yield empty `MYD_sig`. -/
theorem MYD_sig_empty_of_sign_neg_fst {γ : RootType} {s : ℤ × ℤ}
    (h : s.1 < 0) : IsEmpty (MYD_sig γ s) := by
  refine ⟨fun M => ?_⟩
  have h_nn := ILS.sign_fst_nonneg M.E
  rw [M.sign_match] at h_nn
  omega

theorem MYD_sig_empty_of_sign_neg_snd {γ : RootType} {s : ℤ × ℤ}
    (h : s.2 < 0) : IsEmpty (MYD_sig γ s) := by
  refine ⟨fun M => ?_⟩
  have h_nn := ILS.sign_snd_nonneg M.E
  rw [M.sign_match] at h_nn
  omega

/-- Same for `MYD_sig_trim`. -/
theorem MYD_sig_trim_empty_of_sign_neg_fst {γ : RootType} {s : ℤ × ℤ}
    (h : s.1 < 0) : IsEmpty (MYD_sig_trim γ s) := by
  refine ⟨fun M => ?_⟩
  have h_nn := ILS.sign_fst_nonneg M.E
  rw [M.sign_match] at h_nn
  omega

theorem MYD_sig_trim_empty_of_sign_neg_snd {γ : RootType} {s : ℤ × ℤ}
    (h : s.2 < 0) : IsEmpty (MYD_sig_trim γ s) := by
  refine ⟨fun M => ?_⟩
  have h_nn := ILS.sign_snd_nonneg M.E
  rw [M.sign_match] at h_nn
  omega

/-- `Fintype (MYD_sig_trim γ s)` when s has negative first component. -/
noncomputable instance fintype_MYD_sig_trim_neg_fst {γ : RootType} {s : ℤ × ℤ}
    (h : s.1 < 0) : Fintype (MYD_sig_trim γ s) :=
  @Fintype.ofIsEmpty _ (MYD_sig_trim_empty_of_sign_neg_fst h)

/-- `Fintype (MYD_sig_trim γ s)` when s has negative second component. -/
noncomputable instance fintype_MYD_sig_trim_neg_snd {γ : RootType} {s : ℤ × ℤ}
    (h : s.2 < 0) : Fintype (MYD_sig_trim γ s) :=
  @Fintype.ofIsEmpty _ (MYD_sig_trim_empty_of_sign_neg_snd h)


/-- Forget the trim constraint. -/
def MYD_sig_trim.toMYDSig {γ : RootType} {s : ℤ × ℤ}
    (M : MYD_sig_trim γ s) : MYD_sig γ s :=
  ⟨M.E, M.sign_match⟩

/-- The trim canonical form of a MYD_sig_trim is itself (E-level). -/
theorem toTrim_of_MYD_sig_trim_toMYDSig {γ : RootType} {s : ℤ × ℤ}
    (M : MYD_sig_trim γ s) :
    (MYD_sig.toTrim (MYD_sig_trim.toMYDSig M)).E = M.E := by
  unfold MYD_sig.toTrim MYD_sig_trim.toMYDSig
  simp only
  exact ILS.trim_eq_self_of_IsTrim _ M.is_trim

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

/-! ## Chain trim under per-step trim hypothesis

Given a hypothesis that per-step thetaLift preserves trim status,
the chain-extracted ILS is trim. This lets us turn `Phi_γ_sig` into
a function targeting the finite `MYD_sig_trim` type.

The per-step trim hypothesis is paper content — a variant of paper
§11.5/§11.6's claim that chain-step thetaLift produces "canonical"
augmented ILSs. All three trim-preservation building blocks
(charTwistCM_IsTrim, twistBD_IsTrim, augment_IsTrim) are PROVED.
-/

/-- **Per-step trim preservation hypothesis**. Abstracts paper content
    about chain-step thetaLift producing trim ILSs. -/
abbrev StepPreservesTrim : Prop :=
  ∀ (E : ILS) (d : ACStepData) (E' : ILS),
    ILS.IsTrim E →
    ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E'] →
    ILS.IsTrim (stepPostTwist E' d)

/-- **Chain trim**: given per-step trim preservation + trim initial ILS,
    the final chain-extracted ILS is trim. -/
theorem chainSingleton_IsTrim {chain : List ACStepData} {E_init E_final : ILS}
    (h_step_trim : StepPreservesTrim)
    (h_init : ILS.IsTrim E_init)
    (h : ChainSingleton E_init chain E_final) :
    ILS.IsTrim E_final := by
  induction h with
  | nil _ => exact h_init
  | cons E' h_theta _h_rest ih =>
    rename_i E d _rest _E_final
    apply ih
    exact h_step_trim E d E' h_init h_theta

/-- `baseILS γ` is always trim. -/
theorem baseILS_IsTrim (γ : RootType) : ILS.IsTrim (baseILS γ) := by
  cases γ <;> (unfold baseILS ILS.IsTrim; simp)

/-- Helper: `augment pq E` is trim when either nonempty trim E or
    empty E with nonzero pq. -/
theorem augment_is_trim_of_cases {E : ILS} {pq : ℤ × ℤ}
    (h_trim : ILS.IsTrim E)
    (h_ne : E = [] → pq ≠ (0, 0)) :
    ILS.IsTrim (ILS.augment pq E) := by
  by_cases hE : E = []
  · exact ILS.augment_IsTrim E pq (Or.inl ⟨hE, h_ne hE⟩)
  · exact ILS.augment_IsTrim E pq (Or.inr ⟨hE, h_trim⟩)

/-- **Step-trim preservation (std case, target .D)** for `thetaLift_CD`. -/
theorem thetaLift_CD_preserves_trim_std
    (E : ILS) (p q : ℤ)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      q - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       q - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift_CD E p q = [E']) :
    ILS.IsTrim E' := by
  simp only [ILS.thetaLift_CD, if_pos h_std] at h_tl
  simp at h_tl
  subst h_tl
  exact augment_is_trim_of_cases (ILS.charTwistCM_IsTrim _ _ h_trim)
    (by
      intro hE
      unfold ILS.charTwistCM at hE
      rw [List.mapIdx_eq_nil_iff] at hE
      exact h_ne_augment hE)

/-- **Step-trim preservation (std case, target .C)** for `thetaLift_DC`. -/
theorem thetaLift_DC_preserves_trim_std
    (E : ILS) (n : ℤ)
    (h_std :
      n - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      n - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
       n - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift_DC E n = [E']) :
    ILS.IsTrim E' := by
  simp only [ILS.thetaLift_DC, if_pos h_std] at h_tl
  simp at h_tl
  subst h_tl
  apply ILS.charTwistCM_IsTrim
  exact augment_is_trim_of_cases h_trim h_ne_augment

/-- **Step-trim preservation (std case, target .M)** for `thetaLift_BM`. -/
theorem thetaLift_BM_preserves_trim_std
    (E : ILS) (n : ℤ)
    (h_std :
      n - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      n - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
       n - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift_BM E n = [E']) :
    ILS.IsTrim E' := by
  simp only [ILS.thetaLift_BM, if_pos h_std] at h_tl
  simp at h_tl
  subst h_tl
  apply ILS.charTwistCM_IsTrim
  exact augment_is_trim_of_cases h_trim h_ne_augment

/-- **Step-trim preservation (std case, target .Bplus/.Bminus)** for
    `thetaLift_MB`. (augment wraps charTwistCM, like thetaLift_CD) -/
theorem thetaLift_MB_preserves_trim_std
    (E : ILS) (p q : ℤ)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      q - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       q - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift_MB E p q = [E']) :
    ILS.IsTrim E' := by
  simp only [ILS.thetaLift_MB, if_pos h_std] at h_tl
  simp at h_tl
  subst h_tl
  exact augment_is_trim_of_cases (ILS.charTwistCM_IsTrim _ _ h_trim)
    (by
      intro hE
      unfold ILS.charTwistCM at hE
      rw [List.mapIdx_eq_nil_iff] at hE
      exact h_ne_augment hE)

/-- **Dispatched thetaLift trim preservation (std case)** for D/B targets.

    Covers targets where the std condition uses (p, q) meaningfully.
    For C/M targets (where `thetaLift` ignores q and uses p-only std),
    use `thetaLift_preserves_trim_std_CM`. -/
theorem thetaLift_preserves_trim_std_DB
    (E : ILS) (γ : RootType) (p q : ℤ)
    (hγ : γ = .D ∨ γ = .Bplus ∨ γ = .Bminus)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      q - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       q - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift E γ p q = [E']) :
    ILS.IsTrim E' := by
  unfold ILS.thetaLift at h_tl
  rcases hγ with rfl | rfl | rfl
  · exact thetaLift_CD_preserves_trim_std E p q h_std h_ne_augment h_trim h_tl
  · exact thetaLift_MB_preserves_trim_std E p q h_std h_ne_augment h_trim h_tl
  · exact thetaLift_MB_preserves_trim_std E p q h_std h_ne_augment h_trim h_tl

/-- **Dispatched thetaLift trim preservation (std case)** for C/M targets.

    `thetaLift E .C p q` = `thetaLift_DC E p` (ignores q)
    `thetaLift E .M p q` = `thetaLift_BM E p` (ignores q)

    Std condition uses p for both coordinates. -/
theorem thetaLift_preserves_trim_std_CM
    (E : ILS) (γ : RootType) (p q : ℤ)
    (hγ : γ = .C ∨ γ = .M)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      p - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       p - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift E γ p q = [E']) :
    ILS.IsTrim E' := by
  unfold ILS.thetaLift at h_tl
  rcases hγ with rfl | rfl
  · exact thetaLift_DC_preserves_trim_std E p h_std h_ne_augment h_trim h_tl
  · exact thetaLift_BM_preserves_trim_std E p h_std h_ne_augment h_trim h_tl

/-! ### Combined step theorems (singleton + trim + sign) -/

/-- **Complete step (std, target .D)**: thetaLift_CD produces a singleton
    with trim + sign = (p, q). -/
theorem thetaLift_CD_step_complete_std
    (E : ILS) (p q : ℤ)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      q - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       q - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) :
    ∃ E' : ILS, ILS.thetaLift_CD E p q = [E'] ∧
      ILS.IsTrim E' ∧ ILS.sign E' = (p, q) := by
  refine ⟨ILS.augment
    (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
     q - (ILS.sign E).2 - (ILS.firstColSign E).1)
    (ILS.charTwistCM E ((p - q) / 2)), ?_, ?_, ?_⟩
  · simp only [ILS.thetaLift_CD, if_pos h_std]
  · apply augment_is_trim_of_cases (ILS.charTwistCM_IsTrim _ _ h_trim)
    intro hE
    unfold ILS.charTwistCM at hE
    rw [List.mapIdx_eq_nil_iff] at hE
    exact h_ne_augment hE
  · apply ILS.thetaLift_CD_sign E p q
    simp only [ILS.thetaLift_CD, if_pos h_std]
    exact List.mem_singleton.mpr rfl

/-- **Complete step (std, target .C)**: thetaLift_DC produces singleton
    with trim + sign = (n, n). -/
theorem thetaLift_DC_step_complete_std
    (E : ILS) (n : ℤ)
    (h_std :
      n - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      n - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
       n - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) :
    ∃ E' : ILS, ILS.thetaLift_DC E n = [E'] ∧
      ILS.IsTrim E' ∧ ILS.sign E' = (n, n) := by
  refine ⟨ILS.charTwistCM (ILS.augment
    (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
     n - (ILS.sign E).2 - (ILS.firstColSign E).1) E)
    (((ILS.sign E).1 - (ILS.sign E).2) / 2), ?_, ?_, ?_⟩
  · simp only [ILS.thetaLift_DC, if_pos h_std]
  · apply ILS.charTwistCM_IsTrim
    exact augment_is_trim_of_cases h_trim h_ne_augment
  · apply ILS.thetaLift_DC_sign_std E n h_std
    simp only [ILS.thetaLift_DC, if_pos h_std]
    exact List.mem_singleton.mpr rfl

/-- **Complete step (std, target .M)**: thetaLift_BM produces singleton
    with trim + sign = (n, n). -/
theorem thetaLift_BM_step_complete_std
    (E : ILS) (n : ℤ)
    (h_std :
      n - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      n - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
       n - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) :
    ∃ E' : ILS, ILS.thetaLift_BM E n = [E'] ∧
      ILS.IsTrim E' ∧ ILS.sign E' = (n, n) := by
  refine ⟨ILS.charTwistCM (ILS.augment
    (n - (ILS.sign E).1 - (ILS.firstColSign E).2,
     n - (ILS.sign E).2 - (ILS.firstColSign E).1) E)
    (((ILS.sign E).1 - (ILS.sign E).2 - 1) / 2), ?_, ?_, ?_⟩
  · simp only [ILS.thetaLift_BM, if_pos h_std]
  · apply ILS.charTwistCM_IsTrim
    exact augment_is_trim_of_cases h_trim h_ne_augment
  · apply ILS.thetaLift_BM_sign_std E n h_std
    simp only [ILS.thetaLift_BM, if_pos h_std]
    exact List.mem_singleton.mpr rfl

/-- **Complete step (std, target .Bplus/.Bminus)**: thetaLift_MB produces
    singleton with trim + sign = (p, q). -/
theorem thetaLift_MB_step_complete_std
    (E : ILS) (p q : ℤ)
    (h_std :
      p - (ILS.sign E).1 - (ILS.firstColSign E).2 ≥ 0 ∧
      q - (ILS.sign E).2 - (ILS.firstColSign E).1 ≥ 0)
    (h_ne_augment : E = [] →
      (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
       q - (ILS.sign E).2 - (ILS.firstColSign E).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) :
    ∃ E' : ILS, ILS.thetaLift_MB E p q = [E'] ∧
      ILS.IsTrim E' ∧ ILS.sign E' = (p, q) := by
  refine ⟨ILS.augment
    (p - (ILS.sign E).1 - (ILS.firstColSign E).2,
     q - (ILS.sign E).2 - (ILS.firstColSign E).1)
    (ILS.charTwistCM E ((p - q + 1) / 2)), ?_, ?_, ?_⟩
  · simp only [ILS.thetaLift_MB, if_pos h_std]
  · apply augment_is_trim_of_cases (ILS.charTwistCM_IsTrim _ _ h_trim)
    intro hE
    unfold ILS.charTwistCM at hE
    rw [List.mapIdx_eq_nil_iff] at hE
    exact h_ne_augment hE
  · apply ILS.thetaLift_MB_sign E p q
    simp only [ILS.thetaLift_MB, if_pos h_std]
    exact List.mem_singleton.mpr rfl

/-! ### Per-step trim preservation including stepPostTwist

These combine thetaLift trim preservation with stepPostTwist's trim
preservation (which uses `twistBD_IsTrim`). -/

/-- `stepPostTwist E' d` preserves trim. -/
theorem stepPostTwist_IsTrim (E' : ILS) (d : ACStepData)
    (h_trim : ILS.IsTrim E') :
    ILS.IsTrim (stepPostTwist E' d) := by
  unfold stepPostTwist
  split_ifs with hcond
  · exact ILS.twistBD_IsTrim E' 1 (-1) (Or.inl rfl) (Or.inr rfl) h_trim
  · exact h_trim

/-- `stepPreTwist E d` preserves trim. -/
theorem stepPreTwist_IsTrim (E : ILS) (d : ACStepData)
    (h_trim : ILS.IsTrim E) :
    ILS.IsTrim (stepPreTwist E d) := by
  unfold stepPreTwist
  split_ifs with hcond hwp
  · exact ILS.twistBD_IsTrim E (-1) (-1) (Or.inr rfl) (Or.inr rfl) h_trim
  · exact h_trim
  · exact h_trim

/-- **Per-step trim preservation for D chain step**: given std + ne_augment
    on `stepPreTwist E d` and trim E, the post-twist output is trim. -/
theorem step_trim_D (E : ILS) (d : ACStepData) (hd : d.γ = .D)
    (h_std :
      d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
      d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0)
    (h_ne_augment : (stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E']) :
    ILS.IsTrim (stepPostTwist E' d) := by
  apply stepPostTwist_IsTrim
  rw [hd] at h_tl
  unfold ILS.thetaLift at h_tl
  exact thetaLift_CD_preserves_trim_std (stepPreTwist E d) d.p d.q
    h_std h_ne_augment (stepPreTwist_IsTrim E d h_trim) h_tl

/-- **Per-step trim preservation for Bplus chain step**. -/
theorem step_trim_Bplus (E : ILS) (d : ACStepData) (hd : d.γ = .Bplus)
    (h_std :
      d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
      d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0)
    (h_ne_augment : (stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E']) :
    ILS.IsTrim (stepPostTwist E' d) := by
  apply stepPostTwist_IsTrim
  rw [hd] at h_tl
  unfold ILS.thetaLift at h_tl
  exact thetaLift_MB_preserves_trim_std (stepPreTwist E d) d.p d.q
    h_std h_ne_augment (stepPreTwist_IsTrim E d h_trim) h_tl

/-- **Per-step trim preservation for Bminus chain step**. -/
theorem step_trim_Bminus (E : ILS) (d : ACStepData) (hd : d.γ = .Bminus)
    (h_std :
      d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
      d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0)
    (h_ne_augment : (stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E']) :
    ILS.IsTrim (stepPostTwist E' d) := by
  apply stepPostTwist_IsTrim
  rw [hd] at h_tl
  unfold ILS.thetaLift at h_tl
  exact thetaLift_MB_preserves_trim_std (stepPreTwist E d) d.p d.q
    h_std h_ne_augment (stepPreTwist_IsTrim E d h_trim) h_tl

/-- **Per-step trim preservation for C chain step** (uses p as n in DC). -/
theorem step_trim_C (E : ILS) (d : ACStepData) (hd : d.γ = .C)
    (h_std :
      d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
      d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0)
    (h_ne_augment : (stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E']) :
    ILS.IsTrim (stepPostTwist E' d) := by
  apply stepPostTwist_IsTrim
  rw [hd] at h_tl
  unfold ILS.thetaLift at h_tl
  exact thetaLift_DC_preserves_trim_std (stepPreTwist E d) d.p
    h_std h_ne_augment (stepPreTwist_IsTrim E d h_trim) h_tl

/-- Bundled per-step trim/std/ne_augment hypothesis for one chain
    step. Provides everything needed to invoke `step_trim_γ` for the
    matching γ. -/
abbrev StepStdAndAugment_D : Prop :=
  ∀ (E : ILS) (d : ACStepData), d.γ = .D →
    (d.p - (ILS.sign (stepPreTwist E d)).1 -
      (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
     d.q - (ILS.sign (stepPreTwist E d)).2 -
      (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0) ∧
    ((stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))

/-- Helper: chain trim with arbitrary initial ILS, for D-chain. -/
theorem chainSingleton_IsTrim_D_init (h_step_std : StepStdAndAugment_D)
    {τ : PBP} {chain : List ACStepData} {E_init E : ILS}
    (h_init : ILS.IsTrim E_init)
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton E_init chain E) :
    ILS.IsTrim E := by
  induction h_chain generalizing E with
  | base τ hγ h_empty =>
    cases h_sing
    exact h_init
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    have h_trim_mid := ih h_inner_sing
    have h_d_γ : (toACStepData_D τ_outer hγ).γ = .D := rfl
    have ⟨h_std, h_ne⟩ := h_step_std E_mid (toACStepData_D τ_outer hγ) h_d_γ
    have h_trim_step :=
      step_trim_D E_mid (toACStepData_D τ_outer hγ) h_d_γ h_std h_ne h_trim_mid h_theta
    rw [h_E_final]
    exact h_trim_step

/-- **Chain trim for D-chains** (direct induction on chain).

    Given the per-step std + ne_augment hypothesis, the chain-extracted
    ILS for any D-chain is trim. -/
theorem chainSingleton_IsTrim_D (h_step_std : StepStdAndAugment_D)
    {τ : PBP} {chain : List ACStepData} {E : ILS}
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton (baseILS .D) chain E) :
    ILS.IsTrim E :=
  chainSingleton_IsTrim_D_init h_step_std (baseILS_IsTrim .D) h_chain h_sing

/-- Bundled per-step std + ne_augment hypothesis for B+ chains.
    (Used in SigMYDB.lean for `chainSingleton_IsTrim_Bplus`.) -/
abbrev StepStdAndAugment_Bplus : Prop :=
  ∀ (E : ILS) (d : ACStepData), d.γ = .Bplus →
    (d.p - (ILS.sign (stepPreTwist E d)).1 -
      (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
     d.q - (ILS.sign (stepPreTwist E d)).2 -
      (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0) ∧
    ((stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))

abbrev StepStdAndAugment_Bminus : Prop :=
  ∀ (E : ILS) (d : ACStepData), d.γ = .Bminus →
    (d.p - (ILS.sign (stepPreTwist E d)).1 -
      (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
     d.q - (ILS.sign (stepPreTwist E d)).2 -
      (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0) ∧
    ((stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.q - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))

abbrev StepStdAndAugment_C : Prop :=
  ∀ (E : ILS) (d : ACStepData), d.γ = .C →
    (d.p - (ILS.sign (stepPreTwist E d)).1 -
      (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
     d.p - (ILS.sign (stepPreTwist E d)).2 -
      (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0) ∧
    ((stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))

abbrev StepStdAndAugment_M : Prop :=
  ∀ (E : ILS) (d : ACStepData), d.γ = .M →
    (d.p - (ILS.sign (stepPreTwist E d)).1 -
      (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
     d.p - (ILS.sign (stepPreTwist E d)).2 -
      (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0) ∧
    ((stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))

/-- **Per-step trim preservation for M chain step** (uses p as n in BM). -/
theorem step_trim_M (E : ILS) (d : ACStepData) (hd : d.γ = .M)
    (h_std :
      d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2 ≥ 0 ∧
      d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1 ≥ 0)
    (h_ne_augment : (stepPreTwist E d) = [] →
      (d.p - (ILS.sign (stepPreTwist E d)).1 -
        (ILS.firstColSign (stepPreTwist E d)).2,
       d.p - (ILS.sign (stepPreTwist E d)).2 -
        (ILS.firstColSign (stepPreTwist E d)).1) ≠ (0, 0))
    (h_trim : ILS.IsTrim E) {E' : ILS}
    (h_tl : ILS.thetaLift (stepPreTwist E d) d.γ d.p d.q = [E']) :
    ILS.IsTrim (stepPostTwist E' d) := by
  apply stepPostTwist_IsTrim
  rw [hd] at h_tl
  unfold ILS.thetaLift at h_tl
  exact thetaLift_BM_preserves_trim_std (stepPreTwist E d) d.p
    h_std h_ne_augment (stepPreTwist_IsTrim E d h_trim) h_tl

end BMSZ
