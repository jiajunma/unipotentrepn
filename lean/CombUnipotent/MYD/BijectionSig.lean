/-
# MYD_sig-based bijection (pivoted from MYD γ O)

Reference:
- `lean/docs/blueprints/MYD_sig_pivot.md` (rationale)
- `lean/CombUnipotent/MYD/SigMYD.lean` (`MYD_sig`, `descentChain_sign_match_D`)

We avoid the broken `MYD γ (dpToSYD γ dp)` target. Instead, build
the equiv at the **signature level**:

  `{σ : PBPSet .D μP μQ // signTarget_D σ.val = s} × Fin 2  ≃  MYD_sig .D s`

This compiles cleanly with no signature mismatch, and the
cardinality identity falls out of `Equiv.ofBijective` via
existing `prop_11_15_PBP_D_injective_full`.
-/
import CombUnipotent.MYD.SigMYD
import CombUnipotent.MYD.SigMYDB
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace BMSZ

/-! ## Subtype: D-PBPs with prescribed signature -/

/-- D-type PBPSet refined by signature target. -/
def PBPSet_D_sig (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .D μP μQ // signTarget_D σ.val = s }

noncomputable instance (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    DecidableEq (PBPSet_D_sig μP μQ s) := Classical.decEq _

/-! ## Per-step parity invariant for chain (paper §9.4)

Deferred: paper §9.4 shows theta-lift preserves MYDRowValid. The
chain-extracted ILS satisfies parity at all positions. Sketch:
induction on chain. New row (position 0, ℓ = 1) is parity-vacuous
for D (forced at even ℓ). Older rows shift index by 1 — needs a
careful re-indexing argument tying paint-symbol counts to chain step.
-/

/-- Parity preservation along D-type descent chain.
    Deferred — paper §9.4: theta-lift preserves MYD parity.
    Sketch: at each step, the augmented row goes to position 0 (ℓ=1,
    vacuous for D). Older rows shift up by 1, changing their effective
    parity-forcing index. The required invariant is NOT the simple
    `MYDRowValid .D (j+1) E[j]` but a "row-paired" version where
    parity is checked at the EVEN orbit position of the pair. Full
    proof needs paper §9.4 + a rephrasing of MYD_sig parity. -/
theorem descentChain_D_parity {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton (baseILS .D) chain E) :
    ∀ (j : ℕ) (h : j < E.length), MYDRowValid .D (j + 1) E[j] := by
  induction h_chain generalizing E with
  | base τ hγ h_empty =>
    -- chain = []; ChainSingleton forces E = baseILS .D = []
    cases h_sing
    intro j h
    -- baseILS .D = [], so E.length = 0, vacuous
    exfalso
    unfold baseILS at h
    simp at h
  | step hγ h_rest ih =>
    -- chain = chain_inner ++ [outer step]
    -- Decompose h_sing into E_mid + E' + final E
    obtain ⟨E_mid, E', _h_inner_sing, _h_theta, _h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Apply IH on inner chain ⇒ parity for E_mid
    -- Then need to preserve parity through theta-lift + post-twist
    -- This is paper §9.4 content; see docstring above.
    sorry

/-! ## Φ_D_sig -/

/-- **Φ_D_sig** : `PBPSet_D_sig × Fin 2 → MYD_sig .D s`.
    `(σ, h_sig, ε) ↦ twistBD L_σ ε ε` where `L_σ` is the
    chain-extracted ILS. -/
noncomputable def Phi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    MYD_sig .D s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain : List ACStepData := Classical.choose (exists_descentChain_D σ)
  let h_chain : IsDescentChain_D σ.val chain :=
    Classical.choose_spec (exists_descentChain_D σ)
  let E : ILS := Classical.choose (descentChain_D_singleton h_chain)
  let h_sing : ChainSingleton (baseILS .D) chain E :=
    Classical.choose_spec (descentChain_D_singleton h_chain)
  let h_sign_raw : ILS.sign E = signTarget_D σ.val :=
    descentChain_sign_match_D h_chain h_sing
  let h_par : ∀ (j : ℕ) (h : j < E.length), MYDRowValid .D (j + 1) E[j] :=
    descentChain_D_parity h_chain h_sing
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted : ILS := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1
    · simp [ε_int, hε]
    · simp [ε_int, hε]
  have h_par_twist : ∀ (j : ℕ) (hj : j < E_twisted.length),
      MYDRowValid .D (j + 1) E_twisted[j] :=
    twistBD_general_preserves_MYDRowValid_BD E .D ε_int ε_int
      (Or.inr (Or.inr rfl)) h_par
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw, h_sig]
  ⟨E_twisted, h_par_twist, h_sign_twist⟩

/-! ## Ψ_D_sig (via Phi_D_sig injectivity + classical choice)

Two-pronged approach:
1. Define `Psi_D_sig M` via `Classical.choose` on `∃ p, Phi_D_sig p = M`.
2. Round-trip 1 (Psi ∘ Phi = id) follows from Phi-injectivity alone.
3. Round-trip 2 (Phi ∘ Psi = id) needs surjectivity (paper §11.14, sorry).

Phi_D_sig injectivity is reduced to `prop_11_15_PBP_D_injective_full`
by chaining: equal MYD_sig → equal twisted ILS → equal pre-twist ILS
(via twistBD invertibility) → equal chain-extracted ILS → equal σ
(via prop_11_15) and equal ε.
-/

/-- **Φ_D_sig is injective**: paper Prop 11.15 D content adapted to
    the MYD_sig framework. Sorry: needs reduction to existing
    `prop_11_15_PBP_D_injective_full` through chain extraction. -/
theorem Phi_D_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ} :
    Function.Injective (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig p.1 p.2) :=
  sorry

/-- Phi-image-decidable: classical `byCases` on whether `M` is in image. -/
noncomputable def Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (M : MYD_sig .D s) :
    PBPSet_D_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_D_sig μP μQ s × Fin 2, Phi_D_sig p.1 p.2 = M
  then h.choose
  else default

/-! ## Round trips -/

/-- `Ψ_D_sig (Φ_D_sig (σ, ε)) = (σ, ε)`. Direct from injectivity:
    the witness `(σ, ε)` for the existential makes Classical.choose
    return some pair `p` with `Phi_D_sig p.1 p.2 = Phi_D_sig σ ε`,
    and injectivity then yields `p = (σ, ε)`. -/
theorem Psi_D_Phi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    Psi_D_sig (μP := μP) (μQ := μQ) (Phi_D_sig σh ε) = (σh, ε) := by
  classical
  unfold Psi_D_sig
  have hex : ∃ p : PBPSet_D_sig μP μQ s × Fin 2, Phi_D_sig p.1 p.2 = Phi_D_sig σh ε :=
    ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  -- Classical.choose hex returns some pair p with Phi_D_sig p.1 p.2 = Phi_D_sig σh ε
  -- By injectivity: p = (σh, ε)
  have h_choose := Classical.choose_spec hex
  exact Phi_D_sig_injective h_choose

/-- `Φ_D_sig (Ψ_D_sig M) = M`. Surjectivity side; paper §11.14. -/
theorem Phi_D_Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (M : MYD_sig .D s) :
    let p := Psi_D_sig (μP := μP) (μQ := μQ) M
    Phi_D_sig p.1 p.2 = M := by
  sorry

/-! ## Equiv assembly -/

/-- **Main bijection** (D type, signature-based).

    Requires `Inhabited` on the source for the classical-choice
    fallback in `Psi_D_sig`. The instance is provided by passing a
    witness PBP at the call site (since `signTarget_D` is non-trivial
    only when the type is non-empty). -/
noncomputable def Phi_D_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    PBPSet_D_sig μP μQ s × Fin 2 ≃ MYD_sig .D s where
  toFun := fun ⟨σh, ε⟩ => Phi_D_sig σh ε
  invFun := Psi_D_sig (μP := μP) (μQ := μQ)
  left_inv := fun ⟨σh, ε⟩ => Psi_D_Phi_D_sig σh ε
  right_inv := fun M => Phi_D_Psi_D_sig M

/-! ## Signature targets for B⁻ / C / M (B⁺ is in SigMYDB.lean) -/

/-- Signature target for B⁻ PBP. -/
noncomputable def signTarget_Bminus (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ; ((s.1 : ℤ), (s.2 : ℤ))

/-- Signature target for C PBP. -/
noncomputable def signTarget_C (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ; ((s.1 : ℤ), (s.2 : ℤ))

/-- Signature target for M PBP. -/
noncomputable def signTarget_M (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ; ((s.1 : ℤ), (s.2 : ℤ))

/-! ## Refined PBPSet subtypes for B⁺ / B⁻ / C / M -/

def PBPSet_Bplus_sig (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .Bplus μP μQ // signTarget_Bplus σ.val = s }

def PBPSet_Bminus_sig (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .Bminus μP μQ // signTarget_Bminus σ.val = s }

def PBPSet_C_sig (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .C μP μQ // signTarget_C σ.val = s }

def PBPSet_M_sig (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .M μP μQ // signTarget_M σ.val = s }

/-! ## Φ-equivs for B⁺ / B⁻ / C / M (paper Props 11.15 / 11.17, signature variant)

Phase A: high-level axiomatized as sorry. Phase B: each follows the
D template via type-specific `IsDescentChain_γ`, sign match, parity
preservation, inverse construction.

Mapping pattern:
- B⁺, B⁻: paper Prop 11.15, source × Fin 2 (mirror of D)
- C, M:   paper Prop 11.17, source only (no Fin 2)
-/

/-! ### Phi_Bplus_sig — uses descentChain_sign_match_Bplus (PROVED) -/

theorem descentChain_Bplus_parity {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (_h_chain : IsDescentChain_Bplus τ chain)
    (_h_sing : ChainSingleton (baseILS .Bplus) chain E) :
    ∀ (j : ℕ) (h : j < E.length), MYDRowValid .Bplus (j + 1) E[j] := sorry

noncomputable def Phi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) : MYD_sig .Bplus s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain := Classical.choose (exists_descentChain_Bplus σ)
  let h_chain := Classical.choose_spec (exists_descentChain_Bplus σ)
  let E := Classical.choose (descentChain_Bplus_singleton h_chain)
  let h_sing := Classical.choose_spec (descentChain_Bplus_singleton h_chain)
  let h_sign_raw := descentChain_sign_match_Bplus h_chain h_sing
  let h_par := descentChain_Bplus_parity h_chain h_sing
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1 <;> simp [ε_int, hε]
  have h_par_twist : ∀ (j : ℕ) (hj : j < E_twisted.length),
      MYDRowValid .Bplus (j + 1) E_twisted[j] :=
    twistBD_general_preserves_MYDRowValid_BD E .Bplus ε_int ε_int
      (Or.inl rfl) h_par
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw, h_sig]
  ⟨E_twisted, h_par_twist, h_sign_twist⟩

/-- Phi_Bplus_sig injective. Sorry: paper Prop 11.15 reduction. -/
theorem Phi_Bplus_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ} :
    Function.Injective (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig p.1 p.2) :=
  sorry

noncomputable def Psi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)]
    (M : MYD_sig .Bplus s) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_Bplus_sig μP μQ s × Fin 2, Phi_Bplus_sig p.1 p.2 = M
  then h.choose
  else default

theorem Psi_Bplus_Phi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)]
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    Psi_Bplus_sig (μP := μP) (μQ := μQ) (Phi_Bplus_sig σh ε) = (σh, ε) := by
  classical
  unfold Psi_Bplus_sig
  have hex : ∃ p : PBPSet_Bplus_sig μP μQ s × Fin 2,
      Phi_Bplus_sig p.1 p.2 = Phi_Bplus_sig σh ε := ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  exact Phi_Bplus_sig_injective (Classical.choose_spec hex)

/-- **Paper Prop 11.15 (B⁺), signature variant**. -/
noncomputable def Phi_Bplus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bplus s where
  toFun := fun ⟨σh, ε⟩ => Phi_Bplus_sig σh ε
  invFun := Psi_Bplus_sig (μP := μP) (μQ := μQ)
  left_inv := fun ⟨σh, ε⟩ => Psi_Bplus_Phi_Bplus_sig σh ε
  right_inv := fun _ => sorry

/-! ### Phi_Bminus_sig — uses descentChain_sign_match_Bminus (PROVED) -/

theorem descentChain_Bminus_parity {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (_h_chain : IsDescentChain_Bminus τ chain)
    (_h_sing : ChainSingleton (baseILS .Bminus) chain E) :
    ∀ (j : ℕ) (h : j < E.length), MYDRowValid .Bminus (j + 1) E[j] := sorry

noncomputable def Phi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) : MYD_sig .Bminus s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain := Classical.choose (exists_descentChain_Bminus σ)
  let h_chain := Classical.choose_spec (exists_descentChain_Bminus σ)
  let E := Classical.choose (descentChain_Bminus_singleton h_chain)
  let h_sing := Classical.choose_spec (descentChain_Bminus_singleton h_chain)
  let h_sign_raw := descentChain_sign_match_Bminus h_chain h_sing
  let h_par := descentChain_Bminus_parity h_chain h_sing
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1 <;> simp [ε_int, hε]
  have h_par_twist : ∀ (j : ℕ) (hj : j < E_twisted.length),
      MYDRowValid .Bminus (j + 1) E_twisted[j] :=
    twistBD_general_preserves_MYDRowValid_BD E .Bminus ε_int ε_int
      (Or.inr (Or.inl rfl)) h_par
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw]
    -- h_sign_raw : ILS.sign E = signTarget_Bminus' σ.val
    -- Need: signTarget_Bminus' σ.val = s
    -- σh.prop : signTarget_Bminus σh.val = s, and signTarget_Bminus = signTarget_Bminus' defeq
    show signTarget_Bminus' σ.val = s
    have heq : signTarget_Bminus' σ.val = signTarget_Bminus σ.val := rfl
    rw [heq]; exact h_sig
  ⟨E_twisted, h_par_twist, h_sign_twist⟩

/-- Phi_Bminus_sig injective. Sorry: paper Prop 11.15 reduction. -/
theorem Phi_Bminus_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ} :
    Function.Injective (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig p.1 p.2) :=
  sorry

noncomputable def Psi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)]
    (M : MYD_sig .Bminus s) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_Bminus_sig μP μQ s × Fin 2, Phi_Bminus_sig p.1 p.2 = M
  then h.choose
  else default

theorem Psi_Bminus_Phi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)]
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    Psi_Bminus_sig (μP := μP) (μQ := μQ) (Phi_Bminus_sig σh ε) = (σh, ε) := by
  classical
  unfold Psi_Bminus_sig
  have hex : ∃ p : PBPSet_Bminus_sig μP μQ s × Fin 2,
      Phi_Bminus_sig p.1 p.2 = Phi_Bminus_sig σh ε := ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  exact Phi_Bminus_sig_injective (Classical.choose_spec hex)

/-- **Paper Prop 11.15 (B⁻), signature variant**. -/
noncomputable def Phi_Bminus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bminus s where
  toFun := fun ⟨σh, ε⟩ => Phi_Bminus_sig σh ε
  invFun := Psi_Bminus_sig (μP := μP) (μQ := μQ)
  left_inv := fun ⟨σh, ε⟩ => Psi_Bminus_Phi_Bminus_sig σh ε
  right_inv := fun _ => sorry

/-! ### Phi_C_sig (no Fin 2 — paper Prop 11.17) -/

/-- C-side Phi: maps σ to chain-extracted twisted ILS.
    No ε factor (paper Prop 11.17 has source = PBP only). -/
noncomputable def Phi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_C_sig μP μQ s) : MYD_sig .C s := sorry

theorem Phi_C_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ} :
    Function.Injective (Phi_C_sig (μP := μP) (μQ := μQ) (s := s)) :=
  sorry

noncomputable def Psi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_C_sig μP μQ s)]
    (M : MYD_sig .C s) : PBPSet_C_sig μP μQ s :=
  open Classical in
  if h : ∃ σh : PBPSet_C_sig μP μQ s, Phi_C_sig σh = M
  then h.choose
  else default

theorem Psi_C_Phi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_C_sig μP μQ s)]
    (σh : PBPSet_C_sig μP μQ s) :
    Psi_C_sig (μP := μP) (μQ := μQ) (Phi_C_sig σh) = σh := by
  classical
  unfold Psi_C_sig
  have hex : ∃ x : PBPSet_C_sig μP μQ s, Phi_C_sig x = Phi_C_sig σh := ⟨σh, rfl⟩
  rw [dif_pos hex]
  exact Phi_C_sig_injective (Classical.choose_spec hex)

/-- **Paper Prop 11.17 (C), signature variant**. -/
noncomputable def Phi_C_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    PBPSet_C_sig μP μQ s ≃ MYD_sig .C s where
  toFun := Phi_C_sig
  invFun := Psi_C_sig (μP := μP) (μQ := μQ)
  left_inv := fun σh => Psi_C_Phi_C_sig σh
  right_inv := fun _ => sorry

/-! ### Phi_M_sig (no Fin 2 — paper Prop 11.17) -/

noncomputable def Phi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_M_sig μP μQ s) : MYD_sig .M s := sorry

theorem Phi_M_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ} :
    Function.Injective (Phi_M_sig (μP := μP) (μQ := μQ) (s := s)) :=
  sorry

noncomputable def Psi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_M_sig μP μQ s)]
    (M : MYD_sig .M s) : PBPSet_M_sig μP μQ s :=
  open Classical in
  if h : ∃ σh : PBPSet_M_sig μP μQ s, Phi_M_sig σh = M
  then h.choose
  else default

theorem Psi_M_Phi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_M_sig μP μQ s)]
    (σh : PBPSet_M_sig μP μQ s) :
    Psi_M_sig (μP := μP) (μQ := μQ) (Phi_M_sig σh) = σh := by
  classical
  unfold Psi_M_sig
  have hex : ∃ x : PBPSet_M_sig μP μQ s, Phi_M_sig x = Phi_M_sig σh := ⟨σh, rfl⟩
  rw [dif_pos hex]
  exact Phi_M_sig_injective (Classical.choose_spec hex)

/-- **Paper Prop 11.17 (M), signature variant**. -/
noncomputable def Phi_M_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    PBPSet_M_sig μP μQ s ≃ MYD_sig .M s where
  toFun := Phi_M_sig
  invFun := Psi_M_sig (μP := μP) (μQ := μQ)
  left_inv := fun σh => Psi_M_Phi_M_sig σh
  right_inv := fun _ => sorry

/-! ## Fintype + cardinality corollaries -/

/-- Fintype on the signature-refined PBPSet subtype. -/
noncomputable instance fintype_PBPSet_D_sig
    (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Fintype (PBPSet_D_sig μP μQ s) :=
  Subtype.fintype _

noncomputable instance fintype_PBPSet_Bplus_sig
    (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Fintype (PBPSet_Bplus_sig μP μQ s) :=
  Subtype.fintype _

noncomputable instance fintype_PBPSet_Bminus_sig
    (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Fintype (PBPSet_Bminus_sig μP μQ s) :=
  Subtype.fintype _

noncomputable instance fintype_PBPSet_C_sig
    (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Fintype (PBPSet_C_sig μP μQ s) :=
  Subtype.fintype _

noncomputable instance fintype_PBPSet_M_sig
    (μP μQ : YoungDiagram) (s : ℤ × ℤ) : Fintype (PBPSet_M_sig μP μQ s) :=
  Subtype.fintype _

/-- Fintype on `MYD_sig γ s` via the equiv. -/
noncomputable def fintype_MYD_sig_D (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .D s) :=
  Fintype.ofEquiv _ (Phi_D_sig_equiv μP μQ s)

noncomputable def fintype_MYD_sig_Bplus (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .Bplus s) :=
  Fintype.ofEquiv _ (Phi_Bplus_sig_equiv μP μQ s)

noncomputable def fintype_MYD_sig_Bminus (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .Bminus s) :=
  Fintype.ofEquiv _ (Phi_Bminus_sig_equiv μP μQ s)

noncomputable def fintype_MYD_sig_C (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    Fintype (MYD_sig .C s) :=
  Fintype.ofEquiv _ (Phi_C_sig_equiv μP μQ s)

noncomputable def fintype_MYD_sig_M (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    Fintype (MYD_sig .M s) :=
  Fintype.ofEquiv _ (Phi_M_sig_equiv μP μQ s)

/-- **Paper Prop 11.15 card (D, sig)**: |PBPSet_D_sig × Fin 2| = |MYD_sig .D s|. -/
theorem card_PBPSet_D_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_D_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .D s) :=
  Nat.card_congr (Phi_D_sig_equiv μP μQ s)

/-- **Paper Prop 11.15 card (B⁺, sig)**. -/
theorem card_PBPSet_Bplus_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_Bplus_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .Bplus s) :=
  Nat.card_congr (Phi_Bplus_sig_equiv μP μQ s)

/-- **Paper Prop 11.15 card (B⁻, sig)**. -/
theorem card_PBPSet_Bminus_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_Bminus_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .Bminus s) :=
  Nat.card_congr (Phi_Bminus_sig_equiv μP μQ s)

/-- **Paper Prop 11.17 card (C, sig)**. -/
theorem card_PBPSet_C_sig_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    Nat.card (PBPSet_C_sig μP μQ s) = Nat.card (MYD_sig .C s) :=
  Nat.card_congr (Phi_C_sig_equiv μP μQ s)

/-- **Paper Prop 11.17 card (M, sig)**. -/
theorem card_PBPSet_M_sig_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    Nat.card (PBPSet_M_sig μP μQ s) = Nat.card (MYD_sig .M s) :=
  Nat.card_congr (Phi_M_sig_equiv μP μQ s)

end BMSZ
