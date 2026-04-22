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
import CombUnipotent.MYD.SigMYDC
import CombUnipotent.MYD.SigMYDM
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

/-- **Φ_D_sig** : `PBPSet_D_sig × Fin 2 → MYD_sig .D s`.
    `(σ, h_sig, ε) ↦ twistBD L_σ ε ε` where `L_σ` is the
    chain-extracted ILS.
    `h_step` supplies the paper §11.5/§11.6 per-step singleton fact. -/
noncomputable def Phi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    MYD_sig .D s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain : List ACStepData := Classical.choose (exists_descentChain_D σ)
  let h_chain : IsDescentChain_D σ.val chain :=
    Classical.choose_spec (exists_descentChain_D σ)
  let E : ILS := Classical.choose (descentChain_D_singleton h_step h_chain)
  let h_sing : ChainSingleton (baseILS .D) chain E :=
    Classical.choose_spec (descentChain_D_singleton h_step h_chain)
  let h_sign_raw : ILS.sign E = signTarget_D σ.val :=
    descentChain_sign_match_D h_chain h_sing
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted : ILS := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1
    · simp [ε_int, hε]
    · simp [ε_int, hε]
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw, h_sig]
  ⟨E_twisted, h_sign_twist⟩

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

/-- Phi-image-decidable: classical `byCases` on whether `M` is in image. -/
noncomputable def Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (M : MYD_sig .D s) :
    PBPSet_D_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_D_sig μP μQ s × Fin 2, Phi_D_sig h_step p.1 p.2 = M
  then h.choose
  else default

/-! ## Round trips -/

/-- `Ψ_D_sig (Φ_D_sig (σ, ε)) = (σ, ε)` given injectivity hypothesis
    (paper Prop 11.15 D-type, provable under non-empty shape). -/
theorem Psi_D_Phi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    Psi_D_sig (μP := μP) (μQ := μQ) h_step (Phi_D_sig h_step σh ε) = (σh, ε) := by
  classical
  unfold Psi_D_sig
  have hex : ∃ p : PBPSet_D_sig μP μQ s × Fin 2,
      Phi_D_sig h_step p.1 p.2 = Phi_D_sig h_step σh ε :=
    ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  have h_choose := Classical.choose_spec hex
  exact h_inj h_choose

/-- `Φ_D_sig (Ψ_D_sig M) = M` given surjectivity. Paper §11.14 provides
    the surjectivity witness algorithmically. Here we accept it as
    hypothesis so the round-trip is provable. -/
theorem Phi_D_Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)]
    (h_step : DescentStepSingleton_D)
    (h_surj : Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    (M : MYD_sig .D s) :
    let p := Psi_D_sig (μP := μP) (μQ := μQ) h_step M
    Phi_D_sig h_step p.1 p.2 = M := by
  classical
  unfold Psi_D_sig
  have hex : ∃ p : PBPSet_D_sig μP μQ s × Fin 2, Phi_D_sig h_step p.1 p.2 = M :=
    h_surj M
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

/-! ## Equiv assembly -/

/-- **Main bijection** (D type, signature-based). Takes injectivity +
    surjectivity as hypotheses (paper Prop 11.15 + §11.14). -/
noncomputable def Phi_D_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    PBPSet_D_sig μP μQ s × Fin 2 ≃ MYD_sig .D s where
  toFun := fun ⟨σh, ε⟩ => Phi_D_sig h_step σh ε
  invFun := Psi_D_sig (μP := μP) (μQ := μQ) h_step
  left_inv := fun ⟨σh, ε⟩ => Psi_D_Phi_D_sig h_step h_inj σh ε
  right_inv := fun M => Phi_D_Psi_D_sig h_step h_surj M

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


noncomputable def Phi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) : MYD_sig .Bplus s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain := Classical.choose (exists_descentChain_Bplus σ)
  let h_chain := Classical.choose_spec (exists_descentChain_Bplus σ)
  let E := Classical.choose (descentChain_Bplus_singleton h_step h_chain)
  let h_sing := Classical.choose_spec (descentChain_Bplus_singleton h_step h_chain)
  let h_sign_raw := descentChain_sign_match_Bplus h_chain h_sing
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1 <;> simp [ε_int, hε]
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw, h_sig]
  ⟨E_twisted, h_sign_twist⟩

noncomputable def Psi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)]
    (M : MYD_sig .Bplus s) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_Bplus_sig μP μQ s × Fin 2, Phi_Bplus_sig h_step p.1 p.2 = M
  then h.choose
  else default

theorem Psi_Bplus_Phi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)]
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    Psi_Bplus_sig (μP := μP) (μQ := μQ) h_step
      (Phi_Bplus_sig h_step σh ε) = (σh, ε) := by
  classical
  unfold Psi_Bplus_sig
  have hex : ∃ p : PBPSet_Bplus_sig μP μQ s × Fin 2,
      Phi_Bplus_sig h_step p.1 p.2 = Phi_Bplus_sig h_step σh ε := ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  exact h_inj (Classical.choose_spec hex)

theorem Phi_Bplus_Psi_Bplus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)]
    (h_step : DescentStepSingleton_Bplus)
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    (M : MYD_sig .Bplus s) :
    let p := Psi_Bplus_sig (μP := μP) (μQ := μQ) h_step M
    Phi_Bplus_sig h_step p.1 p.2 = M := by
  classical
  unfold Psi_Bplus_sig
  have hex : ∃ p : PBPSet_Bplus_sig μP μQ s × Fin 2,
      Phi_Bplus_sig h_step p.1 p.2 = M := h_surj M
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

/-- **Paper Prop 11.15 (B⁺), signature variant**. -/
noncomputable def Phi_Bplus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bplus s where
  toFun := fun ⟨σh, ε⟩ => Phi_Bplus_sig h_step σh ε
  invFun := Psi_Bplus_sig (μP := μP) (μQ := μQ) h_step
  left_inv := fun ⟨σh, ε⟩ => Psi_Bplus_Phi_Bplus_sig h_step h_inj σh ε
  right_inv := fun M => Phi_Bplus_Psi_Bplus_sig h_step h_surj M

/-! ### Phi_Bminus_sig — uses descentChain_sign_match_Bminus (PROVED) -/


noncomputable def Phi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) : MYD_sig .Bminus s :=
  let σ := σh.val
  let h_sig := σh.prop
  let chain := Classical.choose (exists_descentChain_Bminus σ)
  let h_chain := Classical.choose_spec (exists_descentChain_Bminus σ)
  let E := Classical.choose (h_sing h_chain)
  let h_sing' := Classical.choose_spec (h_sing h_chain)
  let h_sign_raw := descentChain_sign_match_Bminus h_chain h_sing'
  let ε_int : ℤ := if ε = 1 then -1 else 1
  let E_twisted := ILS.twistBD E ε_int ε_int
  have hε_signed : ε_int = 1 ∨ ε_int = -1 := by
    by_cases hε : ε = 1 <;> simp [ε_int, hε]
  have h_sign_twist : ILS.sign E_twisted = s := by
    show ILS.sign (ILS.twistBD E ε_int ε_int) = s
    rw [ILS.twistBD_sign E ε_int ε_int hε_signed hε_signed, h_sign_raw]
    show signTarget_Bminus' σ.val = s
    have heq : signTarget_Bminus' σ.val = signTarget_Bminus σ.val := rfl
    rw [heq]; exact h_sig
  ⟨E_twisted, h_sign_twist⟩

noncomputable def Psi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)]
    (M : MYD_sig .Bminus s) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 :=
  open Classical in
  if h : ∃ p : PBPSet_Bminus_sig μP μQ s × Fin 2, Phi_Bminus_sig h_sing p.1 p.2 = M
  then h.choose
  else default

theorem Psi_Bminus_Phi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)]
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    Psi_Bminus_sig (μP := μP) (μQ := μQ) h_sing
      (Phi_Bminus_sig h_sing σh ε) = (σh, ε) := by
  classical
  unfold Psi_Bminus_sig
  have hex : ∃ p : PBPSet_Bminus_sig μP μQ s × Fin 2,
      Phi_Bminus_sig h_sing p.1 p.2 = Phi_Bminus_sig h_sing σh ε := ⟨(σh, ε), rfl⟩
  rw [dif_pos hex]
  exact h_inj (Classical.choose_spec hex)

theorem Phi_Bminus_Psi_Bminus_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)]
    (h_sing : DescentChainBminusSingleton)
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    (M : MYD_sig .Bminus s) :
    let p := Psi_Bminus_sig (μP := μP) (μQ := μQ) h_sing M
    Phi_Bminus_sig h_sing p.1 p.2 = M := by
  classical
  unfold Psi_Bminus_sig
  have hex : ∃ p : PBPSet_Bminus_sig μP μQ s × Fin 2,
      Phi_Bminus_sig h_sing p.1 p.2 = M := h_surj M
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

/-- **Paper Prop 11.15 (B⁻), signature variant**. -/
noncomputable def Phi_Bminus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bminus s where
  toFun := fun ⟨σh, ε⟩ => Phi_Bminus_sig h_sing σh ε
  invFun := Psi_Bminus_sig (μP := μP) (μQ := μQ) h_sing
  left_inv := fun ⟨σh, ε⟩ => Psi_Bminus_Phi_Bminus_sig h_sing h_inj σh ε
  right_inv := fun M => Phi_Bminus_Psi_Bminus_sig h_sing h_surj M

/-! ### Phi_C_sig (no Fin 2 — paper Prop 11.17)

C type: chain step has γ = .C, no pre-twist unless ε_wp = 1 (which
requires PPSet). For the Phi function, we use the chain to extract E;
sign match is via `descentChain_sign_match_C` (base proved, step sorry'd
pending per-step std condition).

No ε_τ factor at the outermost level (Prop 11.17 has no Fin 2).
-/


/-- C-side Phi: maps σ to chain-extracted ILS. No outer ε twist.

    Hypotheses:
    - `h_step_D` (inner D chain singleton), `h_step_C` (C chain singleton)
    - `h_chain` (chain existence)
    - `h_sm` (sign match)  -/
noncomputable def Phi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (σh : PBPSet_C_sig μP μQ s) : MYD_sig .C s :=
  let σ := σh.val
  let h_sig := σh.prop
  let h_chain_σ := h_chain σ
  let chain := Classical.choose h_chain_σ
  let h_chain' := Classical.choose_spec h_chain_σ
  let E := Classical.choose (descentChain_C_singleton h_step_D h_step_C h_chain')
  let h_sing := Classical.choose_spec
    (descentChain_C_singleton h_step_D h_step_C h_chain')
  have h_sign : ILS.sign E = s := by
    rw [h_sm h_chain' h_sing]
    show signTarget_C' σ.val = s
    exact h_sig
  ⟨E, h_sign⟩

noncomputable def Psi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    [Inhabited (PBPSet_C_sig μP μQ s)]
    (M : MYD_sig .C s) : PBPSet_C_sig μP μQ s :=
  open Classical in
  if h : ∃ σh : PBPSet_C_sig μP μQ s,
      Phi_C_sig h_step_D h_step_C h_chain h_sm σh = M
  then h.choose
  else default

theorem Psi_C_Phi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_C_sig μP μQ s)]
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (σh : PBPSet_C_sig μP μQ s) :
    Psi_C_sig (μP := μP) (μQ := μQ) h_step_D h_step_C h_chain h_sm
      (Phi_C_sig h_step_D h_step_C h_chain h_sm σh) = σh := by
  classical
  unfold Psi_C_sig
  have hex : ∃ x : PBPSet_C_sig μP μQ s,
      Phi_C_sig h_step_D h_step_C h_chain h_sm x =
      Phi_C_sig h_step_D h_step_C h_chain h_sm σh := ⟨σh, rfl⟩
  rw [dif_pos hex]
  exact h_inj (Classical.choose_spec hex)

theorem Phi_C_Psi_C_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_C_sig μP μQ s)]
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_surj : Function.Surjective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (M : MYD_sig .C s) :
    Phi_C_sig h_step_D h_step_C h_chain h_sm
      (Psi_C_sig (μP := μP) (μQ := μQ) h_step_D h_step_C h_chain h_sm M) = M := by
  classical
  unfold Psi_C_sig
  have hex : ∃ σh : PBPSet_C_sig μP μQ s,
      Phi_C_sig h_step_D h_step_C h_chain h_sm σh = M := h_surj M
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

/-- **Paper Prop 11.17 (C), signature variant**. -/
noncomputable def Phi_C_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (h_surj : Function.Surjective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    PBPSet_C_sig μP μQ s ≃ MYD_sig .C s where
  toFun := Phi_C_sig h_step_D h_step_C h_chain h_sm
  invFun := Psi_C_sig (μP := μP) (μQ := μQ) h_step_D h_step_C h_chain h_sm
  left_inv := fun σh =>
    Psi_C_Phi_C_sig h_step_D h_step_C h_chain h_sm h_inj σh
  right_inv := fun M =>
    Phi_C_Psi_C_sig h_step_D h_step_C h_chain h_sm h_surj M

/-! ### Phi_M_sig (no Fin 2 — paper Prop 11.17) -/


noncomputable def Phi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (σh : PBPSet_M_sig μP μQ s) : MYD_sig .M s :=
  let σ := σh.val
  let h_sig := σh.prop
  let h_chain_σ := h_chain σ
  let chain := Classical.choose h_chain_σ
  let h_chain' := Classical.choose_spec h_chain_σ
  let E := Classical.choose (h_sing h_chain')
  let h_sing' := Classical.choose_spec (h_sing h_chain')
  have h_sign : ILS.sign E = s := by
    rw [h_sm h_chain' h_sing']
    show signTarget_M' σ.val = s
    exact h_sig
  ⟨E, h_sign⟩

noncomputable def Psi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    [Inhabited (PBPSet_M_sig μP μQ s)]
    (M : MYD_sig .M s) : PBPSet_M_sig μP μQ s :=
  open Classical in
  if h : ∃ σh : PBPSet_M_sig μP μQ s,
      Phi_M_sig h_chain h_sing h_sm σh = M
  then h.choose
  else default

theorem Psi_M_Phi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_M_sig μP μQ s)]
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (σh : PBPSet_M_sig μP μQ s) :
    Psi_M_sig (μP := μP) (μQ := μQ) h_chain h_sing h_sm
      (Phi_M_sig h_chain h_sing h_sm σh) = σh := by
  classical
  unfold Psi_M_sig
  have hex : ∃ x : PBPSet_M_sig μP μQ s,
      Phi_M_sig h_chain h_sing h_sm x = Phi_M_sig h_chain h_sing h_sm σh :=
    ⟨σh, rfl⟩
  rw [dif_pos hex]
  exact h_inj (Classical.choose_spec hex)

theorem Phi_M_Psi_M_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Inhabited (PBPSet_M_sig μP μQ s)]
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_surj : Function.Surjective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (M : MYD_sig .M s) :
    Phi_M_sig h_chain h_sing h_sm
      (Psi_M_sig (μP := μP) (μQ := μQ) h_chain h_sing h_sm M) = M := by
  classical
  unfold Psi_M_sig
  have hex : ∃ σh : PBPSet_M_sig μP μQ s,
      Phi_M_sig h_chain h_sing h_sm σh = M := h_surj M
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

/-- **Paper Prop 11.17 (M), signature variant**. -/
noncomputable def Phi_M_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (h_surj : Function.Surjective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    PBPSet_M_sig μP μQ s ≃ MYD_sig .M s where
  toFun := Phi_M_sig h_chain h_sing h_sm
  invFun := Psi_M_sig (μP := μP) (μQ := μQ) h_chain h_sing h_sm
  left_inv := fun σh => Psi_M_Phi_M_sig h_chain h_sing h_sm h_inj σh
  right_inv := fun M => Phi_M_Psi_M_sig h_chain h_sing h_sm h_surj M

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
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .D s) :=
  Fintype.ofEquiv _ (Phi_D_sig_equiv μP μQ s h_step h_inj h_surj)

noncomputable def fintype_MYD_sig_Bplus (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .Bplus s) :=
  Fintype.ofEquiv _ (Phi_Bplus_sig_equiv μP μQ s h_step h_inj h_surj)

noncomputable def fintype_MYD_sig_Bminus (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    Fintype (MYD_sig .Bminus s) :=
  Fintype.ofEquiv _ (Phi_Bminus_sig_equiv μP μQ s h_sing h_inj h_surj)

noncomputable def fintype_MYD_sig_C (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (h_surj : Function.Surjective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    Fintype (MYD_sig .C s) :=
  Fintype.ofEquiv _
    (Phi_C_sig_equiv μP μQ s h_step_D h_step_C h_chain h_sm h_inj h_surj)

noncomputable def fintype_MYD_sig_M (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (h_surj : Function.Surjective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    Fintype (MYD_sig .M s) :=
  Fintype.ofEquiv _
    (Phi_M_sig_equiv μP μQ s h_chain h_sing h_sm h_inj h_surj)

/-- **Paper Prop 11.15 card (D, sig)**: |PBPSet_D_sig × Fin 2| = |MYD_sig .D s|. -/
theorem card_PBPSet_D_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2))
    [Inhabited (PBPSet_D_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_D_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .D s) :=
  Nat.card_congr (Phi_D_sig_equiv μP μQ s h_step h_inj h_surj)

/-- **Paper Prop 11.15 card (B⁺, sig)**. -/
theorem card_PBPSet_Bplus_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2))
    [Inhabited (PBPSet_Bplus_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_Bplus_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .Bplus s) :=
  Nat.card_congr (Phi_Bplus_sig_equiv μP μQ s h_step h_inj h_surj)

/-- **Paper Prop 11.15 card (B⁻, sig)**. -/
theorem card_PBPSet_Bminus_sig_Fin2_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2))
    [Inhabited (PBPSet_Bminus_sig μP μQ s × Fin 2)] :
    Nat.card (PBPSet_Bminus_sig μP μQ s × Fin 2) = Nat.card (MYD_sig .Bminus s) :=
  Nat.card_congr (Phi_Bminus_sig_equiv μP μQ s h_sing h_inj h_surj)

/-- **Paper Prop 11.17 card (C, sig)**. -/
theorem card_PBPSet_C_sig_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (h_surj : Function.Surjective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    [Inhabited (PBPSet_C_sig μP μQ s)] :
    Nat.card (PBPSet_C_sig μP μQ s) = Nat.card (MYD_sig .C s) :=
  Nat.card_congr
    (Phi_C_sig_equiv μP μQ s h_step_D h_step_C h_chain h_sm h_inj h_surj)

/-- **Paper Prop 11.17 card (M, sig)**. -/
theorem card_PBPSet_M_sig_eq (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (h_surj : Function.Surjective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    [Inhabited (PBPSet_M_sig μP μQ s)] :
    Nat.card (PBPSet_M_sig μP μQ s) = Nat.card (MYD_sig .M s) :=
  Nat.card_congr
    (Phi_M_sig_equiv μP μQ s h_chain h_sing h_sm h_inj h_surj)

/-! ## Surjectivity reductions from injectivity + cardinality

Paper Prop 11.14 (at PBP level) says: given an injective map `f : α → β`
with `|α| = |β|` (witnessed by any equivalence `e : α ≃ β`), `f` is
surjective. These reductions apply that pattern to reduce the `h_surj`
hypothesis of each `Phi_γ_sig_equiv` to `h_inj` + a cardinality equality.

Discharging the cardinality equality is paper content — follows from
counting theorems of §10 — but is strictly a weaker hypothesis than
supplying `h_surj` directly.
-/

/-- Surjectivity of `Phi_D_sig` reduced to injectivity + cardinality. -/
theorem phi_D_sig_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig .D s)]
    (h_step : DescentStepSingleton_D)
    (h_card : Fintype.card (PBPSet_D_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig .D s))
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-- Surjectivity of `Phi_Bplus_sig` reduced to injectivity + cardinality. -/
theorem phi_Bplus_sig_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig .Bplus s)]
    (h_step : DescentStepSingleton_Bplus)
    (h_card : Fintype.card (PBPSet_Bplus_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig .Bplus s))
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-- Surjectivity of `Phi_Bminus_sig` reduced to injectivity + cardinality. -/
theorem phi_Bminus_sig_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig .Bminus s)]
    (h_sing : DescentChainBminusSingleton)
    (h_card : Fintype.card (PBPSet_Bminus_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig .Bminus s))
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-- Surjectivity of `Phi_C_sig` reduced to injectivity + cardinality. -/
theorem phi_C_sig_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig .C s)]
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_card : Fintype.card (PBPSet_C_sig μP μQ s) =
              Fintype.card (MYD_sig .C s))
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    Function.Surjective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-- Surjectivity of `Phi_M_sig` reduced to injectivity + cardinality. -/
theorem phi_M_sig_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig .M s)]
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_card : Fintype.card (PBPSet_M_sig μP μQ s) =
              Fintype.card (MYD_sig .M s))
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    Function.Surjective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-! ## Trim-canonicalized Phi wrappers

`Phi_γ_sig_trim` outputs `MYD_sig_trim γ s` directly (via `toTrim`).
This gives a function targeting the finite canonical subtype, which
is essential for making `Phi_γ_sig_equiv` instantiable in practice
(since `MYD_sig γ s` is structurally infinite due to trailing zeros).
-/

noncomputable def Phi_D_sig_trim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) : MYD_sig_trim .D s :=
  (Phi_D_sig h_step σh ε).toTrim

noncomputable def Phi_Bplus_sig_trim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) : MYD_sig_trim .Bplus s :=
  (Phi_Bplus_sig h_step σh ε).toTrim

noncomputable def Phi_Bminus_sig_trim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) : MYD_sig_trim .Bminus s :=
  (Phi_Bminus_sig h_sing σh ε).toTrim

noncomputable def Phi_C_sig_trim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (σh : PBPSet_C_sig μP μQ s) : MYD_sig_trim .C s :=
  (Phi_C_sig h_step_D h_step_C h_chain h_sm σh).toTrim

noncomputable def Phi_M_sig_trim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (σh : PBPSet_M_sig μP μQ s) : MYD_sig_trim .M s :=
  (Phi_M_sig h_chain h_sing h_sm σh).toTrim

/-- `Phi_D_sig_trim`'s `.E` field equals `trim` of `Phi_D_sig`'s output. -/
theorem Phi_D_sig_trim_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    (Phi_D_sig_trim h_step σh ε).E = ILS.trim (Phi_D_sig h_step σh ε).E := rfl

theorem Phi_Bplus_sig_trim_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    (Phi_Bplus_sig_trim h_step σh ε).E = ILS.trim (Phi_Bplus_sig h_step σh ε).E := rfl

theorem Phi_Bminus_sig_trim_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    (Phi_Bminus_sig_trim h_sing σh ε).E = ILS.trim (Phi_Bminus_sig h_sing σh ε).E := rfl

theorem Phi_C_sig_trim_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (σh : PBPSet_C_sig μP μQ s) :
    (Phi_C_sig_trim h_step_D h_step_C h_chain h_sm σh).E =
    ILS.trim (Phi_C_sig h_step_D h_step_C h_chain h_sm σh).E := rfl

theorem Phi_M_sig_trim_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (σh : PBPSet_M_sig μP μQ s) :
    (Phi_M_sig_trim h_chain h_sing h_sm σh).E =
    ILS.trim (Phi_M_sig h_chain h_sing h_sm σh).E := rfl

/-! ## Trim-target equiv assembly

These mirror `Phi_γ_sig_equiv` but with `MYD_sig_trim` as target,
making the bijection instantiable (target is finite).
-/

noncomputable def Phi_D_sig_trim_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2)) :
    PBPSet_D_sig μP μQ s × Fin 2 ≃ MYD_sig_trim .D s :=
  Equiv.ofBijective (fun p => Phi_D_sig_trim h_step p.1 p.2) ⟨h_inj, h_surj⟩

noncomputable def Phi_Bplus_sig_trim_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2)) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃ MYD_sig_trim .Bplus s :=
  Equiv.ofBijective (fun p => Phi_Bplus_sig_trim h_step p.1 p.2) ⟨h_inj, h_surj⟩

noncomputable def Phi_Bminus_sig_trim_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2))
    (h_surj : Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2)) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃ MYD_sig_trim .Bminus s :=
  Equiv.ofBijective (fun p => Phi_Bminus_sig_trim h_sing p.1 p.2) ⟨h_inj, h_surj⟩

noncomputable def Phi_C_sig_trim_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm))
    (h_surj : Function.Surjective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    PBPSet_C_sig μP μQ s ≃ MYD_sig_trim .C s :=
  Equiv.ofBijective _ ⟨h_inj, h_surj⟩

noncomputable def Phi_M_sig_trim_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm))
    (h_surj : Function.Surjective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    PBPSet_M_sig μP μQ s ≃ MYD_sig_trim .M s :=
  Equiv.ofBijective _ ⟨h_inj, h_surj⟩

/-! ## Image equivs (only requires injectivity)

Each `Phi_γ_sig_image_equiv` gives an equiv to the IMAGE of Phi
(a Set in MYD_sig γ s) — needs only injectivity, not surjectivity.

Useful as a partial bijection result that's discharge-able with
fewer hypotheses.
-/

noncomputable def Phi_D_sig_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2)) :
    PBPSet_D_sig μP μQ s × Fin 2 ≃
      Set.range (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_Bplus_sig_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2)) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃
      Set.range (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_Bminus_sig_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2)) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃
      Set.range (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_C_sig_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    PBPSet_C_sig μP μQ s ≃
      Set.range (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_M_sig_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    PBPSet_M_sig μP μQ s ≃
      Set.range (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm) :=
  Equiv.ofInjective _ h_inj

/-! ## Image-cardinality bridges

When Phi is injective, |source| = |image| via Nat.card_congr of the
image equiv. These give cardinality results requiring only injectivity.
-/

theorem nat_card_PBPSet_D_eq_image (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2)) :
    Nat.card (PBPSet_D_sig μP μQ s × Fin 2) =
    Nat.card (Set.range
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2)) :=
  Nat.card_congr (Phi_D_sig_image_equiv μP μQ s h_step h_inj)

theorem nat_card_PBPSet_Bplus_eq_image (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2)) :
    Nat.card (PBPSet_Bplus_sig μP μQ s × Fin 2) =
    Nat.card (Set.range
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2)) :=
  Nat.card_congr (Phi_Bplus_sig_image_equiv μP μQ s h_step h_inj)

theorem nat_card_PBPSet_Bminus_eq_image (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2)) :
    Nat.card (PBPSet_Bminus_sig μP μQ s × Fin 2) =
    Nat.card (Set.range
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2)) :=
  Nat.card_congr (Phi_Bminus_sig_image_equiv μP μQ s h_sing h_inj)

theorem nat_card_PBPSet_C_eq_image (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    Nat.card (PBPSet_C_sig μP μQ s) =
    Nat.card (Set.range
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :=
  Nat.card_congr (Phi_C_sig_image_equiv μP μQ s h_step_D h_step_C h_chain h_sm h_inj)

theorem nat_card_PBPSet_M_eq_image (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    Nat.card (PBPSet_M_sig μP μQ s) =
    Nat.card (Set.range
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :=
  Nat.card_congr (Phi_M_sig_image_equiv μP μQ s h_chain h_sing h_sm h_inj)

end BMSZ
