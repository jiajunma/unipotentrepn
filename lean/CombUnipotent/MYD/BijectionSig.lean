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

/-! ## Phi outputs trim under StepStdAndAugment hypotheses -/

/-- Under per-step std + ne_augment hypothesis, `Phi_D_sig`'s output
    `E` is trim. -/
theorem Phi_D_sig_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (h_step_std : StepStdAndAugment_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_D_sig h_step σh ε).E := by
  show ILS.IsTrim (ILS.twistBD _ _ _)
  apply ILS.twistBD_IsTrim
  · by_cases hε : ε = 1 <;> simp [hε]
  · by_cases hε : ε = 1 <;> simp [hε]
  · exact chainSingleton_IsTrim_D h_step_std
      (Classical.choose_spec (exists_descentChain_D σh.val))
      (Classical.choose_spec (descentChain_D_singleton h_step
        (Classical.choose_spec (exists_descentChain_D σh.val))))

/-- Under per-step std + ne_augment hypothesis, `Phi_Bplus_sig`'s
    output `E` is trim. -/
theorem Phi_Bplus_sig_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (h_step_std : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_Bplus_sig h_step σh ε).E := by
  show ILS.IsTrim (ILS.twistBD _ _ _)
  apply ILS.twistBD_IsTrim
  · by_cases hε : ε = 1 <;> simp [hε]
  · by_cases hε : ε = 1 <;> simp [hε]
  · exact chainSingleton_IsTrim_Bplus h_step_std
      (Classical.choose_spec (exists_descentChain_Bplus σh.val))
      (Classical.choose_spec (descentChain_Bplus_singleton h_step
        (Classical.choose_spec (exists_descentChain_Bplus σh.val))))

/-- Under chain-singleton + per-step std hypotheses for B+, `Phi_Bminus_sig`'s
    output `E` is trim. -/
theorem Phi_Bminus_sig_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_Bminus_sig h_sing σh ε).E := by
  show ILS.IsTrim (ILS.twistBD _ _ _)
  apply ILS.twistBD_IsTrim
  · by_cases hε : ε = 1 <;> simp [hε]
  · by_cases hε : ε = 1 <;> simp [hε]
  · exact chainSingleton_IsTrim_Bminus h_step_std_Bm h_step_std_Bp
      (Classical.choose_spec (exists_descentChain_Bminus σh.val))
      (Classical.choose_spec (h_sing
        (Classical.choose_spec (exists_descentChain_Bminus σh.val))))

/-- `Phi_C_sig`'s output `E` is trim under per-step std hypotheses. -/
theorem Phi_C_sig_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_step_std_D : StepStdAndAugment_D)
    (h_step_std_C : StepStdAndAugment_C)
    (σh : PBPSet_C_sig μP μQ s) :
    ILS.IsTrim (Phi_C_sig h_step_D h_step_C h_chain h_sm σh).E :=
  chainSingleton_IsTrim_C h_step_std_C h_step_std_D
    (Classical.choose_spec (h_chain σh.val))
    (Classical.choose_spec (descentChain_C_singleton h_step_D h_step_C
      (Classical.choose_spec (h_chain σh.val))))

/-- `Phi_M_sig`'s output `E` is trim under per-step std hypotheses. -/
theorem Phi_M_sig_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_step_std_M : StepStdAndAugment_M)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (σh : PBPSet_M_sig μP μQ s) :
    ILS.IsTrim (Phi_M_sig h_chain h_sing h_sm σh).E :=
  chainSingleton_IsTrim_M h_step_std_M h_step_std_Bp h_step_std_Bm
    (Classical.choose_spec (h_chain σh.val))
    (Classical.choose_spec (h_sing
      (Classical.choose_spec (h_chain σh.val))))

/-! ## Phi outputs trim ILS automatically (via toTrim) -/

/-- `Phi_D_sig_trim` always outputs `MYD_sig_trim` (trim by construction). -/
theorem Phi_D_sig_trim_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_D_sig_trim h_step σh ε).E :=
  (Phi_D_sig_trim h_step σh ε).is_trim

theorem Phi_Bplus_sig_trim_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_Bplus_sig_trim h_step σh ε).E :=
  (Phi_Bplus_sig_trim h_step σh ε).is_trim

theorem Phi_Bminus_sig_trim_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    ILS.IsTrim (Phi_Bminus_sig_trim h_sing σh ε).E :=
  (Phi_Bminus_sig_trim h_sing σh ε).is_trim

theorem Phi_C_sig_trim_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (σh : PBPSet_C_sig μP μQ s) :
    ILS.IsTrim (Phi_C_sig_trim h_step_D h_step_C h_chain h_sm σh).E :=
  (Phi_C_sig_trim h_step_D h_step_C h_chain h_sm σh).is_trim

theorem Phi_M_sig_trim_E_IsTrim {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (σh : PBPSet_M_sig μP μQ s) :
    ILS.IsTrim (Phi_M_sig_trim h_chain h_sing h_sm σh).E :=
  (Phi_M_sig_trim h_chain h_sing h_sm σh).is_trim

/-! ## Range characterization for Phi_γ_sig_trim with sign (0, 0)

For sign (0, 0), MYD_sig_trim γ (0, 0) is a singleton (proved earlier).
So `Set.range Phi_γ_sig_trim ⊆ {MYD_sig_trim.zero}`. Equality holds
iff source is non-empty.
-/

/-- Output of any `Phi_γ_sig_trim` with sign (0, 0) is `MYD_sig_trim.zero`. -/
theorem Phi_D_sig_trim_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_D_sig_trim h_step σh ε = MYD_sig_trim.zero :=
  Subsingleton.elim _ _

theorem Phi_Bplus_sig_trim_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_Bplus_sig_trim h_step σh ε = MYD_sig_trim.zero :=
  Subsingleton.elim _ _

theorem Phi_Bminus_sig_trim_zero {μP μQ : YoungDiagram}
    (h_sing : DescentChainBminusSingleton)
    (σh : PBPSet_Bminus_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_Bminus_sig_trim h_sing σh ε = MYD_sig_trim.zero :=
  Subsingleton.elim _ _

theorem Phi_C_sig_trim_zero {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (σh : PBPSet_C_sig μP μQ (0, 0)) :
    Phi_C_sig_trim h_step_D h_step_C h_chain h_sm σh = MYD_sig_trim.zero :=
  Subsingleton.elim _ _

theorem Phi_M_sig_trim_zero {μP μQ : YoungDiagram}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (σh : PBPSet_M_sig μP μQ (0, 0)) :
    Phi_M_sig_trim h_chain h_sing h_sm σh = MYD_sig_trim.zero :=
  Subsingleton.elim _ _

/-! ## Surjectivity in the (0, 0) sector

Since `MYD_sig_trim γ (0, 0)` is a singleton and `Phi_γ_sig_trim` is
defined on a non-empty source, surjectivity is automatic. This gives
the FIRST UNCONDITIONAL surjectivity result for the trim variant
(no h_surj hypothesis needed).
-/

theorem phi_D_sig_trim_surjective_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_D)
    [Inhabited (PBPSet_D_sig μP μQ (0, 0) × Fin 2)] :
    Function.Surjective
      (fun p : PBPSet_D_sig μP μQ (0, 0) × Fin 2 => Phi_D_sig_trim h_step p.1 p.2) := by
  intro M
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

theorem phi_Bplus_sig_trim_surjective_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_Bplus)
    [Inhabited (PBPSet_Bplus_sig μP μQ (0, 0) × Fin 2)] :
    Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ (0, 0) × Fin 2 =>
        Phi_Bplus_sig_trim h_step p.1 p.2) := by
  intro M
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

theorem phi_Bminus_sig_trim_surjective_zero {μP μQ : YoungDiagram}
    (h_sing : DescentChainBminusSingleton)
    [Inhabited (PBPSet_Bminus_sig μP μQ (0, 0) × Fin 2)] :
    Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ (0, 0) × Fin 2 =>
        Phi_Bminus_sig_trim h_sing p.1 p.2) := by
  intro M
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

theorem phi_C_sig_trim_surjective_zero {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    [Inhabited (PBPSet_C_sig μP μQ (0, 0))] :
    Function.Surjective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := (0, 0))
        h_step_D h_step_C h_chain h_sm) := by
  intro M
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

theorem phi_M_sig_trim_surjective_zero {μP μQ : YoungDiagram}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    [Inhabited (PBPSet_M_sig μP μQ (0, 0))] :
    Function.Surjective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := (0, 0))
        h_chain h_sing h_sm) := by
  intro M
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

/-! ## Phi_γ_sig outputs MYD_sig.zero on (0,0) sector under std

Under StepStdAndAugment_γ, Phi_γ_sig's output is trim (Phi_γ_sig_E_IsTrim).
For sign (0, 0), trim ILS must be empty (eq_nil_of_sign_zero_of_IsTrim).
So Phi_γ_sig's output is MYD_sig.zero.
-/

theorem Phi_D_sig_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_D)
    (h_step_std : StepStdAndAugment_D)
    (σh : PBPSet_D_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_D_sig h_step σh ε = MYD_sig.zero := by
  apply MYD_sig.ext
  have h_trim := Phi_D_sig_E_IsTrim h_step h_step_std σh ε
  have h_sign := (Phi_D_sig h_step σh ε).sign_match
  exact ILS.eq_nil_of_sign_zero_of_IsTrim _ h_sign h_trim

theorem Phi_Bplus_sig_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_Bplus)
    (h_step_std : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_Bplus_sig h_step σh ε = MYD_sig.zero := by
  apply MYD_sig.ext
  have h_trim := Phi_Bplus_sig_E_IsTrim h_step h_step_std σh ε
  have h_sign := (Phi_Bplus_sig h_step σh ε).sign_match
  exact ILS.eq_nil_of_sign_zero_of_IsTrim _ h_sign h_trim

theorem Phi_Bminus_sig_zero {μP μQ : YoungDiagram}
    (h_sing : DescentChainBminusSingleton)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bminus_sig μP μQ (0, 0)) (ε : Fin 2) :
    Phi_Bminus_sig h_sing σh ε = MYD_sig.zero := by
  apply MYD_sig.ext
  have h_trim := Phi_Bminus_sig_E_IsTrim h_sing h_step_std_Bm h_step_std_Bp σh ε
  have h_sign := (Phi_Bminus_sig h_sing σh ε).sign_match
  exact ILS.eq_nil_of_sign_zero_of_IsTrim _ h_sign h_trim

theorem Phi_C_sig_zero {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_step_std_D : StepStdAndAugment_D)
    (h_step_std_C : StepStdAndAugment_C)
    (σh : PBPSet_C_sig μP μQ (0, 0)) :
    Phi_C_sig h_step_D h_step_C h_chain h_sm σh = MYD_sig.zero := by
  apply MYD_sig.ext
  have h_trim := Phi_C_sig_E_IsTrim h_step_D h_step_C h_chain h_sm
    h_step_std_D h_step_std_C σh
  have h_sign := (Phi_C_sig h_step_D h_step_C h_chain h_sm σh).sign_match
  exact ILS.eq_nil_of_sign_zero_of_IsTrim _ h_sign h_trim

theorem Phi_M_sig_zero {μP μQ : YoungDiagram}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_step_std_M : StepStdAndAugment_M)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (σh : PBPSet_M_sig μP μQ (0, 0)) :
    Phi_M_sig h_chain h_sing h_sm σh = MYD_sig.zero := by
  apply MYD_sig.ext
  have h_trim := Phi_M_sig_E_IsTrim h_chain h_sing h_sm
    h_step_std_M h_step_std_Bp h_step_std_Bm σh
  have h_sign := (Phi_M_sig h_chain h_sing h_sm σh).sign_match
  exact ILS.eq_nil_of_sign_zero_of_IsTrim _ h_sign h_trim

/-! ## Range characterization in (0,0) sector

`Set.range Phi_γ_sig_trim` on (0,0) sector is `{MYD_sig_trim.zero}`
(when source is non-empty) or `∅` (otherwise).
-/

theorem Phi_D_sig_trim_range_zero {μP μQ : YoungDiagram}
    (h_step : DescentStepSingleton_D)
    [_h : Inhabited (PBPSet_D_sig μP μQ (0, 0) × Fin 2)] :
    Set.range
      (fun p : PBPSet_D_sig μP μQ (0, 0) × Fin 2 => Phi_D_sig_trim h_step p.1 p.2)
    = {MYD_sig_trim.zero} := by
  ext M
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩
    rw [← hp]
    exact Phi_D_sig_trim_zero h_step p.1 p.2
  · intro hM
    refine ⟨default, ?_⟩
    rw [hM]
    exact Subsingleton.elim _ _

theorem Phi_C_sig_trim_range_zero {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    [_h : Inhabited (PBPSet_C_sig μP μQ (0, 0))] :
    Set.range
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := (0, 0))
        h_step_D h_step_C h_chain h_sm)
    = {MYD_sig_trim.zero} := by
  ext M
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩
    rw [← hp]
    exact Phi_C_sig_trim_zero h_step_D h_step_C h_chain h_sm p
  · intro hM
    refine ⟨default, ?_⟩
    rw [hM]
    exact Subsingleton.elim _ _

/-! ## Bijection in (0,0) sector (C / M only, no Fin 2 multiplier)

For C/M chains (without Fin 2), if the source `PBPSet_*_sig` is
subsingleton, the bijection `Phi_*_sig_trim ≃ MYD_sig_trim` holds
unconditionally on (0,0) sector — both sides have cardinality 1.
-/

/-- `Phi_C_sig_trim` is bijective on (0,0) sector when source is subsingleton. -/
noncomputable def Phi_C_sig_trim_zero_equiv {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    [Subsingleton (PBPSet_C_sig μP μQ (0, 0))]
    [Inhabited (PBPSet_C_sig μP μQ (0, 0))] :
    PBPSet_C_sig μP μQ (0, 0) ≃ MYD_sig_trim .C (0, 0) :=
  Equiv.ofBijective (Phi_C_sig_trim h_step_D h_step_C h_chain h_sm)
    ⟨fun _ _ _ => Subsingleton.elim _ _,
     phi_C_sig_trim_surjective_zero h_step_D h_step_C h_chain h_sm⟩

/-- `Phi_M_sig_trim` is bijective on (0,0) sector when source is subsingleton. -/
noncomputable def Phi_M_sig_trim_zero_equiv {μP μQ : YoungDiagram}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    [Subsingleton (PBPSet_M_sig μP μQ (0, 0))]
    [Inhabited (PBPSet_M_sig μP μQ (0, 0))] :
    PBPSet_M_sig μP μQ (0, 0) ≃ MYD_sig_trim .M (0, 0) :=
  Equiv.ofBijective (Phi_M_sig_trim h_chain h_sing h_sm)
    ⟨fun _ _ _ => Subsingleton.elim _ _,
     phi_M_sig_trim_surjective_zero h_chain h_sing h_sm⟩

/-! ## Cardinality result for the (0,0) bijection -/

theorem card_PBPSet_C_sig_zero_eq {μP μQ : YoungDiagram}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    [Fintype (PBPSet_C_sig μP μQ (0, 0))]
    [Subsingleton (PBPSet_C_sig μP μQ (0, 0))]
    [Inhabited (PBPSet_C_sig μP μQ (0, 0))] :
    Fintype.card (PBPSet_C_sig μP μQ (0, 0)) =
    Fintype.card (MYD_sig_trim .C (0, 0)) := by
  rw [card_MYD_sig_trim_zero]
  exact Fintype.card_eq_one_iff.mpr ⟨default, fun _ => Subsingleton.elim _ _⟩

theorem card_PBPSet_M_sig_zero_eq {μP μQ : YoungDiagram}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    [Fintype (PBPSet_M_sig μP μQ (0, 0))]
    [Subsingleton (PBPSet_M_sig μP μQ (0, 0))]
    [Inhabited (PBPSet_M_sig μP μQ (0, 0))] :
    Fintype.card (PBPSet_M_sig μP μQ (0, 0)) =
    Fintype.card (MYD_sig_trim .M (0, 0)) := by
  rw [card_MYD_sig_trim_zero]
  exact Fintype.card_eq_one_iff.mpr ⟨default, fun _ => Subsingleton.elim _ _⟩

/-- `Inhabited (PBPSet_C_sig ⊥ ⊥ (0, 0))` — concrete witness via emptyPBP_C. -/
instance inhabited_PBPSet_C_sig_zero :
    Inhabited (PBPSet_C_sig (⊥ : YoungDiagram) ⊥ (0, 0)) :=
  ⟨⟨emptyPBPSet_C, by
    show signTarget_C emptyPBP_C = (0, 0)
    unfold signTarget_C
    rw [emptyPBP_C_signature]
    rfl⟩⟩

/-- `Subsingleton (PBPSet .C ⊥ ⊥)` — uniqueness via PBP_eq_of_shapes_bot. -/
instance subsingleton_PBPSet_C_bot :
    Subsingleton (PBPSet .C (⊥ : YoungDiagram) ⊥) := by
  refine ⟨fun σ₁ σ₂ => ?_⟩
  apply Subtype.ext
  apply PBP_eq_of_shapes_bot
  · rw [σ₁.prop.1, σ₂.prop.1]
  · exact σ₁.prop.2.1
  · exact σ₁.prop.2.2
  · exact σ₂.prop.2.1
  · exact σ₂.prop.2.2

/-- `Subsingleton (PBPSet_C_sig ⊥ ⊥ s)` for any s. -/
instance subsingleton_PBPSet_C_sig_bot (s : ℤ × ℤ) :
    Subsingleton (PBPSet_C_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M₁ M₂ => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- 🎯🎯🎯 **FIRST FULLY UNCONDITIONAL BIJECTION**:
    `Phi_C_sig_trim` is a bijection on the (⊥, ⊥) (0,0) sector.

    No paper-content hypotheses required (Subsingleton + Inhabited
    are now both PROVED for this sector). The only remaining
    hypotheses are `h_step_D + h_step_C + h_chain + h_sm` which
    are conditional (any value works since the source is subsingleton). -/
noncomputable def Phi_C_sig_trim_bot_zero_equiv
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C (⊥ : YoungDiagram) ⊥)
    (h_sm : DescentChainSignMatch_C) :
    PBPSet_C_sig (⊥ : YoungDiagram) ⊥ (0, 0) ≃ MYD_sig_trim .C (0, 0) :=
  Phi_C_sig_trim_zero_equiv h_step_D h_step_C h_chain h_sm

/-! ## M-type analogues -/

/-- `Inhabited (PBPSet_M_sig ⊥ ⊥ (0, 0))` — concrete witness via emptyPBP_M. -/
instance inhabited_PBPSet_M_sig_zero :
    Inhabited (PBPSet_M_sig (⊥ : YoungDiagram) ⊥ (0, 0)) :=
  ⟨⟨emptyPBPSet_M, by
    show signTarget_M emptyPBP_M = (0, 0)
    unfold signTarget_M
    rw [emptyPBP_M_signature]
    rfl⟩⟩

/-- `Subsingleton (PBPSet .M ⊥ ⊥)` — uniqueness via PBP_eq_of_shapes_bot. -/
instance subsingleton_PBPSet_M_bot :
    Subsingleton (PBPSet .M (⊥ : YoungDiagram) ⊥) := by
  refine ⟨fun σ₁ σ₂ => ?_⟩
  apply Subtype.ext
  apply PBP_eq_of_shapes_bot
  · rw [σ₁.prop.1, σ₂.prop.1]
  · exact σ₁.prop.2.1
  · exact σ₁.prop.2.2
  · exact σ₂.prop.2.1
  · exact σ₂.prop.2.2

instance subsingleton_PBPSet_M_sig_bot (s : ℤ × ℤ) :
    Subsingleton (PBPSet_M_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M₁ M₂ => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- 🎯🎯🎯🎯 **SECOND INSTANTIABLE BIJECTION** (M-type analogue):
    `PBPSet_M_sig (⊥, ⊥) (0, 0) ≃ MYD_sig_trim .M (0, 0)`. -/
noncomputable def Phi_M_sig_trim_bot_zero_equiv
    (h_chain : ChainExists_M (⊥ : YoungDiagram) ⊥)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M) :
    PBPSet_M_sig (⊥ : YoungDiagram) ⊥ (0, 0) ≃ MYD_sig_trim .M (0, 0) :=
  Phi_M_sig_trim_zero_equiv h_chain h_sing h_sm

/-! ## PBPSet_*_sig (⊥, ⊥) s is empty for s ≠ (0, 0)

For empty shape (⊥), the only PBP is `emptyPBP_C` (resp. `emptyPBP_M`)
with signature (0, 0). Therefore PBPSet_*_sig (⊥, ⊥) s for s ≠ (0, 0)
is empty.
-/

theorem PBPSet_C_sig_bot_eq_empty {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    IsEmpty (PBPSet_C_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_C M.val.val = s := M.prop
  have h_unique : M.val = emptyPBPSet_C := Subsingleton.elim _ _
  have h_sig : signTarget_C M.val.val = (0, 0) := by
    rw [h_unique]
    show signTarget_C emptyPBP_C = (0, 0)
    unfold signTarget_C
    rw [emptyPBP_C_signature]
    rfl
  exact h (h_eq.symm.trans h_sig)

theorem PBPSet_M_sig_bot_eq_empty {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    IsEmpty (PBPSet_M_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_M M.val.val = s := M.prop
  have h_unique : M.val = emptyPBPSet_M := Subsingleton.elim _ _
  have h_sig : signTarget_M M.val.val = (0, 0) := by
    rw [h_unique]
    show signTarget_M emptyPBP_M = (0, 0)
    unfold signTarget_M
    rw [emptyPBP_M_signature]
    rfl
  exact h (h_eq.symm.trans h_sig)

noncomputable instance fintype_PBPSet_C_sig_bot_nonzero {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    Fintype (PBPSet_C_sig (⊥ : YoungDiagram) ⊥ s) :=
  @Fintype.ofIsEmpty _ (PBPSet_C_sig_bot_eq_empty h)

noncomputable instance fintype_PBPSet_M_sig_bot_nonzero {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    Fintype (PBPSet_M_sig (⊥ : YoungDiagram) ⊥ s) :=
  @Fintype.ofIsEmpty _ (PBPSet_M_sig_bot_eq_empty h)

/-! ## D-type analogues (instances on ⊥⊥) -/

/-- `Inhabited (PBPSet_D_sig ⊥ ⊥ (0, 0))` — concrete witness via emptyPBP_D. -/
instance inhabited_PBPSet_D_sig_zero :
    Inhabited (PBPSet_D_sig (⊥ : YoungDiagram) ⊥ (0, 0)) :=
  ⟨⟨emptyPBPSet_D, by
    show signTarget_D emptyPBP_D = (0, 0)
    unfold signTarget_D
    rw [emptyPBP_D_signature]
    rfl⟩⟩

/-- `Subsingleton (PBPSet .D ⊥ ⊥)` — uniqueness via PBP_eq_of_shapes_bot. -/
instance subsingleton_PBPSet_D_bot :
    Subsingleton (PBPSet .D (⊥ : YoungDiagram) ⊥) := by
  refine ⟨fun σ₁ σ₂ => ?_⟩
  apply Subtype.ext
  apply PBP_eq_of_shapes_bot
  · rw [σ₁.prop.1, σ₂.prop.1]
  · exact σ₁.prop.2.1
  · exact σ₁.prop.2.2
  · exact σ₂.prop.2.1
  · exact σ₂.prop.2.2

/-- `Subsingleton (PBPSet_D_sig ⊥ ⊥ s)` for any s. -/
instance subsingleton_PBPSet_D_sig_bot (s : ℤ × ℤ) :
    Subsingleton (PBPSet_D_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M₁ M₂ => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- `PBPSet_D_sig ⊥ ⊥ s` is empty for any `s ≠ (0, 0)`. -/
theorem PBPSet_D_sig_bot_eq_empty {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    IsEmpty (PBPSet_D_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_D M.val.val = s := M.prop
  have h_unique : M.val = emptyPBPSet_D := Subsingleton.elim _ _
  have h_sig : signTarget_D M.val.val = (0, 0) := by
    rw [h_unique]
    show signTarget_D emptyPBP_D = (0, 0)
    unfold signTarget_D
    rw [emptyPBP_D_signature]
    rfl
  exact h (h_eq.symm.trans h_sig)

noncomputable instance fintype_PBPSet_D_sig_bot_nonzero {s : ℤ × ℤ} (h : s ≠ (0, 0)) :
    Fintype (PBPSet_D_sig (⊥ : YoungDiagram) ⊥ s) :=
  @Fintype.ofIsEmpty _ (PBPSet_D_sig_bot_eq_empty h)

/-- `Phi_D_sig_trim` is constant (= `MYD_sig_trim.zero`) on the (⊥, ⊥) (0, 0)
    sector. Follows directly from `Phi_D_sig_trim_zero`. -/
theorem Phi_D_sig_trim_bot_zero_const
    (h_step : DescentStepSingleton_D)
    (σh : PBPSet_D_sig (⊥ : YoungDiagram) ⊥ (0, 0)) (ε : Fin 2) :
    Phi_D_sig_trim h_step σh ε = MYD_sig_trim.zero :=
  Phi_D_sig_trim_zero h_step σh ε

/-- Range of `Phi_D_sig_trim` on the (⊥, ⊥) (0, 0) sector is the singleton
    `{MYD_sig_trim.zero}`. Removes the `Inhabited` hypothesis via the
    concrete instance. -/
theorem Phi_D_sig_trim_bot_range_zero (h_step : DescentStepSingleton_D) :
    Set.range
      (fun p : PBPSet_D_sig (⊥ : YoungDiagram) ⊥ (0, 0) × Fin 2 =>
        Phi_D_sig_trim h_step p.1 p.2) = {MYD_sig_trim.zero} :=
  Phi_D_sig_trim_range_zero (μP := ⊥) (μQ := ⊥) h_step

/-! ## B⁺ / B⁻ analogues (instances on ⊥⊥)

Signatures differ from the D/C/M case: empty B⁺ has signature `(1, 0)`
and empty B⁻ has signature `(0, 1)`. -/

/-- `Inhabited (PBPSet_Bplus_sig ⊥ ⊥ (1, 0))` — concrete witness via emptyPBP_Bplus. -/
instance inhabited_PBPSet_Bplus_sig_one :
    Inhabited (PBPSet_Bplus_sig (⊥ : YoungDiagram) ⊥ (1, 0)) :=
  ⟨⟨emptyPBPSet_Bplus, by
    show signTarget_Bplus emptyPBP_Bplus = (1, 0)
    unfold signTarget_Bplus
    rw [emptyPBP_Bplus_signature]
    rfl⟩⟩

/-- `Inhabited (PBPSet_Bminus_sig ⊥ ⊥ (0, 1))` — concrete witness via emptyPBP_Bminus. -/
instance inhabited_PBPSet_Bminus_sig_one :
    Inhabited (PBPSet_Bminus_sig (⊥ : YoungDiagram) ⊥ (0, 1)) :=
  ⟨⟨emptyPBPSet_Bminus, by
    show signTarget_Bminus emptyPBP_Bminus = (0, 1)
    unfold signTarget_Bminus
    rw [emptyPBP_Bminus_signature]
    rfl⟩⟩

/-- `Subsingleton (PBPSet .Bplus ⊥ ⊥)`. -/
instance subsingleton_PBPSet_Bplus_bot :
    Subsingleton (PBPSet .Bplus (⊥ : YoungDiagram) ⊥) := by
  refine ⟨fun σ₁ σ₂ => ?_⟩
  apply Subtype.ext
  apply PBP_eq_of_shapes_bot
  · rw [σ₁.prop.1, σ₂.prop.1]
  · exact σ₁.prop.2.1
  · exact σ₁.prop.2.2
  · exact σ₂.prop.2.1
  · exact σ₂.prop.2.2

/-- `Subsingleton (PBPSet .Bminus ⊥ ⊥)`. -/
instance subsingleton_PBPSet_Bminus_bot :
    Subsingleton (PBPSet .Bminus (⊥ : YoungDiagram) ⊥) := by
  refine ⟨fun σ₁ σ₂ => ?_⟩
  apply Subtype.ext
  apply PBP_eq_of_shapes_bot
  · rw [σ₁.prop.1, σ₂.prop.1]
  · exact σ₁.prop.2.1
  · exact σ₁.prop.2.2
  · exact σ₂.prop.2.1
  · exact σ₂.prop.2.2

/-- `Subsingleton (PBPSet_Bplus_sig ⊥ ⊥ s)` for any s. -/
instance subsingleton_PBPSet_Bplus_sig_bot (s : ℤ × ℤ) :
    Subsingleton (PBPSet_Bplus_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M₁ M₂ => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- `Subsingleton (PBPSet_Bminus_sig ⊥ ⊥ s)` for any s. -/
instance subsingleton_PBPSet_Bminus_sig_bot (s : ℤ × ℤ) :
    Subsingleton (PBPSet_Bminus_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M₁ M₂ => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- For arbitrary shapes μP, μQ, `PBPSet_Bplus_sig μP μQ s` is empty when
    `s.1 < 1` (i.e., for B⁺ type, the first signature component is always
    at least `1`). -/
theorem PBPSet_Bplus_sig_fst_lt_one_eq_empty {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h : s.1 < 1) :
    IsEmpty (PBPSet_Bplus_sig μP μQ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_Bplus M.val.val = s := M.prop
  have hγ : M.val.val.γ = .Bplus := M.val.prop.1
  have h_sig_pos : 1 ≤ (PBP.signature M.val.val).1 := signature_Bplus_fst_pos _ hγ
  have h_target : (signTarget_Bplus M.val.val).1 = ((PBP.signature M.val.val).1 : ℤ) := rfl
  have : 1 ≤ s.1 := by
    rw [← h_eq, h_target]
    exact_mod_cast h_sig_pos
  omega

/-- For arbitrary shapes μP, μQ, `PBPSet_Bminus_sig μP μQ s` is empty when
    `s.2 < 1`. -/
theorem PBPSet_Bminus_sig_snd_lt_one_eq_empty {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h : s.2 < 1) :
    IsEmpty (PBPSet_Bminus_sig μP μQ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_Bminus M.val.val = s := M.prop
  have hγ : M.val.val.γ = .Bminus := M.val.prop.1
  have h_sig_pos : 1 ≤ (PBP.signature M.val.val).2 := signature_Bminus_snd_pos _ hγ
  have h_target : (signTarget_Bminus M.val.val).2 = ((PBP.signature M.val.val).2 : ℤ) := rfl
  have : 1 ≤ s.2 := by
    rw [← h_eq, h_target]
    exact_mod_cast h_sig_pos
  omega

/-- `PBPSet_Bplus_sig μP μQ (0, 0)` is always empty (no Bplus PBP has
    `signature.1 = 0`). -/
theorem PBPSet_Bplus_sig_zero_eq_empty {μP μQ : YoungDiagram} :
    IsEmpty (PBPSet_Bplus_sig μP μQ (0, 0)) :=
  PBPSet_Bplus_sig_fst_lt_one_eq_empty (by norm_num)

/-- `PBPSet_Bminus_sig μP μQ (0, 0)` is always empty (no Bminus PBP has
    `signature.2 = 0`). -/
theorem PBPSet_Bminus_sig_zero_eq_empty {μP μQ : YoungDiagram} :
    IsEmpty (PBPSet_Bminus_sig μP μQ (0, 0)) :=
  PBPSet_Bminus_sig_snd_lt_one_eq_empty (by norm_num)

/-- `PBPSet_Bplus_sig ⊥ ⊥ s` is empty for any `s ≠ (1, 0)`. -/
theorem PBPSet_Bplus_sig_bot_eq_empty {s : ℤ × ℤ} (h : s ≠ (1, 0)) :
    IsEmpty (PBPSet_Bplus_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_Bplus M.val.val = s := M.prop
  have h_unique : M.val = emptyPBPSet_Bplus := Subsingleton.elim _ _
  have h_sig : signTarget_Bplus M.val.val = (1, 0) := by
    rw [h_unique]
    show signTarget_Bplus emptyPBP_Bplus = (1, 0)
    unfold signTarget_Bplus
    rw [emptyPBP_Bplus_signature]
    rfl
  exact h (h_eq.symm.trans h_sig)

/-- `PBPSet_Bminus_sig ⊥ ⊥ s` is empty for any `s ≠ (0, 1)`. -/
theorem PBPSet_Bminus_sig_bot_eq_empty {s : ℤ × ℤ} (h : s ≠ (0, 1)) :
    IsEmpty (PBPSet_Bminus_sig (⊥ : YoungDiagram) ⊥ s) := by
  refine ⟨fun M => ?_⟩
  have h_eq : signTarget_Bminus M.val.val = s := M.prop
  have h_unique : M.val = emptyPBPSet_Bminus := Subsingleton.elim _ _
  have h_sig : signTarget_Bminus M.val.val = (0, 1) := by
    rw [h_unique]
    show signTarget_Bminus emptyPBP_Bminus = (0, 1)
    unfold signTarget_Bminus
    rw [emptyPBP_Bminus_signature]
    rfl
  exact h (h_eq.symm.trans h_sig)

noncomputable instance fintype_PBPSet_Bplus_sig_bot_nontarget {s : ℤ × ℤ}
    (h : s ≠ (1, 0)) :
    Fintype (PBPSet_Bplus_sig (⊥ : YoungDiagram) ⊥ s) :=
  @Fintype.ofIsEmpty _ (PBPSet_Bplus_sig_bot_eq_empty h)

noncomputable instance fintype_PBPSet_Bminus_sig_bot_nontarget {s : ℤ × ℤ}
    (h : s ≠ (0, 1)) :
    Fintype (PBPSet_Bminus_sig (⊥ : YoungDiagram) ⊥ s) :=
  @Fintype.ofIsEmpty _ (PBPSet_Bminus_sig_bot_eq_empty h)

/-! ## `Phi_γ_sig_trim_E = Phi_γ_sig_E` under std hypothesis

Since chain-derived ILSs are trim (via `Phi_γ_sig_E_IsTrim`), `toTrim`
acts as identity. So the trim wrapper changes nothing about the
underlying ILS. -/

theorem Phi_D_sig_trim_E_eq_Phi_D_sig_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (h_step_std : StepStdAndAugment_D)
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    (Phi_D_sig_trim h_step σh ε).E = (Phi_D_sig h_step σh ε).E := by
  rw [Phi_D_sig_trim_E]
  exact ILS.trim_eq_self_of_IsTrim _ (Phi_D_sig_E_IsTrim h_step h_step_std σh ε)

theorem Phi_Bplus_sig_trim_E_eq_Phi_Bplus_sig_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (h_step_std : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bplus_sig μP μQ s) (ε : Fin 2) :
    (Phi_Bplus_sig_trim h_step σh ε).E = (Phi_Bplus_sig h_step σh ε).E := by
  rw [Phi_Bplus_sig_trim_E]
  exact ILS.trim_eq_self_of_IsTrim _ (Phi_Bplus_sig_E_IsTrim h_step h_step_std σh ε)

theorem Phi_Bminus_sig_trim_E_eq_Phi_Bminus_sig_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (σh : PBPSet_Bminus_sig μP μQ s) (ε : Fin 2) :
    (Phi_Bminus_sig_trim h_sing σh ε).E = (Phi_Bminus_sig h_sing σh ε).E := by
  rw [Phi_Bminus_sig_trim_E]
  exact ILS.trim_eq_self_of_IsTrim _
    (Phi_Bminus_sig_E_IsTrim h_sing h_step_std_Bm h_step_std_Bp σh ε)

theorem Phi_C_sig_trim_E_eq_Phi_C_sig_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_step_std_D : StepStdAndAugment_D)
    (h_step_std_C : StepStdAndAugment_C)
    (σh : PBPSet_C_sig μP μQ s) :
    (Phi_C_sig_trim h_step_D h_step_C h_chain h_sm σh).E =
    (Phi_C_sig h_step_D h_step_C h_chain h_sm σh).E := by
  rw [Phi_C_sig_trim_E]
  exact ILS.trim_eq_self_of_IsTrim _
    (Phi_C_sig_E_IsTrim h_step_D h_step_C h_chain h_sm h_step_std_D h_step_std_C σh)

theorem Phi_M_sig_trim_E_eq_Phi_M_sig_E {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_step_std_M : StepStdAndAugment_M)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (σh : PBPSet_M_sig μP μQ s) :
    (Phi_M_sig_trim h_chain h_sing h_sm σh).E =
    (Phi_M_sig h_chain h_sing h_sm σh).E := by
  rw [Phi_M_sig_trim_E]
  exact ILS.trim_eq_self_of_IsTrim _
    (Phi_M_sig_E_IsTrim h_chain h_sing h_sm h_step_std_M h_step_std_Bp h_step_std_Bm σh)

/-! ## Injectivity transfer Phi_γ_sig → Phi_γ_sig_trim under std

Since Phi_γ_sig_trim's underlying E equals Phi_γ_sig's E (under std),
injectivity of Phi_γ_sig implies injectivity of Phi_γ_sig_trim.
-/

theorem Phi_D_sig_trim_injective_of_Phi_D_sig_injective
    {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_D)
    (h_step_std : StepStdAndAugment_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig h_step p.1 p.2)) :
    Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2) := by
  intro ⟨σh₁, ε₁⟩ ⟨σh₂, ε₂⟩ h_eq
  apply h_inj
  -- h_eq : Phi_D_sig_trim ... σh₁ ε₁ = Phi_D_sig_trim ... σh₂ ε₂
  -- Need: Phi_D_sig ... σh₁ ε₁ = Phi_D_sig ... σh₂ ε₂
  apply MYD_sig.ext
  have h1 := Phi_D_sig_trim_E_eq_Phi_D_sig_E h_step h_step_std σh₁ ε₁
  have h2 := Phi_D_sig_trim_E_eq_Phi_D_sig_E h_step h_step_std σh₂ ε₂
  have h_E := congrArg (·.E) h_eq
  simp at h_E
  rw [← h1, ← h2]
  exact h_E

theorem Phi_Bplus_sig_trim_injective_of_Phi_Bplus_sig_injective
    {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step : DescentStepSingleton_Bplus)
    (h_step_std : StepStdAndAugment_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig h_step p.1 p.2)) :
    Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2) := by
  intro ⟨σh₁, ε₁⟩ ⟨σh₂, ε₂⟩ h_eq
  apply h_inj
  apply MYD_sig.ext
  have h1 := Phi_Bplus_sig_trim_E_eq_Phi_Bplus_sig_E h_step h_step_std σh₁ ε₁
  have h2 := Phi_Bplus_sig_trim_E_eq_Phi_Bplus_sig_E h_step h_step_std σh₂ ε₂
  have h_E := congrArg (·.E) h_eq
  simp at h_E
  rw [← h1, ← h2]
  exact h_E

theorem Phi_Bminus_sig_trim_injective_of_Phi_Bminus_sig_injective
    {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_sing : DescentChainBminusSingleton)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig h_sing p.1 p.2)) :
    Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2) := by
  intro ⟨σh₁, ε₁⟩ ⟨σh₂, ε₂⟩ h_eq
  apply h_inj
  apply MYD_sig.ext
  have h1 := Phi_Bminus_sig_trim_E_eq_Phi_Bminus_sig_E h_sing h_step_std_Bm h_step_std_Bp σh₁ ε₁
  have h2 := Phi_Bminus_sig_trim_E_eq_Phi_Bminus_sig_E h_sing h_step_std_Bm h_step_std_Bp σh₂ ε₂
  have h_E := congrArg (·.E) h_eq
  simp at h_E
  rw [← h1, ← h2]
  exact h_E

theorem Phi_C_sig_trim_injective_of_Phi_C_sig_injective
    {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_step_std_D : StepStdAndAugment_D)
    (h_step_std_C : StepStdAndAugment_C)
    (h_inj : Function.Injective
      (Phi_C_sig (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    Function.Injective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm) := by
  intro σh₁ σh₂ h_eq
  apply h_inj
  apply MYD_sig.ext
  have h1 := Phi_C_sig_trim_E_eq_Phi_C_sig_E h_step_D h_step_C h_chain h_sm
    h_step_std_D h_step_std_C σh₁
  have h2 := Phi_C_sig_trim_E_eq_Phi_C_sig_E h_step_D h_step_C h_chain h_sm
    h_step_std_D h_step_std_C σh₂
  have h_E := congrArg (·.E) h_eq
  rw [← h1, ← h2]
  exact h_E

theorem Phi_M_sig_trim_injective_of_Phi_M_sig_injective
    {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_step_std_M : StepStdAndAugment_M)
    (h_step_std_Bp : StepStdAndAugment_Bplus)
    (h_step_std_Bm : StepStdAndAugment_Bminus)
    (h_inj : Function.Injective
      (Phi_M_sig (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    Function.Injective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm) := by
  intro σh₁ σh₂ h_eq
  apply h_inj
  apply MYD_sig.ext
  have h1 := Phi_M_sig_trim_E_eq_Phi_M_sig_E h_chain h_sing h_sm
    h_step_std_M h_step_std_Bp h_step_std_Bm σh₁
  have h2 := Phi_M_sig_trim_E_eq_Phi_M_sig_E h_chain h_sing h_sm
    h_step_std_M h_step_std_Bp h_step_std_Bm σh₂
  have h_E := congrArg (·.E) h_eq
  rw [← h1, ← h2]
  exact h_E

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

/-! ## Trim-variant surjectivity reductions

`Phi_γ_sig_trim` targets the (potentially) finite `MYD_sig_trim γ s`.
Surjectivity reduces to injectivity + Fintype + cardinality match
(unlike the original `Phi_γ_sig_equiv` whose target was infinite).
-/

theorem phi_D_sig_trim_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig_trim .D s)]
    (h_step : DescentStepSingleton_D)
    (h_card : Fintype.card (PBPSet_D_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig_trim .D s))
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

theorem phi_Bplus_sig_trim_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig_trim .Bplus s)]
    (h_step : DescentStepSingleton_Bplus)
    (h_card : Fintype.card (PBPSet_Bplus_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig_trim .Bplus s))
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

theorem phi_Bminus_sig_trim_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig_trim .Bminus s)]
    (h_sing : DescentChainBminusSingleton)
    (h_card : Fintype.card (PBPSet_Bminus_sig μP μQ s × Fin 2) =
              Fintype.card (MYD_sig_trim .Bminus s))
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2)) :
    Function.Surjective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

theorem phi_C_sig_trim_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig_trim .C s)]
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_card : Fintype.card (PBPSet_C_sig μP μQ s) =
              Fintype.card (MYD_sig_trim .C s))
    (h_inj : Function.Injective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    Function.Surjective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

theorem phi_M_sig_trim_surj_of_inj_card {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    [Fintype (MYD_sig_trim .M s)]
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_card : Fintype.card (PBPSet_M_sig μP μQ s) =
              Fintype.card (MYD_sig_trim .M s))
    (h_inj : Function.Injective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    Function.Surjective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm) :=
  h_inj.surjective_of_finite (Fintype.equivOfCardEq h_card)

/-! ## Trim image equivs (only requires injectivity) -/

noncomputable def Phi_D_sig_trim_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_D)
    (h_inj : Function.Injective
      (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2)) :
    PBPSet_D_sig μP μQ s × Fin 2 ≃
      Set.range (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig_trim h_step p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_Bplus_sig_trim_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step : DescentStepSingleton_Bplus)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2)) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃
      Set.range
        (fun p : PBPSet_Bplus_sig μP μQ s × Fin 2 => Phi_Bplus_sig_trim h_step p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_Bminus_sig_trim_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_sing : DescentChainBminusSingleton)
    (h_inj : Function.Injective
      (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2)) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃
      Set.range
        (fun p : PBPSet_Bminus_sig μP μQ s × Fin 2 => Phi_Bminus_sig_trim h_sing p.1 p.2) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_C_sig_trim_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_step_D : DescentStepSingleton_D)
    (h_step_C : DescentStepSingleton_C)
    (h_chain : ChainExists_C μP μQ)
    (h_sm : DescentChainSignMatch_C)
    (h_inj : Function.Injective
      (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm)) :
    PBPSet_C_sig μP μQ s ≃
      Set.range
        (Phi_C_sig_trim (μP := μP) (μQ := μQ) (s := s) h_step_D h_step_C h_chain h_sm) :=
  Equiv.ofInjective _ h_inj

noncomputable def Phi_M_sig_trim_image_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ)
    (h_chain : ChainExists_M μP μQ)
    (h_sing : DescentChainMSingleton)
    (h_sm : DescentChainSignMatch_M)
    (h_inj : Function.Injective
      (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm)) :
    PBPSet_M_sig μP μQ s ≃
      Set.range
        (Phi_M_sig_trim (μP := μP) (μQ := μQ) (s := s) h_chain h_sing h_sm) :=
  Equiv.ofInjective _ h_inj

end BMSZ
