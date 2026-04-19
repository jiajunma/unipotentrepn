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
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.Basic

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

/-- Parity preservation along D-type descent chain. -/
theorem descentChain_D_parity {τ : PBP} {chain : List ACStepData}
    {E : ILS}
    (_h_chain : IsDescentChain_D τ chain)
    (_h_sing : ChainSingleton (baseILS .D) chain E) :
    ∀ (j : ℕ) (h : j < E.length), MYDRowValid .D (j + 1) E[j] := by
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

/-! ## Ψ_D_sig

Inverse construction. Deferred to paper §11.14 algorithm: peel one
row of `M.E` at a time, run inverse theta-lift to recover one PBP
step, recurse on shifted ILS. Final assembly gives the source PBP.
-/

/-- **Ψ_D_sig** : `MYD_sig .D s → PBPSet_D_sig × Fin 2`. -/
noncomputable def Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (_M : MYD_sig .D s) :
    PBPSet_D_sig μP μQ s × Fin 2 := sorry

/-! ## Round trips -/

/-- `Ψ_D_sig (Φ_D_sig (σ, ε)) = (σ, ε)`. Uses
    `prop_11_15_PBP_D_injective_full` (existing) on the σ side. -/
theorem Psi_D_Phi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (σh : PBPSet_D_sig μP μQ s) (ε : Fin 2) :
    Psi_D_sig (μP := μP) (μQ := μQ) (Phi_D_sig σh ε) = (σh, ε) := by
  sorry

/-- `Φ_D_sig (Ψ_D_sig M) = M`. Surjectivity side; paper §11.14. -/
theorem Phi_D_Psi_D_sig {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (M : MYD_sig .D s) :
    let p := Psi_D_sig (μP := μP) (μQ := μQ) M
    Phi_D_sig p.1 p.2 = M := by
  sorry

/-! ## Equiv assembly -/

/-- **Main bijection** (D type, signature-based). -/
noncomputable def Phi_D_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    PBPSet_D_sig μP μQ s × Fin 2 ≃ MYD_sig .D s where
  toFun := fun ⟨σh, ε⟩ => Phi_D_sig σh ε
  invFun := Psi_D_sig (μP := μP) (μQ := μQ)
  left_inv := fun ⟨σh, ε⟩ => Psi_D_Phi_D_sig σh ε
  right_inv := fun M => Phi_D_Psi_D_sig M

/-! ## Signature targets for B⁺ / B⁻ / C / M -/

/-- Signature target for B⁺ PBP (parallel to `signTarget_D`). -/
noncomputable def signTarget_Bplus (τ : PBP) : ℤ × ℤ :=
  let s := PBP.signature τ; ((s.1 : ℤ), (s.2 : ℤ))

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

/-- **Paper Prop 11.15 (B⁺), signature variant**. -/
noncomputable def Phi_Bplus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    PBPSet_Bplus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bplus s := sorry

/-- **Paper Prop 11.15 (B⁻), signature variant**. -/
noncomputable def Phi_Bminus_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    PBPSet_Bminus_sig μP μQ s × Fin 2 ≃ MYD_sig .Bminus s := sorry

/-- **Paper Prop 11.17 (C), signature variant**. -/
noncomputable def Phi_C_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    PBPSet_C_sig μP μQ s ≃ MYD_sig .C s := sorry

/-- **Paper Prop 11.17 (M), signature variant**. -/
noncomputable def Phi_M_sig_equiv (μP μQ : YoungDiagram) (s : ℤ × ℤ) :
    PBPSet_M_sig μP μQ s ≃ MYD_sig .M s := sorry

end BMSZ
