/-
# Quasi-distinguished restricted bijection (refactor stub)

Per paper [BMSZ] Lemma 11.14: the bijection `PBP × Fin 2 ≃ MYD`
holds only for **quasi-distinguished** orbits Ǒ. The current
`MYD_sig γ s` formulation without quasi-distinguished restriction
admits counterexamples to parity (documented in memory
`project_parity_requires_quasi_distinguished.md`).

This file introduces a quasi-distinguished-restricted type
`PBPSet_γ_qd μP μQ dp (h_coh, h_qd, ...)` that scopes the
bijection to the valid setting.

**Status**: scaffolding only. Full integration requires updating
`IsDescentChain_γ`, `Phi_γ_sig_equiv`, etc., to thread the
quasi-distinguished hypothesis. Deferred to future session.
-/
import CombUnipotent.MYD.BijectionSig
import CombUnipotent.MYD.DPToSYD

namespace BMSZ

/-! ## Quasi-distinguished PBPSet subtypes -/

/-- PBPSet refined by dp coherence + quasi-distinguished + signature match.
    This is the paper-valid source for `Phi_γ` bijection (Lemma 11.14/Prop 11.15). -/
def PBPSet_D_qd (μP μQ : YoungDiagram) (dp : DualPart)
    (_h_coh : PBPIsCoherent_D_ext μP μQ dp)
    (_hsort : dp.SortedGE)
    (_hodd : ∀ r ∈ dp, Odd r)
    (_h_qd : IsQuasiDistinguished .D dp) : Type :=
  PBPSet .D μP μQ

/-- Refined with signature too. -/
def PBPSet_D_qd_sig (μP μQ : YoungDiagram) (dp : DualPart)
    (_h_coh : PBPIsCoherent_D_ext μP μQ dp)
    (_hsort : dp.SortedGE)
    (_hodd : ∀ r ∈ dp, Odd r)
    (_h_qd : IsQuasiDistinguished .D dp) (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .D μP μQ // signTarget_D σ.val = s }

/-! ## Quasi-distinguished bijection (deferred)

The proper statement of paper Prop 11.15 (D type, signature level):
```
Phi_D_qd_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (h_coh : ...) (h_qd : IsQuasiDistinguished .D dp) (s : ℤ × ℤ) :
    PBPSet_D_qd_sig μP μQ dp h_coh hsort hodd h_qd s × Fin 2 ≃ MYD_sig .D s
```

Under quasi-distinguished restriction:
- `descentChain_D_parity` becomes provable (paper §9.4 uses QD)
- `Phi_D_qd_injective` follows from `prop_11_15_PBP_D_injective_full`
- `Phi_D_qd_surjective` follows from paper Lemma 11.14 algorithm

Deferred: full refactor requires updating `IsDescentChain_D` to carry
QD predicate through each step and proving doubleDescent preserves QD.
-/

noncomputable def Phi_D_qd_sig_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (h_coh : PBPIsCoherent_D_ext μP μQ dp)
    (hsort : dp.SortedGE)
    (hodd : ∀ r ∈ dp, Odd r)
    (h_qd : IsQuasiDistinguished .D dp) (s : ℤ × ℤ)
    [Inhabited (PBPSet_D_qd_sig μP μQ dp h_coh hsort hodd h_qd s × Fin 2)] :
    PBPSet_D_qd_sig μP μQ dp h_coh hsort hodd h_qd s × Fin 2 ≃ MYD_sig .D s := by
  sorry

-- B+/B-/C/M QD refinements

def PBPSet_Bplus_qd_sig (μP μQ : YoungDiagram) (dp : DualPart)
    (_hsort : dp.SortedGE) (_h_qd : IsQuasiDistinguished .Bplus dp)
    (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .Bplus μP μQ // signTarget_Bplus σ.val = s }

def PBPSet_Bminus_qd_sig (μP μQ : YoungDiagram) (dp : DualPart)
    (_hsort : dp.SortedGE) (_h_qd : IsQuasiDistinguished .Bminus dp)
    (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .Bminus μP μQ // signTarget_Bminus σ.val = s }

def PBPSet_C_qd_sig (μP μQ : YoungDiagram) (dp : DualPart)
    (_hsort : dp.SortedGE) (_h_qd : IsQuasiDistinguished .C dp)
    (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .C μP μQ // signTarget_C σ.val = s }

def PBPSet_M_qd_sig (μP μQ : YoungDiagram) (dp : DualPart)
    (_hsort : dp.SortedGE) (_h_qd : IsQuasiDistinguished .M dp)
    (s : ℤ × ℤ) : Type :=
  { σ : PBPSet .M μP μQ // signTarget_M σ.val = s }

noncomputable def Phi_Bplus_qd_sig_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (hsort : dp.SortedGE) (h_qd : IsQuasiDistinguished .Bplus dp) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bplus_qd_sig μP μQ dp hsort h_qd s × Fin 2)] :
    PBPSet_Bplus_qd_sig μP μQ dp hsort h_qd s × Fin 2 ≃ MYD_sig .Bplus s :=
  sorry

noncomputable def Phi_Bminus_qd_sig_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (hsort : dp.SortedGE) (h_qd : IsQuasiDistinguished .Bminus dp) (s : ℤ × ℤ)
    [Inhabited (PBPSet_Bminus_qd_sig μP μQ dp hsort h_qd s × Fin 2)] :
    PBPSet_Bminus_qd_sig μP μQ dp hsort h_qd s × Fin 2 ≃ MYD_sig .Bminus s :=
  sorry

noncomputable def Phi_C_qd_sig_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (hsort : dp.SortedGE) (h_qd : IsQuasiDistinguished .C dp) (s : ℤ × ℤ)
    [Inhabited (PBPSet_C_qd_sig μP μQ dp hsort h_qd s)] :
    PBPSet_C_qd_sig μP μQ dp hsort h_qd s ≃ MYD_sig .C s :=
  sorry

noncomputable def Phi_M_qd_sig_equiv (μP μQ : YoungDiagram) (dp : DualPart)
    (hsort : dp.SortedGE) (h_qd : IsQuasiDistinguished .M dp) (s : ℤ × ℤ)
    [Inhabited (PBPSet_M_qd_sig μP μQ dp hsort h_qd s)] :
    PBPSet_M_qd_sig μP μQ dp hsort h_qd s ≃ MYD_sig .M s :=
  sorry

end BMSZ
