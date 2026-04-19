/-
# M1.6: Constructive bijection extended to B⁺, B⁻, C, M types

Reference: NL proof at `lean/docs/blueprints/M1_6_extend_to_BCM.md`.

**Thin Phase A**: for B⁺, B⁻, C, M we axiomatize the top-level
`Equiv` directly (without the internal `IsDescentChain_γ` /
`Psi_γ` / round-trip decomposition that D type has). The full
decomposition for each γ is deferred to type-specific Phase B
milestones; each would follow the D template.

Paper references:
- B⁺, B⁻: Prop 11.15 (same as D, with source × Fin 2)
- C, M:   Prop 11.17 (source only; no Fin 2)
-/
import CombUnipotent.MYD.Bijection
import CombUnipotent.CountingProof.Basic

namespace BMSZ

/-! ## Shape-dp coherence predicates per γ -/

/-- B⁺ / B⁻ share the same shape-from-dp conventions. -/
def DPCoherent_B (μP μQ : YoungDiagram) (dp : DualPart) : Prop :=
  μP.colLens = dpartColLensP_B dp ∧ μQ.colLens = dpartColLensQ_B dp

def DPCoherent_Bplus : YoungDiagram → YoungDiagram → DualPart → Prop :=
  DPCoherent_B

def DPCoherent_Bminus : YoungDiagram → YoungDiagram → DualPart → Prop :=
  DPCoherent_B

def DPCoherent_C (μP μQ : YoungDiagram) (dp : DualPart) : Prop :=
  μP.colLens = dpartColLensP_C dp ∧ μQ.colLens = dpartColLensQ_C dp

def DPCoherent_M (μP μQ : YoungDiagram) (dp : DualPart) : Prop :=
  μP.colLens = dpartColLensP_M dp ∧ μQ.colLens = dpartColLensQ_M dp

/-! ## Paper Prop 11.15: B⁺ / B⁻ bijections

Identical signature to D's `Phi_D_equiv`: source has `× Fin 2`.
-/

/-- **Paper Prop 11.15 (B⁺)**: constructive bijection
    `PBPSet .Bplus μP μQ × Fin 2 ≃ MYD .Bplus (dpToSYD .Bplus dp)`.

    Phase A axiom; Phase B construction follows the D template with
    `doubleDescent_B_PBP` and `toACStepData_Bplus`. -/
axiom Phi_Bplus_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (_h_coh : DPCoherent_Bplus μP μQ dp) :
    PBPSet .Bplus μP μQ × Fin 2 ≃ MYD .Bplus (dpToSYD .Bplus dp)

/-- **Paper Prop 11.15 (B⁻)**: analogous to B⁺. -/
axiom Phi_Bminus_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (_h_coh : DPCoherent_Bminus μP μQ dp) :
    PBPSet .Bminus μP μQ × Fin 2 ≃ MYD .Bminus (dpToSYD .Bminus dp)

/-! ## Paper Prop 11.17: C / M bijections

Source has NO `Fin 2` factor — paper's C/M result doesn't need the
extra ε (the ε_℘ primitive pair choice absorbs the degree of
freedom).
-/

/-- **Paper Prop 11.17 (C)**: constructive bijection
    `PBPSet .C μP μQ ≃ MYD .C (dpToSYD .C dp)`.

    Phase A axiom. Phase B construction would use the C → D → C
    descent structure (single descent alternates types; double = C→C). -/
axiom Phi_C_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (_h_coh : DPCoherent_C μP μQ dp) :
    PBPSet .C μP μQ ≃ MYD .C (dpToSYD .C dp)

/-- **Paper Prop 11.17 (M = C̃)**: analogous to C. -/
axiom Phi_M_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (_h_coh : DPCoherent_M μP μQ dp) :
    PBPSet .M μP μQ ≃ MYD .M (dpToSYD .M dp)

end BMSZ
