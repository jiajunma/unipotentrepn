/-
# M1.7: `Fintype (MYD γ O)` instances + cardinality theorems

Reference: NL proof at `lean/docs/blueprints/M1_7_Fintype_MYD.md`.

Uses the `Phi_γ_equiv` from M1.5 / M1.6 to derive `Fintype (MYD γ O)`
via `Fintype.ofEquiv`. Then card equalities are immediate from
`Fintype.card_congr`.

The Fintype instances are `noncomputable` (inherited from the
`noncomputable` Phi_γ_equiv axioms).
-/
import CombUnipotent.MYD.Bijection
import CombUnipotent.MYD.BijectionBCM
import Mathlib.SetTheory.Cardinal.Finite

namespace BMSZ

/-! ## Fintype instances for MYD γ O via the bijections -/

/-- `MYD .D (dpToSYD .D dp)` is finite via the `Phi_D_equiv` bijection. -/
noncomputable def fintype_MYD_D {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp) :
    Fintype (MYD .D (dpToSYD .D dp)) :=
  Fintype.ofEquiv _ (Phi_D_equiv dp h_coh)

/-- Similarly for `.Bplus`. -/
noncomputable def fintype_MYD_Bplus {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_Bplus μP μQ dp) :
    Fintype (MYD .Bplus (dpToSYD .Bplus dp)) :=
  Fintype.ofEquiv _ (Phi_Bplus_equiv dp h_coh)

/-- `.Bminus`. -/
noncomputable def fintype_MYD_Bminus {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_Bminus μP μQ dp) :
    Fintype (MYD .Bminus (dpToSYD .Bminus dp)) :=
  Fintype.ofEquiv _ (Phi_Bminus_equiv dp h_coh)

/-- `.C`. -/
noncomputable def fintype_MYD_C {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_C μP μQ dp) :
    Fintype (MYD .C (dpToSYD .C dp)) :=
  Fintype.ofEquiv _ (Phi_C_equiv dp h_coh)

/-- `.M`. -/
noncomputable def fintype_MYD_M {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_M μP μQ dp) :
    Fintype (MYD .M (dpToSYD .M dp)) :=
  Fintype.ofEquiv _ (Phi_M_equiv dp h_coh)

/-! ## Cardinality equalities

Paper Prop 11.15 card-content for B/D, Prop 11.17 for C/M.
-/

/-- **Paper Prop 11.15 card content (D)**: `|PBPSet .D × Fin 2| = |MYD .D|`. -/
theorem card_PBPSet_D_Fin2_eq_MYD {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp) :
    Nat.card (PBPSet .D μP μQ × Fin 2) =
    Nat.card (MYD .D (dpToSYD .D dp)) :=
  Nat.card_congr (Phi_D_equiv dp h_coh)

/-- **Paper Prop 11.15 card content (B⁺)**. -/
theorem card_PBPSet_Bplus_Fin2_eq_MYD {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_Bplus μP μQ dp) :
    Nat.card (PBPSet .Bplus μP μQ × Fin 2) =
    Nat.card (MYD .Bplus (dpToSYD .Bplus dp)) :=
  Nat.card_congr (Phi_Bplus_equiv dp h_coh)

/-- **Paper Prop 11.15 card content (B⁻)**. -/
theorem card_PBPSet_Bminus_Fin2_eq_MYD {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_Bminus μP μQ dp) :
    Nat.card (PBPSet .Bminus μP μQ × Fin 2) =
    Nat.card (MYD .Bminus (dpToSYD .Bminus dp)) :=
  Nat.card_congr (Phi_Bminus_equiv dp h_coh)

/-- **Paper Prop 11.17 card content (C)**: `|PBPSet .C| = |MYD .C|`. -/
theorem card_PBPSet_C_eq_MYD {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_C μP μQ dp) :
    Nat.card (PBPSet .C μP μQ) =
    Nat.card (MYD .C (dpToSYD .C dp)) :=
  Nat.card_congr (Phi_C_equiv dp h_coh)

/-- **Paper Prop 11.17 card content (M = C̃)**. -/
theorem card_PBPSet_M_eq_MYD {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_M μP μQ dp) :
    Nat.card (PBPSet .M μP μQ) =
    Nat.card (MYD .M (dpToSYD .M dp)) :=
  Nat.card_congr (Phi_M_equiv dp h_coh)

end BMSZ
