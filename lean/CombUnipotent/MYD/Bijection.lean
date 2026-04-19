/-
# M1.5 Phase A: constructive bijection PBPSet × Fin 2 ≃ MYD

Reference: NL proof at `lean/docs/blueprints/M1_5_bijection.md`
(3-pass self-reviewed, 2026-04-19).

**Phase A (this file)**: state the inverse `Psi_D` and round-trip
identities as axioms, construct `Phi_D_equiv` as a genuine
`Equiv`.

**Phase B (future, M1.5.1+)**: prove the three axioms by
implementing paper §11.14's algorithmic inverse construction (un-truncate,
un-twist, recurse) and the round-trip induction.

Coherence hypothesis: the external `μP`, `μQ` must be compatible with
`dp` (i.e., `μP.colLens = dpartColLensP_D dp` and similarly for `μQ`).
This is required for the bijection to be between non-trivially related
finite sets.
-/
import CombUnipotent.MYD.PhiDTyped
import CombUnipotent.CountingProof.Basic

namespace BMSZ

/-- Coherence between external shapes `μP, μQ` and the dual partition `dp`.
    Alias for `PBPIsCoherent_D_ext` (defined in PhiDTyped.lean) to keep
    the API at this layer readable. -/
@[reducible] def DPCoherent_D : YoungDiagram → YoungDiagram → DualPart → Prop :=
  PBPIsCoherent_D_ext

/-- **Inverse map** `Psi_D : MYD .D O → PBPSet .D μP μQ × Fin 2`.

    TODO: paper §11.14 algorithmic construction — iterate inverse
    theta-lift, un-truncate + un-twist + recurse until hitting the
    base MYD, then assemble the PBP by augmenting inner-to-outer. -/
noncomputable def Psi_D {μP μQ : YoungDiagram} (dp : DualPart)
    (_h_coh : DPCoherent_D μP μQ dp)
    (_E : MYD .D (dpToSYD .D dp)) :
    PBPSet .D μP μQ × Fin 2 := sorry

/-- `Psi_D ∘ Phi_D = id` on the source side.

    TODO: induction on the chain — each descent step of `Phi_D` is
    exactly reversed by the inverse-theta-lift step of `Psi_D`. -/
theorem Psi_D_Phi_D {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp)
    (hsort : dp.SortedGE) (hodd : ∀ r ∈ dp, Odd r)
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    Psi_D dp h_coh (Phi_D dp h_coh hsort hodd σ ε) = (σ, ε) := by
  sorry

/-- `Phi_D ∘ Psi_D = id` on the target side.

    TODO: symmetric to `Psi_D_Phi_D`; follows from paper's surjectivity
    (§11.14). -/
theorem Phi_D_Psi_D {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp)
    (hsort : dp.SortedGE) (hodd : ∀ r ∈ dp, Odd r)
    (E : MYD .D (dpToSYD .D dp)) :
    let ⟨σ, ε⟩ := Psi_D dp h_coh E
    Phi_D dp h_coh hsort hodd σ ε = E := by
  sorry

/-- **Main theorem (M1.5)**: constructive bijection
    `PBPSet .D μP μQ × Fin 2 ≃ MYD .D (dpToSYD .D dp)`.

    Constructed from the three interface axioms. The `Equiv` is
    non-computable because `Phi_D` internally uses `Classical.choose`
    on the M1.4 existence axioms. -/
noncomputable def Phi_D_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_D μP μQ dp)
    (hsort : dp.SortedGE) (hodd : ∀ r ∈ dp, Odd r) :
    PBPSet .D μP μQ × Fin 2 ≃ MYD .D (dpToSYD .D dp) where
  toFun := fun ⟨σ, ε⟩ => Phi_D dp h_coh hsort hodd σ ε
  invFun := Psi_D dp h_coh
  left_inv := fun ⟨σ, ε⟩ => Psi_D_Phi_D dp h_coh hsort hodd σ ε
  right_inv := fun E => Phi_D_Psi_D dp h_coh hsort hodd E

-- **Corollary** (commented out — pending Fintype (MYD γ O)):
-- `|PBPSet × Fin 2| = |MYD|` follows via `Fintype.card_congr` once
-- `MYD .D (dpToSYD .D dp)` has a Fintype instance. That instance
-- needs to prove the MYD subtype is bounded — deferred to a later
-- milestone where we enumerate MYD via bounded ILS search.
--
-- theorem card_PBPSet_D_Fin2_eq_card_MYD {μP μQ : YoungDiagram}
--     (dp : DualPart) (h_coh : DPCoherent_D μP μQ dp) :
--     Fintype.card (PBPSet .D μP μQ × Fin 2) =
--     Fintype.card (MYD .D (dpToSYD .D dp)) :=
--   Fintype.card_congr (Phi_D_equiv dp h_coh)

end BMSZ
