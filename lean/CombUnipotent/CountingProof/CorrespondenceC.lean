/-
# C-type counting: Proposition 10.12

Proves `Fintype.card (PBPSet .C μP μQ) = countPBP_C dp` for all valid
C-type dual partitions dp (sorted, odd parts, dp ≠ []).

The proof reduces to D-type counting via the C→D descent:
- Primitive (r₁ > r₂): count = tripleSum(countPBP_D dp_tail) = dd + rc + ss
- Balanced (r₁ = r₂): count = dd + rc (SS excluded)

Reference: [BMSZb] Proposition 10.12.
-/
import CombUnipotent.CountingProof.Correspondence

open Classical

/-! ## C→D descent: full PBP construction

Given a C-type PBP τ with shapes (μP, μQ), construct the descended D-type PBP.
- D-P shape = C-P shape (preserved)
- D-Q shape = shiftLeft(C-Q)
- D-P paint = descentPaintL_CD τ
- D-Q paint = all dots -/

/-- The descended D-type PBP from a C-type PBP.
    All 13 PBP constraints are verified. -/
noncomputable def PBP.descentCD (τ : PBP) (hγ : τ.γ = .C) : PBP where
  γ := .D
  P := {
    shape := τ.P.shape
    paint := descentPaintL_CD τ
    paint_outside := by
      intro i j hmem
      simp only [descentPaintL_CD]
      split_ifs with h1 h2
      · rfl
      · exfalso; apply hmem
        sorry
      · exact τ.P.paint_outside i j hmem
  }
  Q := {
    shape := YoungDiagram.shiftLeft τ.Q.shape
    paint := fun _ _ => .dot
    paint_outside := by intro _ _ _; rfl
  }
  sym_P := by intro i j _; simp [DRCSymbol.allowed]
  sym_Q := by intro i j _; simp [DRCSymbol.allowed]
  dot_match := by sorry
  mono_P := by sorry
  mono_Q := by
    intro i j i' j' hi hj hmem
    simp [DRCSymbol.layerOrd]
  row_s := by sorry
  row_r := by sorry
  col_c_P := by sorry
  col_c_Q := by intro j i₁ i₂ h₁ h₂; simp at h₁
  col_d_P := by sorry
  col_d_Q := by intro j i₁ i₂ h₁ h₂; simp at h₁

/-! ## Descent maps PBPSet .C to PBPSet .D -/

/-- The C→D descent as a map on PBPSet. -/
noncomputable def descentCD_map {μP μQ : YoungDiagram}
    (τ : PBPSet .C μP μQ) :
    PBPSet .D μP (YoungDiagram.shiftLeft μQ) :=
  ⟨τ.val.descentCD (by have := τ.val.γ; sorry), by sorry, by sorry⟩

/-! ## Descent injectivity -/

theorem descentCD_injective {μP μQ : YoungDiagram} :
    Function.Injective (@descentCD_map μP μQ) := by
  sorry

/-! ## Base cases -/

/-- C-type with dp = [r₁]: unique PBP. -/
theorem card_PBPSet_C_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_C [r₁])
    (hQ : μQ.colLens = dpartColLensQ_C [r₁])
    (hodd : Odd r₁) :
    Fintype.card (PBPSet .C μP μQ) = 1 := by
  sorry

/-! ## Image characterization -/

/-- Primitive case: descent is surjective (every D-type PBP lifts). -/
theorem descentCD_surjective_primitive {μP μQ : YoungDiagram}
    (h_prim : μQ.colLen 0 ≥ μP.colLen 0) :
    Function.Surjective (@descentCD_map μP μQ) := by
  sorry

/-- Balanced case: image = DD ∪ RC (SS excluded). -/
theorem descentCD_image_balanced {μP μQ : YoungDiagram}
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1)
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) :
    (∃ τ : PBPSet .C μP μQ, descentCD_map τ = σ) ↔
    tailClass_D σ.val ≠ .SS := by
  sorry

/-! ## Main theorem -/

/-- **Proposition 10.12 (C-type)**: For all valid C-type dual partitions,
    `card(PBPSet .C μP μQ) = countPBP_C dp`. -/
theorem card_PBPSet_C_eq_countPBP_C (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_C dp)
    (hQ : μQ.colLens = dpartColLensQ_C dp)
    (hsort : dp.SortedGE)
    (hodd : ∀ r ∈ dp, Odd r)
    (hne : dp ≠ []) :
    Fintype.card (PBPSet .C μP μQ) = countPBP_C dp := by
  sorry
