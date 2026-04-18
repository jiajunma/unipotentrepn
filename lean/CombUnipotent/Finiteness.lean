/-
# Finiteness of PBP sets

For fixed shapes and type, the set of PBPs is finite.

The proof uses the injection PBP ↦ (paint_P restricted to cells, paint_Q restricted to cells),
which maps into a finite type (cells → DRCSymbol) × (cells → DRCSymbol).
-/
import CombUnipotent.PBP
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

-- Fintype for Pi types from Finset subtypes to DRCSymbol.
-- Must be stated early before any conflicting instances from Mathlib.
instance instFintypeCellsPaint (μ : YoungDiagram) :
    Fintype (↥μ.cells → DRCSymbol) := inferInstance

/-! ## Restricted painting -/

/-- Restrict a PYD's paint to cells of a given shape. -/
def PaintedYoungDiagram.restrict (D : PaintedYoungDiagram) (μ : YoungDiagram)
    (_h : D.shape = μ) : ↥μ.cells → DRCSymbol :=
  fun ⟨(i, j), _⟩ => D.paint i j

/-! ## Extensionality -/

theorem PaintedYoungDiagram.ext' {D₁ D₂ : PaintedYoungDiagram}
    (h_shape : D₁.shape = D₂.shape) (h_paint : D₁.paint = D₂.paint) :
    D₁ = D₂ := by
  cases D₁; cases D₂; simp only [mk.injEq]; exact ⟨h_shape, h_paint⟩

theorem PBP.ext'' {τ₁ τ₂ : PBP}
    (hγ : τ₁.γ = τ₂.γ) (hP : τ₁.P = τ₂.P) (hQ : τ₁.Q = τ₂.Q) :
    τ₁ = τ₂ := by
  cases τ₁; cases τ₂; simp only [PBP.mk.injEq]; exact ⟨hγ, hP, hQ⟩

/-! ## Injectivity of restrict -/

theorem PaintedYoungDiagram.restrict_injective
    {D₁ D₂ : PaintedYoungDiagram} {μ : YoungDiagram}
    (h₁ : D₁.shape = μ) (h₂ : D₂.shape = μ)
    (h : D₁.restrict μ h₁ = D₂.restrict μ h₂) : D₁ = D₂ := by
  apply PaintedYoungDiagram.ext' (h₁.trans h₂.symm)
  ext i j
  by_cases hm : (i, j) ∈ μ
  · exact congr_fun h ⟨(i,j), (YoungDiagram.mem_cells _).mpr hm⟩
  · rw [D₁.paint_outside i j (by rw [h₁]; exact hm),
        D₂.paint_outside i j (by rw [h₂]; exact hm)]

/-! ## PBPSet and Fintype -/

def PBPSet (γ : RootType) (μP μQ : YoungDiagram) :=
  {τ : PBP // τ.γ = γ ∧ τ.P.shape = μP ∧ τ.Q.shape = μQ}

theorem PBPSet.restrict_injective (γ : RootType) (μP μQ : YoungDiagram) :
    Function.Injective (fun (x : PBPSet γ μP μQ) =>
      (x.val.P.restrict μP x.prop.2.1, x.val.Q.restrict μQ x.prop.2.2)) := by
  intro ⟨τ₁, hγ₁, hP₁, hQ₁⟩ ⟨τ₂, hγ₂, hP₂, hQ₂⟩ h
  simp only [Prod.mk.injEq] at h
  apply Subtype.ext; apply PBP.ext''
  · rw [hγ₁, hγ₂]
  · exact PaintedYoungDiagram.restrict_injective hP₁ hP₂ h.1
  · exact PaintedYoungDiagram.restrict_injective hQ₁ hQ₂ h.2

-- Provide Fintype and Finite for the injection target
instance instFintypePaintProd (μP μQ : YoungDiagram) :
    Fintype ((↥μP.cells → DRCSymbol) × (↥μQ.cells → DRCSymbol)) :=
  instFintypeProd _ _

instance instFinitePaintProd (μP μQ : YoungDiagram) :
    Finite ((↥μP.cells → DRCSymbol) × (↥μQ.cells → DRCSymbol)) :=
  Finite.of_fintype _

instance instFinitePBPSet (γ : RootType) (μP μQ : YoungDiagram) :
    Finite (PBPSet γ μP μQ) :=
  Finite.of_injective _ (PBPSet.restrict_injective γ μP μQ)

noncomputable instance instFintypePBPSet (γ : RootType) (μP μQ : YoungDiagram) :
    Fintype (PBPSet γ μP μQ) :=
  Fintype.ofFinite _
