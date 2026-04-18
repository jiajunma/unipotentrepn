/-
# [BMSZb] Section 10: explicit named wrappers

This file aliases the counting/descent theorems to the exact proposition
numbers used in the paper [BMSZb, Section 10], so that downstream users can
cite `prop_10_11_B`, `cor_10_10_D`, etc. by name.

Scope: ★ ∈ {B, D, C, M = C̃}. The C*/D* real-form variants are omitted per
the audit directive (they mirror B/D with quaternionic non-existence of
Prop 10.1).

Each wrapper is a *definitional* alias: the underlying theorem is fully
proved elsewhere (see references in each doc-comment). No new proof
obligations are introduced here.

Reference: papers/BMSZ_counting_reduction_v4.pdf, Section 10 (pp. 63-74).
-/
import CombUnipotent.CountingProof.Prop10_8_M
import CombUnipotent.CountingProof.CorrespondenceC

open Classical

/-! ## Proposition 10.2 — PP independence (shape shifting) -/

/-- **Proposition 10.2 (M type)** — PBP count is independent of the PP set.

    Expressed as the shape-shifting bijection
    `#PBP_M(μP, μQ) = #PBP_M(μP', μQ')` for shapes that swap column 0.
    This is the operational content of Prop 10.2 for the M case.

    Reference: [BMSZb] Proposition 10.2 / Lemma 10.3. -/
theorem prop_10_2_PBP_M {μP μQ μP' μQ' : YoungDiagram}
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ μQ)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ μP)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ μP)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ μQ) :
    Fintype.card (PBPSet .M μP μQ) = Fintype.card (PBPSet .M μP' μQ') :=
  card_PBPSet_M_shapeShift hP'0 hP'S hQ'0 hQ'S

/-! ## Lemma 10.3 — shape shifting involution (M / C̃) -/

/-- **Lemma 10.3 (M type)** — the shape-shift map on PBPs is an involution.

    Applying `shapeShiftM` twice returns the original PBP. This is the
    structural content underlying Prop 10.2 for M.

    Reference: [BMSZb] Lemma 10.3. -/
theorem lemma_10_3_M (τ : PBP) (hγ : τ.γ = .M)
    (μP' μQ' : YoungDiagram)
    (hP'0 : ∀ i, (i, 0) ∈ μP' ↔ (i, 0) ∈ τ.Q.shape)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ τ.P.shape)
    (hQ'0 : ∀ i, (i, 0) ∈ μQ' ↔ (i, 0) ∈ τ.P.shape)
    (hQ'S : ∀ i j, (i, j + 1) ∈ μQ' ↔ (i, j + 1) ∈ τ.Q.shape) :
    shapeShiftM (shapeShiftM τ hγ μP' μQ' hP'0 hP'S hQ'0 hQ'S) rfl
      τ.P.shape τ.Q.shape
      (fun i => by simp [shapeShiftM]; exact (hQ'0 i).symm)
      (fun i j => by simp [shapeShiftM]; exact (hP'S i j).symm)
      (fun i => by simp [shapeShiftM]; exact (hP'0 i).symm)
      (fun i j => by simp [shapeShiftM]; exact (hQ'S i j).symm) = τ :=
  shapeShiftM_involution τ hγ μP' μQ' hP'0 hP'S hQ'0 hQ'S

/-! ## Lemma 10.4 / 10.5 — naive descent uniqueness -/

/-- **Lemma 10.4 (C type)** — the C→D descent is injective on PBPSet.

    Reference: [BMSZb] Lemma 10.4. -/
theorem lemma_10_4_C {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    Function.Injective (descentCD_PBP · h_sub : PBPSet .C μP μQ → _) :=
  descentCD_injective h_sub

/-- **Lemma 10.5 (M type)** — the M→B descent on PBPs is injective.

    More precisely: if two M-type PBPs with the same shapes have the same
    descent paint, they are equal. This is the uniqueness half of Lemma 10.5
    for the M case (the existence half is `descentMB_liftMB_round_trip`).

    Reference: [BMSZb] Lemma 10.5. -/
theorem lemma_10_5_M (μP μQ : YoungDiagram)
    (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .M) (hγ₂ : τ₂.γ = .M)
    (hshapeP : τ₁.P.shape = μP) (hshapeQ : τ₁.Q.shape = μQ)
    (hshapeP' : τ₂.P.shape = μP) (hshapeQ' : τ₂.Q.shape = μQ)
    (h_desc_eq : descentMB_PBP τ₁ hγ₁ = descentMB_PBP τ₂ hγ₂) :
    τ₁ = τ₂ := by
  -- Extract equality of PBPSet elements via descentMB_injective.
  have h_eq := descentMB_injective μP μQ
    (⟨τ₁, hγ₁, hshapeP, hshapeQ⟩ : PBPSet .M μP μQ)
    (⟨τ₂, hγ₂, hshapeP', hshapeQ'⟩ : PBPSet .M μP μQ)
    (by simpa using h_desc_eq)
  exact congrArg Subtype.val h_eq

/-- **Lemma 10.5 (D type)** — the double descent D→C→D is injective on PBPSet
    modulo signature and epsilon.

    Reference: [BMSZb] Lemma 10.5. -/
theorem lemma_10_5_D {μP μQ : YoungDiagram} (τ₁ τ₂ : PBPSet .D μP μQ)
    (hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val i j = PBP.doubleDescent_D_paintL τ₂.val i j)
    (hsig : PBP.signature τ₁.val = PBP.signature τ₂.val)
    (heps : PBP.epsilon τ₁.val = PBP.epsilon τ₂.val) :
    τ₁ = τ₂ :=
  doubleDescent_D_injective_on_PBPSet τ₁ τ₂ hdd hsig heps

/-! ## Proposition 10.8 — descent bijective (primitive) / injective (balanced) -/

/-- **Proposition 10.8(a) (C type, primitive case)** — when
    `μQ.colLen 0 ≥ μP.colLen 0`, the C→D descent is a bijection
    onto `PBPSet .D μP (μQ.shiftLeft)`.

    Expressed as cardinality equality.
    Reference: [BMSZb] Proposition 10.8(a) for C. -/
theorem prop_10_8_C_primitive {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_prim : μQ.colLen 0 ≥ μP.colLen 0) :
    Fintype.card (PBPSet .C μP μQ) =
      Fintype.card (PBPSet .D μP (YoungDiagram.shiftLeft μQ)) :=
  card_C_eq_card_D_primitive h_sub h_prim

/-- **Proposition 10.8(b) (C type, balanced case)** — when
    `μP.colLen 0 = μQ.colLen 0 + 1`, the C→D descent is injective with
    image equal to `{σ ∈ D | tailClass_D σ ∈ {DD, RC}}`.

    Reference: [BMSZb] Proposition 10.8(b) for C. -/
theorem prop_10_8_C_balanced {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1) :
    Fintype.card (PBPSet .C μP μQ) =
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card +
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card :=
  card_C_eq_DD_plus_RC_balanced h_sub h_bal

/-- **Proposition 10.8(a) (M = C̃ type, primitive case)** — when
    `μP.colLen 0 > μQ.colLen 0`, the M→B descent is a bijection onto
    `PBPSet .Bplus (μP.shiftLeft) μQ ⊕ PBPSet .Bminus (μP.shiftLeft) μQ`.

    Reference: [BMSZb] Proposition 10.8(a) for M. -/
theorem prop_10_8_M_primitive {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_prim : μP.colLen 0 > μQ.colLen 0) :
    Fintype.card (PBPSet .M μP μQ) =
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ) +
      Fintype.card (PBPSet .Bminus μP.shiftLeft μQ) :=
  descent_bijective_primitive h_sub h_QleP h_prim

/-- **Proposition 10.8(b) (M = C̃ type, balanced case)** — when
    `μP.colLen 0 = μQ.colLen 0 > 0`, the M→B descent is injective;
    the image is all of B⁺ plus the `{σ.Q(bottom, 0).layerOrd > 1}` subset of B⁻.

    Reference: [BMSZb] Proposition 10.8(b) for M. -/
theorem prop_10_8_M_balanced {μP μQ : YoungDiagram}
    (h_sub : μP.shiftLeft ≤ μQ) (h_QleP : μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0) (h_pos : μP.colLen 0 > 0) :
    Fintype.card (PBPSet .M μP μQ) =
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ) +
      (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card :=
  descent_image_balanced h_sub h_QleP h_bal h_pos

/-! ## Proposition 10.9 — double descent (B, D) -/

/-- **Proposition 10.9 (D type)** — the double descent
    `τ ↦ (∇²τ, signature τ, epsilon τ)` is injective on `PBPSet .D μP μQ`.

    Reference: [BMSZb] Proposition 10.9 for D. -/
theorem prop_10_9_D (τ₁ τ₂ : PBP)
    (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁ i j = PBP.doubleDescent_D_paintL τ₂ i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) :=
  PBP.ddescent_inj_D τ₁ τ₂ hγ₁ hγ₂ hshapeP hshapeQ hdd hsig heps

/-- **Proposition 10.9 (B type)** — for fixed γ ∈ {B⁺, B⁻}, the double descent
    `τ ↦ (∇²τ, signature τ, epsilon τ)` is injective on `PBPSet .γ μP μQ`.

    Reference: [BMSZb] Proposition 10.9 for B. -/
theorem prop_10_9_B (τ₁ τ₂ : PBP)
    (hγ : τ₁.γ = .Bplus ∨ τ₁.γ = .Bminus)
    (hγ_eq : τ₁.γ = τ₂.γ)
    (hshapeP : τ₁.P.shape = τ₂.P.shape)
    (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (hinterl₁ : ∀ j, PBP.dotScolLen τ₁.P j ≥ PBP.dotScolLen τ₁.Q (j + 1))
    (hinterl₂ : ∀ j, PBP.dotScolLen τ₂.P j ≥ PBP.dotScolLen τ₂.Q (j + 1))
    (hddL : ∀ i j, PBP.doubleDescent_B_paintL τ₁ i j = PBP.doubleDescent_B_paintL τ₂ i j)
    (hddR : ∀ i j, PBP.doubleDescent_B_paintR τ₁ i j = PBP.doubleDescent_B_paintR τ₂ i j)
    (hsig : PBP.signature τ₁ = PBP.signature τ₂)
    (heps : PBP.epsilon τ₁ = PBP.epsilon τ₂) :
    (∀ i j, τ₁.P.paint i j = τ₂.P.paint i j) ∧
    (∀ i j, τ₁.Q.paint i j = τ₂.Q.paint i j) :=
  PBP.ddescent_inj_B τ₁ τ₂ hγ hγ_eq hshapeP hshapeQ hinterl₁ hinterl₂ hddL hddR hsig heps

/-! ## Corollary 10.10 — injectivity via descent + Sign (B, D) -/

/-- **Corollary 10.10 (D type)** — on `PBPSet .D μP μQ`, the map
    `τ ↦ (∇²τ, signature τ, epsilon τ)` is injective (as elements of PBPSet).

    This is the PBPSet-level wrapper of Prop 10.9 for D.
    Reference: [BMSZb] Corollary 10.10 for D. -/
theorem cor_10_10_D {μP μQ : YoungDiagram}
    (τ₁ τ₂ : PBPSet .D μP μQ)
    (hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val i j = PBP.doubleDescent_D_paintL τ₂.val i j)
    (hsig : PBP.signature τ₁.val = PBP.signature τ₂.val)
    (heps : PBP.epsilon τ₁.val = PBP.epsilon τ₂.val) :
    τ₁ = τ₂ :=
  doubleDescent_D_injective_on_PBPSet τ₁ τ₂ hdd hsig heps

/-- **Corollary 10.10 (B type)** — on `PBPSet .γ μP μQ` for γ ∈ {Bplus, Bminus},
    the map `τ ↦ (∇²τ, signature τ, epsilon τ)` is injective.

    PBPSet-level wrapper of `ddescent_inj_B`. -/
theorem cor_10_10_B {μP μQ : YoungDiagram} (γ : RootType) (hγ : γ = .Bplus ∨ γ = .Bminus)
    (τ₁ τ₂ : PBPSet γ μP μQ)
    (hinterl₁ : ∀ j, PBP.dotScolLen τ₁.val.P j ≥ PBP.dotScolLen τ₁.val.Q (j + 1))
    (hinterl₂ : ∀ j, PBP.dotScolLen τ₂.val.P j ≥ PBP.dotScolLen τ₂.val.Q (j + 1))
    (hddL : ∀ i j, PBP.doubleDescent_B_paintL τ₁.val i j = PBP.doubleDescent_B_paintL τ₂.val i j)
    (hddR : ∀ i j, PBP.doubleDescent_B_paintR τ₁.val i j = PBP.doubleDescent_B_paintR τ₂.val i j)
    (hsig : PBP.signature τ₁.val = PBP.signature τ₂.val)
    (heps : PBP.epsilon τ₁.val = PBP.epsilon τ₂.val) :
    τ₁ = τ₂ := by
  have hγ₁ : τ₁.val.γ = .Bplus ∨ τ₁.val.γ = .Bminus := by rw [τ₁.prop.1]; exact hγ
  have hγ_eq : τ₁.val.γ = τ₂.val.γ := by rw [τ₁.prop.1, τ₂.prop.1]
  have hshapeP : τ₁.val.P.shape = τ₂.val.P.shape := by
    rw [τ₁.prop.2.1, τ₂.prop.2.1]
  have hshapeQ : τ₁.val.Q.shape = τ₂.val.Q.shape := by
    rw [τ₁.prop.2.2, τ₂.prop.2.2]
  have ⟨hPeq, hQeq⟩ := PBP.ddescent_inj_B τ₁.val τ₂.val hγ₁ hγ_eq hshapeP hshapeQ
    hinterl₁ hinterl₂ hddL hddR hsig heps
  exact Subtype.ext (PBP.ext'' hγ_eq
    (PaintedYoungDiagram.ext' hshapeP (funext fun i => funext (hPeq i)))
    (PaintedYoungDiagram.ext' hshapeQ (funext fun i => funext (hQeq i))))

/-! ## Proposition 10.11 — counting (B, D) -/

/-- **Proposition 10.11 (B type)** — for any valid B-type dual partition `dp`,
    the total count `|PBPSet .Bplus μP μQ| + |PBPSet .Bminus μP μQ|`
    equals `tripleSum (countPBP_B dp)`.

    Reference: [BMSZb] Proposition 10.11 for B. -/
theorem prop_10_11_B (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B dp) :=
  card_PBPSet_B_eq_tripleSum_countPBP_B dp μP μQ hP hQ hsort heven hpos

/-- **Proposition 10.11 (D type)** — for any valid D-type dual partition `dp`,
    `|PBPSet .D μP μQ|` equals `tripleSum (countPBP_D dp)`.

    Reference: [BMSZb] Proposition 10.11 for D. -/
theorem prop_10_11_D (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_D dp)
    (hQ : μQ.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE)
    (hodd : ∀ r ∈ dp, Odd r) :
    Fintype.card (PBPSet .D μP μQ) = tripleSum (countPBP_D dp) :=
  card_PBPSet_D_eq_tripleSum_countPBP_D dp μP μQ hP hQ hsort hodd

/-! ## Proposition 10.12 — counting (C, C̃ = M) -/

/-- **Proposition 10.12 (C type)** — for any valid C-type dual partition `dp`,
    `|PBPSet .C μP μQ|` equals `countPBP_C dp`.

    Reference: [BMSZb] Proposition 10.12 for C. -/
theorem prop_10_12_C (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_C dp)
    (hQ : μQ.colLens = dpartColLensQ_C dp)
    (hsort : dp.SortedGE)
    (hodd : ∀ r ∈ dp, Odd r)
    (hne : dp ≠ []) :
    Fintype.card (PBPSet .C μP μQ) = countPBP_C dp :=
  card_PBPSet_C_eq_countPBP_C dp μP μQ hP hQ hsort hodd hne

/-- **Proposition 10.12 (M = C̃ type)** — for any valid M-type dual partition `dp`,
    `|PBPSet .M μP μQ|` equals `countPBP_M dp`.

    Reference: [BMSZb] Proposition 10.12 for M. -/
theorem prop_10_12_M (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M dp)
    (hQ : μQ.colLens = dpartColLensQ_M dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .M μP μQ) = countPBP_M dp :=
  card_PBPSet_M_eq_countPBP_M dp μP μQ hP hQ hsort heven hpos
