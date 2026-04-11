/-
# Counting Proof: Fiber counting and step theorems (D type)

Extracted from the monolithic `CountingProof.lean`.
-/
import CombUnipotent.CountingProof.TSeq

open Classical

/-! ### Framework for sandwich argument

Extract column 0 from a fiber element as a ValidCol0 structure.
This is the inverse direction of liftPBP_primitive_D and gives
the injection fiber(σ) ↪ ValidCol0 needed for the upper bound.
-/

/-- Extract column 0 data from a D-type PBP as a ValidCol0.
    For D type, P column 0 has dots in rows < Q.colLen(0) and non-dot cells
    in the tail [Q.colLen(0), P.colLen(0)). -/
noncomputable def PBP.extractCol0_D {μP μQ : YoungDiagram}
    (τ : PBPSet .D μP μQ) : ValidCol0 μP μQ where
  paint i := τ.val.P.paint i 0
  dot_below i hi := by
    -- (i, 0) ∈ μQ = τ.Q.shape → (i, 0) is P-dot by dot_match
    have hmemQ : (i, 0) ∈ τ.val.Q.shape := by
      rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi
    have hmemP : (i, 0) ∈ τ.val.P.shape :=
      ((τ.val.dot_match i 0).mpr ⟨hmemQ,
        PBP.Q_all_dot_of_D τ.val τ.prop.1 i 0 hmemQ⟩).1
    exact ((τ.val.dot_match i 0).mpr
      ⟨hmemQ, PBP.Q_all_dot_of_D τ.val τ.prop.1 i 0 hmemQ⟩).2
  nondot_tail i hi1 hi2 := by
    -- i ≥ μQ.colLen 0 → (i, 0) ∉ μQ → P.paint not dot (by dot_match contrapositive)
    intro hpaint
    have hmemP : (i, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi2
    have ⟨hmemQ, _⟩ := (τ.val.dot_match i 0).mp ⟨hmemP, hpaint⟩
    rw [τ.prop.2.2] at hmemQ
    have := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
    omega
  dot_above i hi := by
    apply τ.val.P.paint_outside
    rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  mono i₁ i₂ h₁ h₂ := by
    apply τ.val.mono_P i₁ 0 i₂ 0 h₁ (Nat.le_refl 0)
    rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr h₂
  col_c_unique i₁ i₂ := τ.val.col_c_P 0 i₁ i₂
  col_d_unique i₁ i₂ := τ.val.col_d_P 0 i₁ i₂

/-- extractCol0_D is injective on the fiber over σ.
    Given τ₁, τ₂ ∈ fiber(σ) with same column 0 paint, same P everywhere
    (columns ≥ 1 determined by σ), same Q (Q = dotDiag P), so τ₁ = τ₂. -/
theorem extractCol0_D_injective_on_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    {τ₁ τ₂ : doubleDescent_D_fiber σ}
    (h : (PBP.extractCol0_D τ₁.val).paint = (PBP.extractCol0_D τ₂.val).paint) :
    τ₁ = τ₂ := by
  -- From τ₁.prop = τ₂.prop = σ: both τ have the same ∇² paint
  have hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val.val i j =
                    PBP.doubleDescent_D_paintL τ₂.val.val i j := by
    intro i j
    have hdd_eq : doubleDescent_D_map τ₁.val = doubleDescent_D_map τ₂.val := by
      rw [τ₁.prop, τ₂.prop]
    have : doubleDescent_D_PBP τ₁.val.val τ₁.val.prop.1 =
            doubleDescent_D_PBP τ₂.val.val τ₂.val.prop.1 :=
      congrArg Subtype.val hdd_eq
    exact congr_fun (congr_fun (congrArg (fun d => d.P.paint) this) i) j
  -- Apply ddescent_D_determines_single to get single descent equality
  have hshapeP : τ₁.val.val.P.shape = τ₂.val.val.P.shape := by
    rw [τ₁.val.prop.2.1, τ₂.val.prop.2.1]
  have hshapeQ : τ₁.val.val.Q.shape = τ₂.val.val.Q.shape := by
    rw [τ₁.val.prop.2.2, τ₂.val.prop.2.2]
  have hdesc := PBP.ddescent_D_determines_single τ₁.val.val τ₂.val.val
    τ₁.val.prop.1 τ₂.val.prop.1 hshapeP hshapeQ hdd
  -- Apply descent_eq_implies_cols_ge1_D to get cols ≥ 1 equal
  have hcols := PBP.descent_eq_implies_cols_ge1_D τ₁.val.val τ₂.val.val
    τ₁.val.prop.1 τ₂.val.prop.1 hshapeP hshapeQ hdesc
  -- Assemble P.paint equality (col 0 from h, cols ≥ 1 from hcols)
  have hP : τ₁.val.val.P.paint = τ₂.val.val.P.paint := by
    ext i j
    cases j with
    | zero => exact congr_fun h i
    | succ j => exact hcols i (j + 1) (by omega)
  have hPeq : τ₁.val.val.P = τ₂.val.val.P := PaintedYoungDiagram.ext' hshapeP hP
  have hQeq : τ₁.val.val.Q = τ₂.val.val.Q := by
    apply PaintedYoungDiagram.ext' hshapeQ
    ext i j
    by_cases hmem : (i, j) ∈ τ₁.val.val.Q.shape
    · rw [PBP.Q_all_dot_of_D τ₁.val.val τ₁.val.prop.1 i j hmem,
          PBP.Q_all_dot_of_D τ₂.val.val τ₂.val.prop.1 i j (hshapeQ ▸ hmem)]
    · rw [τ₁.val.val.Q.paint_outside i j hmem,
          τ₂.val.val.Q.paint_outside i j (hshapeQ ▸ hmem)]
  have hτeq : τ₁.val.val = τ₂.val.val := PBP.ext''
    (by rw [τ₁.val.prop.1, τ₂.val.prop.1]) hPeq hQeq
  exact Subtype.ext (Subtype.ext hτeq)

/-! ### Injection lemmas for sandwich argument -/

/-- Generalized injectivity: liftPBP_D is injective across (σ, col0). -/
theorem liftPBP_D_injective {μP μQ : YoungDiagram}
    {σ₁ σ₂ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    {col0₁ col0₂ : ValidCol0 μP μQ}
    {h_cond₁ : LiftCondition σ₁} {h_cond₂ : LiftCondition σ₂}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (h : liftPBP_D σ₁ col0₁ h_cond₁ hQP = liftPBP_D σ₂ col0₂ h_cond₂ hQP) :
    σ₁ = σ₂ ∧ col0₁ = col0₂ := by
  have hval := congrArg Subtype.val h
  have hP : (liftPBP_D σ₁ col0₁ h_cond₁ hQP).val.P.paint =
            (liftPBP_D σ₂ col0₂ h_cond₂ hQP).val.P.paint :=
    congr_arg (fun τ => τ.P.paint) hval
  have hcol0 : col0₁.paint = col0₂.paint := by
    ext i; have := congr_fun (congr_fun hP i) 0; simp [liftPaint_D] at this; exact this
  have hcol0_eq : col0₁ = col0₂ := by
    cases col0₁; cases col0₂; simp only [ValidCol0.mk.injEq]; exact hcol0
  have hσP : σ₁.val.P.paint = σ₂.val.P.paint := by
    ext i j; have := congr_fun (congr_fun hP i) (j + 1); simp [liftPaint_D] at this; exact this
  have hσQ : σ₁.val.Q = σ₂.val.Q := by
    apply PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.2, σ₂.prop.2.2])
    ext i j
    have hQshape_eq : σ₁.val.Q.shape = σ₂.val.Q.shape := by rw [σ₁.prop.2.2, σ₂.prop.2.2]
    by_cases hmem : (i, j) ∈ σ₁.val.Q.shape
    · rw [PBP.Q_all_dot_of_D σ₁.val σ₁.prop.1 i j hmem,
          PBP.Q_all_dot_of_D σ₂.val σ₂.prop.1 i j (hQshape_eq ▸ hmem)]
    · rw [σ₁.val.Q.paint_outside i j hmem,
          σ₂.val.Q.paint_outside i j (hQshape_eq ▸ hmem)]
  have hσ_eq : σ₁.val = σ₂.val := PBP.ext'' (by rw [σ₁.prop.1, σ₂.prop.1])
    (PaintedYoungDiagram.ext' (by rw [σ₁.prop.2.1, σ₂.prop.2.1]) hσP) hσQ
  exact ⟨Subtype.ext hσ_eq, hcol0_eq⟩

/-- Primitive-case lift injectivity as a thin wrapper. -/
theorem liftPBP_primitive_D_injective {μP μQ : YoungDiagram}
    {σ₁ σ₂ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)}
    {col0₁ col0₂ : ValidCol0 μP μQ}
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (h : liftPBP_primitive_D σ₁ col0₁ h_prim hQP = liftPBP_primitive_D σ₂ col0₂ h_prim hQP) :
    σ₁ = σ₂ ∧ col0₁ = col0₂ :=
  liftPBP_D_injective hQP h

/-! ### Primitive case fiber counting

Using the sandwich argument with validCol0_card, extractCol0_D_injective_on_fiber,
and liftPBP_primitive_D_injective. -/

/-- Round-trip property (general): ∇²(liftPBP_D σ col0 h_cond) = σ. -/
theorem liftPBP_D_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_cond : LiftCondition σ)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    doubleDescent_D_map (liftPBP_D σ col0 h_cond hQP) = σ := by
  apply Subtype.ext
  show doubleDescent_D_PBP (liftPBP_D σ col0 h_cond hQP).val
    (liftPBP_D σ col0 h_cond hQP).prop.1 = σ.val
  apply PBP.ext''
  · rw [σ.prop.1]; rfl
  · apply PaintedYoungDiagram.ext'
    · rw [σ.prop.2.1]; rfl
    · funext i j
      show PBP.doubleDescent_D_paintL _ i j = σ.val.P.paint i j
      have hQshape : (liftPBP_D σ col0 h_cond hQP).val.Q.shape = μQ := rfl
      have hPshape : (liftPBP_D σ col0 h_cond hQP).val.P.shape = μP := rfl
      have hPpaint : ∀ k m, (liftPBP_D σ col0 h_cond hQP).val.P.paint k m =
                       liftPaint_D σ.val col0.paint k m := fun _ _ => rfl
      have hQ_eq : μQ.colLen (j + 1) = σ.val.Q.shape.colLen j := by
        rw [σ.prop.2.2, YoungDiagram.colLen_shiftLeft]
      have hP_eq : μP.colLen (j + 1) = σ.val.P.shape.colLen j := by
        rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]
      simp only [PBP.doubleDescent_D_paintL, hQshape]
      by_cases hA : i < μQ.colLen (j + 1)
      · rw [if_pos hA]
        rw [hQ_eq] at hA
        have hmemQ : (i, j) ∈ σ.val.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr hA
        have hQdot : σ.val.Q.paint i j = .dot :=
          PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hmemQ
        have ⟨_, hPdot⟩ := (σ.val.dot_match i j).mpr ⟨hmemQ, hQdot⟩
        exact hPdot.symm
      · rw [if_neg hA]
        rw [hQ_eq] at hA
        have hnotQ : (i, j) ∉ σ.val.Q.shape := by
          intro hmem
          exact hA (YoungDiagram.mem_iff_lt_colLen.mp hmem)
        by_cases hB : i < PBP.dotScolLen (liftPBP_D σ col0 h_cond hQP).val.P (j + 1)
        · rw [if_pos hB]
          set lift := (liftPBP_D σ col0 h_cond hQP).val
          have hlift_mono : lift.P.layerMonotone := lift.mono_P
          have hdscol_le : PBP.dotScolLen lift.P (j + 1) ≤ lift.P.shape.colLen (j + 1) :=
            PBP.dotScolLen_le_colLen lift.P hlift_mono (j + 1)
          have hi_lt_shape : i < lift.P.shape.colLen (j + 1) := lt_of_lt_of_le hB hdscol_le
          have hlo_lift : (lift.P.paint i (j + 1)).layerOrd ≤ 1 := by
            have hds_eq : PBP.dotScolLen lift.P (j + 1) =
                (PBP.dotSdiag lift.P hlift_mono).colLen (j + 1) :=
              PBP.dotScolLen_eq_dotSdiag_colLen _ hlift_mono _
            rw [hds_eq] at hB
            exact PBP.layerOrd_le_one_of_lt_dotSdiag_colLen _ hlift_mono hB
          rw [hPpaint] at hlo_lift
          simp only [liftPaint_D] at hlo_lift
          have hmemP : (i, j) ∈ σ.val.P.shape := by
            rw [hPshape] at hi_lt_shape
            rw [YoungDiagram.mem_iff_lt_colLen, ← hP_eq]; exact hi_lt_shape
          have hne_dot : σ.val.P.paint i j ≠ .dot := by
            intro hpd
            have ⟨hqm, _⟩ := (σ.val.dot_match i j).mp ⟨hmemP, hpd⟩
            exact hnotQ hqm
          revert hlo_lift hne_dot
          cases σ.val.P.paint i j <;> simp [DRCSymbol.layerOrd]
        · rw [if_neg hB]
          rw [hPpaint]; rfl
  · apply PaintedYoungDiagram.ext'
    · rw [σ.prop.2.2]; rfl
    · funext i j
      show DRCSymbol.dot = σ.val.Q.paint i j
      by_cases hmem : (i, j) ∈ σ.val.Q.shape
      · exact (PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hmem).symm
      · exact (σ.val.Q.paint_outside i j hmem).symm

/-- Primitive-case round-trip as a thin wrapper. -/
theorem liftPBP_primitive_D_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    doubleDescent_D_map (liftPBP_primitive_D σ col0 h_prim hQP) = σ :=
  liftPBP_D_round_trip σ col0 (liftCondition_of_primitive σ h_prim) hQP

/-- Balanced DD-case round-trip as a thin wrapper. -/
theorem liftPBP_balanced_DD_D_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_tc : tailClass_D σ.val = .DD)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    doubleDescent_D_map (liftPBP_balanced_DD_D σ col0 h_bal h_tc hQP) = σ :=
  liftPBP_D_round_trip σ col0 (liftCondition_of_balanced_DD σ h_bal h_tc) hQP

/-- liftPBP_primitive_D produces an element of the fiber over σ. -/
noncomputable def liftPBP_to_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    doubleDescent_D_fiber σ :=
  ⟨liftPBP_primitive_D σ col0 h_prim hQP,
   liftPBP_primitive_D_round_trip σ col0 h_prim hQP⟩

/-- liftPBP_to_fiber is injective as a function ValidCol0 → fiber(σ). -/
theorem liftPBP_to_fiber_injective {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    Function.Injective (fun col0 : ValidCol0 μP μQ => liftPBP_to_fiber σ col0 h_prim hQP) := by
  intro col0₁ col0₂ h
  -- h : liftPBP_to_fiber col0₁ = liftPBP_to_fiber col0₂
  -- Extract .val equality
  have h_val : (liftPBP_to_fiber σ col0₁ h_prim hQP).val =
               (liftPBP_to_fiber σ col0₂ h_prim hQP).val :=
    congrArg Subtype.val h
  simp only [liftPBP_to_fiber] at h_val
  -- h_val : liftPBP_primitive_D σ col0₁ = liftPBP_primitive_D σ col0₂
  exact (liftPBP_primitive_D_injective h_prim hQP h_val).2

/-- Key counting lemma (primitive case):
    When μQ.colLen(0) ≥ μP.colLen(1), every sub-PBP has the same fiber size. -/
theorem fiber_card_primitive {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (doubleDescent_D_fiber σ) =
        let ((tDD, tRC, tSS), _) := tailCoeffs k
        tDD + tRC + tSS := by
  show Fintype.card (doubleDescent_D_fiber σ) =
    (tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2
  rw [← validCol0_card k hk hQP hk_pos]
  -- Upper bound: fiber → ValidCol0 via extractCol0_D is injective
  have h_le : Fintype.card (doubleDescent_D_fiber σ) ≤
      Fintype.card (ValidCol0 μP μQ) := by
    apply Fintype.card_le_of_injective
      (fun τ => PBP.extractCol0_D τ.val)
    intro τ₁ τ₂ h
    apply extractCol0_D_injective_on_fiber σ
    exact congr_arg ValidCol0.paint h
  -- Lower bound: ValidCol0 ↪ fiber via liftPBP_to_fiber (uses round-trip)
  have h_ge : Fintype.card (ValidCol0 μP μQ) ≤
      Fintype.card (doubleDescent_D_fiber σ) := by
    apply Fintype.card_le_of_injective
      (fun col0 => liftPBP_to_fiber σ col0 h_prim hQP)
    exact liftPBP_to_fiber_injective σ h_prim hQP
  omega

/-! ### Balanced case fiber counting

Balanced condition for D type: μP.colLen(1) = μQ.colLen(0) + 1.
In shiftLeft form: (shiftLeft μP).colLen(0) = μQ.colLen(0) + 1.
This is the complement of the primitive case (μQ.colLen(0) ≥ shiftLeft μP.colLen(0)).
-/

/-- Key counting lemma (balanced case, DD class):
    When balanced and tc(σ) = DD, fiber has size tDD+tRC+tSS.

    **Proof approach**: In balanced case, μP.colLen 1 = μQ.colLen 0 + 1, so row b
    (= μQ.colLen 0) is in P.shape at column 1. DD class means σ.P.paint(b, 0) = d
    (layerOrd 4 ≥ all symbols). So P.paint(b, 1) = d, and mono_P gives
    col0(b).layerOrd ≤ 4, which is vacuous (all symbols satisfy this).
    Row uniqueness for d is column-based (col_d_unique), so no row_d constraint.
    Hence the tail cell at row b is unconstrained, same as primitive case.
    Sandwich argument gives fiber = |ValidCol0| = tDD + tRC + tSS. -/
theorem fiber_card_balanced_DD {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k)
    (h_tc : tailClass_D σ.val = .DD) :
    Fintype.card (doubleDescent_D_fiber σ) =
      let ((tDD, tRC, tSS), _) := tailCoeffs k
      tDD + tRC + tSS := by
  show Fintype.card (doubleDescent_D_fiber σ) =
    (tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2
  rw [← validCol0_card k hk hQP hk_pos]
  -- Upper bound: fiber ↪ ValidCol0 via extractCol0_D
  have h_le : Fintype.card (doubleDescent_D_fiber σ) ≤
      Fintype.card (ValidCol0 μP μQ) := by
    apply Fintype.card_le_of_injective
      (fun τ => PBP.extractCol0_D τ.val)
    intro τ₁ τ₂ h
    apply extractCol0_D_injective_on_fiber σ
    exact congr_arg ValidCol0.paint h
  -- Lower bound: ValidCol0 ↪ fiber via liftPBP_balanced_DD_D
  have h_ge : Fintype.card (ValidCol0 μP μQ) ≤
      Fintype.card (doubleDescent_D_fiber σ) := by
    let f : ValidCol0 μP μQ → doubleDescent_D_fiber σ :=
      fun col0 => ⟨liftPBP_balanced_DD_D σ col0 h_bal h_tc hQP,
                    liftPBP_balanced_DD_D_round_trip σ col0 h_bal h_tc hQP⟩
    have hinj : Function.Injective f := by
      intro col0₁ col0₂ h
      have h_val : (liftPBP_balanced_DD_D σ col0₁ h_bal h_tc hQP).val =
                   (liftPBP_balanced_DD_D σ col0₂ h_bal h_tc hQP).val :=
        congrArg (fun x : doubleDescent_D_fiber σ => x.val.val) h
      have h_eq : liftPBP_balanced_DD_D σ col0₁ h_bal h_tc hQP =
                  liftPBP_balanced_DD_D σ col0₂ h_bal h_tc hQP :=
        Subtype.ext h_val
      exact (liftPBP_D_injective hQP h_eq).2
    exact Fintype.card_le_of_injective f hinj
  omega

/-- **Balanced RC case — aggregate form.**

    The per-σ fiber size in balanced RC case is NOT constant: it depends on
    whether σ's tail bottom is .r or .c. Concrete counts (verified numerically
    for k = 2): r-bottom σ has fiber size 4, c-bottom σ has fiber size 8.
    The average is 6 = scTotal, and `RCp · scTotal` works in Counting.lean's
    formula because `#r = #c` in the RC class (an equal count established by
    a symmetry argument, not yet formalized).

    The correct per-σ statements are `fiber_card_balanced_R` and `fiber_card_balanced_C`
    (to be added with a 4-class TailClass refinement). For now, we state the
    AGGREGATE sum as the top-level recursive theorem would use it:

      `Σ_{σ ∈ RC class} |fiber(σ)| = #RC class · scTotal`

    where `scTotal = scDD + scRC + scSS`. This requires the lemma `#r = #c`. -/
theorem fiber_card_balanced_RC_aggregate {μP μQ : YoungDiagram}
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hk_pos : 1 ≤ k) :
    (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                            (YoungDiagram.shiftLeft μQ) =>
      tailClass_D σ.val = .RC)).sum (fun σ =>
        Fintype.card (doubleDescent_D_fiber σ)) =
      let (_, (scDD, scRC, scSS)) := tailCoeffs k
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card * (scDD + scRC + scSS) := by
  sorry -- TODO: requires #r = #c lemma + per-r-σ / per-c-σ fiber computations

/-- Key counting lemma (balanced case, SS class): fiber is empty.

    Reason: In balanced case, `σ.P.paint b 0 = .s` (where `b = μQ.colLen 0`).
    For any `τ ∈ fiber(σ)`, the ∇² formula forces `τ.P.paint b 1 = .s`, and
    then `τ.P.paint b 0` is blocked by mono_P (layerOrd ≤ 1 ⇒ ∈ {dot, s}),
    dot_match (≠ .dot), and row_s (≠ .s since (b, 1) is already .s). -/
theorem fiber_card_balanced_SS {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hQP_lt : μQ.colLen 0 < μP.colLen 0)
    (h_tc : tailClass_D σ.val = .SS) :
    Fintype.card (doubleDescent_D_fiber σ) = 0 := by
  set b := μQ.colLen 0 with hb_def
  have hbal' : μP.colLen 1 = b + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  -- σ.P.shape.colLen 0 = b + 1 (from balanced condition)
  have hσP_colLen : σ.val.P.shape.colLen 0 = b + 1 := by
    rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]; exact hbal'
  -- σ.Q.shape.colLen 0 = μQ.colLen 1 ≤ b (YD anti-monotone)
  have hσQ_le : σ.val.Q.shape.colLen 0 ≤ b := by
    rw [σ.prop.2.2, YoungDiagram.colLen_shiftLeft]
    exact μQ.colLen_anti 0 1 (by omega)
  -- (b, 0) ∈ σ.P.shape but ∉ σ.Q.shape
  have hb_memP : (b, 0) ∈ σ.val.P.shape :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hb_notQ : (b, 0) ∉ σ.val.Q.shape := by
    intro hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmem) (by omega)
  -- σ.val.P.paint b 0 = tailSymbol (bottom of col 0 tail)
  have hσ_bottom : σ.val.P.paint b 0 = PBP.tailSymbol_D σ.val := by
    simp only [PBP.tailSymbol_D, hσP_colLen, Nat.add_sub_cancel]
  -- tailClass = SS with nonzero tailLen ⇒ tailSymbol ∈ {s, dot}
  have htailLen_pos : PBP.tailLen_D σ.val > 0 := by
    simp only [PBP.tailLen_D, hσP_colLen]; omega
  have htail : PBP.tailSymbol_D σ.val = .s ∨ PBP.tailSymbol_D σ.val = .dot := by
    simp only [tailClass_D] at h_tc
    rw [if_neg (by omega : PBP.tailLen_D σ.val ≠ 0)] at h_tc
    cases hs : PBP.tailSymbol_D σ.val <;> rw [hs] at h_tc <;> simp at h_tc
    · right; rfl
    · left; rfl
  -- Rule out dot via dot_match: if σ.P.paint b 0 = .dot, (b, 0) ∈ σ.Q.shape, contradiction
  have hσ_s : σ.val.P.paint b 0 = .s := by
    rcases htail with hs | hd
    · rw [hσ_bottom]; exact hs
    · exfalso
      have hdot : σ.val.P.paint b 0 = .dot := hσ_bottom.trans hd
      have ⟨hqm, _⟩ := (σ.val.dot_match b 0).mp ⟨hb_memP, hdot⟩
      exact hb_notQ hqm
  -- Main argument: show fiber is empty
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨τ, hτ⟩ => ?_⟩
  -- hτ : doubleDescent_D_map τ = σ
  -- Extract ∇²τ.P.paint = σ.val.P.paint at (b, 0)
  have hdd : PBP.doubleDescent_D_paintL τ.val b 0 = σ.val.P.paint b 0 := by
    have hdmap := congrArg (fun x => x.val.P.paint b 0) hτ
    simp only [doubleDescent_D_map, doubleDescent_D_PBP] at hdmap
    exact hdmap
  rw [hσ_s] at hdd
  -- Unfold ∇² to derive τ.P.paint b 1 = .s
  have hτQ_le : τ.val.Q.shape.colLen 1 ≤ b := by
    rw [τ.prop.2.2]
    exact μQ.colLen_anti 0 1 (by omega)
  have hnot_Qzone : ¬(b < τ.val.Q.shape.colLen 1) := by omega
  simp only [PBP.doubleDescent_D_paintL, if_neg hnot_Qzone] at hdd
  -- (b, 1) ∈ τ.P.shape = μP (since b < μP.colLen 1 = b + 1)
  have hτP_mem1 : (b, 1) ∈ τ.val.P.shape := by
    rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega
  -- (b, 1) ∉ τ.Q.shape = μQ
  have hb_notQ1 : (b, 1) ∉ τ.val.Q.shape := by
    intro hmem
    rw [τ.prop.2.2, YoungDiagram.mem_iff_lt_colLen] at hmem
    have : μQ.colLen 1 ≤ b := μQ.colLen_anti 0 1 (by omega)
    omega
  have hτP1_ne_dot : τ.val.P.paint b 1 ≠ .dot := by
    intro hdot
    exact hb_notQ1 ((τ.val.dot_match b 1).mp ⟨hτP_mem1, hdot⟩).1
  have hτP1_s : τ.val.P.paint b 1 = .s := by
    by_cases hS : b < PBP.dotScolLen τ.val.P 1
    · have hmono_τ : τ.val.P.layerMonotone := τ.val.mono_P
      have hds_eq := PBP.dotScolLen_eq_dotSdiag_colLen τ.val.P hmono_τ 1
      rw [hds_eq] at hS
      have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P hmono_τ hS
      revert hlo hτP1_ne_dot
      cases τ.val.P.paint b 1 <;> simp [DRCSymbol.layerOrd]
    · rw [if_neg hS] at hdd; exact hdd
  -- Now apply mono_P and row_s for contradiction
  have hτP0_lo : (τ.val.P.paint b 0).layerOrd ≤ 1 := by
    have := τ.val.mono_P b 0 b 1 (le_refl _) (by omega) hτP_mem1
    rw [hτP1_s, DRCSymbol.layerOrd] at this; exact this
  have hτP_mem0 : (b, 0) ∈ τ.val.P.shape := by
    rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; exact hQP_lt
  have hb_notQ0 : (b, 0) ∉ τ.val.Q.shape := by
    intro hmem
    rw [τ.prop.2.2, YoungDiagram.mem_iff_lt_colLen] at hmem
    omega
  have hτP0_ne_dot : τ.val.P.paint b 0 ≠ .dot := by
    intro hdot
    exact hb_notQ0 ((τ.val.dot_match b 0).mp ⟨hτP_mem0, hdot⟩).1
  have hτP0_ne_dot : τ.val.P.paint b 0 ≠ .dot := by
    intro hdot
    exact hb_notQ0 ((τ.val.dot_match b 0).mp ⟨hτP_mem0, hdot⟩).1
  -- So τP b 0 = .s (layerOrd ≤ 1 and ≠ .dot)
  have hτP0_s : τ.val.P.paint b 0 = .s := by
    revert hτP0_lo hτP0_ne_dot
    cases τ.val.P.paint b 0 <;> simp [DRCSymbol.layerOrd]
  -- row_s contradiction: both (b, 0) and (b, 1) are .s on side L
  have := τ.val.row_s b .L .L 0 1
    (by simp [paintBySide]; exact hτP0_s)
    (by simp [paintBySide]; exact hτP1_s)
  exact absurd this.2 (by omega)

/-! ### Fiber sum = total count (no surjectivity needed) -/

/-- |PBPSet(dp)| = Σ_σ |fiber(σ)|. This is just Equiv.sigmaFiberEquiv. -/
theorem card_PBPSet_eq_sum_fiber {μP μQ : YoungDiagram} :
    Fintype.card (PBPSet .D μP μQ) =
      Finset.sum Finset.univ (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
        (YoungDiagram.shiftLeft μQ) =>
        Fintype.card (doubleDescent_D_fiber σ)) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv doubleDescent_D_map).symm

/-! ### Decomposition of PBPSet by tail class -/

/-- PBPSet restricted to a tail class. -/
def PBPSet_tc (γ : RootType) (μP μQ : YoungDiagram) (tc : TailClass) :=
  {τ : PBPSet γ μP μQ // tailClass_D τ.val = tc}

instance : Finite (PBPSet_tc γ μP μQ tc) :=
  Finite.of_injective (fun x => x.val) (fun _ _ h => Subtype.ext h)

noncomputable instance : Fintype (PBPSet_tc γ μP μQ tc) :=
  Fintype.ofFinite _

/-- PBPSet decomposes by tail class: |PBPSet| = |DD| + |RC| + |SS|. -/
theorem card_PBPSet_eq_sum_tc (μP μQ : YoungDiagram) :
    Fintype.card (PBPSet .D μP μQ) =
      Fintype.card (PBPSet_tc .D μP μQ .DD) +
      Fintype.card (PBPSet_tc .D μP μQ .RC) +
      Fintype.card (PBPSet_tc .D μP μQ .SS) := by
  -- Decompose PBPSet into 3 disjoint subsets by tailClass
  have h_disj : ∀ τ : PBPSet .D μP μQ,
      tailClass_D τ.val = .DD ∨ tailClass_D τ.val = .RC ∨ tailClass_D τ.val = .SS := by
    intro τ; simp only [tailClass_D]
    split_ifs with h
    · right; right; rfl
    · cases PBP.tailSymbol_D τ.val <;> simp [TailClass.noConfusion]
      <;> first | left; rfl | right; left; rfl | right; right; rfl
  -- Use Equiv with Sum type, then Fintype.card_sum
  have h_ss : ∀ τ : PBPSet .D μP μQ,
      tailClass_D τ.val ≠ .DD → tailClass_D τ.val ≠ .RC → tailClass_D τ.val = .SS :=
    fun τ h₁ h₂ => (h_disj τ).elim (absurd · h₁) (·.elim (absurd · h₂) id)
  let e : PBPSet .D μP μQ ≃
      PBPSet_tc .D μP μQ .DD ⊕ (PBPSet_tc .D μP μQ .RC ⊕ PBPSet_tc .D μP μQ .SS) :=
    { toFun := fun τ =>
        if h : tailClass_D τ.val = .DD then Sum.inl ⟨τ, h⟩
        else if h' : tailClass_D τ.val = .RC then Sum.inr (Sum.inl ⟨τ, h'⟩)
        else Sum.inr (Sum.inr ⟨τ, h_ss τ h h'⟩)
      invFun := fun
        | Sum.inl ⟨τ, _⟩ => τ
        | Sum.inr (Sum.inl ⟨τ, _⟩) => τ
        | Sum.inr (Sum.inr ⟨τ, _⟩) => τ
      left_inv := fun τ => by simp only; split_ifs <;> rfl
      right_inv := fun
        | Sum.inl ⟨τ, h⟩ => by simp [dif_pos h]
        | Sum.inr (Sum.inl ⟨τ, h⟩) => by
            simp only; rw [dif_neg (by rw [h]; decide), dif_pos h]
        | Sum.inr (Sum.inr ⟨τ, h⟩) => by
            simp only; rw [dif_neg (by rw [h]; decide), dif_neg (by rw [h]; decide)] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_sum, Nat.add_assoc]

/-! ### Top-level recursive theorems (Prop 10.11 D type, primitive case) -/

/-- **Primitive recursive step**: in the primitive case, the D-type count
    multiplies by `4k = tDD + tRC + tSS` at each descent step.

    This is the core of Prop 10.11(a): since every fiber has size `4k` (regardless
    of tailClass), the total count is `|sub-PBPSet| · 4k`. -/
theorem card_PBPSet_D_primitive_step {μP μQ : YoungDiagram}
    (k : ℕ) (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (PBPSet .D μP μQ) =
      Fintype.card (PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) *
        ((tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2) := by
  rw [card_PBPSet_eq_sum_fiber]
  -- Rewrite each fiber size to 4k using fiber_card_primitive (independent of σ)
  have hfiber : ∀ σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ),
      Fintype.card (doubleDescent_D_fiber σ) =
      (tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2 := by
    intro σ
    have h := fiber_card_primitive σ k h_prim hk hQP hk_pos
    exact h
  rw [Finset.sum_congr rfl (fun σ _ => hfiber σ)]
  rw [Finset.sum_const, Finset.card_univ]
  rfl

/-! #### Balanced step (total form, depending on fiber_card_balanced_RC_aggregate) -/

/-- **Balanced recursive step (total form)**: in the balanced case, the D-type
    count recursive formula has the matrix-multiply structure from Prop 10.11(b).

    The SS class contributes 0 (balanced SS fiber is empty), so only DD and RC
    parent classes contribute. For the total (DD + RC + SS summed) form, we get
    a clean formula matching `countPBP_D` balanced case summed. -/
theorem card_PBPSet_D_balanced_step {μP μQ : YoungDiagram}
    (k : ℕ) (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (PBPSet .D μP μQ) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card *
          ((tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2) +
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card *
          ((tailCoeffs k).2.1 + (tailCoeffs k).2.2.1 + (tailCoeffs k).2.2.2) := by
  -- Derive hQP_lt from hk_pos + hk for fiber_card_balanced_SS
  have hQP_lt : μQ.colLen 0 < μP.colLen 0 := by omega
  -- Step 1: rewrite |PBPSet .D μP μQ| as Σ_σ |fiber σ|
  rw [card_PBPSet_eq_sum_fiber]
  -- Step 2: split the sum over PBPSet_sub into three parts by σ's tailClass.
  --    Σ_σ f σ = Σ_{σ: tc=DD} f σ + Σ_{σ: tc=RC} f σ + Σ_{σ: tc=SS} f σ
  set univ_sub : Finset (PBPSet .D (YoungDiagram.shiftLeft μP)
                                    (YoungDiagram.shiftLeft μQ)) := Finset.univ with hsub_def
  have h_split :
      univ_sub.sum (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
      (univ_sub.filter (fun σ => tailClass_D σ.val = .DD)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) +
      (univ_sub.filter (fun σ => tailClass_D σ.val = .RC)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) +
      (univ_sub.filter (fun σ => tailClass_D σ.val = .SS)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) := by
    -- First split: DD vs ¬DD
    have step1 : univ_sub.sum (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
        (univ_sub.filter (fun σ => tailClass_D σ.val = .DD)).sum
          (fun σ => Fintype.card (doubleDescent_D_fiber σ)) +
        (univ_sub.filter (fun σ => ¬(tailClass_D σ.val = .DD))).sum
          (fun σ => Fintype.card (doubleDescent_D_fiber σ)) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    -- Trichotomy helper: every σ has tailClass ∈ {DD, RC, SS}
    have h_trichotomy : ∀ σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                        (YoungDiagram.shiftLeft μQ),
        tailClass_D σ.val = .DD ∨ tailClass_D σ.val = .RC ∨ tailClass_D σ.val = .SS := by
      intro σ; simp only [tailClass_D]
      split_ifs with h
      · right; right; rfl
      · cases PBP.tailSymbol_D σ.val <;> simp
    -- Second split: rewrite filter-by-¬DD as filter-by-(RC ∨ SS), then split into RC + SS
    have hfilter_eq : univ_sub.filter (fun σ => ¬(tailClass_D σ.val = .DD)) =
        univ_sub.filter (fun σ => tailClass_D σ.val = .RC ∨ tailClass_D σ.val = .SS) := by
      apply Finset.filter_congr
      intro σ _
      constructor
      · intro hnDD
        rcases h_trichotomy σ with h | h | h
        · exact absurd h hnDD
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h) <;> rw [h] <;> decide
    have step2 : (univ_sub.filter (fun σ => ¬(tailClass_D σ.val = .DD))).sum
          (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
        (univ_sub.filter (fun σ => tailClass_D σ.val = .RC)).sum
          (fun σ => Fintype.card (doubleDescent_D_fiber σ)) +
        (univ_sub.filter (fun σ => tailClass_D σ.val = .SS)).sum
          (fun σ => Fintype.card (doubleDescent_D_fiber σ)) := by
      rw [hfilter_eq, Finset.filter_or]
      -- Disjoint union (RC and SS are disjoint)
      rw [Finset.sum_union]
      -- Prove disjointness
      rw [Finset.disjoint_filter]
      intros σ _ hRC hSS
      rw [hRC] at hSS; exact absurd hSS (by decide)
    rw [step1, step2, ← Nat.add_assoc]
  rw [h_split]
  -- Step 3: simplify the DD part: Σ_{σ∈DD} |fiber σ| = #DD · 4k
  have h_DD_part :
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card *
          ((tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2) := by
    -- Each σ in DD filter has fiber_card = tDD + tRC + tSS (constant)
    rw [Finset.sum_congr rfl (fun σ hσ => ?_)]
    · rw [Finset.sum_const]
      rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have h := fiber_card_balanced_DD σ k h_bal hk hQP hk_pos hσ
      simpa using h
  rw [h_DD_part]
  -- Step 4: simplify the RC part: Σ_{σ∈RC} |fiber σ| = #RC · scTotal
  have h_RC_part :
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) =
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card *
          ((tailCoeffs k).2.1 + (tailCoeffs k).2.2.1 + (tailCoeffs k).2.2.2) := by
    have := fiber_card_balanced_RC_aggregate (μP := μP) (μQ := μQ) k h_bal hk hk_pos
    exact this
  rw [h_RC_part]
  -- Step 5: simplify the SS part: Σ_{σ∈SS} |fiber σ| = 0
  have h_SS_part :
      (Finset.univ.filter (fun σ : PBPSet .D (YoungDiagram.shiftLeft μP)
                                              (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .SS)).sum
        (fun σ => Fintype.card (doubleDescent_D_fiber σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact fiber_card_balanced_SS σ h_bal hQP hQP_lt hσ
  rw [h_SS_part, Nat.add_zero]

