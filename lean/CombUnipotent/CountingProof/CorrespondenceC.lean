/-
# C-type counting: Proposition 10.12

Proves `Fintype.card (PBPSet .C μP μQ) = countPBP_C dp` for all valid
C-type dual partitions dp (sorted, odd parts, dp ≠ []).

Reference: [BMSZb] Proposition 10.12.
-/
import CombUnipotent.CountingProof.Correspondence

open Classical

/-! ## Helper lemmas for C→D descent -/

/-- If (i,j) ∉ P.shape then descentPaintL_CD gives dot. -/
private lemma descentPaintL_CD_outside {τ : PBP} (hγ : τ.γ = .C)
    {i j : ℕ} (hmem : (i, j) ∉ τ.P.shape) :
    PBP.descentPaintL_CD τ i j = .dot := by
  simp only [PBP.descentPaintL_CD]
  split_ifs with h1 h2
  · rfl
  · exfalso; apply hmem
    exact YoungDiagram.mem_iff_lt_colLen.mpr
      (lt_of_lt_of_le h2 (PBP.dotScolLen_le_colLen τ.P τ.mono_P j))
  · exact τ.P.paint_outside i j hmem

/-- In C-type, if P.paint = dot and (i,j) ∈ P, then i < dotScolLen(P, j). -/
private lemma C_dot_lt_dotScolLen {τ : PBP} (hγ : τ.γ = .C)
    {i j : ℕ} (hmem : (i, j) ∈ τ.P.shape) (hdot : τ.P.paint i j = .dot) :
    i < PBP.dotScolLen τ.P j := by
  -- C-type P has no .s, so dot cells have layerOrd 0 ≤ 1.
  -- By mono_P, all cells above (i,j) also have layerOrd ≤ 1.
  -- dotScolLen counts exactly these cells.
  sorry

/-- shiftLeft(Q) ≤ P when shapes come from dp. -/
private lemma shiftLeft_Q_le_P_of_dp {μP μQ : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (hP : μP.colLens = dpartColLensP_C (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_C (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (hodd : ∀ r ∈ r₁ :: r₂ :: rest, Odd r) :
    YoungDiagram.shiftLeft μQ ≤ μP := by
  sorry

/-! ## C→D descent PBP construction -/

/-- Construct D-type PBP from C-type via descent.
    Sorry: 5 constraint proofs (mono_P, row_s, row_r, col_c_P, col_d_P). -/
noncomputable def descentCD_PBP {μP μQ : YoungDiagram}
    (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    PBPSet .D μP (YoungDiagram.shiftLeft μQ) := by
  have hγ : τ.val.γ = .C := τ.prop.1
  have hPsh : τ.val.P.shape = μP := τ.prop.2.1
  have hQsh : τ.val.Q.shape = μQ := τ.prop.2.2
  -- Extract key properties before constructing the PBP
  -- row_r: .r in descent paint only from zone 3 (preserved P paint)
  have h_row_r : ∀ i j, PBP.descentPaintL_CD τ.val i j = .r → τ.val.P.paint i j = .r := by
    intro i j h; simp only [PBP.descentPaintL_CD] at h
    split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
  -- col_c_P: .c in descent paint only from zone 3
  have h_col_c : ∀ i j, PBP.descentPaintL_CD τ.val i j = .c → τ.val.P.paint i j = .c := by
    intro i j h; simp only [PBP.descentPaintL_CD] at h
    split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
  -- col_d_P: .d in descent paint only from zone 3
  have h_col_d : ∀ i j, PBP.descentPaintL_CD τ.val i j = .d → τ.val.P.paint i j = .d := by
    intro i j h; simp only [PBP.descentPaintL_CD] at h
    split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
  exact ⟨{
    γ := .D
    P := {
      shape := μP
      paint := PBP.descentPaintL_CD τ.val
      paint_outside := fun i j hmem => descentPaintL_CD_outside hγ (by rw [hPsh]; exact hmem)
    }
    Q := {
      shape := YoungDiagram.shiftLeft μQ
      paint := fun _ _ => .dot
      paint_outside := fun _ _ _ => rfl
    }
    sym_P := fun _ _ _ => by simp [DRCSymbol.allowed]
    sym_Q := fun _ _ _ => by simp [DRCSymbol.allowed]
    dot_match := sorry
    mono_P := sorry
    mono_Q := fun _ _ _ _ _ _ _ => by simp [DRCSymbol.layerOrd]
    row_s := sorry
    row_r := by
      intro i s₁ s₂ j₁ j₂ h₁ h₂
      simp only [paintBySide] at h₁ h₂
      cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
      · have := τ.val.row_r i .L .L j₁ j₂
            (by simp [paintBySide]; exact h_row_r i j₁ h₁)
            (by simp [paintBySide]; exact h_row_r i j₂ h₂)
        exact ⟨rfl, this.2⟩
      · exact absurd h₂ (by simp)
      · exact absurd h₁ (by simp)
      · exact absurd h₁ (by simp)
    col_c_P := fun j i₁ i₂ h₁ h₂ =>
      τ.val.col_c_P j i₁ i₂ (h_col_c i₁ j h₁) (h_col_c i₂ j h₂)
    col_c_Q := fun _ _ _ h => DRCSymbol.noConfusion h
    col_d_P := fun j i₁ i₂ h₁ h₂ =>
      τ.val.col_d_P j i₁ i₂ (h_col_d i₁ j h₁) (h_col_d i₂ j h₂)
    col_d_Q := fun _ _ _ h => DRCSymbol.noConfusion h
  }, ⟨rfl, rfl, rfl⟩⟩

/-! ## Descent injectivity -/

theorem descentCD_injective {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    Function.Injective (descentCD_PBP · h_sub : PBPSet .C μP μQ → _) := by
  sorry

/-! ## Column length lemmas -/

lemma dpartColLensP_C_cons₂ (r₁ r₂ : ℕ) (rest : DualPart) :
    dpartColLensP_C (r₁ :: r₂ :: rest) = dpartColLensP_D (r₂ :: rest) := rfl

lemma dpartColLensQ_C_cons₂_pos (r₁ r₂ : ℕ) (rest : DualPart) (h : r₁ > 1) :
    dpartColLensQ_C (r₁ :: r₂ :: rest) =
      (r₁ - 1) / 2 :: dpartColLensQ_D (r₂ :: rest) := by
  simp [dpartColLensQ_C, h]

lemma shiftLeft_Q_eq_D_Q {μQ : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (hQ : μQ.colLens = dpartColLensQ_C (r₁ :: r₂ :: rest)) (h : r₁ > 1) :
    (YoungDiagram.shiftLeft μQ).colLens = dpartColLensQ_D (r₂ :: rest) := by
  rw [YoungDiagram.colLens_shiftLeft, hQ, dpartColLensQ_C_cons₂_pos _ _ _ h]; rfl

/-! ## Image characterization -/

theorem card_C_eq_card_D_primitive {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_prim : μQ.colLen 0 ≥ μP.colLen 0) :
    Fintype.card (PBPSet .C μP μQ) =
      Fintype.card (PBPSet .D μP (YoungDiagram.shiftLeft μQ)) := by
  sorry

theorem card_C_eq_DD_plus_RC_balanced {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1) :
    Fintype.card (PBPSet .C μP μQ) =
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card +
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card := by
  sorry

/-! ## Base case -/

theorem card_PBPSet_C_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_C [r₁])
    (hQ : μQ.colLens = dpartColLensQ_C [r₁])
    (hodd : Odd r₁) :
    Fintype.card (PBPSet .C μP μQ) = 1 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  by_cases hr : r₁ > 1
  · -- Q has cells, all forced to s. P = ⊥ means all Q cells are non-dot (by dot_match).
    -- The unique PBP has P = all dot, Q = all s.
    sorry
  · -- r₁ = 1, Q = ⊥
    have : r₁ = 1 := by obtain ⟨m, rfl⟩ := hodd; omega
    subst this
    have hQ_nil : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    rw [hQ_nil]; exact card_PBPSet_bot .C

/-! ## Main theorem -/

/-- **Proposition 10.12 (C-type)**: `card(PBPSet .C μP μQ) = countPBP_C dp`. -/
theorem card_PBPSet_C_eq_countPBP_C (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_C dp)
    (hQ : μQ.colLens = dpartColLensQ_C dp)
    (hsort : dp.SortedGE)
    (hodd : ∀ r ∈ dp, Odd r)
    (hne : dp ≠ []) :
    Fintype.card (PBPSet .C μP μQ) = countPBP_C dp := by
  match dp, hP, hQ, hsort, hodd, hne with
  | [r₁], hP, hQ, _, hodd, _ =>
    rw [show countPBP_C [r₁] = 1 from rfl]
    exact card_PBPSet_C_singleton r₁ hP hQ (hodd r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, hodd, _ =>
    set dp_D := r₂ :: rest
    have hr₁_odd := hodd r₁ (by simp)
    have hr₂_odd := hodd r₂ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))
    have hr₁_ge_r₂ : r₂ ≤ r₁ := by
      have := hsort.pairwise; rw [List.pairwise_cons] at this
      exact this.1 r₂ (List.mem_cons.mpr (Or.inl rfl))
    have hP_D : μP.colLens = dpartColLensP_D dp_D := by rw [hP]; rfl
    have hsort_D : dp_D.SortedGE := by
      have hp := hsort.pairwise; rw [List.pairwise_cons] at hp; exact hp.2.sortedGE
    have hodd_D : ∀ r ∈ dp_D, Odd r :=
      fun r hr => hodd r (List.mem_cons_of_mem _ hr)
    have h_sub := shiftLeft_Q_le_P_of_dp hP hQ hsort hodd
    have hQ_D : (YoungDiagram.shiftLeft μQ).colLens = dpartColLensQ_D dp_D := by
      sorry
    show Fintype.card (PBPSet .C μP μQ) = countPBP_C (r₁ :: r₂ :: rest)
    simp only [countPBP_C]
    by_cases h_prim : r₁ > r₂
    · simp only [if_pos h_prim]
      have h_prim_geo : μQ.colLen 0 ≥ μP.colLen 0 := by sorry
      rw [card_C_eq_card_D_primitive h_sub h_prim_geo]
      exact card_PBPSet_D_eq_tripleSum_countPBP_D dp_D μP
        (YoungDiagram.shiftLeft μQ) hP_D hQ_D hsort_D hodd_D
    · push_neg at h_prim
      have hr₁_eq : r₁ = r₂ := le_antisymm h_prim hr₁_ge_r₂
      simp only [if_neg (by omega : ¬(r₁ > r₂))]
      have h_bal_geo : μP.colLen 0 = μQ.colLen 0 + 1 := by sorry
      rw [card_C_eq_DD_plus_RC_balanced h_sub h_bal_geo]
      have hne_D : dp_D ≠ [] := List.cons_ne_nil _ _
      have ⟨h_dd, h_rc⟩ := card_PBPSet_D_per_tc dp_D μP
        (YoungDiagram.shiftLeft μQ) hP_D hQ_D hsort_D hodd_D hne_D
      rw [h_dd, h_rc]
