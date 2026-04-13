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
  rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
  exact YoungDiagram.mem_iff_lt_colLen.mp (show (i, j) ∈ PBP.dotSdiag τ.P τ.mono_P from by
    simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hmem, by rw [hdot]; decide⟩)

/-- shiftLeft(Q) ≤ P when shapes come from dp. -/
private lemma shiftLeft_Q_le_P_of_dp {μP μQ : YoungDiagram} {r₁ r₂ : ℕ} {rest : DualPart}
    (hP : μP.colLens = dpartColLensP_C (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_C (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (hodd : ∀ r ∈ r₁ :: r₂ :: rest, Odd r) :
    YoungDiagram.shiftLeft μQ ≤ μP := by
  -- shiftLeft(Q).colLens = dpartColLensQ_D(r₂::rest) (the D-type Q cols)
  -- P.colLens = dpartColLensP_D(r₂::rest) (the D-type P cols)
  -- Need: D-type Q ≤ D-type P, i.e., each Q col entry ≤ corresponding P col entry
  -- For each pair in the D dp: Q entry (r-1)/2 ≤ P entry (r'+1)/2 since r' ≥ r (sorted)
  sorry

/-! ## C→D descent PBP construction -/

/-- Raw PBP for C→D descent. Uses `where` for field transparency. -/
noncomputable def descentCD_raw (τ : PBP) (hγ : τ.γ = .C)
    (μP μQ : YoungDiagram) (hPsh : τ.P.shape = μP) (hQsh : τ.Q.shape = μQ)
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) : PBP where
  γ := .D
  P := { shape := μP
         paint := PBP.descentPaintL_CD τ
         paint_outside := fun i j hmem => descentPaintL_CD_outside hγ (by rw [hPsh]; exact hmem) }
  Q := { shape := YoungDiagram.shiftLeft μQ
         paint := fun _ _ => .dot
         paint_outside := fun _ _ _ => rfl }
  sym_P := fun _ _ _ => by simp [DRCSymbol.allowed]
  sym_Q := fun _ _ _ => by simp [DRCSymbol.allowed]
  dot_match := sorry
  mono_P := sorry
  mono_Q := fun _ _ _ _ _ _ _ => by simp [DRCSymbol.layerOrd]
  row_s := sorry
  row_r := sorry
  col_c_P := sorry
  col_c_Q := fun _ _ _ h => DRCSymbol.noConfusion h
  col_d_P := sorry
  col_d_Q := fun _ _ _ h => DRCSymbol.noConfusion h

/-- C→D descent as PBPSet map. Fields are transparent via `descentCD_raw`. -/
noncomputable def descentCD_PBP {μP μQ : YoungDiagram}
    (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    PBPSet .D μP (YoungDiagram.shiftLeft μQ) :=
  ⟨descentCD_raw τ.val τ.prop.1 μP μQ τ.prop.2.1 τ.prop.2.2 h_sub, ⟨rfl, rfl, rfl⟩⟩

-- Verify transparency: paint access reduces by rfl
example {μP μQ : YoungDiagram} (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (i j : ℕ) : (descentCD_PBP τ h_sub).val.P.paint i j = PBP.descentPaintL_CD τ.val i j := rfl
example {μP μQ : YoungDiagram} (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (descentCD_PBP τ h_sub).val.γ = .D := rfl
example {μP μQ : YoungDiagram} (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (descentCD_PBP τ h_sub).val.P.shape = μP := rfl
example {μP μQ : YoungDiagram} (τ : PBPSet .C μP μQ) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (descentCD_PBP τ h_sub).val.Q.shape = YoungDiagram.shiftLeft μQ := rfl

/-! ## Descent injectivity -/

theorem descentCD_injective {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    Function.Injective (descentCD_PBP · h_sub : PBPSet .C μP μQ → _) := by
  intro τ₁ τ₂ h_eq
  -- descentCD_PBP τ₁ = descentCD_PBP τ₂ implies their P paints agree:
  -- descentPaintL_CD τ₁ = descentPaintL_CD τ₂
  have h_paint : ∀ i j, PBP.descentPaintL_CD τ₁.val i j = PBP.descentPaintL_CD τ₂.val i j := by
    intro i j
    have := congrArg (fun σ => σ.val.P.paint i j) h_eq
    simp [descentCD_PBP] at this
    exact this
  -- By descent_inj_CD, the original C-type PBPs are equal
  have ⟨hP_eq, hQ_eq⟩ := PBP.descent_inj_CD τ₁.val τ₂.val
    τ₁.prop.1 τ₂.prop.1
    (τ₁.prop.2.1.trans τ₂.prop.2.1.symm)
    (τ₁.prop.2.2.trans τ₂.prop.2.2.symm)
    h_paint
  exact Subtype.ext (PBP.ext'' (τ₁.prop.1.trans τ₂.prop.1.symm)
    (PaintedYoungDiagram.ext' (τ₁.prop.2.1.trans τ₂.prop.2.1.symm) (funext fun i => funext fun j => hP_eq i j))
    (PaintedYoungDiagram.ext' (τ₁.prop.2.2.trans τ₂.prop.2.2.symm) (funext fun i => funext fun j => hQ_eq i j)))

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

/-! ## Inverse construction: D→C lift -/

/-- The C-type P paint from a D-type PBP: replace dot+s with dot, keep r/c/d. -/
private noncomputable def liftPaintP_CD (σ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j => if (σ.P.paint i j).layerOrd ≤ 1 then .dot else σ.P.paint i j

/-- The C-type Q paint: s where P is non-dot inside Q shape, dot elsewhere. -/
private noncomputable def liftPaintQ_CD (σ : PBP) (μQ : YoungDiagram) : ℕ → ℕ → DRCSymbol :=
  fun i j => if (i, j) ∈ μQ ∧ ¬(σ.P.paint i j).layerOrd ≤ 1 then .s else .dot

/-- Construct C-type PBP from D-type. Sorry: PBP constraints. -/
noncomputable def liftCD_PBP {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ))
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    PBPSet .C μP μQ := by
  have hγ : σ.val.γ = .D := σ.prop.1
  have hPsh : σ.val.P.shape = μP := σ.prop.2.1
  have hQsh : σ.val.Q.shape = YoungDiagram.shiftLeft μQ := σ.prop.2.2
  -- Extract: r/c/d preserved from D-type
  have h_rcd : ∀ i j, (σ.val.P.paint i j).layerOrd > 1 →
      liftPaintP_CD σ.val i j = σ.val.P.paint i j := by
    intro i j h; simp [liftPaintP_CD, show ¬(σ.val.P.paint i j).layerOrd ≤ 1 by omega]
  exact ⟨{
    γ := .C
    P := { shape := μP, paint := liftPaintP_CD σ.val
           paint_outside := fun i j hmem => by
             simp [liftPaintP_CD, σ.val.P.paint_outside i j (by rw [hPsh]; exact hmem)] }
    Q := { shape := μQ, paint := liftPaintQ_CD σ.val μQ
           paint_outside := fun i j hmem => by simp [liftPaintQ_CD, hmem] }
    sym_P := by
      intro i j hmem; simp only [liftPaintP_CD]
      split_ifs with h
      · exact Or.inl rfl  -- dot is allowed for C-L
      · -- layerOrd > 1: paint ∈ {r,c,d} (D-type allows all, C-L allows dot/r/c/d)
        have := σ.val.sym_P i j (by rw [hPsh]; exact hmem)
        -- paint has layerOrd > 1, so ∈ {r, c, d} — all allowed for C-L
        cases hp : σ.val.P.paint i j <;> (rw [hp] at h; simp [DRCSymbol.layerOrd] at h) <;>
          simp [DRCSymbol.allowed]
    sym_Q := by
      intro i j hmem; simp only [liftPaintQ_CD]
      split_ifs with h
      · exact Or.inr rfl  -- s is allowed for C-R
      · exact Or.inl rfl  -- dot is allowed for C-R
    dot_match := sorry
    mono_P := sorry
    mono_Q := sorry
    row_s := sorry
    row_r := sorry
    col_c_P := by
      intro j i₁ i₂ h₁ h₂; simp only [liftPaintP_CD] at h₁ h₂
      split_ifs at h₁ with ha₁ <;> split_ifs at h₂ with ha₂ <;>
        first | exact absurd h₁ (by decide) | exact absurd h₂ (by decide) |
          exact σ.val.col_c_P j i₁ i₂ h₁ h₂
    col_c_Q := by
      intro j i₁ i₂ h₁ h₂; simp only [liftPaintQ_CD] at h₁ h₂
      split_ifs at h₁ <;> exact absurd h₁ (by decide)
    col_d_P := by
      intro j i₁ i₂ h₁ h₂; simp only [liftPaintP_CD] at h₁ h₂
      split_ifs at h₁ with ha₁ <;> split_ifs at h₂ with ha₂ <;>
        first | exact absurd h₁ (by decide) | exact absurd h₂ (by decide) |
          exact σ.val.col_d_P j i₁ i₂ h₁ h₂
    col_d_Q := by
      intro j i₁ i₂ h₁ h₂; simp only [liftPaintQ_CD] at h₁ h₂
      split_ifs at h₁ <;> exact absurd h₁ (by decide)
  }, ⟨rfl, rfl, rfl⟩⟩

-- Access lemmas for liftCD_PBP
@[simp] lemma liftCD_PBP_γ {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (liftCD_PBP σ h_sub).val.γ = .C := (liftCD_PBP σ h_sub).prop.1
@[simp] lemma liftCD_PBP_P_shape {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (liftCD_PBP σ h_sub).val.P.shape = μP := (liftCD_PBP σ h_sub).prop.2.1
@[simp] lemma liftCD_PBP_Q_shape {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    (liftCD_PBP σ h_sub).val.Q.shape = μQ := (liftCD_PBP σ h_sub).prop.2.2
@[simp] lemma liftCD_PBP_P_paint {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) (i j : ℕ) :
    (liftCD_PBP σ h_sub).val.P.paint i j = liftPaintP_CD σ.val i j := by
  rfl

/-- Round trip: descent ∘ lift = id on D-type PBPs. -/
theorem descentCD_liftCD_round_trip {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) :
    descentCD_PBP (liftCD_PBP σ h_sub) h_sub = σ := by
  -- Use descentCD_injective: descent ∘ lift is injective (from round trip)
  -- Equivalent: show paint equality, then use PBP extensionality
  -- Round trip: paint equality by zone analysis (dot→dot, s→dot→s, r/c/d→same→same)
  -- Access lemmas make paint functions transparent; zone boundaries match.
  sorry

/-- Descent image excludes SS in the balanced case. -/
theorem descentCD_not_SS {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1)
    (τ : PBPSet .C μP μQ) :
    tailClass_D (descentCD_PBP τ h_sub).val ≠ .SS := by
  -- Tail class depends on tailLen_D and tailSymbol_D.
  -- For balanced: P.colLen(0) > Q.colLen(0) (= shiftLeft Q.colLen(0)),
  -- so tailLen > 0 and tailSymbol determines tail class.
  -- The tail cell at (P.colLen(0)-1, 0) has C-type P paint ∈ {r,c,d}
  -- (not dot since outside Q zone, not s since C-type).
  -- In descent: this paint is preserved (zone 3). So tail ∈ {r,c,d} → DD or RC.
  sorry

/-! ## Image characterization -/

theorem card_C_eq_card_D_primitive {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_prim : μQ.colLen 0 ≥ μP.colLen 0) :
    Fintype.card (PBPSet .C μP μQ) =
      Fintype.card (PBPSet .D μP (YoungDiagram.shiftLeft μQ)) := by
  apply le_antisymm
  · exact Fintype.card_le_of_injective _ (descentCD_injective h_sub)
  · apply Fintype.card_le_of_injective (liftCD_PBP · h_sub)
    intro σ₁ σ₂ h
    have h1 := congrArg (descentCD_PBP · h_sub) h
    simp only [descentCD_liftCD_round_trip] at h1
    exact h1

theorem card_C_eq_DD_plus_RC_balanced {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1) :
    Fintype.card (PBPSet .C μP μQ) =
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card +
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card := by
  -- Use: |C| = |image of descent| = |{σ ∈ D | tc ≠ SS}| = |DD| + |RC|
  -- Forward: descent maps into DD ∪ RC (descentCD_not_SS)
  -- Backward: DD ∪ RC PBPs have preimages (liftCD_PBP + round trip)
  -- Total = DD + RC + SS, image = DD + RC
  have h_total := card_PBPSet_eq_sum_tc μP (YoungDiagram.shiftLeft μQ)
  -- |C| ≤ |DD| + |RC|: descent is injective and image ⊆ DD ∪ RC
  have h_le : Fintype.card (PBPSet .C μP μQ) ≤
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card +
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card := by
    sorry
  -- |C| ≥ |DD| + |RC|: lift DD∪RC PBPs to C-type
  have h_ge : Fintype.card (PBPSet .C μP μQ) ≥
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .DD)).card +
      (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
        tailClass_D σ.val = .RC)).card := by
    sorry
  omega

/-! ## Base case -/

theorem card_PBPSet_C_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_C [r₁])
    (hQ : μQ.colLens = dpartColLensQ_C [r₁])
    (hodd : Odd r₁) :
    Fintype.card (PBPSet .C μP μQ) = 1 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  by_cases hr : r₁ > 1
  · -- P = ⊥. For any C-type PBP:
    -- P paint = dot everywhere (paint_outside, since ⊥ has no cells)
    -- For (i,j) ∈ Q: dot_match LHS = False (since (i,j) ∉ ⊥), so RHS = False,
    --   so Q(i,j) ≠ dot, so Q(i,j) = s (only other C-type Q symbol)
    -- Q paint is fully determined. Hence card = 1.
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
      by_cases hr₁ : r₁ > 1
      · exact shiftLeft_Q_eq_D_Q hQ hr₁
      · -- r₁ = 1 → r₂ = 1 (sorted) → all rest ≤ 1 → Q = ⊥
        have hr₁_eq : r₁ = 1 := by obtain ⟨m, rfl⟩ := hr₁_odd; omega
        subst hr₁_eq
        have hr₂_le : r₂ ≤ 1 := hr₁_ge_r₂
        have hr₂_eq : r₂ = 1 := by obtain ⟨m, rfl⟩ := hr₂_odd; omega
        subst hr₂_eq
        have hrest_le := rest_all_one_of_sorted_r2_one 1 rest hsort
        have hQ_nil : μQ.colLens = [] := by
          rw [hQ]; simp [dpartColLensQ_C]
          exact dpartColLensQ_D_eq_nil_of_le_one (1 :: rest) (by
            intro r hr; rcases List.mem_cons.mp hr with rfl | hr
            · omega
            · exact hrest_le r hr)
        have hμQ := yd_of_colLens_nil hQ_nil
        rw [hμQ, shiftLeft_bot, colLens_bot]
        exact (dpartColLensQ_D_eq_nil_of_le_one dp_D (by
          intro r hr; rcases List.mem_cons.mp hr with rfl | hr
          · omega
          · exact hrest_le r hr)).symm
    -- colLen formulas
    have hQ_col0 : μQ.colLen 0 = (r₁ - 1) / 2 := by
      by_cases hr₁ : r₁ > 1
      · exact colLen_0_eq_of_colLens_cons (by
          rw [hQ, dpartColLensQ_C_cons₂_pos _ _ _ hr₁])
      · have : r₁ = 1 := by obtain ⟨m, rfl⟩ := hr₁_odd; omega
        subst this; simp
        have hQ_nil : μQ.colLens = [] := by
          rw [hQ]; simp [dpartColLensQ_C]
          have hr₂_eq : r₂ = 1 := by obtain ⟨m, rfl⟩ := hr₂_odd; omega
          subst hr₂_eq
          exact dpartColLensQ_D_eq_nil_of_le_one (1 :: rest)
            (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr
                · omega
                · exact rest_all_one_of_sorted_r2_one 1 rest hsort r hr)
        rw [yd_of_colLens_nil hQ_nil, colLen_bot]
    have hP_col0 : μP.colLen 0 = (r₂ + 1) / 2 := by
      have hexp : ∃ t, dpartColLensP_D dp_D = (r₂ + 1) / 2 :: t := by
        show ∃ t, dpartColLensP_D (r₂ :: rest) = _
        match rest with
        | [] => exact ⟨[], by simp [dpartColLensP_D]⟩
        | r₃ :: rest' => exact ⟨dpartColLensP_D rest', by rfl⟩
      obtain ⟨t, ht⟩ := hexp
      exact colLen_0_eq_of_colLens_cons (by rw [hP_D, ht])
    show Fintype.card (PBPSet .C μP μQ) = countPBP_C (r₁ :: r₂ :: rest)
    simp only [countPBP_C]
    by_cases h_prim : r₁ > r₂
    · simp only [if_pos h_prim]
      have h_prim_geo : μQ.colLen 0 ≥ μP.colLen 0 := by
        rw [hP_col0, hQ_col0]; obtain ⟨a, rfl⟩ := hr₁_odd; obtain ⟨b, rfl⟩ := hr₂_odd; omega
      rw [card_C_eq_card_D_primitive h_sub h_prim_geo]
      exact card_PBPSet_D_eq_tripleSum_countPBP_D dp_D μP
        (YoungDiagram.shiftLeft μQ) hP_D hQ_D hsort_D hodd_D
    · push_neg at h_prim
      have hr₁_eq : r₁ = r₂ := le_antisymm h_prim hr₁_ge_r₂
      simp only [if_neg (by omega : ¬(r₁ > r₂))]
      have h_bal_geo : μP.colLen 0 = μQ.colLen 0 + 1 := by
        rw [hP_col0, hQ_col0, hr₁_eq]; obtain ⟨a, rfl⟩ := hr₂_odd; omega
      rw [card_C_eq_DD_plus_RC_balanced h_sub h_bal_geo]
      have hne_D : dp_D ≠ [] := List.cons_ne_nil _ _
      have ⟨h_dd, h_rc⟩ := card_PBPSet_D_per_tc dp_D μP
        (YoungDiagram.shiftLeft μQ) hP_D hQ_D hsort_D hodd_D hne_D
      rw [h_dd, h_rc]
