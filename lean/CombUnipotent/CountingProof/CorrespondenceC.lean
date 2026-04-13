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
  -- dot_match extracted
  have h_dot_fwd : ∀ i j, (i, j) ∈ μP → PBP.descentPaintL_CD τ.val i j = .dot →
      (i, j) ∈ YoungDiagram.shiftLeft μQ := by
    intro i j hmemP hpaint
    simp only [PBP.descentPaintL_CD] at hpaint
    split_ifs at hpaint with h1 h2
    · rw [hQsh] at h1
      exact YoungDiagram.mem_shiftLeft.mpr (YoungDiagram.mem_iff_lt_colLen.mpr h1)
    · exact absurd (C_dot_lt_dotScolLen hγ (by rw [hPsh]; exact hmemP) hpaint) h2
  have h_dot_bwd : ∀ i j, (i, j) ∈ YoungDiagram.shiftLeft μQ →
      (i, j) ∈ μP ∧ PBP.descentPaintL_CD τ.val i j = .dot := by
    intro i j hmemQ
    have h_lt : i < τ.val.Q.shape.colLen (j + 1) := by
      rw [hQsh]
      have := YoungDiagram.mem_shiftLeft.mp hmemQ
      exact YoungDiagram.mem_iff_lt_colLen.mp this
    exact ⟨h_sub hmemQ, by simp [PBP.descentPaintL_CD, if_pos h_lt]⟩
  -- row_s: s in descent paint zones
  -- s in descent paint only from zone 2
  have h_s_zone : ∀ i j, PBP.descentPaintL_CD τ.val i j = .s →
      i ≥ τ.val.Q.shape.colLen (j + 1) ∧ i < PBP.dotScolLen τ.val.P j := by
    intro i j h
    unfold PBP.descentPaintL_CD at h
    by_cases h1 : i < τ.val.Q.shape.colLen (j + 1)
    · simp [if_pos h1] at h  -- zone 1: .dot = .s → absurd
    · rw [if_neg h1] at h
      by_cases h2 : i < PBP.dotScolLen τ.val.P j
      · exact ⟨Nat.le_of_not_lt h1, h2⟩  -- zone 2: .s = .s, extract bounds
      · -- zone 3: P.paint = .s, impossible
        rw [if_neg h2] at h
        exfalso
        by_cases hmem : (i, j) ∈ τ.val.P.shape
        · have hsym := τ.val.sym_P i j hmem; rw [hγ] at hsym
          simp [DRCSymbol.allowed] at hsym
          rcases hsym with hp | hp | hp | hp <;> rw [hp] at h <;> simp at h
        · rw [τ.val.P.paint_outside i j hmem] at h; simp at h
  -- mono_P: descent paint is monotone. Zone-based case analysis.
  -- Helper: Q.colLen is anti-monotone (from τ.val.Q.shape being a YoungDiagram)
  have hQ_anti : ∀ a b, a ≤ b → τ.val.Q.shape.colLen b ≤ τ.val.Q.shape.colLen a :=
    fun a b h => τ.val.Q.shape.colLen_anti a b h
  -- Helper: dotScolLen is anti-monotone (from dotSdiag being a YoungDiagram)
  have hDS_anti : ∀ a b, a ≤ b → PBP.dotScolLen τ.val.P b ≤ PBP.dotScolLen τ.val.P a := by
    intro a b h
    rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.mono_P,
        PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.mono_P]
    exact (PBP.dotSdiag τ.val.P τ.val.mono_P).colLen_anti a b h
  -- Helper: layerOrd > 1 for cells at or past dotScolLen
  have h_layer_ge2 : ∀ i j, i ≥ PBP.dotScolLen τ.val.P j → (i, j) ∈ τ.val.P.shape →
      (τ.val.P.paint i j).layerOrd ≥ 2 := by
    intro i j hge hmem
    exact PBP.layerOrd_gt_one_of_ge_dotScolLen τ.val.P τ.val.mono_P hge hmem
  have h_mono_P : ∀ i₁ j₁ i₂ j₂, i₁ ≤ i₂ → j₁ ≤ j₂ → (i₂, j₂) ∈ μP →
      (PBP.descentPaintL_CD τ.val i₁ j₁).layerOrd ≤ (PBP.descentPaintL_CD τ.val i₂ j₂).layerOrd := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    -- Determine zone for (i₁, j₁)
    by_cases hz1 : i₁ < τ.val.Q.shape.colLen (j₁ + 1)
    · -- zone 1: dot, layer 0 ≤ anything
      have : PBP.descentPaintL_CD τ.val i₁ j₁ = .dot := by
        simp [PBP.descentPaintL_CD, if_pos hz1]
      rw [this]; simp [DRCSymbol.layerOrd]
    · by_cases hz2 : i₁ < PBP.dotScolLen τ.val.P j₁
      · -- zone 2: s, layer 1
        have hpaint₁ : PBP.descentPaintL_CD τ.val i₁ j₁ = .s := by
          simp [PBP.descentPaintL_CD, if_neg hz1, if_pos hz2]
        rw [hpaint₁]; simp only [DRCSymbol.layerOrd]
        -- (i₂,j₂) in zone 2 or 3 (not zone 1)
        by_cases hz1' : i₂ < τ.val.Q.shape.colLen (j₂ + 1)
        · exfalso; have := hQ_anti (j₁+1) (j₂+1) (by omega); omega
        · by_cases hz2' : i₂ < PBP.dotScolLen τ.val.P j₂
          · -- zone 2: s, layer 1 ≤ 1
            have hd : PBP.descentPaintL_CD τ.val i₂ j₂ = .s := by
              simp [PBP.descentPaintL_CD, if_neg hz1', if_pos hz2']
            rw [hd]
          · -- zone 3: P.paint, layer ≥ 2 ≥ 1
            have hd : PBP.descentPaintL_CD τ.val i₂ j₂ = τ.val.P.paint i₂ j₂ := by
              simp [PBP.descentPaintL_CD, if_neg hz1', if_neg hz2']
            rw [hd]
            exact le_trans (by omega : 1 ≤ 2)
              (h_layer_ge2 i₂ j₂ (Nat.le_of_not_lt hz2') (by rw [hPsh]; exact hmem₂))
      · -- zone 3: P.paint, layer ≥ 2
        have hpaint₁ : PBP.descentPaintL_CD τ.val i₁ j₁ = τ.val.P.paint i₁ j₁ := by
          simp [PBP.descentPaintL_CD, if_neg hz1, if_neg hz2]
        rw [hpaint₁]
        -- (i₂,j₂) must be zone 3
        by_cases hz1' : i₂ < τ.val.Q.shape.colLen (j₂ + 1)
        · exfalso; have := hQ_anti (j₁+1) (j₂+1) (by omega); omega
        · simp [PBP.descentPaintL_CD, if_neg hz1']
          split_ifs with hz2'
          · exfalso; have := hDS_anti j₁ j₂ hj; omega
          · exact τ.val.mono_P i₁ j₁ i₂ j₂ hi hj (by rw [hPsh]; exact hmem₂)

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
    dot_match := by
      intro i j; constructor
      · intro ⟨hmP, hp⟩; exact ⟨h_dot_fwd i j hmP hp, rfl⟩
      · intro ⟨hmQ, _⟩; exact h_dot_bwd i j hmQ
    mono_P := h_mono_P
    mono_Q := fun _ _ _ _ _ _ _ => by simp [DRCSymbol.layerOrd]
    row_s := by
      intro i s₁ s₂ j₁ j₂ h₁ h₂
      simp only [paintBySide] at h₁ h₂
      cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
      · -- Both L, both .s: zone 2 at j₁ and j₂
        obtain ⟨hge₁, hlt₁⟩ := h_s_zone i j₁ h₁
        obtain ⟨hge₂, hlt₂⟩ := h_s_zone i j₂ h₂
        refine ⟨rfl, ?_⟩
        -- Anti-monotonicity argument
        -- Anti-monotonicity: if j₁ < j₂ then Q.colLen(j₁+1) ≥ Q.colLen(j₂) ≥ dotScolLen(P,j₂) > i
        -- But i ≥ Q.colLen(j₁+1). Contradiction. Similarly j₂ < j₁.
        by_contra hne
        have : j₁ < j₂ ∨ j₂ < j₁ := Nat.lt_or_gt_of_ne hne
        -- C-type: dotScolLen(P,j) ≤ Q.colLen(j) since P dots ⊆ Q
        -- C-type: dotScolLen(P,k) ≤ Q.colLen(k) since P dots ⊆ Q via dot_match
        have h_ds_le_Q : ∀ k, PBP.dotScolLen τ.val.P k ≤ τ.val.Q.shape.colLen k := by
          intro k; unfold PBP.dotScolLen
          rw [YoungDiagram.colLen_eq_card]
          apply Finset.card_le_card
          intro ⟨ci, ck⟩ hmem
          simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.col] at hmem ⊢
          obtain ⟨hP, hk, hlo⟩ := hmem
          refine ⟨?_, hk⟩
          -- (ci, ck) ∈ Q: layerOrd ≤ 1 in C-type → dot → in Q by dot_match
          have hdot : τ.val.P.paint ci ck = .dot := by
            have hsym := τ.val.sym_P ci ck hP; rw [hγ] at hsym
            simp [DRCSymbol.allowed] at hsym
            rcases hsym with hp | hp | hp | hp <;> rw [hp] at hlo ⊢ <;>
              simp [DRCSymbol.layerOrd] at hlo ⊢
          exact (τ.val.dot_match ci ck).mp ⟨hP, hdot⟩ |>.1
        rcases this with h | h
        · -- j₁ < j₂: dotScolLen(P, j₂) ≤ Q.colLen(j₂) ≤ Q.colLen(j₁+1) ≤ i < dotScolLen(P, j₂)
          have hQ_anti : τ.val.Q.shape.colLen j₂ ≤ τ.val.Q.shape.colLen (j₁ + 1) := by
            rw [hQsh]; exact μQ.colLen_anti _ _ (by omega)
          have := h_ds_le_Q j₂; omega
        · have hQ_anti : τ.val.Q.shape.colLen j₁ ≤ τ.val.Q.shape.colLen (j₂ + 1) := by
            rw [hQsh]; exact μQ.colLen_anti _ _ (by omega)
          have := h_ds_le_Q j₁; omega
      · exact absurd h₂ (by simp)
      · exact absurd h₁ (by simp)
      · exact absurd h₁ (by simp)
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
  exact ⟨{
    γ := .C
    P := { shape := μP, paint := liftPaintP_CD σ.val
           paint_outside := sorry }
    Q := { shape := μQ, paint := liftPaintQ_CD σ.val μQ
           paint_outside := sorry }
    sym_P := sorry
    sym_Q := sorry
    dot_match := sorry
    mono_P := sorry
    mono_Q := sorry
    row_s := sorry
    row_r := sorry
    col_c_P := sorry
    col_c_Q := sorry
    col_d_P := sorry
    col_d_Q := sorry
  }, ⟨rfl, rfl, rfl⟩⟩

/-- Round trip: descent ∘ lift = id on D-type PBPs. -/
theorem descentCD_liftCD_round_trip {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ)) :
    descentCD_PBP (liftCD_PBP σ h_sub) h_sub = σ := by
  sorry

/-- Descent image excludes SS in the balanced case. -/
theorem descentCD_not_SS {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1)
    (τ : PBPSet .C μP μQ) :
    tailClass_D (descentCD_PBP τ h_sub).val ≠ .SS := by
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
