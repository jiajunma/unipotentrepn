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
  -- shiftLeft(Q) ≤ P: for all (i,j), (i,j) ∈ shiftLeft Q → (i,j) ∈ P.
  -- Equiv: ∀ j, Q.colLen(j+1) ≤ P.colLen(j) (from dp structure).
  -- This is a property of the dp-derived shapes.
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
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP, hpaint⟩
      simp only [PBP.descentPaintL_CD] at hpaint
      split_ifs at hpaint with h1 h2
      · rw [hQsh] at h1
        exact ⟨YoungDiagram.mem_shiftLeft.mpr (YoungDiagram.mem_iff_lt_colLen.mpr h1), rfl⟩
      · exact absurd (C_dot_lt_dotScolLen hγ (by rw [hPsh]; exact hmemP) hpaint) h2
    · intro ⟨hmemQ, _⟩
      have h_lt : i < τ.Q.shape.colLen (j + 1) := by
        rw [hQsh]; exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_shiftLeft.mp hmemQ)
      exact ⟨hPsh ▸ (h_sub hmemQ), by simp [PBP.descentPaintL_CD, if_pos h_lt]⟩
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    -- Normalize: {shape, paint, ...}.paint i j = paint i j
    show (PBP.descentPaintL_CD τ i₁ j₁).layerOrd ≤ (PBP.descentPaintL_CD τ i₂ j₂).layerOrd
    have hmem₂' : (i₂, j₂) ∈ τ.P.shape := by rw [hPsh]; exact hmem₂
    have hQ_anti := fun a b (h : a ≤ b) => τ.Q.shape.colLen_anti a b h
    have hDS_anti : ∀ a b, a ≤ b → PBP.dotScolLen τ.P b ≤ PBP.dotScolLen τ.P a := by
      intro a b h; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
        PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
      exact (PBP.dotSdiag τ.P τ.mono_P).colLen_anti a b h
    by_cases hz1 : i₁ < τ.Q.shape.colLen (j₁ + 1)
    · simp [PBP.descentPaintL_CD, if_pos hz1, DRCSymbol.layerOrd]
    · by_cases hz2 : i₁ < PBP.dotScolLen τ.P j₁
      · simp only [PBP.descentPaintL_CD, if_neg hz1, if_pos hz2, DRCSymbol.layerOrd]
        by_cases hz1' : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · exfalso; have := hQ_anti (j₁+1) (j₂+1) (by omega); omega
        · by_cases hz2' : i₂ < PBP.dotScolLen τ.P j₂
          · simp [PBP.descentPaintL_CD, if_neg hz1', if_pos hz2', DRCSymbol.layerOrd]
          · simp only [PBP.descentPaintL_CD, if_neg hz1', if_neg hz2']
            exact le_trans (by omega : 1 ≤ 2)
              (PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P (Nat.le_of_not_lt hz2') hmem₂')
      · simp only [PBP.descentPaintL_CD, if_neg hz1, if_neg hz2]
        by_cases hz1' : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · exfalso; have := hQ_anti (j₁+1) (j₂+1) (by omega); omega
        · by_cases hz2' : i₂ < PBP.dotScolLen τ.P j₂
          · exfalso; have := hDS_anti j₁ j₂ hj; omega
          · simp only [PBP.descentPaintL_CD, if_neg hz1', if_neg hz2']
            exact τ.mono_P i₁ j₁ i₂ j₂ hi hj hmem₂'
  mono_Q := fun _ _ _ _ _ _ _ => by simp [DRCSymbol.layerOrd]
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- s zone analysis
      have h_s_zone : ∀ i' j', PBP.descentPaintL_CD τ i' j' = .s →
          i' ≥ τ.Q.shape.colLen (j' + 1) ∧ i' < PBP.dotScolLen τ.P j' := by
        intro i' j' h; unfold PBP.descentPaintL_CD at h
        by_cases h1 : i' < τ.Q.shape.colLen (j' + 1)
        · simp [if_pos h1] at h
        · rw [if_neg h1] at h; by_cases h2 : i' < PBP.dotScolLen τ.P j'
          · exact ⟨Nat.le_of_not_lt h1, h2⟩
          · rw [if_neg h2] at h; exfalso
            by_cases hmem : (i', j') ∈ τ.P.shape
            · have hsym := τ.sym_P i' j' hmem; rw [hγ] at hsym
              simp [DRCSymbol.allowed] at hsym
              rcases hsym with hp | hp | hp | hp <;> rw [hp] at h <;> simp at h
            · rw [τ.P.paint_outside i' j' hmem] at h; simp at h
      obtain ⟨hge₁, hlt₁⟩ := h_s_zone i j₁ h₁
      obtain ⟨hge₂, hlt₂⟩ := h_s_zone i j₂ h₂
      refine ⟨rfl, ?_⟩
      by_contra hne; have : j₁ < j₂ ∨ j₂ < j₁ := Nat.lt_or_gt_of_ne hne
      have h_ds_le_Q : ∀ k, PBP.dotScolLen τ.P k ≤ τ.Q.shape.colLen k := by
        intro k; unfold PBP.dotScolLen; rw [YoungDiagram.colLen_eq_card]
        apply Finset.card_le_card; intro ⟨ci, ck⟩ hmem
        simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.col] at hmem ⊢
        obtain ⟨hP, hk, hlo⟩ := hmem; refine ⟨?_, hk⟩
        have hdot : τ.P.paint ci ck = .dot := by
          have hsym := τ.sym_P ci ck hP; rw [hγ] at hsym
          simp [DRCSymbol.allowed] at hsym
          rcases hsym with hp | hp | hp | hp <;> rw [hp] at hlo ⊢ <;>
            simp [DRCSymbol.layerOrd] at hlo ⊢
        exact (τ.dot_match ci ck).mp ⟨hP, hdot⟩ |>.1
      rcases this with h | h
      · have hQ_anti := τ.Q.shape.colLen_anti (j₁+1) j₂ (by omega)
        have := h_ds_le_Q j₂; omega
      · have hQ_anti := τ.Q.shape.colLen_anti (j₂+1) j₁ (by omega)
        have := h_ds_le_Q j₁; omega
    · exact absurd h₂ (by simp)
    · exact absurd h₁ (by simp)
    · exact absurd h₁ (by simp)
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · have hr : ∀ i' j', PBP.descentPaintL_CD τ i' j' = .r → τ.P.paint i' j' = .r := by
        intro i' j' h; simp only [PBP.descentPaintL_CD] at h
        split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
      exact ⟨rfl, (τ.row_r i .L .L j₁ j₂
        (by simp [paintBySide]; exact hr i j₁ h₁) (by simp [paintBySide]; exact hr i j₂ h₂)).2⟩
    · exact absurd h₂ (by simp)
    · exact absurd h₁ (by simp)
    · exact absurd h₁ (by simp)
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    have hc : ∀ i' j', PBP.descentPaintL_CD τ i' j' = .c → τ.P.paint i' j' = .c := by
      intro i' j' h; simp only [PBP.descentPaintL_CD] at h
      split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
    exact τ.col_c_P j i₁ i₂ (hc i₁ j h₁) (hc i₂ j h₂)
  col_c_Q := fun _ _ _ h => DRCSymbol.noConfusion h
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    have hd : ∀ i' j', PBP.descentPaintL_CD τ i' j' = .d → τ.P.paint i' j' = .d := by
      intro i' j' h; simp only [PBP.descentPaintL_CD] at h
      split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
    exact τ.col_d_P j i₁ i₂ (hd i₁ j h₁) (hd i₂ j h₂)
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

/-- The C-type Q paint: s where Q cell is outside P OR P is non-dot. -/
private noncomputable def liftPaintQ_CD (σ : PBP) (μP μQ : YoungDiagram) : ℕ → ℕ → DRCSymbol :=
  fun i j => if (i, j) ∈ μQ ∧ ((i, j) ∉ μP ∨ ¬(σ.P.paint i j).layerOrd ≤ 1) then .s else .dot

private lemma liftPaintP_CD_ne_s (σ : PBP) (i j : ℕ) : liftPaintP_CD σ i j ≠ .s := by
  simp only [liftPaintP_CD]; split_ifs with h
  · exact (by decide : DRCSymbol.dot ≠ .s)
  · intro heq; rw [heq] at h; simp [DRCSymbol.layerOrd] at h
private lemma liftPaintP_CD_r (σ : PBP) (i j : ℕ) (h : liftPaintP_CD σ i j = .r) :
    σ.P.paint i j = .r := by
  simp only [liftPaintP_CD] at h; split_ifs at h <;> first | exact absurd h (by decide) | exact h
private lemma liftPaintQ_CD_ne_r (σ : PBP) (μQ : YoungDiagram) (i j : ℕ) :
    liftPaintQ_CD σ μP μQ i j ≠ .r := by
  simp only [liftPaintQ_CD]; split_ifs <;> decide

/-- Raw PBP for D→C lift. Uses `where` for field transparency. -/
noncomputable def liftCD_raw (σ : PBP) (hγ : σ.γ = .D)
    (μP μQ : YoungDiagram) (hPsh : σ.P.shape = μP)
    (hQsh : σ.Q.shape = YoungDiagram.shiftLeft μQ)
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) : PBP where
  γ := .C
  P := { shape := μP, paint := liftPaintP_CD σ
         paint_outside := fun i j hmem => by
           simp [liftPaintP_CD, σ.P.paint_outside i j (by rw [hPsh]; exact hmem)] }
  Q := { shape := μQ, paint := liftPaintQ_CD σ μP μQ
         paint_outside := fun i j hmem => by simp [liftPaintQ_CD, hmem] }
  sym_P := by
    intro i j hmem; simp only [liftPaintP_CD]; split_ifs with h
    · exact Or.inl rfl
    · cases hp : σ.P.paint i j <;> (rw [hp] at h; simp [DRCSymbol.layerOrd] at h) <;>
        simp [DRCSymbol.allowed]
  sym_Q := by
    intro i j hmem; simp only [liftPaintQ_CD]; split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  dot_match := by
    intro i j; constructor
    · -- Forward: liftP = dot ∧ ∈ μP → ∈ μQ ∧ liftQ = dot
      intro ⟨hmemP, hpaint⟩
      simp only [liftPaintP_CD] at hpaint
      split_ifs at hpaint with h
      · -- σ.P layerOrd ≤ 1. Need ∈ μQ.
        -- D-type dot_match: P = dot → ∈ shiftLeft μQ. shiftLeft μQ ⊆ μQ.
        -- For s: use anti-mono argument.
        sorry
      · exact absurd hpaint (by decide)
    · -- Backward: ∈ μQ ∧ liftQ = dot → liftP = dot ∧ ∈ μP
      intro ⟨hmemQ, hpaint⟩
      simp only [liftPaintQ_CD] at hpaint
      -- s = dot auto-closes. Remaining: ¬condition → liftQ = dot.
      split_ifs at hpaint with h
      -- h: ¬(∈ μQ ∧ (∉ μP ∨ layerOrd > 1)). Since ∈ μQ: ∈ μP ∧ layerOrd ≤ 1.
      push_neg at h
      have h' := h hmemQ
      exact ⟨h'.1, by simp [liftPaintP_CD, h'.2]⟩
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaintP_CD σ i₁ j₁).layerOrd ≤ (liftPaintP_CD σ i₂ j₂).layerOrd
    simp only [liftPaintP_CD]
    split_ifs with h1 h2
    · simp [DRCSymbol.layerOrd]
    · simp [DRCSymbol.layerOrd]
    · exfalso; exact absurd (σ.mono_P i₁ j₁ i₂ j₂ hi hj (by rw [hPsh]; exact hmem₂)) (by omega)
    · exact σ.mono_P i₁ j₁ i₂ j₂ hi hj (by rw [hPsh]; exact hmem₂)
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaintQ_CD σ μP μQ i₁ j₁).layerOrd ≤ (liftPaintQ_CD σ μP μQ i₂ j₂).layerOrd
    simp only [liftPaintQ_CD]
    by_cases h2 : (i₂, j₂) ∈ μQ ∧ ((i₂, j₂) ∉ μP ∨ ¬(σ.P.paint i₂ j₂).layerOrd ≤ 1)
    · rw [if_pos h2]; split_ifs <;> simp [DRCSymbol.layerOrd]  -- anything ≤ s(1)
    · rw [if_neg h2]  -- Q(i₂) = dot(0). Need Q(i₁) = dot(0).
      by_cases h1 : (i₁, j₁) ∈ μQ ∧ ((i₁, j₁) ∉ μP ∨ ¬(σ.P.paint i₁ j₁).layerOrd ≤ 1)
      · -- Q(i₁) = s but Q(i₂) = dot. Contradiction.
        exfalso; push_neg at h2
        obtain ⟨hmQ₁, hcase₁⟩ := h1
        obtain ⟨hmP₂, hlo₂⟩ := h2 hmem₂
        rcases hcase₁ with hnoP₁ | hhi₁
        · exact hnoP₁ (μP.isLowerSet (show (i₁, j₁) ≤ (i₂, j₂) from ⟨hi, hj⟩) hmP₂)
        · have hmP₁ : (i₁, j₁) ∈ σ.P.shape := by
            by_contra hout; exact hhi₁ (by rw [σ.P.paint_outside i₁ j₁ hout]; decide)
          exact absurd (σ.mono_P i₁ j₁ i₂ j₂ hi hj (by rw [hPsh]; exact hmP₂))
            (by omega)
      · rw [if_neg h1]  -- dot ≤ dot
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · exact absurd h₁ (liftPaintP_CD_ne_s σ i j₁)
    · exact absurd h₁ (liftPaintP_CD_ne_s σ i j₁)
    · exact absurd h₂ (liftPaintP_CD_ne_s σ i j₂)
    · -- Both R: Q(i,j₁) = s, Q(i,j₂) = s. Need j₁ = j₂.
      -- Anti-mono argument: j₁ < j₂ impossible.
      -- Q=s at (i,j₁): σ.P layerOrd > 1 → P ≠ dot → (i,j₁) ∉ shiftLeft μQ → i ≥ μQ.colLen(j₁+1)
      -- Q=s at (i,j₂): (i,j₂) ∈ μQ → i < μQ.colLen(j₂)
      -- Anti-mono: j₂ ≥ j₁+1 → μQ.colLen(j₂) ≤ μQ.colLen(j₁+1) → i < i. Contradiction!
      -- Extract Q=s conditions from h₁, h₂
      have ha₁ : (i, j₁) ∈ μQ ∧ ((i, j₁) ∉ μP ∨ ¬(σ.P.paint i j₁).layerOrd ≤ 1) := by
        simp only [liftPaintQ_CD] at h₁; split_ifs at h₁ with ha; exact ha
      have ha₂ : (i, j₂) ∈ μQ ∧ ((i, j₂) ∉ μP ∨ ¬(σ.P.paint i j₂).layerOrd ≤ 1) := by
        simp only [liftPaintQ_CD] at h₂; split_ifs at h₂ with ha; exact ha
      refine ⟨rfl, ?_⟩
      by_contra hne
      obtain ⟨hmQ₁, hcase₁⟩ := ha₁; obtain ⟨hmQ₂, hcase₂⟩ := ha₂
      -- Either ∉ μP or σ.P layerOrd > 1 → σ.P ≠ dot → ∉ shiftLeft μQ
      have h_notDQ₁ : (i, j₁) ∉ σ.Q.shape := by
        intro hmem
        have hQdot : σ.Q.paint i j₁ = .dot := by
          have := σ.sym_Q i j₁ hmem; rw [hγ] at this; simp [DRCSymbol.allowed] at this; exact this
        have hPdot := ((σ.dot_match i j₁).mpr ⟨hmem, hQdot⟩).2
        rcases hcase₁ with hnoP | hhi
        · exact hnoP (by rw [← hPsh]; exact ((σ.dot_match i j₁).mpr ⟨hmem, hQdot⟩).1)
        · rw [hPdot] at hhi; simp [DRCSymbol.layerOrd] at hhi
      rw [hQsh] at h_notDQ₁
      -- i ≥ μQ.colLen(j₁+1) from ∉ shiftLeft μQ
      have hge : i ≥ μQ.colLen (j₁ + 1) := by
        rwa [YoungDiagram.mem_shiftLeft, YoungDiagram.mem_iff_lt_colLen, not_lt] at h_notDQ₁
      -- i < μQ.colLen(j₂) from ∈ μQ
      have hlt : i < μQ.colLen j₂ := YoungDiagram.mem_iff_lt_colLen.mp hmQ₂
      -- Anti-mono: if j₁ < j₂ or j₂ < j₁, contradiction
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := μQ.colLen_anti (j₁+1) j₂ (by omega); omega
      · -- Symmetric: j₂ < j₁
        have h_notDQ₂ : (i, j₂) ∉ σ.Q.shape := by
          intro hmem
          have hQdot : σ.Q.paint i j₂ = .dot := by
            have := σ.sym_Q i j₂ hmem; rw [hγ] at this; simp [DRCSymbol.allowed] at this; exact this
          have hPdot := ((σ.dot_match i j₂).mpr ⟨hmem, hQdot⟩).2
          rcases hcase₂ with hnoP | hhi
          · exact hnoP (by rw [← hPsh]; exact ((σ.dot_match i j₂).mpr ⟨hmem, hQdot⟩).1)
          · rw [hPdot] at hhi; simp [DRCSymbol.layerOrd] at hhi
        rw [hQsh] at h_notDQ₂
        have hge₂ : i ≥ μQ.colLen (j₂ + 1) := by
          rwa [YoungDiagram.mem_shiftLeft, YoungDiagram.mem_iff_lt_colLen, not_lt] at h_notDQ₂
        have hlt₁ : i < μQ.colLen j₁ := YoungDiagram.mem_iff_lt_colLen.mp hmQ₁
        have := μQ.colLen_anti (j₂+1) j₁ (by omega); omega
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- L.L: both r from liftPaintP → from σ.P
      exact ⟨rfl, (σ.row_r i .L .L j₁ j₂
        (by simp [paintBySide]; exact liftPaintP_CD_r σ i j₁ h₁)
        (by simp [paintBySide]; exact liftPaintP_CD_r σ i j₂ h₂)).2⟩
    · exact absurd h₂ (liftPaintQ_CD_ne_r σ μQ i j₂)
    · exact absurd h₁ (liftPaintQ_CD_ne_r σ μQ i j₁)
    · exact absurd h₁ (liftPaintQ_CD_ne_r σ μQ i j₁)
  col_c_P := by
    intro j i₁ i₂ h₁ h₂; simp only [liftPaintP_CD] at h₁ h₂
    split_ifs at h₁ with ha₁ <;> split_ifs at h₂ with ha₂ <;>
      first | exact absurd h₁ (by decide) | exact absurd h₂ (by decide) |
        exact σ.col_c_P j i₁ i₂ h₁ h₂
  col_c_Q := by
    intro j i₁ i₂ h₁ h₂; simp only [liftPaintQ_CD] at h₁ h₂
    split_ifs at h₁ <;> exact absurd h₁ (by decide)
  col_d_P := by
    intro j i₁ i₂ h₁ h₂; simp only [liftPaintP_CD] at h₁ h₂
    split_ifs at h₁ with ha₁ <;> split_ifs at h₂ with ha₂ <;>
      first | exact absurd h₁ (by decide) | exact absurd h₂ (by decide) |
        exact σ.col_d_P j i₁ i₂ h₁ h₂
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂; simp only [liftPaintQ_CD] at h₁ h₂
    split_ifs at h₁ <;> exact absurd h₁ (by decide)

/-- D→C lift as PBPSet map. Fields transparent via `liftCD_raw`. -/
noncomputable def liftCD_PBP {μP μQ : YoungDiagram}
    (σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ))
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP) :
    PBPSet .C μP μQ :=
  ⟨liftCD_raw σ.val σ.prop.1 μP μQ σ.prop.2.1 σ.prop.2.2 h_sub, ⟨rfl, rfl, rfl⟩⟩

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
  apply Subtype.ext; apply PBP.ext'' σ.prop.1.symm
  · apply PaintedYoungDiagram.ext' σ.prop.2.1.symm; funext i j
    show PBP.descentPaintL_CD (liftCD_raw σ.val σ.prop.1 μP μQ σ.prop.2.1 σ.prop.2.2 h_sub) i j =
        σ.val.P.paint i j
    -- Zone analysis: descent ∘ lift recovers σ.P.paint
    -- Blocked by dotScolLen(liftP) vs dotScolLen(σ.P) definitional mismatch.
    sorry
  · apply PaintedYoungDiagram.ext' σ.prop.2.2.symm; funext i j
    -- D-type Q is all dots: σ.Q.paint = dot everywhere
    have hγ := σ.prop.1
    have := σ.val.sym_Q i j
    rw [hγ] at this
    by_cases hmem : (i, j) ∈ σ.val.Q.shape
    · simp [DRCSymbol.allowed] at this; exact (this hmem).symm
    · exact (σ.val.Q.paint_outside i j hmem).symm

/-- Descent image excludes SS in the balanced case. -/
theorem descentCD_not_SS {μP μQ : YoungDiagram}
    (h_sub : YoungDiagram.shiftLeft μQ ≤ μP)
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1)
    (τ : PBPSet .C μP μQ) :
    tailClass_D (descentCD_PBP τ h_sub).val ≠ .SS := by
  -- With transparent fields: tailClass_D unfolds on descentCD_raw directly.
  simp only [tailClass_D, descentCD_PBP, descentCD_raw, PBP.tailLen_D, PBP.tailSymbol_D]
  -- tailLen = μP.colLen 0 - (shiftLeft μQ).colLen 0 > 0 (from h_bal)
  have h_pos : μP.colLen 0 - (YoungDiagram.shiftLeft μQ).colLen 0 ≠ 0 := by
    -- shiftLeft.colLen 0 = μQ.colLen 1 ≤ μQ.colLen 0 = μP.colLen 0 - 1
    suffices (YoungDiagram.shiftLeft μQ).colLen 0 < μP.colLen 0 by omega
    calc (YoungDiagram.shiftLeft μQ).colLen 0
        ≤ μQ.colLen 0 := by rw [YoungDiagram.colLen_shiftLeft]; exact μQ.colLen_anti 0 1 (by omega)
      _ < μP.colLen 0 := by omega
  rw [if_neg h_pos]
  -- tailSymbol = descentPaintL_CD τ.val (μP.colLen 0 - 1) 0
  -- This is in zone 3: the tail cell is outside Q zone, C-P paint ∈ {r,c,d}
  simp only [PBP.descentPaintL_CD]
  -- Zone 1 check: μP.colLen 0 - 1 < τ.val.Q.colLen(1)?
  -- τ.Q.shape = μQ, so Q.colLen(1) ≤ Q.colLen(0) = μP.colLen(0) - 1
  have h_z1 : ¬(μP.colLen 0 - 1 < τ.val.Q.shape.colLen (0 + 1)) := by
    rw [τ.prop.2.2]; exact not_lt.mpr (le_trans (μQ.colLen_anti 0 1 (by omega)) (by omega))
  rw [if_neg h_z1]
  -- Zone 2 check: μP.colLen 0 - 1 < dotScolLen(τ.P, 0)?
  -- The tail cell (μP.colLen 0 - 1, 0) ∉ μQ (since μQ.colLen 0 = μP.colLen 0 - 1)
  -- By C-type dot_match: not in Q → P paint ≠ dot → layerOrd > 1 → not in dotScolLen zone
  have h_notQ : ¬((μP.colLen 0 - 1, 0) ∈ μQ) := by
    rw [YoungDiagram.mem_iff_lt_colLen]; omega
  have h_notdot : τ.val.P.paint (μP.colLen 0 - 1) 0 ≠ .dot := by
    intro heq
    have hmem : (μP.colLen 0 - 1, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have := (τ.val.dot_match _ _).mp ⟨hmem, heq⟩
    rw [τ.prop.2.2] at this; exact h_notQ this.1
  have h_z2 : ¬(μP.colLen 0 - 1 < PBP.dotScolLen τ.val.P 0) := by
    intro hlt
    exact h_notdot (by
      rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.mono_P] at hlt
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := (PBP.dotSdiag τ.val.P τ.val.mono_P).isLowerSet
      simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
      obtain ⟨hP, hlo⟩ := hmem
      have hsym := τ.val.sym_P _ _ hP; rw [τ.prop.1] at hsym
      simp [DRCSymbol.allowed] at hsym
      rcases hsym with hp | hp | hp | hp <;> rw [hp] at hlo ⊢ <;>
        simp [DRCSymbol.layerOrd] at hlo ⊢)
  rw [if_neg h_z2]
  -- Now: match τ.val.P.paint (μP.colLen 0 - 1) 0 with ... ≠ SS
  -- C-type P paint ∈ {dot, r, c, d}. Not dot (proved). So ∈ {r, c, d} → DD or RC.
  have hsym := τ.val.sym_P (μP.colLen 0 - 1) 0
    (by rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  rw [τ.prop.1] at hsym; simp [DRCSymbol.allowed] at hsym
  rcases hsym with hp | hp | hp | hp <;> rw [hp] at h_notdot ⊢ <;>
    simp [DRCSymbol.layerOrd] at h_notdot ⊢ <;> decide

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
