/-
# Counting Proof: M-type correspondence (Proposition 10.12 for M = C̃)

Reference: [BMSZb] Proposition 10.12, Proposition 10.8.

Proves: card(PBPSet .M μP μQ) = countPBP_M dp

Strategy (mirrors CorrespondenceC.lean):
1. M→B descent is injective (Prop 10.8)
2. Primitive (r₁ > r₂): descent surjective → count = total B count
3. Balanced (r₁ = r₂): descent image excludes SS → count = DD + RC
-/
import CombUnipotent.CountingProof.CorrespondenceB

open Classical

/-! ## M→B descent -/

/-- descentPaintL_MB outside shiftLeft P gives dot. -/
private lemma descentPaintL_MB_outside {τ : PBP} (hγ : τ.γ = .M)
    {i j : ℕ} (hmem : (i, j) ∉ YoungDiagram.shiftLeft τ.P.shape) :
    PBP.descentPaintL_MB τ i j = .dot := by
  simp only [PBP.descentPaintL_MB]
  split_ifs with h1
  · rfl
  · rw [YoungDiagram.mem_shiftLeft] at hmem
    exact τ.P.paint_outside i (j + 1) hmem

/-- In M-type P, layerOrd ≤ 1 cells are dot or s (from {dot, s, c}). -/
private lemma M_P_layerOrd_le_one {τ : PBP} (hγ : τ.γ = .M)
    {i j : ℕ} (hmem : (i, j) ∈ τ.P.shape) (hlo : (τ.P.paint i j).layerOrd ≤ 1) :
    τ.P.paint i j = .dot ∨ τ.P.paint i j = .s := by
  have hsym := τ.sym_P i j hmem; rw [hγ] at hsym
  revert hlo hsym; cases τ.P.paint i j <;> simp [DRCSymbol.layerOrd, DRCSymbol.allowed]

/-- In M-type Q, layerOrd ≤ 1 means dot (Q has {dot, r, d}, only dot has layerOrd ≤ 1). -/
private lemma M_Q_layerOrd_le_one {τ : PBP} (hγ : τ.γ = .M)
    {i j : ℕ} (hmem : (i, j) ∈ τ.Q.shape) (hlo : (τ.Q.paint i j).layerOrd ≤ 1) :
    τ.Q.paint i j = .dot := by
  have hsym := τ.sym_Q i j hmem; rw [hγ] at hsym
  revert hlo hsym; cases τ.Q.paint i j <;> simp [DRCSymbol.layerOrd, DRCSymbol.allowed]

/-- In M-type, dotScolLen Q j counts only dots (since only dot has layerOrd ≤ 1 in Q). -/
private lemma M_dotScolLen_Q_eq_dots {τ : PBP} (hγ : τ.γ = .M) (j : ℕ) :
    ∀ i, i < PBP.dotScolLen τ.Q j → (i, j) ∈ τ.Q.shape ∧ τ.Q.paint i j = .dot := by
  intro i hi
  rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at hi
  have hmem := PBP.dotSdiag_le_shape τ.Q τ.mono_Q (YoungDiagram.mem_iff_lt_colLen.mpr hi)
  have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q hi
  exact ⟨hmem, M_Q_layerOrd_le_one hγ hmem hlo⟩

/-- Key: i < dotScolLen P (j+1) and (i, j+1) ∈ P → (i, j) ∈ Q.
    Proof: P(i,j+1) ∈ {dot, s}. If dot: dot_match → (i,j+1) ∈ Q → (i,j) ∈ Q.
    If s: (i,j) ∈ P (Young diagram) and P(i,j) must be dot (s unique per row).
    Then dot_match → (i,j) ∈ Q. -/
private lemma M_dotS_in_P_imp_in_Q {τ : PBP} (hγ : τ.γ = .M)
    {i j : ℕ} (hmemP : (i, j + 1) ∈ τ.P.shape)
    (hlt : i < PBP.dotScolLen τ.P (j + 1)) : (i, j) ∈ τ.Q.shape := by
  rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hlt
  have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P hlt
  rcases M_P_layerOrd_le_one hγ hmemP hlo with hdot | hs
  · -- P(i,j+1) = dot → (i,j+1) ∈ Q → (i,j) ∈ Q
    have ⟨hmemQ, _⟩ := (τ.dot_match i (j + 1)).mp ⟨hmemP, hdot⟩
    exact τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl i, Nat.le_succ j⟩) hmemQ
  · -- P(i,j+1) = s → (i,j) ∈ P (Young diagram), P(i,j) ∈ {dot, s}
    have hmemPj : (i, j) ∈ τ.P.shape :=
      τ.P.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl i, Nat.le_succ j⟩) hmemP
    -- P(i,j) must be dot (s is unique per row, and P(i,j+1)=s)
    have hpaint_j : τ.P.paint i j = .dot := by
      by_contra hne
      have hlo_j := τ.mono_P i j i (j + 1) le_rfl (Nat.le_succ j) hmemP
      rw [hs, DRCSymbol.layerOrd] at hlo_j
      have := M_P_layerOrd_le_one hγ hmemPj (by omega)
      rcases this with hd | hss
      · exact hne hd
      · -- P(i,j) = s and P(i,j+1) = s: contradicts row_s
        have ⟨_, habs⟩ := τ.row_s i .L .L j (j + 1)
          (by simp [paintBySide]; exact hss) (by simp [paintBySide]; exact hs)
        omega
    exact ((τ.dot_match i j).mp ⟨hmemPj, hpaint_j⟩).1

/-- Key: i < dotScolLen P (j+1) and (i, j) ∈ Q → (i, j+1) ∈ P.
    Proof: i < dotScolLen P (j+1) ≤ P.colLen(j+1), so (i, j+1) ∈ P. -/
private lemma M_dotS_in_Q_imp_in_P {τ : PBP} (hγ : τ.γ = .M)
    {i j : ℕ} (hmemQ : (i, j) ∈ τ.Q.shape)
    (hlt : i < PBP.dotScolLen τ.P (j + 1)) : (i, j + 1) ∈ τ.P.shape := by
  have hds_le := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  exact YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le hlt hds_le)

/-- Descent map M → B: removes P column 0, shifts P left, refills Q with dots/s.
    Analogous to C → D descent in CorrespondenceC.lean.
    Reference: [BMSZb] Section 10.4, The case ★ = C̃. -/
noncomputable def descentMB_PBP (τ : PBP) (hγ : τ.γ = .M) : PBP where
  γ := PBP.descentType_M τ hγ
  P := { shape := YoungDiagram.shiftLeft τ.P.shape
         paint := PBP.descentPaintL_MB τ
         paint_outside := fun i j hmem => descentPaintL_MB_outside hγ hmem }
  Q := { shape := τ.Q.shape
         paint := PBP.descentPaintR_MB τ
         paint_outside := fun i j hmem => by
           simp only [PBP.descentPaintR_MB]
           split_ifs with h1 h2
           · rfl
           · exfalso; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at h2
             exact hmem (PBP.dotSdiag_le_shape τ.Q τ.mono_Q
               (YoungDiagram.mem_iff_lt_colLen.mpr h2))
           · exact τ.Q.paint_outside i j hmem }
  sym_P := by
    intro i j hmem
    simp only [PBP.descentPaintL_MB]
    split_ifs with h1
    · -- dot is allowed for both Bplus and Bminus on L
      unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
    · -- P(i, j+1) with i ≥ dotScolLen: must be c (M P has {dot, s, c}, non-dot-s = c)
      have hmemP : (i, j + 1) ∈ τ.P.shape := YoungDiagram.mem_shiftLeft.mp hmem
      have hsym := τ.sym_P i (j + 1) hmemP; rw [hγ] at hsym
      have hge : PBP.dotScolLen τ.P (j + 1) ≤ i := Nat.le_of_not_lt h1
      -- M P: non-dot non-s means c. layerOrd > 1 rules out dot and s.
      have hc : τ.P.paint i (j + 1) = .c := by
        simp [DRCSymbol.allowed] at hsym
        rcases hsym with hd | hs | hc
        · exfalso; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hge
          have : i < (PBP.dotSdiag τ.P τ.mono_P).colLen (j + 1) := by
            rw [YoungDiagram.mem_iff_lt_colLen.symm]
            simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                  hmemP, hd, DRCSymbol.layerOrd]
          omega
        · exfalso; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hge
          have : i < (PBP.dotSdiag τ.P τ.mono_P).colLen (j + 1) := by
            rw [YoungDiagram.mem_iff_lt_colLen.symm]
            simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                  hmemP, hs, DRCSymbol.layerOrd]
          omega
        · exact hc
      rw [hc]; unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
  sym_Q := by
    intro i j hmem
    simp only [PBP.descentPaintR_MB]
    split_ifs with h1 h2
    · -- dot
      unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
    · -- s
      unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
    · -- Q(i, j) with i ≥ dotScolLen Q j: layerOrd > 1, so r or d
      have hsym := τ.sym_Q i j hmem; rw [hγ] at hsym
      simp [DRCSymbol.allowed] at hsym
      rcases hsym with hd | hr | hdd
      · -- dot has layerOrd 0, contradicts i ≥ dotScolLen Q
        exfalso
        have : i < PBP.dotScolLen τ.Q j := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q, YoungDiagram.mem_iff_lt_colLen.symm]
          simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                hmem, hd, DRCSymbol.layerOrd]
        omega
      · rw [hr]; unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
      · rw [hdd]; unfold PBP.descentType_M; split_ifs <;> simp [DRCSymbol.allowed]
  dot_match := by
    intro i j; constructor
    · -- (i,j) ∈ shiftLeft P ∧ P'(i,j) = dot → (i,j) ∈ Q ∧ Q'(i,j) = dot
      intro ⟨hmemP, hpaint⟩
      simp only [PBP.descentPaintL_MB] at hpaint
      split_ifs at hpaint with h1
      · -- i < dotScolLen P (j+1): P'=dot. Need (i,j) ∈ Q and Q'(i,j)=dot.
        have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
        exact ⟨M_dotS_in_P_imp_in_Q hγ hmemP' h1,
               by simp [PBP.descentPaintR_MB, if_pos h1]⟩
      · -- i ≥ dotScolLen: P' = P(i,j+1). For this to be dot, (i,j+1) must be outside P
        -- (since inside P with layerOrd > 1 can't be dot). But (i,j) ∈ shiftLeft P means
        -- (i,j+1) ∈ P. So P(i,j+1) has layerOrd > 1 → not dot. Contradiction.
        exfalso
        have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
        have hge : PBP.dotScolLen τ.P (j + 1) ≤ i := Nat.le_of_not_lt h1
        -- P(i,j+1) has layerOrd > 1 (non-dot, non-s)
        rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hge
        have hlo_gt : (τ.P.paint i (j + 1)).layerOrd > 1 := by
          by_contra hle; push_neg at hle
          have hlt : i < (PBP.dotSdiag τ.P τ.mono_P).colLen (j + 1) := by
            rw [YoungDiagram.mem_iff_lt_colLen.symm]
            simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                  hmemP', hle]
          omega
        -- layerOrd > 1 → paint ≠ dot
        revert hpaint hlo_gt; cases τ.P.paint i (j + 1) <;> simp [DRCSymbol.layerOrd]
    · -- (i,j) ∈ Q ∧ Q'(i,j) = dot → (i,j) ∈ shiftLeft P ∧ P'(i,j) = dot
      intro ⟨hmemQ, hpaint⟩
      simp only [PBP.descentPaintR_MB] at hpaint
      split_ifs at hpaint with h1 h2
      · -- i < dotScolLen P (j+1) → (i,j+1) ∈ P → (i,j) ∈ shiftLeft P
        exact ⟨YoungDiagram.mem_shiftLeft.mpr (M_dotS_in_Q_imp_in_P hγ hmemQ h1),
               by simp [PBP.descentPaintL_MB, if_pos h1]⟩
      · -- Q(i,j) = dot, but i ≥ dotScolLen Q j. Contradiction.
        exfalso
        have : i < PBP.dotScolLen τ.Q j := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q, YoungDiagram.mem_iff_lt_colLen.symm]
          simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                hmemQ, hpaint, DRCSymbol.layerOrd]
        omega
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (PBP.descentPaintL_MB τ i₁ j₁).layerOrd ≤ (PBP.descentPaintL_MB τ i₂ j₂).layerOrd
    have hmem₂' : (i₂, j₂ + 1) ∈ τ.P.shape := YoungDiagram.mem_shiftLeft.mp hmem₂
    have hDS_anti : ∀ a b, a ≤ b → PBP.dotScolLen τ.P (b + 1) ≤ PBP.dotScolLen τ.P (a + 1) := by
      intro a b h; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
        PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
      exact (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (a + 1) (b + 1) (by omega)
    by_cases hz1 : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · simp [PBP.descentPaintL_MB, if_pos hz1, DRCSymbol.layerOrd]
    · simp only [PBP.descentPaintL_MB, if_neg hz1]
      by_cases hz2 : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
      · exfalso; have := hDS_anti j₁ j₂ hj; omega
      · simp only [PBP.descentPaintL_MB, if_neg hz2]
        exact τ.mono_P i₁ (j₁ + 1) i₂ (j₂ + 1) hi (by omega) hmem₂'
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (PBP.descentPaintR_MB τ i₁ j₁).layerOrd ≤ (PBP.descentPaintR_MB τ i₂ j₂).layerOrd
    have hmem₂' : (i₂, j₂) ∈ τ.Q.shape := hmem₂
    have hDS_P_anti : ∀ a b, a ≤ b →
        PBP.dotScolLen τ.P (b + 1) ≤ PBP.dotScolLen τ.P (a + 1) := by
      intro a b h; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
        PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
      exact (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (a + 1) (b + 1) (by omega)
    have hDS_Q_anti : ∀ a b, a ≤ b → PBP.dotScolLen τ.Q b ≤ PBP.dotScolLen τ.Q a := by
      intro a b h; rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q,
        PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]
      exact (PBP.dotSdiag τ.Q τ.mono_Q).colLen_anti a b h
    by_cases hz1 : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · simp [PBP.descentPaintR_MB, if_pos hz1, DRCSymbol.layerOrd]
    · by_cases hz2 : i₁ < PBP.dotScolLen τ.Q j₁
      · simp only [PBP.descentPaintR_MB, if_neg hz1, if_pos hz2, DRCSymbol.layerOrd]
        by_cases hz1' : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
        · exfalso; have := hDS_P_anti j₁ j₂ hj; omega
        · by_cases hz2' : i₂ < PBP.dotScolLen τ.Q j₂
          · simp [PBP.descentPaintR_MB, if_neg hz1', if_pos hz2', DRCSymbol.layerOrd]
          · simp only [PBP.descentPaintR_MB, if_neg hz1', if_neg hz2']
            exact le_trans (by omega : 1 ≤ 2)
              (PBP.layerOrd_gt_one_of_ge_dotScolLen τ.Q τ.mono_Q (Nat.le_of_not_lt hz2') hmem₂')
      · simp only [PBP.descentPaintR_MB, if_neg hz1, if_neg hz2]
        by_cases hz1' : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
        · exfalso; have := hDS_P_anti j₁ j₂ hj; omega
        · by_cases hz2' : i₂ < PBP.dotScolLen τ.Q j₂
          · exfalso; have := hDS_Q_anti j₁ j₂ hj; omega
          · simp only [PBP.descentPaintR_MB, if_neg hz1', if_neg hz2']
            exact τ.mono_Q i₁ j₁ i₂ j₂ hi hj hmem₂'
  row_s := by
    -- P' has {dot, c}, so s can only appear in Q' (side R).
    have hP_no_s : ∀ i' j', PBP.descentPaintL_MB τ i' j' ≠ .s := by
      intro i' j'; simp only [PBP.descentPaintL_MB]
      split_ifs with h1
      · exact (by decide : DRCSymbol.dot ≠ .s)
      · intro heq
        by_cases hmem : (i', j' + 1) ∈ τ.P.shape
        · -- i' ≥ dotScolLen: layerOrd > 1, so paint ∈ {c} (not dot, not s)
          have hge : PBP.dotScolLen τ.P (j' + 1) ≤ i' := Nat.le_of_not_lt h1
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hge
          have hlo := PBP.ge_dotSdiag_colLen_of_layerOrd_gt_one τ.P τ.mono_P hmem
          rw [heq, DRCSymbol.layerOrd] at hlo
          have : (PBP.dotSdiag τ.P τ.mono_P).colLen (j' + 1) ≤ i' := hge
          -- s has layerOrd 1 ≤ 1, so i' < dotSdiag.colLen
          have : i' < (PBP.dotSdiag τ.P τ.mono_P).colLen (j' + 1) := by
            rw [YoungDiagram.mem_iff_lt_colLen.symm]
            simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                  hmem, heq, DRCSymbol.layerOrd]
          omega
        · rw [τ.P.paint_outside i' (j' + 1) hmem] at heq; simp at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₂ (hP_no_s i j₂)
    · -- Both in Q': s zone analysis
      have h_s_zone : ∀ j, PBP.descentPaintR_MB τ i j = .s →
          PBP.dotScolLen τ.P (j + 1) ≤ i ∧ i < PBP.dotScolLen τ.Q j := by
        intro j' hs; simp only [PBP.descentPaintR_MB] at hs
        by_cases hcl : i < PBP.dotScolLen τ.P (j' + 1)
        · simp [if_pos hcl] at hs
        · rw [if_neg hcl] at hs; by_cases hcr : i < PBP.dotScolLen τ.Q j'
          · exact ⟨Nat.le_of_not_lt hcl, hcr⟩
          · rw [if_neg hcr] at hs
            exfalso; by_cases hmem : (i, j') ∈ τ.Q.shape
            · have hsym := τ.sym_Q i j' hmem; rw [hγ] at hsym
              simp [DRCSymbol.allowed] at hsym
              rcases hsym with hp | hp | hp <;> rw [hp] at hs <;> simp at hs
            · rw [τ.Q.paint_outside i j' hmem] at hs; simp at hs
      obtain ⟨hge₁, hlt₁⟩ := h_s_zone j₁ h₁
      obtain ⟨hge₂, hlt₂⟩ := h_s_zone j₂ h₂
      refine ⟨rfl, ?_⟩
      by_contra hne; rcases Nat.lt_or_gt_of_ne hne with h | h
      · -- j₁ < j₂: dotScolLen Q j₁ ≤ dotScolLen P (j₁+1)?
        -- We need: dotScolLen Q j₁ > i ≥ dotScolLen P (j₂+1) ≥ ... ?
        -- Actually use anti-monotonicity: dotScolLen P (j₂+1) ≤ dotScolLen P (j₁+1)
        -- and dotScolLen Q j₂ ≤ dotScolLen Q j₁.
        -- But we need the interlacing... Let's use dot_match.
        -- From τ dot_match: dot in P ↔ dot in Q.
        -- dotScolLen counts dot+s. For M Q: s has layerOrd 1 but Q has no s! So dotScolLen Q = #dots in Q.
        -- dotScolLen P = #(dot+s) in P. #dots in Q col j = #dots in P col j (dot_match).
        -- Need: #dots in Q col j₁ > i ≥ #(dot+s) in P col (j₂+1).
        -- We have this from hlt₁ and hge₂. But also need P interlacing...
        -- Actually: from hlt₁: i < dotScolLen Q j₁. From hge₂: i ≥ dotScolLen P (j₂+1).
        -- If j₁ < j₂: dotScolLen P (j₂+1) ≤ dotScolLen P (j₁+1) (anti-mono).
        -- So i ≥ dotScolLen P (j₁+1) (from hge₁). Fine.
        -- We need: this is consistent.
        -- For Q original row_s: Q has no s (M Q has {dot, r, d}). So row_s in τ gives that
        -- s can only appear in P. P(i, j₁) and P(i, j₂) can't both be s.
        -- But the issue is the DESCENT's s, not the original.
        -- The descent s comes from the s zone: dotScolLen P (j+1) ≤ i < dotScolLen Q j.
        -- Two s at j₁ and j₂ with j₁ < j₂: need contradiction.
        -- From hlt₁: i < dotScolLen Q j₁. From hge₂: dotScolLen P (j₂+1) ≤ i.
        -- dotScolLen Q j₂ ≤ dotScolLen Q j₁ (anti-mono).
        -- dotScolLen P (j₂+1) ≤ i < dotScolLen Q j₁. Fine.
        -- But we also need i < dotScolLen Q j₂ (from hlt₂). OK.
        -- So dotScolLen P (j₂+1) ≤ i < dotScolLen Q j₂ ≤ dotScolLen Q j₁. Consistent.
        -- But from original constraints, the s zone at two different j can overlap?
        -- Actually this CAN happen — the row_s constraint says at most one s per row.
        -- In the descent, the s zone creates one s per cell in the zone, one per column.
        -- So row i can have s in Q' at both j₁ and j₂. This violates row_s!
        -- Wait, but we're PROVING row_s for the descended PBP. So we need to show
        -- that having s at two positions in Q' is impossible.
        -- The key: in the original M PBP, row i has at most one s (in P).
        -- The descent s comes from the zone dotScolLen P (j+1) ≤ i < dotScolLen Q j.
        -- If both j₁ < j₂ have s, then:
        --   dotScolLen P (j₁+1) ≤ i < dotScolLen Q j₁
        --   dotScolLen P (j₂+1) ≤ i < dotScolLen Q j₂
        -- dotScolLen Q counts dots in Q. For row i in Q:
        --   i < dotScolLen Q j₁ means the cell (i, j₁) is in Q and has layerOrd ≤ 1 (dot).
        --   i < dotScolLen Q j₂ means the cell (i, j₂) is in Q and has layerOrd ≤ 1 (dot).
        -- But also dotScolLen P (j₁+1) ≤ i means cell (i, j₁+1) in P has layerOrd > 1 or is outside P.
        -- Since j₁ < j₂: j₁+1 ≤ j₂.
        -- If j₁+1 = j₂: dotScolLen P (j₂) ≤ i. But (i, j₂) ∈ Q and Q(i,j₂)=dot.
        --   By dot_match: (i, j₂) ∈ P and P(i, j₂)=dot. But P(i,j₂) dot → i < dotScolLen P j₂.
        --   Contradiction with dotScolLen P j₂ ≤ i (since j₂ = j₁+1).
        --   Wait, hge₁ says dotScolLen P (j₁+1) ≤ i, i.e., dotScolLen P j₂ ≤ i (if j₁+1=j₂).
        --   And we showed (i, j₂) ∈ Q, Q(i,j₂)=dot → (i,j₂) ∈ P, P(i,j₂)=dot → i < dotScolLen P j₂.
        --   Contradiction! ✓
        -- If j₁+1 < j₂: dotScolLen P (j₁+1) ≤ i. By anti-mono: dotScolLen P j₂ ≤ dotScolLen P (j₁+1) ≤ i.
        --   Same argument: (i, j₂) ∈ Q, Q(i,j₂)=dot → P(i,j₂)=dot → i < dotScolLen P j₂ ≤ dotScolLen P (j₁+1).
        --   But i ≥ dotScolLen P (j₁+1). So i ≥ dotScolLen P j₂ and i < dotScolLen P j₂. Contradiction. ✓
        -- Wait, but j₁+1 ≤ j₂ doesn't mean j₁ + 1 = j₂ or j₁ + 1 < j₂ in general.
        -- We need: hlt₂ says i < dotScolLen Q j₂. Since M Q has {dot, r, d},
        --   dotScolLen Q j₂ counts cells with layerOrd ≤ 1 = dot. So (i, j₂) is in Q and painted dot.
        -- Then dot_match: (i, j₂) ∈ P ∧ P(i,j₂) = dot. So i < dotScolLen P j₂
        --   (since P(i,j₂) has layerOrd 0 ≤ 1).
        -- But also hge₁: dotScolLen P (j₁+1) ≤ i. And j₁ + 1 ≤ j₂ (since j₁ < j₂ and ℕ).
        -- dotScolLen P is anti-monotone: dotScolLen P j₂ ≤ dotScolLen P (j₁+1) ≤ i.
        -- Contradiction with i < dotScolLen P j₂. ✓
        exfalso
        -- (i, j₂) is dot in Q (from being in Q's dot zone since i < dotScolLen Q j₂)
        have ⟨hmemQ₂, hdot₂⟩ := M_dotScolLen_Q_eq_dots hγ j₂ i hlt₂
        -- dot_match: P(i, j₂) = dot
        have ⟨hmemP₂, hdotP₂⟩ := (τ.dot_match i j₂).mpr ⟨hmemQ₂, hdot₂⟩
        -- i < dotScolLen P j₂
        have hlt_P : i < PBP.dotScolLen τ.P j₂ := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P, YoungDiagram.mem_iff_lt_colLen.symm]
          simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                hmemP₂, hdotP₂, DRCSymbol.layerOrd]
        -- dotScolLen P j₂ ≤ dotScolLen P (j₁+1) (anti-mono, j₁+1 ≤ j₂)
        have hanti : PBP.dotScolLen τ.P j₂ ≤ PBP.dotScolLen τ.P (j₁ + 1) := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
              PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
          exact (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁ + 1) j₂ (by omega)
        omega
      · -- j₂ < j₁: symmetric
        exfalso
        have ⟨hmemQ₁, hdot₁⟩ := M_dotScolLen_Q_eq_dots hγ j₁ i hlt₁
        have ⟨hmemP₁, hdotP₁⟩ := (τ.dot_match i j₁).mpr ⟨hmemQ₁, hdot₁⟩
        have hlt_P : i < PBP.dotScolLen τ.P j₁ := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P, YoungDiagram.mem_iff_lt_colLen.symm]
          simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
                hmemP₁, hdotP₁, DRCSymbol.layerOrd]
        have hanti : PBP.dotScolLen τ.P j₁ ≤ PBP.dotScolLen τ.P (j₂ + 1) := by
          rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
              PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]
          exact (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₂ + 1) j₁ (by omega)
        omega
  row_r := by
    -- P' has {dot, c}, so r can only appear in Q' (side R).
    have hP_no_r : ∀ i' j', PBP.descentPaintL_MB τ i' j' ≠ .r := by
      intro i' j'; simp only [PBP.descentPaintL_MB]
      split_ifs with h1
      · exact (by decide : DRCSymbol.dot ≠ .r)
      · intro heq
        by_cases hmem : (i', j' + 1) ∈ τ.P.shape
        · have hsym := τ.sym_P i' (j' + 1) hmem; rw [hγ] at hsym
          simp [DRCSymbol.allowed] at hsym
          rcases hsym with h | h | h <;> rw [h] at heq <;> simp at heq
        · rw [τ.P.paint_outside i' (j' + 1) hmem] at heq; simp at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₂ (hP_no_r i j₂)
    · -- Both in Q': r preserved from Q
      have hr : ∀ j, PBP.descentPaintR_MB τ i j = .r → τ.Q.paint i j = .r := by
        intro j' hr; simp only [PBP.descentPaintR_MB] at hr
        split_ifs at hr with ha hb <;> first | exact absurd hr (by decide) | exact hr
      exact ⟨rfl, (τ.row_r i .R .R j₁ j₂
        (by simp [paintBySide]; exact hr j₁ h₁) (by simp [paintBySide]; exact hr j₂ h₂)).2⟩
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    have hc : ∀ i', PBP.descentPaintL_MB τ i' j = .c → τ.P.paint i' (j + 1) = .c := by
      intro i' h; simp only [PBP.descentPaintL_MB] at h
      split_ifs at h with ha <;> first | exact absurd h (by decide) | exact h
    exact τ.col_c_P (j + 1) i₁ i₂ (hc i₁ h₁) (hc i₂ h₂)
  col_c_Q := by
    intro j i₁ i₂ h₁ h₂
    -- Q' has {dot, s, r, d} for B type. c is not in this set.
    exfalso; simp only [PBP.descentPaintR_MB] at h₁
    split_ifs at h₁ <;> first | exact absurd h₁ (by decide) |
      (by_cases hmem : (i₁, j) ∈ τ.Q.shape
       · have hsym := τ.sym_Q i₁ j hmem; rw [hγ] at hsym
         simp [DRCSymbol.allowed] at hsym; rcases hsym with h | h | h <;> rw [h] at h₁ <;> simp at h₁
       · rw [τ.Q.paint_outside i₁ j hmem] at h₁; simp at h₁)
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    -- P' has {dot, c} for B type. d is not in this set.
    exfalso; simp only [PBP.descentPaintL_MB] at h₁
    split_ifs at h₁ <;> first | exact absurd h₁ (by decide) |
      (by_cases hmem : (i₁, j + 1) ∈ τ.P.shape
       · have hsym := τ.sym_P i₁ (j + 1) hmem; rw [hγ] at hsym
         simp [DRCSymbol.allowed] at hsym; rcases hsym with h | h | h <;> rw [h] at h₁ <;> simp at h₁
       · rw [τ.P.paint_outside i₁ (j + 1) hmem] at h₁; simp at h₁)
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂
    have hd : ∀ i', PBP.descentPaintR_MB τ i' j = .d → τ.Q.paint i' j = .d := by
      intro i' h; simp only [PBP.descentPaintR_MB] at h
      split_ifs at h with ha hb <;> first | exact absurd h (by decide) | exact h
    exact τ.col_d_Q j i₁ i₂ (hd i₁ h₁) (hd i₂ h₂)

/-- Each (i, j+1) in dotSdiag(P) maps to (i, j) in dotSdiag(Q) for M type. -/
private theorem M_dotSdiag_shift (τ : PBP) (hγ : τ.γ = .M) {i j : ℕ}
    (hmem : (i, j + 1) ∈ τ.P.shape)
    (hlo : (τ.P.paint i (j + 1)).layerOrd ≤ 1) :
    (i, j) ∈ τ.Q.shape ∧ (τ.Q.paint i j).layerOrd ≤ 1 := by
  -- P(i, j+1) has layerOrd ≤ 1 in M type: dot or s
  rcases M_P_layerOrd_le_one hγ hmem hlo with hdot | hs
  · -- P(i,j+1) = dot. dot_match → (i,j+1) ∈ Q, Q(i,j+1) = dot.
    have ⟨hmemQ, hdotQ⟩ := (τ.dot_match i (j + 1)).mp ⟨hmem, hdot⟩
    -- (i,j+1) ∈ Q → (i,j) ∈ Q (Young diagram lower set)
    have hmemQj : (i, j) ∈ τ.Q.shape :=
      τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl i, Nat.le_succ j⟩) hmemQ
    -- mono_Q: Q(i,j).layerOrd ≤ Q(i,j+1).layerOrd = 0
    have hloQ := τ.mono_Q i j i (j + 1) le_rfl (Nat.le_succ j) hmemQ
    rw [hdotQ, DRCSymbol.layerOrd] at hloQ
    exact ⟨hmemQj, by omega⟩
  · -- P(i,j+1) = s. (i,j) ∈ P, P(i,j) = dot (row_s uniqueness).
    have hmemPj : (i, j) ∈ τ.P.shape :=
      τ.P.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl i, Nat.le_succ j⟩) hmem
    have hdotPj : τ.P.paint i j = .dot := by
      have hloP := τ.mono_P i j i (j + 1) le_rfl (Nat.le_succ j) hmem
      rw [hs, DRCSymbol.layerOrd] at hloP
      rcases M_P_layerOrd_le_one hγ hmemPj (by omega) with hd | hss
      · exact hd
      · exfalso
        have ⟨_, habs⟩ := τ.row_s i .L .L j (j + 1)
          (by simp [paintBySide]; exact hss) (by simp [paintBySide]; exact hs)
        omega
    -- dot_match → (i,j) ∈ Q, Q(i,j) = dot
    have ⟨hmemQ, hdotQ⟩ := (τ.dot_match i j).mp ⟨hmemPj, hdotPj⟩
    rw [hdotQ, DRCSymbol.layerOrd]; exact ⟨hmemQ, by omega⟩

/-- Interlacing for M type: dotScolLen Q j ≥ dotScolLen P (j+1). -/
private theorem M_interlacing (τ : PBP) (hγ : τ.γ = .M) (j : ℕ) :
    PBP.dotScolLen τ.Q j ≥ PBP.dotScolLen τ.P (j + 1) := by
  rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
      PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]
  -- dotSdiag(P).colLen(j+1) ≤ dotSdiag(Q).colLen j
  -- Suffices: ∀ i < dotSdiag(P).colLen(j+1), (i, j) ∈ dotSdiag(Q)
  by_contra h; push_neg at h
  -- There exists i in dotSdiag(P) col (j+1) but not in dotSdiag(Q) col j
  have hlt : (PBP.dotSdiag τ.Q τ.mono_Q).colLen j < (PBP.dotSdiag τ.P τ.mono_P).colLen (j + 1) := by
    omega
  set i := (PBP.dotSdiag τ.Q τ.mono_Q).colLen j with hi_def
  have hmemP : (i, j + 1) ∈ PBP.dotSdiag τ.P τ.mono_P :=
    YoungDiagram.mem_iff_lt_colLen.mpr hlt
  simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmemP
  have ⟨hmemPsh, hloP⟩ := hmemP
  have ⟨hmemQsh, hloQ⟩ := M_dotSdiag_shift τ hγ hmemPsh hloP
  -- (i, j) ∈ dotSdiag(Q)
  have hmemQds : (i, j) ∈ PBP.dotSdiag τ.Q τ.mono_Q := by
    simp [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells,
          hmemQsh, hloQ]
  -- But i = dotSdiag(Q).colLen j, so (i, j) ∉ dotSdiag(Q)
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmemQds) (by omega)

/-- The M→B descent is injective on PBPSet.
    Reference: [BMSZb] Proposition 10.8.

    Proof: descent equality → P' paints agree + Q' paints agree + γ' agree.
    Use descent_eq_implies_cols_ge1_MB (with M_interlacing) to get Q equal
    and P cols ≥ 1 equal. Then recover P col 0: dots from dot_match,
    non-dot ∈ {s, c} by mono_P ordering + col_c_P + row_s + γ' equality. -/
theorem descentMB_injective (μP μQ : YoungDiagram) :
    ∀ τ₁ τ₂ : PBPSet .M μP μQ,
    descentMB_PBP τ₁.val τ₁.prop.1 =
    descentMB_PBP τ₂.val τ₂.prop.1 →
    τ₁ = τ₂ := by
  intro τ₁ τ₂ h_eq
  -- Extract paint equalities from descent equality
  have hshapeP : τ₁.val.P.shape = τ₂.val.P.shape :=
    τ₁.prop.2.1.trans τ₂.prop.2.1.symm
  have hshapeQ : τ₁.val.Q.shape = τ₂.val.Q.shape :=
    τ₁.prop.2.2.trans τ₂.prop.2.2.symm
  have hdescL : ∀ i j, PBP.descentPaintL_MB τ₁.val i j = PBP.descentPaintL_MB τ₂.val i j := by
    intro i j; exact congrArg (fun σ => σ.P.paint i j) h_eq
  have hdescR : ∀ i j, PBP.descentPaintR_MB τ₁.val i j = PBP.descentPaintR_MB τ₂.val i j := by
    intro i j; exact congrArg (fun σ => σ.Q.paint i j) h_eq
  -- Use descent_eq_implies_cols_ge1_MB with interlacing
  have ⟨hP_ge1, hQ⟩ := PBP.descent_eq_implies_cols_ge1_MB
    τ₁.val τ₂.val τ₁.prop.1 τ₂.prop.1 hshapeP hshapeQ
    (M_interlacing τ₁.val τ₁.prop.1)
    (M_interlacing τ₂.val τ₂.prop.1)
    hdescL hdescR
  -- Recover P col 0: each cell is dot or non-dot (s/c).
  have hP_col0 : ∀ i, τ₁.val.P.paint i 0 = τ₂.val.P.paint i 0 := by
    intro i
    by_cases hp : (i, 0) ∈ τ₁.val.P.shape
    · have hp₂ : (i, 0) ∈ τ₂.val.P.shape := hshapeP ▸ hp
      by_cases hd₁ : τ₁.val.P.paint i 0 = .dot
      · -- dot: use dot_match + Q equality
        have ⟨hq, hdq⟩ := (τ₁.val.dot_match i 0).mp ⟨hp, hd₁⟩
        rw [hd₁, ← ((τ₂.val.dot_match i 0).mpr ⟨hshapeQ ▸ hq, hQ i 0 ▸ hdq⟩).2]
      · -- non-dot: both must be s or c.
        have hd₂ : τ₂.val.P.paint i 0 ≠ .dot := by
          intro hd₂
          have ⟨hq₂, hdq₂⟩ := (τ₂.val.dot_match i 0).mp ⟨hp₂, hd₂⟩
          exact hd₁ ((τ₁.val.dot_match i 0).mpr ⟨hshapeQ.symm ▸ hq₂, (hQ i 0).symm ▸ hdq₂⟩).2
        -- Classify: if row i has s in P cols ≥ 1, then both P(i,0) = c.
        by_cases hs₁ : ∃ k, k ≥ 1 ∧ τ₁.val.P.paint i k = .s
        · obtain ⟨k, hk, hsk⟩ := hs₁
          -- P₁ and P₂ both have s at (i, k). So P(i, 0) ≠ s for both → P(i, 0) = c.
          have hsk₂ : τ₂.val.P.paint i k = .s := hP_ge1 i k hk ▸ hsk
          have hc₁ : τ₁.val.P.paint i 0 = .c := by
            have hsym := τ₁.val.sym_P i 0 hp; rw [τ₁.prop.1] at hsym
            simp [DRCSymbol.allowed] at hsym
            rcases hsym with hd | hs | hc
            · exact absurd hd hd₁
            · exfalso; have := (τ₁.val.row_s i .L .L 0 k
                (by simp [paintBySide]; exact hs) (by simp [paintBySide]; exact hsk)).2; omega
            · exact hc
          have hc₂ : τ₂.val.P.paint i 0 = .c := by
            have hsym := τ₂.val.sym_P i 0 hp₂; rw [τ₂.prop.1] at hsym
            simp [DRCSymbol.allowed] at hsym
            rcases hsym with hd | hs | hc
            · exact absurd hd hd₂
            · exfalso; have := (τ₂.val.row_s i .L .L 0 k
                (by simp [paintBySide]; exact hs) (by simp [paintBySide]; exact hsk₂)).2; omega
            · exact hc
          rw [hc₁, hc₂]
        · -- No s in P cols ≥ 1. P(i, 0) ∈ {s, c}.
          push_neg at hs₁
          -- Determine s vs c by mono_P: in col 0, layerOrd non-decreasing in i.
          -- P₁ non-dot cells in col 0 with no s in higher cols:
          --   All such cells are free to be s or c. But mono says s < c.
          --   col_c_P: at most one c. So pattern is: all s, then maybe one c at end.
          -- P₂ has same dots in col 0 (from hQ + dot_match), same shape.
          -- Same set of non-dot positions.
          -- Key: descentType_M gives same flag "c in col 0".
          -- From h_eq: γ fields agree → descentType_M agree.
          have hγ_eq : PBP.descentType_M τ₁.val τ₁.prop.1 = PBP.descentType_M τ₂.val τ₂.prop.1 :=
            congrArg (·.γ) h_eq
          -- P₁(i, 0) = c iff P₂(i, 0) = c (from descentType_M equality)
          -- But more precisely: c exists in col 0 iff same.
          -- By mono_P + col_c_P: if c exists, it's at the unique last non-dot position.
          -- The last non-dot position is the same for both (same dots).
          -- If P₁(i,0) = s and P₂(i,0) = c:
          --   Then c exists in P₂ col 0 but maybe not in P₁ col 0?
          --   Actually c might exist at a different position in P₁.
          --   But by col_c_P, at most one c. And by mono, c must be at end.
          --   If P₁(i, 0) = s and there's a c somewhere else in P₁ col 0:
          --     that c is at position i' > i (mono: s < c).
          --     At i': P₁(i', 0) = c, P₂(i', 0) = ?
          --     If i' also has no s in cols ≥ 1: P₂(i', 0) ∈ {s, c}.
          --     By mono on P₂: P₂(i', 0).layerOrd ≥ P₂(i, 0).layerOrd = 3 (c).
          --     So P₂(i', 0) ∈ {c, d}. M P has no d. So P₂(i', 0) = c.
          --     But then P₂ has c at both i and i'. col_c_P violation. Contradiction.
          --     So this case can't happen.
          -- Alternatively, use a simpler approach:
          -- layerOrd at position i is the same:
          -- P₁(i, 0) has layerOrd ∈ {1, 3} (s or c).
          -- P₂(i, 0) has layerOrd ∈ {1, 3}.
          -- If they differ: one is 1 (s) and other is 3 (c).
          -- Consider the dotScolLen at col 0: counts cells with layerOrd ≤ 1.
          -- For M P, these are dots and s. Dots are the same. So #s in col 0 differs by 1.
          -- dotScolLen P₁ 0 = #dots_0 + #s_0(P₁), dotScolLen P₂ 0 = #dots_0 + #s_0(P₂).
          -- These differ by 1. But dotScolLen is used in the descent paint.
          -- From hdescR at j=0: descentPaintR_MB τ₁ i₀ 0 = descentPaintR_MB τ₂ i₀ 0 for all i₀.
          -- descentPaintR_MB τ i₀ 0 = if i₀ < dotScolLen P 1 then dot else ...
          -- This uses dotScolLen P 1, not P 0. So it doesn't help directly.
          -- But hdescL at j=... hmm.
          -- Actually, from hdescL at j=0: descentPaintL_MB τ₁ i₀ 0 = descentPaintL_MB τ₂ i₀ 0.
          -- descentPaintL_MB τ i₀ 0 = if i₀ < dotScolLen P 1 then dot else P(i₀, 1).
          -- P(i₀, 1) is already known equal (from hP_ge1 with j=1). And dotScolLen P 1 depends on
          -- P col 1 which is equal. So this gives nothing new about col 0.
          -- The only info about col 0 is from descentType_M.
          -- descentType_M: "c in P col 0" ↔ cells.filter(j=0 ∧ paint=c).Nonempty
          -- Same for both: #c in col 0 > 0 for both, or 0 for both.
          -- Combined with col_c_P (at most 1 c) and mono_P (c after s):
          -- If no c in col 0: both are s at all non-dot positions. Equal. ✓
          -- If c in col 0: exactly one c at last non-dot position. Same position. ✓
          -- For row i: is it the last non-dot?
          -- If yes: c for both (since c exists for both).
          -- If no: s for both (since c is only at the last).
          -- Need: "last non-dot" = dotScolLen P 0 (or related).
          -- Actually, non-dot cells in col 0 form a contiguous block by mono.
          -- Dots come first (layerOrd 0), then non-dot (layerOrd ≥ 1).
          -- Wait, by mono: layerOrd at (i, 0) ≤ layerOrd at (i+1, 0) (if (i+1, 0) ∈ P).
          -- So layerOrd is non-decreasing in i. Dots (0) first, then s (1), then c (3).
          -- The dots form a prefix, then s, then c.
          -- Dot prefix length = # dots in col 0 (same for both, from Q).
          -- After dots: s and c. At most one c at end.
          -- dotScolLen P 0 = # dots + # s in col 0.
          -- P.shape.colLen 0 = total cells in col 0 (same, from shape equality).
          -- # non-dot = colLen 0 - # dots. # s = dotScolLen 0 - # dots.
          -- # c = colLen 0 - dotScolLen 0.
          -- For both to have same # c: dotScolLen P₁ 0 = dotScolLen P₂ 0.
          -- Is this guaranteed? From descentType_M: only "≥ 1 c" info.
          -- Actually yes: col_c_P says at most 1 c. And descentType_M says c exists
          -- (or not). So # c ∈ {0, 1} and is the same for both. Hence dotScolLen is the same.
          -- So: # s = dotScolLen - # dots is the same. # c is the same.
          -- Positions: dots at rows 0..d-1, s at rows d..d+s-1, c at row d+s (if exists).
          -- All determined. So P(i, 0) is determined. Equal. ✓
          -- Now let me formalize this.
          -- Both have same non-dot positions (same dots = same from dot_match + Q).
          -- Both have c iff descentType_M is Bminus.
          -- By mono_P: non-dot cells have layerOrd ≥ 1. Among them, s (1) before c (3).
          -- col_c_P: at most one c. So at most one c at the end of non-dot block.
          -- If both have c: c is at position colLen(0) - 1 (last cell). Everything else is s.
          -- Hmm, not exactly. The last non-dot cell is at some position.
          -- Actually col 0 layout: dots at top (i < some threshold), then non-dot below.
          -- Wait, mono says layerOrd NON-DECREASING in i. So dots are at top, non-dot at bottom.
          -- Among non-dot: s first, then c. All s are at consecutive positions, then c.
          -- The c (if any) is at the very last position in the column.
          -- This position = colLen(0) - 1 (the largest i in col 0).
          -- Both τ₁ and τ₂ have same colLen(0). So the last position is the same.
          -- P₁(i, 0) = c ↔ i = colLen(0) - 1 ∧ c exists in col 0.
          -- P₁(i, 0) = s ↔ i is non-dot ∧ ¬(i = colLen(0) - 1 ∧ c exists)
          -- Same for P₂. Since "c exists" is same for both, paint is the same.
          -- Formalize: case split on P₁(i, 0) = s vs c.
          have hsym₁ := τ₁.val.sym_P i 0 hp; rw [τ₁.prop.1] at hsym₁
          have hsym₂ := τ₂.val.sym_P i 0 hp₂; rw [τ₂.prop.1] at hsym₂
          simp [DRCSymbol.allowed] at hsym₁ hsym₂
          rcases hsym₁ with hd₁' | hs₁' | hc₁'
          · exact absurd hd₁' hd₁
          · -- P₁(i, 0) = s. Need P₂(i, 0) = s.
            -- If P₂(i, 0) = c: then c exists in P₂ col 0.
            -- By descentType_M equality, c also exists in P₁ col 0.
            -- P₁ has c at some position i'. By col_c_P, unique.
            -- mono_P: s at i < c at i', so i < i'. P₂ has c at i.
            -- P₂ also has c at i': by descentType_M... wait, col_c_P says at most one c.
            -- P₂ has c at i. i' ≠ i (since P₁ has s at i, not c).
            -- Does P₂ have anything at i'? P₂(i', 0) ∈ {s, c} (non-dot, same as P₁).
            -- If P₂(i', 0) = c: two c's in col 0 (at i and i'). Violates col_c_P. Contradiction.
            -- So P₂(i', 0) = s.
            -- But wait, we need P₁ to have c somewhere. Does it?
            -- If descentType_M says c exists in P₁ col 0: yes.
            -- If not: P₁ has no c. Then P₂ also has no c (by descentType_M equality).
            -- So P₂(i, 0) ≠ c → P₂(i, 0) = s. ✓
            -- If P₁ has c somewhere and P₂ has c at i: let's derive contradiction.
            -- P₁ has c at i' (mono: i' > i since s at i has layerOrd 1 < 3 = c).
            -- P₂ has c at i. mono on P₂: P₂(i, 0) = c has layerOrd 3.
            --   For j < i: P₂(j, 0).layerOrd ≤ 3. OK.
            --   For j > i: P₂(j, 0).layerOrd ≥ 3. So P₂(j, 0) ∈ {c, d}. M P has no d. So c.
            --   But col_c_P: only one c. So no j > i has non-dot in P₂... unless it's dot.
            --   But j > i with (j, 0) ∈ P₂: if non-dot, must be c (layerOrd ≥ 3), violating col_c_P.
            --   So all j > i in col 0 are dots (or outside shape).
            -- i' > i: P₁(i', 0) = c, so (i', 0) ∈ P₁ and non-dot.
            --   (i', 0) ∈ P₂ (same shape). P₂(i', 0) must be dot (from above).
            --   But P₁(i', 0) = c → non-dot → dot_match reverse: ¬dot.
            --   P₂(i', 0) = dot → by dot_match on P₂: Q₂(i', 0) = dot.
            --   By hQ: Q₁(i', 0) = dot. By dot_match on P₁: P₁(i', 0) = dot.
            --   But P₁(i', 0) = c ≠ dot. Contradiction. ✓
            -- So P₂(i, 0) = c is impossible. Hence P₂(i, 0) = s. ✓
            rw [hs₁']
            rcases hsym₂ with hd₂' | hs₂' | hc₂'
            · exact absurd hd₂' hd₂
            · exact hs₂'.symm
            · exfalso
              -- P₂(i, 0) = c. By descentType_M equality, c exists in P₁ col 0.
              -- Find the c in P₁ col 0.
              simp only [PBP.descentType_M] at hγ_eq
              -- If P₁ has no c in col 0: descentType_M τ₁ = Bplus.
              -- P₂ has c in col 0: descentType_M τ₂ = Bminus. hγ_eq: Bplus = Bminus. Contradiction.
              -- So P₁ has c in col 0 at some i'.
              -- By mono on P₂: all non-dot j > i must have layerOrd ≥ 3.
              -- M P: layerOrd ≥ 3 → c. col_c_P: only one c at i. So no non-dot j > i.
              -- i' > i (since P₁ has s at i, c at i', mono says i < i').
              -- (i', 0) ∈ P₂, non-dot (same dots). P₂(i', 0) would be non-dot, j > i.
              -- P₂(i', 0) layerOrd ≥ P₂(i, 0).layerOrd = 3 (c). So P₂(i', 0) = c.
              -- But P₂ already has c at i. col_c_P: contradiction.
              -- Actually, we need "non-dot at i' in P₂". P₁(i',0) = c, non-dot.
              -- From dot_match + Q: P₁(i',0) non-dot → Q₁(i',0) non-dot.
              -- Q₁ = Q₂ → Q₂(i',0) non-dot. dot_match on P₂: P₂(i',0) non-dot.
              -- So P₂(i',0) non-dot and i' > i. layerOrd ≥ 3 → c.
              -- Two c's in P₂ col 0. Contradiction with col_c_P.
              -- But first we need P₁ to HAVE a c in col 0.
              -- From descentType_M: c in P₂ col 0 (hc₂') →
              --   (cells.filter(j=0 ∧ paint=c)).Nonempty for P₂. descentType_M τ₂ = Bminus.
              --   By hγ_eq: descentType_M τ₁ = Bminus.
              --   So (cells.filter(j=0 ∧ paint=c)).Nonempty for P₁ too.
              -- P₂(i,0)=c → descentType_M τ₂ = Bminus → descentType_M τ₁ = Bminus
              -- → P₁ has c in col 0 at some i'. Then derive contradiction.
              -- descentType_M τ₂ = Bminus (c in col 0):
              -- descentType_M τ₂ = Bminus (c exists in col 0)
              have hdt₁ : PBP.descentType_M τ₁.val τ₁.prop.1 = .Bminus := by
                have hdt₂ : PBP.descentType_M τ₂.val τ₂.prop.1 = .Bminus := by
                  simp only [PBP.descentType_M]
                  rw [if_pos]; exact ⟨⟨i, 0⟩, by simp [Finset.mem_filter, YoungDiagram.mem_cells, hp₂, hc₂']⟩
                rw [← hdt₂]; exact hγ_eq
              simp only [PBP.descentType_M] at hdt₁
              split_ifs at hdt₁ with hne
              · -- P₁ has c at some (i', 0)
                obtain ⟨⟨i', _⟩, hmemf⟩ := hne
                simp [Finset.mem_filter, YoungDiagram.mem_cells] at hmemf
                obtain ⟨hmem_i', hj0, hc_i'⟩ := hmemf; subst hj0
                -- i' ≠ i (P₁(i,0) = s, P₁(i',0) = c)
                have hne_ii' : i ≠ i' := by intro heq; subst heq; rw [hs₁'] at hc_i'; simp at hc_i'
                -- By mono_P on P₁: i' < i → c.layerOrd ≤ s.layerOrd → 3 ≤ 1. Contradiction.
                -- So i' > i.
                have hi'_gt : i' > i := by
                  rcases Nat.lt_or_ge i i' with h | h
                  · exact h
                  · exfalso
                    rcases Nat.eq_or_lt_of_le h with heq | hlt
                    · exact hne_ii' heq.symm
                    · have := τ₁.val.mono_P i' 0 i 0 (Nat.le_of_lt hlt) le_rfl hp
                      rw [hc_i', hs₁'] at this; simp [DRCSymbol.layerOrd] at this
                -- (i', 0) ∈ P₂ and non-dot
                have hp₂_i' : (i', 0) ∈ τ₂.val.P.shape := hshapeP ▸ hmem_i'
                have hnd₂_i' : τ₂.val.P.paint i' 0 ≠ .dot := by
                  intro hd_i'
                  have ⟨hq_i', hdq_i'⟩ := (τ₂.val.dot_match i' 0).mp ⟨hp₂_i', hd_i'⟩
                  rw [← hQ i' 0] at hdq_i'
                  have hd₁_i' := ((τ₁.val.dot_match i' 0).mpr ⟨hshapeQ.symm ▸ hq_i', hdq_i'⟩).2
                  rw [hc_i'] at hd₁_i'; simp at hd₁_i'
                -- P₂(i',0) has layerOrd ≥ P₂(i,0).layerOrd = 3 (mono, i' > i)
                have hlo := τ₂.val.mono_P i 0 i' 0 (Nat.le_of_lt hi'_gt) le_rfl hp₂_i'
                rw [hc₂', DRCSymbol.layerOrd] at hlo
                -- P₂(i',0) ∈ {s, c} with layerOrd ≥ 3 → c
                have hsym₂_i' := τ₂.val.sym_P i' 0 hp₂_i'; rw [τ₂.prop.1] at hsym₂_i'
                simp [DRCSymbol.allowed] at hsym₂_i'
                rcases hsym₂_i' with hd | hs' | hc'
                · exact hnd₂_i' hd
                · rw [hs', DRCSymbol.layerOrd] at hlo; omega
                · -- P₂ has c at both i and i'. col_c_P contradiction.
                  exact hne_ii' (τ₂.val.col_c_P 0 i i' hc₂' hc')
          · -- P₁(i, 0) = c. Need P₂(i, 0) = c.
            rw [hc₁']
            rcases hsym₂ with hd₂' | hs₂' | hc₂'
            · exact absurd hd₂' hd₂
            · exfalso
              -- P₁(i,0)=c, P₂(i,0)=s. Symmetric to above.
              have hdt₂ : PBP.descentType_M τ₂.val τ₂.prop.1 = .Bminus := by
                have hdt₁' : PBP.descentType_M τ₁.val τ₁.prop.1 = .Bminus := by
                  simp only [PBP.descentType_M]
                  rw [if_pos]; exact ⟨⟨i, 0⟩, by simp [Finset.mem_filter, YoungDiagram.mem_cells, hp, hc₁']⟩
                rw [← hdt₁']; exact hγ_eq.symm
              simp only [PBP.descentType_M] at hdt₂
              split_ifs at hdt₂ with hne
              · obtain ⟨⟨i', _⟩, hmemf⟩ := hne
                simp [Finset.mem_filter, YoungDiagram.mem_cells] at hmemf
                obtain ⟨hmem_i', hj0, hc_i'⟩ := hmemf; subst hj0
                have hne_ii' : i ≠ i' := by intro heq; subst heq; rw [hs₂'] at hc_i'; simp at hc_i'
                have hi'_gt : i' > i := by
                  rcases Nat.lt_or_ge i i' with h | h
                  · exact h
                  · exfalso
                    rcases Nat.eq_or_lt_of_le h with heq | hlt
                    · exact hne_ii' heq.symm
                    · have := τ₂.val.mono_P i' 0 i 0 (Nat.le_of_lt hlt) le_rfl hp₂
                      rw [hc_i', hs₂'] at this; simp [DRCSymbol.layerOrd] at this
                have hp₁_i' : (i', 0) ∈ τ₁.val.P.shape := hshapeP.symm ▸ hmem_i'
                have hnd₁_i' : τ₁.val.P.paint i' 0 ≠ .dot := by
                  intro hd_i'
                  have ⟨hq_i', hdq_i'⟩ := (τ₁.val.dot_match i' 0).mp ⟨hp₁_i', hd_i'⟩
                  rw [hQ i' 0] at hdq_i'
                  have hd₂_i' := ((τ₂.val.dot_match i' 0).mpr ⟨hshapeQ ▸ hq_i', hdq_i'⟩).2
                  rw [hc_i'] at hd₂_i'; simp at hd₂_i'
                have hlo := τ₁.val.mono_P i 0 i' 0 (Nat.le_of_lt hi'_gt) le_rfl hp₁_i'
                rw [hc₁', DRCSymbol.layerOrd] at hlo
                have hsym₁_i' := τ₁.val.sym_P i' 0 hp₁_i'; rw [τ₁.prop.1] at hsym₁_i'
                simp [DRCSymbol.allowed] at hsym₁_i'
                rcases hsym₁_i' with hd | hs' | hc'
                · exact hnd₁_i' hd
                · rw [hs', DRCSymbol.layerOrd] at hlo; omega
                · exact hne_ii' (τ₁.val.col_c_P 0 i i' hc₁' hc')
            · exact hc₂'.symm
    · rw [τ₁.val.P.paint_outside i 0 hp,
          τ₂.val.P.paint_outside i 0 (hshapeP ▸ hp)]
  -- Combine: all paints agree
  have hP : ∀ i j, τ₁.val.P.paint i j = τ₂.val.P.paint i j := by
    intro i j; cases j with
    | zero => exact hP_col0 i
    | succ j' => exact hP_ge1 i (j' + 1) (by omega)
  exact Subtype.ext (PBP.ext'' (τ₁.prop.1.trans τ₂.prop.1.symm)
    (PaintedYoungDiagram.ext' (τ₁.prop.2.1.trans τ₂.prop.2.1.symm)
      (funext fun i => funext fun j => hP i j))
    (PaintedYoungDiagram.ext' (τ₁.prop.2.2.trans τ₂.prop.2.2.symm)
      (funext fun i => funext fun j => hQ i j)))

/-! ## M→B descent image characterization -/

/-- M→B descent target: B⁺ or B⁻ type PBP with shifted shapes.
    The target type (B⁺ vs B⁻) depends on whether c appears in P col 0.
    Uses descentType_M from Descent.lean. -/
noncomputable def descentMB_targetType (τ : PBP) (hγ : τ.γ = .M) : RootType :=
  PBP.descentType_M τ hγ

/-! ## M→B descent image characterization

The following properties of M→B descent are USED by the inductive step
(card_PBPSet_M_inductive_step) but are subsumed by that admitted theorem.
The mathematical arguments are:

- **Primitive (r₁ > r₂):** Every B-type PBP on the target shapes has an M
  preimage via the lift construction (mirrors liftCD_PBP).
  Reference: [BMSZb] Proposition 10.8(a).

- **Balanced (r₁ = r₂):** The descent image is exactly {τ' | tailClass_B ≠ SS}.
  No M-type PBP descends to a B PBP with tail symbol s.
  Reference: [BMSZb] Proposition 10.8(b).

- **Lift construction** (liftMB_PBP): The partial inverse of descent, building
  an M-type PBP from a B-type PBP by prepending a column to P and refilling Q
  with dots. This is a ~200 line construction with 12 proof obligations,
  analogous to liftCD_PBP in CorrespondenceC.lean. -/

/-! ## Base case: M-type singleton

For M type with P = ⊥ and Q single column of height r₁/2:
- dot_match forces no dots in Q (since P = ⊥)
- Q paint ∈ {r, d} on all cells
- Column mono + at most one d gives exactly 2 options:
  all-r or (r...r, d at bottom)
- countPBP_M [r₁] = 2 (= 0 + 1 + 1 from countPBP_B []) -/

/-- MSeq k: length-k sequences in {r, d}, monotone layerOrd, at most one d.
    These enumerate M-type Q columns when P = ⊥. -/
private def MSeq (k : ℕ) : Type :=
  { f : Fin k → DRCSymbol //
    (∀ i, f i = .r ∨ f i = .d) ∧
    (∀ i j : Fin k, i ≤ j → (f i).layerOrd ≤ (f j).layerOrd) ∧
    (∀ i j : Fin k, f i = .d → f j = .d → i = j) }

private instance (k : ℕ) : Fintype (MSeq k) := by unfold MSeq; infer_instance
private instance (k : ℕ) : DecidableEq (MSeq k) := by unfold MSeq; infer_instance

/-- MSeq k has exactly 2 elements when k > 0: all-r and (r...r, d at bottom).
    MSeq 0 has exactly 1 element (empty sequence). -/
-- The all-r MSeq.
private def MSeq_allr_fun (k : ℕ) : Fin k → DRCSymbol := fun _ => .r

private def MSeq_allr (k : ℕ) : MSeq k :=
  ⟨MSeq_allr_fun k,
   ⟨fun _ => Or.inl rfl,
    fun _ _ _ => le_refl _,
    fun i _ h1 _ => by simp [MSeq_allr_fun] at h1⟩⟩

-- The r...r,d MSeq (all r except last is d). Requires k > 0.
private def MSeq_lastd_fun (k : ℕ) : Fin k → DRCSymbol :=
  fun i => if (i : ℕ) = k - 1 then .d else .r

private def MSeq_lastd (k : ℕ) (hk : k > 0) : MSeq k :=
  ⟨MSeq_lastd_fun k,
   ⟨fun i => by simp only [MSeq_lastd_fun]; split_ifs <;> simp,
    fun i j hij => by
      simp only [MSeq_lastd_fun, DRCSymbol.layerOrd]
      by_cases h1 : (i : ℕ) = k - 1 <;> by_cases h2 : (j : ℕ) = k - 1
      · simp [h1, h2]
      · exfalso; have : (j : ℕ) < k - 1 := by omega
        have : (i : ℕ) ≤ (j : ℕ) := hij; omega
      · simp [h1, h2]
      · simp [h1, h2],
    fun i j hi hj => by
      simp only [MSeq_lastd_fun] at hi hj
      split_ifs at hi with h1
      split_ifs at hj with h2
      exact Fin.ext (by omega)⟩⟩

-- Any MSeq is either all-r or lastd.
private theorem MSeq_exhaust (k : ℕ) (hk : k > 0) (x : MSeq k) :
    x = MSeq_allr k ∨ x = MSeq_lastd k hk := by
  obtain ⟨f, hrd, hmono, huniq⟩ := x
  by_cases hd : ∃ i, f i = .d
  · right
    apply Subtype.ext; funext i; simp only [MSeq_lastd, MSeq_lastd_fun]
    obtain ⟨j, hj⟩ := hd
    -- j must be the last index
    have hj_last : (j : ℕ) = k - 1 := by
      by_contra hne
      have hjlt : (j : ℕ) < k - 1 := by have := j.isLt; omega
      have hk1 : k - 1 < k := Nat.sub_lt hk (by omega)
      have hmj := hmono j ⟨k - 1, hk1⟩ (by exact Fin.mk_le_mk.mpr (by omega))
      rw [hj] at hmj; simp [DRCSymbol.layerOrd] at hmj
      rcases hrd ⟨k - 1, hk1⟩ with h | h <;> rw [h] at hmj <;> simp at hmj
      exact hne (congrArg Fin.val (huniq j ⟨k - 1, hk1⟩ hj h))
    by_cases h : (i : ℕ) = k - 1
    · rw [if_pos h]
      have hi_eq_j : i = j := Fin.ext (by omega)
      rw [hi_eq_j]; exact hj
    · rw [if_neg h]
      rcases hrd i with hr | hd_i
      · exact hr
      · exfalso; exact h (congrArg Fin.val (huniq i j hd_i hj) |>.trans hj_last)
  · left
    apply Subtype.ext; funext i; simp only [MSeq_allr]
    push_neg at hd
    rcases hrd i with h | h
    · exact h
    · exact absurd h (hd i)

-- MSeq_allr ≠ MSeq_lastd.
private theorem MSeq_allr_ne_lastd (k : ℕ) (hk : k > 0) :
    MSeq_allr k ≠ MSeq_lastd k hk := by
  intro h
  have := congrArg (fun s => s.val ⟨k - 1, by omega⟩) h
  simp [MSeq_allr, MSeq_allr_fun, MSeq_lastd, MSeq_lastd_fun] at this

private theorem MSeq_card_pos (k : ℕ) (hk : k > 0) : Fintype.card (MSeq k) = 2 := by
  have h_two : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [← h_two]
  apply Fintype.card_eq.mpr
  refine ⟨{
    toFun := fun x => if x = MSeq_allr k then 0 else 1
    invFun := fun i => if i = 0 then MSeq_allr k else MSeq_lastd k hk
    left_inv := by
      intro x; rcases MSeq_exhaust k hk x with rfl | rfl
      · simp
      · simp [Ne.symm (MSeq_allr_ne_lastd k hk)]
    right_inv := by
      intro ⟨i, hi⟩; cases i with
      | zero => simp
      | succ n => simp [Ne.symm (MSeq_allr_ne_lastd k hk)]; omega }⟩

private lemma singleCol_j0_M {μQ : YoungDiagram} (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0)
    {i j : ℕ} (hmem : (i, j) ∈ μQ) : j = 0 := by
  by_contra hj
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmem) (by rw [hsc j (by omega)]; omega)

/-- Paint Q column 0 from an MSeq, dots elsewhere. -/
private def mkQpaint_M (μQ : YoungDiagram) (m : MSeq (μQ.colLen 0)) (i j : ℕ) : DRCSymbol :=
  if h : j = 0 ∧ i < μQ.colLen 0 then m.val ⟨i, h.2⟩ else .dot

private lemma mkQpaint_M_nondot_imp {μQ : YoungDiagram} {m : MSeq (μQ.colLen 0)}
    {i j : ℕ} (h : mkQpaint_M μQ m i j ≠ .dot) : j = 0 ∧ i < μQ.colLen 0 := by
  unfold mkQpaint_M at h; split_ifs at h with hc; exact hc; exact absurd rfl h

@[simp] private lemma mkQpaint_M_col0 {μQ : YoungDiagram} {m : MSeq (μQ.colLen 0)}
    {i : ℕ} (hi : i < μQ.colLen 0) : mkQpaint_M μQ m i 0 = m.val ⟨i, hi⟩ := by
  simp [mkQpaint_M, hi]

/-- Construct PBPSet .M ⊥ μQ from an MSeq, for single-column Q. -/
private noncomputable def MSeq_to_PBP_M {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (m : MSeq (μQ.colLen 0)) :
    PBPSet .M ⊥ μQ := by
  refine ⟨⟨.M, emptyPYD,
    ⟨μQ, mkQpaint_M μQ m, fun i j hmem => ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  -- paint_outside
  · unfold mkQpaint_M; split_ifs with hc
    · exact absurd (YoungDiagram.mem_iff_lt_colLen.mpr (hc.1 ▸ hc.2)) hmem
    · rfl
  -- sym_P
  · intro _ _ h; exact absurd h (YoungDiagram.notMem_bot _)
  -- sym_Q
  · intro i j hmem'; change (i, j) ∈ μQ at hmem'
    have hj := singleCol_j0_M hsc hmem'; subst hj
    have hi := YoungDiagram.mem_iff_lt_colLen.mp hmem'
    show DRCSymbol.allowed .M .R (mkQpaint_M μQ m i 0)
    rw [mkQpaint_M_col0 hi]; simp [DRCSymbol.allowed]
    rcases m.prop.1 ⟨i, hi⟩ with h | h <;> simp [h]
  -- dot_match
  · intro i' j'; constructor
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
    · intro ⟨hmemQ, hpaint⟩; exfalso
      change (i', j') ∈ μQ at hmemQ; change mkQpaint_M μQ m i' j' = .dot at hpaint
      have hj' := singleCol_j0_M hsc hmemQ; subst hj'
      rw [mkQpaint_M_col0 (YoungDiagram.mem_iff_lt_colLen.mp hmemQ)] at hpaint
      rcases m.prop.1 ⟨i', YoungDiagram.mem_iff_lt_colLen.mp hmemQ⟩ with h | h <;> simp [h] at hpaint
  -- mono_P
  · intro _ _ _ _ _ _ h; exact absurd h (YoungDiagram.notMem_bot _)
  -- mono_Q
  · intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (mkQpaint_M μQ m i₁ j₁).layerOrd ≤ (mkQpaint_M μQ m i₂ j₂).layerOrd
    change (i₂, j₂) ∈ μQ at hmem₂
    have hj₂ := singleCol_j0_M hsc hmem₂; subst hj₂
    have hj₁ : j₁ = 0 := by omega
    subst hj₁
    have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
    rw [mkQpaint_M_col0 (show i₁ < μQ.colLen 0 by omega), mkQpaint_M_col0 hi₂]
    exact m.prop.2.1 ⟨i₁, by omega⟩ ⟨i₂, hi₂⟩ hi
  -- row_s
  · intro i' s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> dsimp at h₁ h₂
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₂
    · exact ⟨rfl, by
        rw [(mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i' j₁ ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)).1,
            (mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i' j₂ ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)).1]⟩
  -- row_r
  · intro i' s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> dsimp at h₁ h₂
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₂
    · exact ⟨rfl, by
        rw [(mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i' j₁ ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)).1,
            (mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i' j₂ ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)).1]⟩
  -- col_c_P
  · intro _ _ _ h; simp [emptyPYD] at h
  -- col_c_Q
  · intro j' i₁ _ h₁ _; exfalso
    change mkQpaint_M μQ m i₁ j' = .c at h₁
    have ⟨hj', hi₁⟩ := mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i₁ j' ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)
    subst hj'; rw [mkQpaint_M_col0 hi₁] at h₁
    rcases m.prop.1 ⟨i₁, hi₁⟩ with h | h <;> simp [h] at h₁
  -- col_d_P
  · intro _ _ _ h; simp [emptyPYD] at h
  -- col_d_Q
  · intro j' i₁ i₂ h₁ h₂
    change mkQpaint_M μQ m i₁ j' = .d at h₁
    change mkQpaint_M μQ m i₂ j' = .d at h₂
    have ⟨hj', hi₁⟩ := mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i₁ j' ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)
    have ⟨_, hi₂⟩ := mkQpaint_M_nondot_imp (show mkQpaint_M μQ m i₂ j' ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)
    subst hj'; rw [mkQpaint_M_col0 hi₁] at h₁; rw [mkQpaint_M_col0 hi₂] at h₂
    exact Fin.val_eq_of_eq (m.prop.2.2 ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ h₁ h₂)

/-- Extract Q col 0 as an MSeq from a PBPSet .M ⊥ μQ. -/
private noncomputable def PBPSet_M_bot_to_MSeq {μQ : YoungDiagram}
    (τ : PBPSet .M ⊥ μQ) : MSeq (μQ.colLen 0) :=
  ⟨fun i => τ.val.Q.paint i.val 0, by
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hi hj => ?_⟩
    · have hmemQ : (i.val, 0) ∈ τ.val.Q.shape := by
        rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr i.isLt
      have hne : τ.val.Q.paint i.val 0 ≠ .dot := by
        intro hdot
        have ⟨hmemP, _⟩ := (τ.val.dot_match i.val 0).mpr ⟨hmemQ, hdot⟩
        rw [τ.prop.2.1] at hmemP; exact absurd hmemP (YoungDiagram.notMem_bot _)
      have hall := τ.val.sym_Q i.val 0 hmemQ
      simp [DRCSymbol.allowed, τ.prop.1] at hall
      rcases hall with h | h | h
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h
    · exact τ.val.mono_Q i.val 0 j.val 0 hij (le_refl 0)
        (by rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr j.isLt)
    · exact Fin.ext (τ.val.col_d_Q 0 i.val j.val hi hj)⟩

/-- Round-trip: extract then reconstruct gives the same PBP (single-column Q, M-type). -/
private theorem MSeq_roundtrip_left {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (τ : PBPSet .M ⊥ μQ) :
    MSeq_to_PBP_M hsc (PBPSet_M_bot_to_MSeq τ) = τ := by
  apply Subtype.ext; apply PBP.ext''
  · -- γ: both .M
    unfold MSeq_to_PBP_M; dsimp; exact τ.prop.1.symm
  · -- P: both emptyPYD
    unfold MSeq_to_PBP_M; dsimp
    exact (PYD_eq_emptyPYD_of_shape_bot τ.prop.2.1).symm
  · -- Q: paint agrees
    apply PaintedYoungDiagram.ext'
    · unfold MSeq_to_PBP_M; dsimp; exact τ.prop.2.2.symm
    · ext i j
      unfold MSeq_to_PBP_M PBPSet_M_bot_to_MSeq; dsimp
      simp only [mkQpaint_M]
      split_ifs with hc
      · rw [hc.1]
      · push_neg at hc
        symm; apply τ.val.Q.paint_outside
        intro hmem; rw [τ.prop.2.2] at hmem
        by_cases hj : j = 0
        · subst hj; exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmem) (not_lt.mpr (hc rfl))
        · exact absurd (singleCol_j0_M hsc hmem) hj

/-- Round-trip: reconstruct then extract gives the same MSeq. -/
private theorem MSeq_roundtrip_right {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (m : MSeq (μQ.colLen 0)) :
    PBPSet_M_bot_to_MSeq (MSeq_to_PBP_M hsc m) = m := by
  apply Subtype.ext; funext i
  simp only [PBPSet_M_bot_to_MSeq, MSeq_to_PBP_M, mkQpaint_M]
  dsimp; simp [i.isLt]

/-- PBPSet .M ⊥ μQ ≃ MSeq (μQ.colLen 0) for single-column Q. -/
private noncomputable def PBPSet_M_bot_equiv_MSeq {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) :
    PBPSet .M ⊥ μQ ≃ MSeq (μQ.colLen 0) where
  toFun := PBPSet_M_bot_to_MSeq
  invFun := MSeq_to_PBP_M hsc
  left_inv := MSeq_roundtrip_left hsc
  right_inv := MSeq_roundtrip_right hsc

/-- card(PBPSet .M ⊥ μQ) = 2 for single-column Q with positive height.
    Proof via PBPSet .M ⊥ μQ ≃ MSeq (μQ.colLen 0).

    The equivalence:
    - Forward: extract Q col 0 paint (values ∈ {r,d} by dot_match + P=⊥)
    - Backward: construct PBP with P=⊥, Q col 0 from MSeq, rest dots

    The backward direction requires verifying ~12 PBP proof obligations
    (sym_P/Q, dot_match, mono_P/Q, row_s/r, col_c/d_P/Q).
    The forward direction uses sym_Q, dot_match, mono_Q, col_d_Q. -/
private theorem card_PBPSet_M_bot_singleCol (μQ : YoungDiagram)
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (hpos : μQ.colLen 0 > 0) :
    Fintype.card (PBPSet .M ⊥ μQ) = 2 := by
  rw [Fintype.card_congr (PBPSet_M_bot_equiv_MSeq hsc)]
  exact MSeq_card_pos _ hpos

/-- Base case: M with single even row [r₁].
    By (1,2) always primitive: count = total B count of []. -/
theorem card_PBPSet_M_singleton (r₁ : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M [r₁])
    (hQ : μQ.colLens = dpartColLensQ_M [r₁])
    (heven : Even r₁) (hr : r₁ > 0) :
    Fintype.card (PBPSet .M μP μQ) = countPBP_M [r₁] := by
  -- P = ⊥ for M singleton
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  -- Q has single column of height r₁/2
  have hQ_form : dpartColLensQ_M [r₁] = [r₁ / 2] := by
    simp [dpartColLensQ_M, hr]
  have hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0 := by
    intro j hj
    -- rowLen 0 = colLens.length = 1, so j ≥ 1 → j ≥ rowLen 0 → colLen j = 0
    have hlen := YoungDiagram.length_colLens μQ
    rw [hQ, hQ_form] at hlen; simp at hlen
    -- colLen j = 0 when j ≥ rowLen 0
    by_contra h; push_neg at h
    have hpos : 0 < μQ.colLen j := by omega
    have hmem : (0, j) ∈ μQ := YoungDiagram.mem_iff_lt_colLen.mpr hpos
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega)
  have hcol0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, hQ_form])
  -- r₁ > 0 and even → r₁/2 > 0
  have hr2 : r₁ / 2 > 0 := by obtain ⟨k, rfl⟩ := heven; omega
  -- card = 2
  have h_card := card_PBPSet_M_bot_singleCol μQ hsc (by omega)
  -- countPBP_M [r₁] = dd + rc + ss = 0 + 1 + 1 = 2
  have h_count : countPBP_M [r₁] = 2 := by
    simp only [countPBP_M, List.filter]
    simp [hr, countPBP_B]
  rw [h_card, h_count]

/-- Base case: empty orbit for M type. -/
theorem card_PBPSet_M_empty :
    Fintype.card (PBPSet .M ⊥ ⊥) = countPBP_M [] := by
  simp [countPBP_M, card_PBPSet_bot]

/-- **M-type inductive step (admitted).**
    Proves: card(PBPSet .M μP μQ) = countPBP_M (r₁ :: r₂ :: rest)
    for the inductive case of the M main theorem.

    This requires building the M→B lift (partial inverse of descent) and
    proving surjectivity (primitive) or image characterization (balanced).
    The construction mirrors liftCD_PBP in CorrespondenceC.lean (~500 lines total).

    Key admitted facts:
    1. liftMB_PBP: B→M lift construction (~200 lines)
    2. descentMB_liftMB_round_trip: descent ∘ lift = id (~50 lines)
    3. Primitive: lift is total → card(M) = card(B target) = tripleSum(countPBP_B tail)
    4. Balanced: lift defined on DD∪RC, SS excluded → card(M) = dd + rc

    Computationally verified for all dual partitions up to size 24 (test_verify_drc.py).
    Reference: [BMSZb] Proposition 10.8 + 10.12. -/
theorem card_PBPSet_M_inductive_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_M (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r) :
    Fintype.card (PBPSet .M μP μQ) = countPBP_M (r₁ :: r₂ :: rest) := by
  sorry

/-! ## Main theorem -/

/-- **Proposition 10.12 for M type (= C̃):**
    card(PBPSet .M μP μQ) = countPBP_M dp.

    Proof: M→B descent is injective. Image analysis:
    - Primitive (r₁ > r₂): surjective → count = DD + RC + SS
    - Balanced (r₁ = r₂): image excludes SS → count = DD + RC

    The inductive step requires:
    1. M→B descent raw PBP construction (descentMB_PBP)
    2. Injectivity (descentMB_injective)
    3. Lift construction (liftMB_PBP) with round-trip proof
    4. Primitive/balanced cardinality theorems
    Each mirrors the corresponding C→D infrastructure in CorrespondenceC.lean. -/
theorem card_PBPSet_M_eq_countPBP_M (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M dp)
    (hQ : μQ.colLens = dpartColLensQ_M dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .M μP μQ) = countPBP_M dp := by
  match dp, hP, hQ, hsort, heven, hpos with
  | [], hP, hQ, _, _, _ =>
    have h1 := yd_of_colLens_nil (by rw [hP]; rfl)
    have h2 := yd_of_colLens_nil (by rw [hQ]; rfl)
    subst h1; subst h2
    exact card_PBPSet_M_empty
  | [r₁], hP, hQ, _, heven, hpos =>
    exact card_PBPSet_M_singleton r₁ μP μQ hP hQ (heven r₁ (by simp)) (hpos r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos =>
    -- Inductive step: M→B descent + lift give card(M) = countPBP_M formula.
    --
    -- The M→B descent (descentMB_PBP, fully proved) maps PBPSet .M μP μQ
    -- injectively (descentMB_injective, fully proved) into B-type PBPs with
    -- shapes (shiftLeft μP, μQ).
    --
    -- Primitive (r₁ > r₂): descent is bijective onto all B-type PBPs on target,
    --   card(M) = tripleSum(countPBP_B (r₂::rest)) = dd + rc + ss = countPBP_M dp
    --
    -- Balanced (r₁ = r₂): descent image = {σ ∈ B | tailClass_B ≠ SS},
    --   card(M) = dd + rc = countPBP_M dp
    --
    -- Infrastructure needed (~500 lines, mirrors CorrespondenceC.lean C→D case):
    --   1. Lift B→M (liftMB_PBP): ~200 lines building PBP with 12 proof obligations
    --   2. Round-trip: descent ∘ lift = id: ~50 lines
    --   3. Primitive surjectivity: ~50 lines (lift is defined for all B PBPs)
    --   4. Balanced image characterization: ~100 lines (SS exclusion)
    --   5. Shape compatibility: target shapes match B dp_B = (r₂::rest) counting
    --
    -- All five dependencies have been verified computationally (Python tests pass
    -- for all dual partitions up to size 24).
    exact card_PBPSet_M_inductive_step r₁ r₂ rest μP μQ hP hQ hsort heven hpos

/-! ## Structural theorems -/

/-- Filter by positivity is identity on lists of positive naturals. -/
private lemma filter_pos_of_all_pos (l : List ℕ) (h : ∀ x ∈ l, 0 < x) :
    l.filter (fun x => decide (x > 0)) = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter]
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    simp [ha, ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

theorem countPBP_M_primitive {r₁ r₂ : ℕ} {rest : DualPart}
    (h : r₁ > r₂) (hpos : ∀ x ∈ r₁ :: r₂ :: rest, 0 < x) :
    countPBP_M (r₁ :: r₂ :: rest) =
      let (dd, rc, ss) := countPBP_B (r₂ :: rest)
      dd + rc + ss := by
  have hr1 : r₁ > 0 := hpos r₁ (by simp)
  have hr2 : r₂ > 0 := hpos r₂ (by simp)
  have hrest : ∀ x ∈ rest, 0 < x := fun x hx => hpos x (by simp [hx])
  simp only [countPBP_M, List.filter, hr1, hr2, decide_true, h, ite_true, List.tail_cons]
  congr 1; congr 1
  all_goals (congr 1; rw [filter_pos_of_all_pos rest hrest])

theorem countPBP_M_balanced {r₁ r₂ : ℕ} {rest : DualPart}
    (h : ¬(r₁ > r₂)) (hpos : ∀ x ∈ r₁ :: r₂ :: rest, 0 < x) :
    countPBP_M (r₁ :: r₂ :: rest) =
      let (dd, rc, _) := countPBP_B (r₂ :: rest)
      dd + rc := by
  have hr1 : r₁ > 0 := hpos r₁ (by simp)
  have hr2 : r₂ > 0 := hpos r₂ (by simp)
  have hrest : ∀ x ∈ rest, 0 < x := fun x hx => hpos x (by simp [hx])
  simp only [countPBP_M, List.filter, hr1, hr2, decide_true, h, ite_false, List.tail_cons]
  congr 1
  all_goals (congr 1; rw [filter_pos_of_all_pos rest hrest])
