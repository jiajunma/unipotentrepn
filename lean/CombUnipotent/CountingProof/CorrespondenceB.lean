/-
# Counting Proof: B-type correspondence (Proposition 10.11 for B)

Reference: [BMSZb] Proposition 10.11, Section 10.5–10.6.

Proves: card(PBPSet .Bplus μP μQ) + card(PBPSet .Bminus μP μQ) = tripleSum(countPBP_B dp)

Proof strategy (mirrors Correspondence.lean for D-type):
1. Double descent B→M→B maps PBPSet_B(μP, μQ) → PBPSet_B(shiftLeft μP, shiftLeft μQ)
2. Combined with (signature, epsilon), the map is injective (ddescent_inj_B)
3. Fiber cardinality per tail class gives the tailCoeffs recursion
4. Primitive case: uniform fiber → multiply by total
5. Balanced case: matrix multiply by (tDD, tRC, tSS) / (scDD, scRC, scSS)
-/
import CombUnipotent.CountingProof.Basic
import CombUnipotent.CountingProof.Fiber
import CombUnipotent.CountingProof.LiftRC
import CombUnipotent.CountingProof.Correspondence
import Mathlib.Algebra.Ring.Parity

open Classical

/-! ## B-type recursion: dropping 2 rows = shiftLeft -/

/-- Recursion: tail of B-P columns = B-P columns of rest. -/
theorem dpartColLensP_B_tail (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensP_B (r₁ :: r₂ :: rest)).tail = dpartColLensP_B rest := by
  simp [dpartColLensP_B]

/-- Recursion: tail of B-Q columns = B-Q columns of rest. -/
theorem dpartColLensQ_B_tail (r₁ r₂ : ℕ) (rest : DualPart) :
    (dpartColLensQ_B (r₁ :: r₂ :: rest)).tail = dpartColLensQ_B rest := by
  simp [dpartColLensQ_B]

/-! ## B⁺/B⁻ symmetry -/

/-- PBP equality follows from equality of the three data fields (γ, P, Q);
    proof fields are irrelevant by proof irrelevance. -/
private theorem PBP_eq_of_data (τ₁ τ₂ : PBP)
    (h1 : τ₁.γ = τ₂.γ) (h2 : τ₁.P = τ₂.P) (h3 : τ₁.Q = τ₂.Q) : τ₁ = τ₂ := by
  cases τ₁; cases τ₂; simp at h1 h2 h3; subst h1; subst h2; subst h3; rfl

/-- Swap B⁺ ↔ B⁻ in a PBP, preserving all constraints.
    This works because `DRCSymbol.allowed .Bplus s σ ↔ DRCSymbol.allowed .Bminus s σ`
    for all sides `s` and symbols `σ` (both have P∈{•,c}, Q∈{•,s,r,d}). -/
def PBP.swapBplusBminus (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) : PBP where
  γ := if τ.γ = .Bplus then .Bminus else .Bplus
  P := τ.P
  Q := τ.Q
  sym_P := by
    intro i j hmem; have := τ.sym_P i j hmem
    rcases hγ with h | h <;> simp [h, DRCSymbol.allowed] at this ⊢ <;> exact this
  sym_Q := by
    intro i j hmem; have := τ.sym_Q i j hmem
    rcases hγ with h | h <;> simp [h, DRCSymbol.allowed] at this ⊢ <;> exact this
  dot_match := τ.dot_match
  mono_P := τ.mono_P
  mono_Q := τ.mono_Q
  row_s := τ.row_s
  row_r := τ.row_r
  col_c_P := τ.col_c_P
  col_c_Q := τ.col_c_Q
  col_d_P := τ.col_d_P
  col_d_Q := τ.col_d_Q

/-- B⁺ and B⁻ have the same cardinality: the allowed symbol sets are identical,
    so swapping the γ tag gives a bijection PBPSet .Bplus μP μQ ≃ PBPSet .Bminus μP μQ. -/
theorem card_Bplus_eq_Bminus (μP μQ : YoungDiagram) :
    Fintype.card (PBPSet .Bplus μP μQ) = Fintype.card (PBPSet .Bminus μP μQ) := by
  apply Fintype.card_congr
  refine {
    toFun := fun ⟨τ, hγ, hP, hQ⟩ =>
      ⟨τ.swapBplusBminus (Or.inl hγ), by simp [PBP.swapBplusBminus, hγ], hP, hQ⟩
    invFun := fun ⟨τ, hγ, hP, hQ⟩ =>
      ⟨τ.swapBplusBminus (Or.inr hγ), by simp [PBP.swapBplusBminus, hγ], hP, hQ⟩
    left_inv := fun ⟨τ, hγ, hP, hQ⟩ => by
      simp only; congr 1
      exact PBP_eq_of_data _ _ (by simp [PBP.swapBplusBminus, hγ]) rfl rfl
    right_inv := fun ⟨τ, hγ, hP, hQ⟩ => by
      simp only; congr 1
      exact PBP_eq_of_data _ _ (by simp [PBP.swapBplusBminus, hγ]) rfl rfl
  }

/-! ## Base cases -/

/-! ### Singleton base case infrastructure

For B-type with dp = [r₁], P = ⊥ and Q has one column of height c₁ = r₁/2.
The PBPs biject with DSeq(c₁) ≃ GSeq(c₁), giving card = 2c₁+1. -/

/-- Sequences from {s,r,d}, monotone (layerOrd), at most one d.
    B-type Q-column analogue of `GSeq` (which uses {s,r,c}). -/
private def DSeq (k : ℕ) : Type :=
  { v : Fin k → DRCSymbol //
    (∀ i, v i = .s ∨ v i = .r ∨ v i = .d) ∧
    (∀ i j : Fin k, i.val ≤ j.val → (v i).layerOrd ≤ (v j).layerOrd) ∧
    (∀ i j : Fin k, v i = .d → v j = .d → i = j) }

private instance (k : ℕ) : Fintype (DSeq k) := by unfold DSeq; infer_instance

/-- Swap c ↔ d preserves the relative order s < r < {c, d}. -/
private def swapCD : DRCSymbol → DRCSymbol | .c => .d | .d => .c | x => x
@[simp] private lemma swapCD_invol (x : DRCSymbol) : swapCD (swapCD x) = x := by cases x <;> rfl

private lemma swapCD_mono_srd {a b : DRCSymbol}
    (ha : a = .s ∨ a = .r ∨ a = .d) (hb : b = .s ∨ b = .r ∨ b = .d)
    (hle : a.layerOrd ≤ b.layerOrd) :
    (swapCD a).layerOrd ≤ (swapCD b).layerOrd := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [swapCD, DRCSymbol.layerOrd]

private lemma swapCD_mono_src {a b : DRCSymbol}
    (ha : a = .s ∨ a = .r ∨ a = .c) (hb : b = .s ∨ b = .r ∨ b = .c)
    (hle : a.layerOrd ≤ b.layerOrd) :
    (swapCD a).layerOrd ≤ (swapCD b).layerOrd := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [swapCD, DRCSymbol.layerOrd]

/-- DSeq(k) ≃ GSeq(k) via swapping c ↔ d. -/
private noncomputable def DSeq_equiv_GSeq (k : ℕ) : DSeq k ≃ GSeq k where
  toFun d := ⟨fun i => swapCD (d.val i), by
    refine ⟨fun i => ?_, fun i j hij => swapCD_mono_srd (d.prop.1 i) (d.prop.1 j) (d.prop.2.1 i j hij),
      fun i j hi hj => d.prop.2.2 i j ?_ ?_⟩
    · rcases d.prop.1 i with h | h | h <;> simp [h, swapCD]
    · rcases d.prop.1 i with h | h | h <;> simp [h, swapCD] at hi ⊢ <;> exact h
    · rcases d.prop.1 j with h | h | h <;> simp [h, swapCD] at hj ⊢ <;> exact h⟩
  invFun g := ⟨fun i => swapCD (g.val i), by
    refine ⟨fun i => ?_, fun i j hij => swapCD_mono_src (g.prop.1 i) (g.prop.1 j) (g.prop.2.1 i j hij),
      fun i j hi hj => g.prop.2.2 i j ?_ ?_⟩
    · rcases g.prop.1 i with h | h | h <;> simp [h, swapCD]
    · rcases g.prop.1 i with h | h | h <;> simp [h, swapCD] at hi ⊢ <;> exact h
    · rcases g.prop.1 j with h | h | h <;> simp [h, swapCD] at hj ⊢ <;> exact h⟩
  left_inv d := by apply Subtype.ext; funext i; simp
  right_inv g := by apply Subtype.ext; funext i; simp

private theorem DSeq_card (k : ℕ) : Fintype.card (DSeq k) = 2 * k + 1 :=
  (Fintype.card_congr (DSeq_equiv_GSeq k)).trans (GSeq_card k)

/-- Paint Q column 0 from a DSeq, dots elsewhere. -/
private def mkQpaint (μQ : YoungDiagram) (d : DSeq (μQ.colLen 0)) (i j : ℕ) : DRCSymbol :=
  if h : j = 0 ∧ i < μQ.colLen 0 then d.val ⟨i, h.2⟩ else .dot

private lemma mkQpaint_nondot_imp {μQ : YoungDiagram} {d : DSeq (μQ.colLen 0)}
    {i j : ℕ} (h : mkQpaint μQ d i j ≠ .dot) : j = 0 ∧ i < μQ.colLen 0 := by
  unfold mkQpaint at h; split_ifs at h with hc; exact hc; exact absurd rfl h

@[simp] private lemma mkQpaint_col0 {μQ : YoungDiagram} {d : DSeq (μQ.colLen 0)}
    {i : ℕ} (hi : i < μQ.colLen 0) : mkQpaint μQ d i 0 = d.val ⟨i, hi⟩ := by
  simp [mkQpaint, hi]

private lemma singleCol_j0 {μQ : YoungDiagram} (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0)
    {i j : ℕ} (hmem : (i, j) ∈ μQ) : j = 0 := by
  by_contra hj
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmem) (by rw [hsc j (by omega)]; omega)

/-- Construct PBPSet .Bminus ⊥ μQ from a DSeq, for single-column Q.
    The Q painting uses mkQpaint; P = emptyPYD.
    All PBP constraints hold because Q has a single column with non-dot symbols. -/
private noncomputable def DSeq_to_PBP_Bminus {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (d : DSeq (μQ.colLen 0)) :
    PBPSet .Bminus ⊥ μQ := by
  refine ⟨⟨.Bminus, emptyPYD,
    ⟨μQ, mkQpaint μQ d, fun i j hmem => ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  -- paint_outside
  · unfold mkQpaint; split_ifs with hc
    · exact absurd (YoungDiagram.mem_iff_lt_colLen.mpr (hc.1 ▸ hc.2)) hmem
    · rfl
  -- sym_P
  · intro _ _ h; exact absurd h (YoungDiagram.notMem_bot _)
  -- sym_Q
  · intro i j hmem'; change (i, j) ∈ μQ at hmem'
    have hj := singleCol_j0 hsc hmem'; subst hj
    have hi := YoungDiagram.mem_iff_lt_colLen.mp hmem'
    show DRCSymbol.allowed .Bminus .R (mkQpaint μQ d i 0)
    rw [mkQpaint_col0 hi]; simp [DRCSymbol.allowed]
    rcases d.prop.1 ⟨i, hi⟩ with h | h | h <;> simp [h]
  -- dot_match
  · intro i' j'; constructor
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
    · intro ⟨hmemQ, hpaint⟩; exfalso
      change (i', j') ∈ μQ at hmemQ; change mkQpaint μQ d i' j' = .dot at hpaint
      have hj' := singleCol_j0 hsc hmemQ; subst hj'
      rw [mkQpaint_col0 (YoungDiagram.mem_iff_lt_colLen.mp hmemQ)] at hpaint
      rcases d.prop.1 ⟨i', YoungDiagram.mem_iff_lt_colLen.mp hmemQ⟩ with h | h | h <;> simp [h] at hpaint
  -- mono_P
  · intro _ _ _ _ _ _ h; exact absurd h (YoungDiagram.notMem_bot _)
  -- mono_Q
  · intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (mkQpaint μQ d i₁ j₁).layerOrd ≤ (mkQpaint μQ d i₂ j₂).layerOrd
    change (i₂, j₂) ∈ μQ at hmem₂
    have hj₂ := singleCol_j0 hsc hmem₂; subst hj₂
    have hj₁ : j₁ = 0 := by omega
    subst hj₁
    have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
    rw [mkQpaint_col0 (show i₁ < μQ.colLen 0 by omega), mkQpaint_col0 hi₂]
    exact d.prop.2.1 ⟨i₁, by omega⟩ ⟨i₂, hi₂⟩ hi
  -- row_s
  · intro i' s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> dsimp at h₁ h₂
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₂
    · exact ⟨rfl, by
        rw [(mkQpaint_nondot_imp (show mkQpaint μQ d i' j₁ ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)).1,
            (mkQpaint_nondot_imp (show mkQpaint μQ d i' j₂ ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)).1]⟩
  -- row_r
  · intro i' s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> dsimp at h₁ h₂
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₁
    · simp [emptyPYD] at h₂
    · exact ⟨rfl, by
        rw [(mkQpaint_nondot_imp (show mkQpaint μQ d i' j₁ ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)).1,
            (mkQpaint_nondot_imp (show mkQpaint μQ d i' j₂ ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)).1]⟩
  -- col_c_P
  · intro _ _ _ h; simp [emptyPYD] at h
  -- col_c_Q
  · intro j' i₁ _ h₁ _; exfalso
    change mkQpaint μQ d i₁ j' = .c at h₁
    have ⟨hj', hi₁⟩ := mkQpaint_nondot_imp (show mkQpaint μQ d i₁ j' ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)
    subst hj'; rw [mkQpaint_col0 hi₁] at h₁
    rcases d.prop.1 ⟨i₁, hi₁⟩ with h | h | h <;> simp [h] at h₁
  -- col_d_P
  · intro _ _ _ h; simp [emptyPYD] at h
  -- col_d_Q
  · intro j' i₁ i₂ h₁ h₂
    change mkQpaint μQ d i₁ j' = .d at h₁
    change mkQpaint μQ d i₂ j' = .d at h₂
    have ⟨hj', hi₁⟩ := mkQpaint_nondot_imp (show mkQpaint μQ d i₁ j' ≠ .dot by rw [h₁]; exact DRCSymbol.noConfusion)
    have ⟨_, hi₂⟩ := mkQpaint_nondot_imp (show mkQpaint μQ d i₂ j' ≠ .dot by rw [h₂]; exact DRCSymbol.noConfusion)
    subst hj'; rw [mkQpaint_col0 hi₁] at h₁; rw [mkQpaint_col0 hi₂] at h₂
    exact Fin.val_eq_of_eq (d.prop.2.2 ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ h₁ h₂)

/-- Extract Q col 0 as a DSeq from a PBPSet .Bminus ⊥ μQ. -/
private noncomputable def PBPSet_Bminus_bot_to_DSeq {μQ : YoungDiagram}
    (τ : PBPSet .Bminus ⊥ μQ) : DSeq (μQ.colLen 0) :=
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
      rcases hall with h | h | h | h
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact τ.val.mono_Q i.val 0 j.val 0 hij (le_refl 0)
        (by rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr j.isLt)
    · exact Fin.ext (τ.val.col_d_Q 0 i.val j.val hi hj)⟩

/-- Round-trip: extract then reconstruct gives the same PBP (single-column Q). -/
private theorem DSeq_roundtrip_left {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (τ : PBPSet .Bminus ⊥ μQ) :
    DSeq_to_PBP_Bminus hsc (PBPSet_Bminus_bot_to_DSeq τ) = τ := by
  apply Subtype.ext; apply PBP.ext''
  · -- γ: both .Bminus
    unfold DSeq_to_PBP_Bminus; dsimp; exact τ.prop.1.symm
  · -- P: both emptyPYD
    unfold DSeq_to_PBP_Bminus; dsimp
    exact (PYD_eq_emptyPYD_of_shape_bot τ.prop.2.1).symm
  · -- Q: paint agrees
    apply PaintedYoungDiagram.ext'
    · unfold DSeq_to_PBP_Bminus; dsimp; exact τ.prop.2.2.symm
    · ext i j
      unfold DSeq_to_PBP_Bminus PBPSet_Bminus_bot_to_DSeq; dsimp
      simp only [mkQpaint]
      split_ifs with hc
      · rw [hc.1]
      · push_neg at hc
        symm; apply τ.val.Q.paint_outside
        intro hmem; rw [τ.prop.2.2] at hmem
        by_cases hj : j = 0
        · subst hj; exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmem) (not_lt.mpr (hc rfl))
        · exact absurd (singleCol_j0 hsc hmem) hj

/-- Round-trip: reconstruct then extract gives the same DSeq. -/
private theorem DSeq_roundtrip_right {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (d : DSeq (μQ.colLen 0)) :
    PBPSet_Bminus_bot_to_DSeq (DSeq_to_PBP_Bminus hsc d) = d := by
  apply Subtype.ext; funext i
  simp only [PBPSet_Bminus_bot_to_DSeq, DSeq_to_PBP_Bminus, mkQpaint]
  dsimp; simp [i.isLt]

/-- PBPSet .Bminus ⊥ μQ ≃ DSeq (μQ.colLen 0) for single-column Q. -/
private noncomputable def PBPSet_Bminus_bot_equiv_DSeq {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) :
    PBPSet .Bminus ⊥ μQ ≃ DSeq (μQ.colLen 0) where
  toFun := PBPSet_Bminus_bot_to_DSeq
  invFun := DSeq_to_PBP_Bminus hsc
  left_inv := DSeq_roundtrip_left hsc
  right_inv := DSeq_roundtrip_right hsc

/-- card(PBPSet .Bminus ⊥ μQ) = 2 * μQ.colLen 0 + 1 for single-column Q. -/
private theorem card_PBPSet_Bminus_bot_singleCol {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) :
    Fintype.card (PBPSet .Bminus ⊥ μQ) = 2 * (μQ.colLen 0) + 1 := by
  rw [Fintype.card_congr (PBPSet_Bminus_bot_equiv_DSeq hsc)]
  exact DSeq_card _

/-- colLen j = 0 when j ≥ rowLen 0. -/
private lemma colLen_eq_zero_of_ge_rowLen0 (μ : YoungDiagram) (j : ℕ) (hj : j ≥ μ.rowLen 0) :
    μ.colLen j = 0 := by
  by_contra h
  have hpos : 0 < μ.colLen j := by omega
  have hmem : (0, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hpos
  exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega)

/-- For dpartColLensQ_B [r₁] with r₁ > 0: single column, colLen j = 0 for j ≥ 1. -/
private lemma dpartColLensQ_B_singleton_singleCol {r₁ : ℕ} {μQ : YoungDiagram}
    (hQ : μQ.colLens = dpartColLensQ_B [r₁]) (hr : r₁ > 0) :
    ∀ j, j ≥ 1 → μQ.colLen j = 0 := by
  intro j hj
  apply colLen_eq_zero_of_ge_rowLen0
  have hlen := YoungDiagram.length_colLens μQ
  have : dpartColLensQ_B [r₁] = [r₁ / 2] := by simp [dpartColLensQ_B, hr]
  rw [hQ, this] at hlen; simp at hlen; omega

/-- For dpartColLensQ_B [r₁] with r₁ > 0: colLen 0 = r₁/2. -/
private lemma dpartColLensQ_B_singleton_colLen0 {r₁ : ℕ} {μQ : YoungDiagram}
    (hQ : μQ.colLens = dpartColLensQ_B [r₁]) (hr : r₁ > 0) :
    μQ.colLen 0 = r₁ / 2 := by
  have : dpartColLensQ_B [r₁] = [r₁ / 2] := by simp [dpartColLensQ_B, hr]
  exact colLen_0_eq_of_colLens_cons (by rw [hQ, this])

/-- Base case: empty orbit → 1 B⁺ PBP and 1 B⁻ PBP. -/
theorem card_PBPSet_B_empty :
    Fintype.card (PBPSet .Bplus ⊥ ⊥) + Fintype.card (PBPSet .Bminus ⊥ ⊥) =
    tripleSum (countPBP_B []) := by
  simp [card_PBPSet_bot, tripleSum, countPBP_B]

/-- Single row base case. -/
theorem card_PBPSet_B_singleton (r₁ : ℕ) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : Even r₁) (hr : r₁ > 0) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B [r₁]) := by
  -- P = ⊥ since dpartColLensP_B [r₁] = [].
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  -- Use B⁺/B⁻ symmetry: total = 2 × card(B⁻).
  have h_sym := card_Bplus_eq_Bminus (⊥ : YoungDiagram) μQ
  rw [h_sym, ← Nat.two_mul]
  -- Compute the RHS. Since r₁ > 0 and Even r₁, c₁ = r₁/2 ≥ 1.
  have hc₁ : r₁ / 2 ≥ 1 := by
    obtain ⟨m, rfl⟩ := heven; omega
  simp only [countPBP_B, tripleSum, hc₁, ite_true, nu]
  -- Simplify RHS to 2 * (2 * (r₁/2) + 1)
  suffices h : Fintype.card (PBPSet RootType.Bminus ⊥ μQ) = 2 * (r₁ / 2) + 1 by omega
  have hsc := dpartColLensQ_B_singleton_singleCol hQ hr
  rw [card_PBPSet_Bminus_bot_singleCol hsc, dpartColLensQ_B_singleton_colLen0 hQ hr]

/-! ## Double descent B→M→B -/

/-! ### Helper lemmas for B-type double descent -/

/-- For B⁺/B⁻ type: dotScolLen(P) = dotDiag(P).colLen, since P only has {dot, c}
    and c has layerOrd = 3 > 1. So dotSdiag(P) = dotDiag(P). -/
private theorem dotScolLen_P_eq_dotDiag_colLen_B (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) (j : ℕ) :
    PBP.dotScolLen τ.P j = (PBP.dotDiag τ.P τ.mono_P).colLen j := by
  rw [PBP.dotScolLen_eq_dotSdiag_colLen τ.P τ.mono_P]
  congr 1; ext ⟨i, k⟩
  simp only [PBP.dotSdiag, PBP.dotDiag, Finset.mem_filter, YoungDiagram.mem_cells]
  constructor
  · intro ⟨hmem, hlo⟩
    by_cases hd : τ.P.paint i k = .dot
    · exact ⟨hmem, hd⟩
    · exfalso
      have := PBP.P_nonDot_eq_c_of_B τ hγ i k hmem hd
      rw [this, DRCSymbol.layerOrd] at hlo; omega
  · intro ⟨hmem, hd⟩; exact ⟨hmem, by rw [hd]; decide⟩

/-- For B⁺/B⁻: dotScolLen(P, j) ≤ dotScolLen(Q, j).
    Because dotScolLen(P) = dotDiag(P).colLen = dotDiag(Q).colLen ≤ dotSdiag(Q).colLen = dotScolLen(Q). -/
private theorem dotScolLen_P_le_Q_of_B (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) (j : ℕ) :
    PBP.dotScolLen τ.P j ≤ PBP.dotScolLen τ.Q j := by
  rw [dotScolLen_P_eq_dotDiag_colLen_B τ hγ, PBP.dotScolLen_eq_dotSdiag_colLen τ.Q τ.mono_Q]
  -- dotDiag(P).colLen j ≤ dotSdiag(Q).colLen j because dotDiag(P) ⊆ dotSdiag(Q)
  by_contra hlt; push_neg at hlt
  set b := (PBP.dotSdiag τ.Q τ.mono_Q).colLen j
  have hmem : (b, j) ∈ PBP.dotDiag τ.P τ.mono_P := YoungDiagram.mem_iff_lt_colLen.mpr hlt
  simp only [PBP.dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  have ⟨hmemP, hpaint⟩ := hmem
  have ⟨hmemQ, hQpaint⟩ := (τ.dot_match b j).mp ⟨hmemP, hpaint⟩
  have hmemS : (b, j) ∈ PBP.dotSdiag τ.Q τ.mono_Q := by
    rw [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hmemQ, by rw [hQpaint]; decide⟩
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmemS) (by omega)

/-- For B⁺/B⁻: if i < dotScolLen(P, j) then (i,j) ∈ P.shape and P.paint(i,j) = dot. -/
private theorem P_dot_of_lt_dotScolLen_B (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) {i j : ℕ}
    (h : i < PBP.dotScolLen τ.P j) :
    (i, j) ∈ τ.P.shape ∧ τ.P.paint i j = .dot := by
  rw [dotScolLen_P_eq_dotDiag_colLen_B τ hγ] at h
  have hmem : (i, j) ∈ PBP.dotDiag τ.P τ.mono_P := YoungDiagram.mem_iff_lt_colLen.mpr h
  simp only [PBP.dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem

/-- B-type paintL outside P.shape gives dot. -/
private theorem doubleDescent_B_paintL_dot (τ : PBP)
    (_hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i j : ℕ} (h_ge : i ≥ τ.P.shape.colLen (j + 1)) :
    PBP.doubleDescent_B_paintL τ i j = .dot := by
  simp only [PBP.doubleDescent_B_paintL]
  have hds := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  rw [if_neg (by omega)]
  exact τ.P.paint_outside i (j + 1) (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

/-- B-type paintR outside Q.shape gives dot. -/
private theorem doubleDescent_B_paintR_dot (τ : PBP)
    (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus)
    {i j : ℕ} (h_ge : i ≥ τ.Q.shape.colLen (j + 1)) :
    PBP.doubleDescent_B_paintR τ i j = .dot := by
  simp only [PBP.doubleDescent_B_paintR]
  have hdsP := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
  have hdsQ := PBP.dotScolLen_le_colLen τ.Q τ.mono_Q (j + 1)
  have hPQ := dotScolLen_P_le_Q_of_B τ hγ (j + 1)
  rw [if_neg (by omega), if_neg (by omega)]
  exact τ.Q.paint_outside i (j + 1) (by rw [YoungDiagram.mem_iff_lt_colLen]; omega)

/-- The double descent PBP ∇²τ for B type. -/
noncomputable def doubleDescent_B_PBP (τ : PBP) (hγ : τ.γ = .Bplus ∨ τ.γ = .Bminus) : PBP where
  γ := .Bplus  -- B⁺/B⁻ have identical allowed symbols; choose B⁺ as default
  P := {
    shape := τ.P.shape.shiftLeft
    paint := PBP.doubleDescent_B_paintL τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_B_paintL_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  Q := {
    shape := τ.Q.shape.shiftLeft
    paint := PBP.doubleDescent_B_paintR τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_B_paintR_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  sym_P := by
    intro i j hmem
    simp only [PBP.doubleDescent_B_paintL, DRCSymbol.allowed]
    by_cases h : i < PBP.dotScolLen τ.P (j + 1)
    · simp [if_pos h]
    · simp only [if_neg h]
      have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
      have hds := PBP.dotScolLen_le_colLen τ.P τ.mono_P (j + 1)
      -- P.paint(i, j+1) ∈ {dot, c} for B type
      have hP_in_shape : (i, j + 1) ∈ τ.P.shape := hmem'
      have := τ.sym_P i (j + 1) hP_in_shape
      rcases hγ with h₁ | h₁ <;> rw [h₁] at this <;> simp [DRCSymbol.allowed] at this ⊢ <;>
        exact this
  sym_Q := by
    intro i j hmem
    simp only [PBP.doubleDescent_B_paintR, DRCSymbol.allowed]
    by_cases h₁ : i < PBP.dotScolLen τ.P (j + 1)
    · simp [if_pos h₁]
    · simp only [if_neg h₁]
      by_cases h₂ : i < PBP.dotScolLen τ.Q (j + 1)
      · simp [if_pos h₂]
      · simp only [if_neg h₂]
        have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
        have := τ.sym_Q i (j + 1) hmem'
        rcases hγ with h₁ | h₁ <;> rw [h₁] at this <;> simp [DRCSymbol.allowed] at this ⊢ <;>
          exact this
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP, hpaint⟩
      have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
      simp only [PBP.doubleDescent_B_paintL] at hpaint
      by_cases h : i < PBP.dotScolLen τ.P (j + 1)
      · -- dot zone: P.paint(i, j+1) = dot → (i,j+1) ∈ Q.shape by dot_match
        have ⟨_, hpd⟩ := P_dot_of_lt_dotScolLen_B τ hγ h
        have ⟨hmemQ, _⟩ := (τ.dot_match i (j + 1)).mp ⟨hmemP', hpd⟩
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemQ, ?_⟩
        simp [PBP.doubleDescent_B_paintR, if_pos h]
      · -- non-dot zone: P.paint(i, j+1) = dot
        rw [if_neg h] at hpaint
        -- P.paint(i, j+1) = dot but i ≥ dotScolLen(P, j+1)
        -- This means (i, j+1) ∈ P.shape and paint = dot
        have hmemP2 : (i, j + 1) ∈ τ.P.shape := hmemP'
        have ⟨hmemQ, _⟩ := (τ.dot_match i (j + 1)).mp ⟨hmemP2, hpaint⟩
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemQ, ?_⟩
        simp only [PBP.doubleDescent_B_paintR, if_neg h]
        -- Q.paint(i, j+1) = dot by dot_match
        have hQd := ((τ.dot_match i (j + 1)).mp ⟨hmemP2, hpaint⟩).2
        -- need i ≥ dotScolLen(Q, j+1) too, then paintR gives Q.paint = dot
        -- Actually: if P.paint = dot at i ≥ dotScolLen(P), contradiction with
        -- the fact that dotScolLen(P) = dotDiag(P).colLen for B type
        exfalso
        have := PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp h) hmemP2
        exact this hpaint
    · intro ⟨hmemQ, hpaint⟩
      have hmemQ' := YoungDiagram.mem_shiftLeft.mp hmemQ
      simp only [PBP.doubleDescent_B_paintR] at hpaint
      by_cases h : i < PBP.dotScolLen τ.P (j + 1)
      · -- dot zone: Q.paint(i, j+1) = dot → (i,j+1) ∈ P.shape
        have ⟨_, hpd⟩ := P_dot_of_lt_dotScolLen_B τ hγ h
        have hmemP := (τ.dot_match i (j + 1)).mpr
          ⟨hmemQ', ((τ.dot_match i (j + 1)).mp
            ⟨(P_dot_of_lt_dotScolLen_B τ hγ h).1, hpd⟩).2⟩ |>.1
        refine ⟨YoungDiagram.mem_shiftLeft.mpr hmemP, ?_⟩
        simp [PBP.doubleDescent_B_paintL, if_pos h]
      · rw [if_neg h] at hpaint
        by_cases h₂ : i < PBP.dotScolLen τ.Q (j + 1)
        · -- s zone: Q'(i,j) = s ≠ dot, contradiction
          rw [if_pos h₂] at hpaint; exact absurd hpaint (by decide)
        · -- pass-through zone: Q.paint(i, j+1) = dot
          rw [if_neg h₂] at hpaint
          have ⟨hmemP, hpPd⟩ := (τ.dot_match i (j + 1)).mpr ⟨hmemQ', hpaint⟩
          -- But i ≥ dotScolLen(P) and P.paint = dot → contradiction
          exfalso
          exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp h) hmemP hpPd
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_B_paintL]
    by_cases h₁ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · rw [if_neg h₁]
      have hds_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
      rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
          ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hds_anti
      by_cases h₂ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
      · -- impossible: i₁ ≥ dotScolLen(j₁+1) ≥ dotScolLen(j₂+1) > i₂ ≥ i₁
        omega
      · rw [if_neg h₂]
        exact τ.mono_P i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  mono_Q := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_B_paintR]
    by_cases h₁ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · rw [if_neg h₁]
      by_cases h₂ : i₁ < PBP.dotScolLen τ.Q (j₁ + 1)
      · rw [if_pos h₂]
        -- s has layerOrd 1
        have hdsP_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hdsP_anti
        have hdsQ_anti := (PBP.dotSdiag τ.Q τ.mono_Q).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at hdsQ_anti
        -- i₁ ≤ i₂ and dotScolLen(P) is anti-monotone, so i₂ ≥ dotScolLen(P, j₂+1) too
        -- (since i₁ ≥ dotScolLen(P, j₁+1) ≥ dotScolLen(P, j₂+1))
        have h₃ : ¬(i₂ < PBP.dotScolLen τ.P (j₂ + 1)) := by omega
        rw [if_neg h₃]
        by_cases h₄ : i₂ < PBP.dotScolLen τ.Q (j₂ + 1)
        · simp [if_pos h₄, DRCSymbol.layerOrd]
        · rw [if_neg h₄]
          have hlo := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.Q τ.mono_Q
            (Nat.not_lt.mp h₄) hmem'
          simp only [DRCSymbol.layerOrd] at hlo ⊢; omega
      · rw [if_neg h₂]
        have hdsP_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hdsP_anti
        have hdsQ_anti := (PBP.dotSdiag τ.Q τ.mono_Q).colLen_anti (j₁+1) (j₂+1) (by omega)
        rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q,
            ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q] at hdsQ_anti
        have hPQ := dotScolLen_P_le_Q_of_B τ hγ (j₁ + 1)
        have h₃ : ¬(i₂ < PBP.dotScolLen τ.P (j₂ + 1)) := by omega
        rw [if_neg h₃]
        have h₄ : ¬(i₂ < PBP.dotScolLen τ.Q (j₂ + 1)) := by omega
        rw [if_neg h₄]
        exact τ.mono_Q i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: s in P' = doubleDescent_B_paintL. But B-type P has {dot, c}.
      -- paintL gives dot or P.paint (∈ {dot, c}). s ∉ {dot, c}.
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        -- P.paint(i, j₁+1) = s, but P ∈ {dot, c} for B type
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- L,R: s in P' impossible (same as above)
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- R,L: s in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i < PBP.dotScolLen τ.P (j₂ + 1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₂+1) hmem (by rw [h₂]; decide)
        rw [this] at h₂; exact absurd h₂ (by decide)
    · -- Both R: s in Q' comes from doubleDescent_B_paintR
      simp only [PBP.doubleDescent_B_paintR] at h₁ h₂
      -- s comes from zone 2 (dotScolLen(P) ≤ i < dotScolLen(Q)) or zone 3 (Q.paint = s)
      by_cases ha₁ : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁
        by_cases ha₂ : i < PBP.dotScolLen τ.P (j₂ + 1)
        · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg ha₂] at h₂
          by_cases hb₁ : i < PBP.dotScolLen τ.Q (j₁ + 1)
          · rw [if_pos hb₁] at h₁  -- h₁ : s = s
            by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂ + 1)
            · rw [if_pos hb₂] at h₂  -- h₂ : s = s
              -- Both in zone 2: s came from the middle zone, row_s not constraining
              -- Actually row_s says: at most one s per row. But both are from zone 2.
              -- Need to use row_s of τ or argue differently.
              -- In zone 2: paintR = s (synthetic). The original Q.paint at those positions
              -- has layerOrd ≤ 1 (below dotScolLen(Q)) and ≥ dotScolLen(P).
              -- For Q with {dot, s, r, d}: layerOrd ≤ 1 means {dot, s}.
              -- And i ≥ dotScolLen(P, j+1) means P.paint ≠ dot (for B type, layerOrd > 1).
              -- By dot_match: P.paint ≠ dot ↔ Q.paint ≠ dot. So Q.paint = s.
              -- So both Q.paint(i, j₁+1) = s and Q.paint(i, j₂+1) = s.
              -- By row_s of τ on Q side: j₁+1 = j₂+1.
              have hQs₁ : τ.Q.paint i (j₁ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₁)
                have hne : τ.Q.paint i (j₁ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₁+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₁ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  have ⟨_, hpd⟩ := (τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₁)
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).1 hpd
                revert hlo hne; cases τ.Q.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
              have hQs₂ : τ.Q.paint i (j₂ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₂)
                have hne : τ.Q.paint i (j₂ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₂+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₂ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  have ⟨_, hpd⟩ := (τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₂)
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).1 hpd
                revert hlo hne; cases τ.Q.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact hQs₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact hQs₂)
              exact ⟨rfl, by omega⟩
            · rw [if_neg hb₂] at h₂
              -- h₂ : Q.paint(i, j₂+1) = s. Combined with Q zone 2 at j₁.
              -- Q.paint(i, j₁+1) = s (proved above). Q.paint(i, j₂+1) = s (= h₂).
              -- Use row_s of τ.
              have hQs₁ : τ.Q.paint i (j₁ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₁)
                have hne : τ.Q.paint i (j₁ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₁+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₁ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₁)
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).1
                    ((τ.dot_match i (j₁+1)).mpr ⟨hmem, heq⟩).2
                revert hlo hne; cases τ.Q.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact hQs₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
          · rw [if_neg hb₁] at h₁
            by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂ + 1)
            · rw [if_pos hb₂] at h₂
              -- h₁ : Q.paint(i, j₁+1) = s, zone 2 at j₂.
              have hQs₂ : τ.Q.paint i (j₂ + 1) = .s := by
                have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.Q τ.mono_Q
                  (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_Q]; exact hb₂)
                have hne : τ.Q.paint i (j₂ + 1) ≠ .dot := by
                  intro heq
                  have hmem : (i, j₂+1) ∈ τ.Q.shape := YoungDiagram.mem_iff_lt_colLen.mpr
                    (Nat.lt_of_lt_of_le hb₂ (PBP.dotScolLen_le_colLen τ.Q τ.mono_Q _))
                  exact PBP.paint_ne_dot_of_ge_dotScolLen τ.P τ.mono_P (Nat.not_lt.mp ha₂)
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).1
                    ((τ.dot_match i (j₂+1)).mpr ⟨hmem, heq⟩).2
                revert hlo hne; cases τ.Q.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact hQs₂)
              exact ⟨rfl, by omega⟩
            · rw [if_neg hb₂] at h₂
              -- Both in zone 3: Q.paint(i, j₁+1) = s and Q.paint(i, j₂+1) = s
              have := τ.row_s i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .s by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .s by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: r in P' impossible (P ∈ {dot, c} for B type, paintL gives dot or P.paint)
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- L: r in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₁+1) hmem (by rw [h₁]; decide)
        rw [this] at h₁; exact absurd h₁ (by decide)
    · -- R: r in P' impossible
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i < PBP.dotScolLen τ.P (j₂ + 1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout; exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.P_nonDot_eq_c_of_B τ hγ i (j₂+1) hmem (by rw [h₂]; decide)
        rw [this] at h₂; exact absurd h₂ (by decide)
    · -- Both R: r in Q' from doubleDescent_B_paintR
      simp only [PBP.doubleDescent_B_paintR] at h₁ h₂
      by_cases ha₁ : i < PBP.dotScolLen τ.P (j₁+1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁; by_cases hb₁ : i < PBP.dotScolLen τ.Q (j₁+1)
        · rw [if_pos hb₁] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb₁] at h₁
          by_cases ha₂ : i < PBP.dotScolLen τ.P (j₂+1)
          · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
          · rw [if_neg ha₂] at h₂; by_cases hb₂ : i < PBP.dotScolLen τ.Q (j₂+1)
            · rw [if_pos hb₂] at h₂; exact absurd h₂ (by decide)
            · rw [if_neg hb₂] at h₂
              have := τ.row_r i .R .R (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .R i (j₁+1) = .r by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .R i (j₂+1) = .r by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    -- c only from the P.paint branch of paintL
    have hc₁ : τ.P.paint i₁ (j+1) = .c := by
      simp only [PBP.doubleDescent_B_paintL] at h₁
      by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; exact h₁
    have hc₂ : τ.P.paint i₂ (j+1) = .c := by
      simp only [PBP.doubleDescent_B_paintL] at h₂
      by_cases ha : i₂ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; exact h₂
    exact τ.col_c_P (j+1) i₁ i₂ hc₁ hc₂
  col_c_Q := by
    intro j i₁ i₂ h₁ h₂
    -- c in Q' from doubleDescent_B_paintR: can only come from zone 3 (Q.paint)
    -- But Q has {dot, s, r, d} for B type. c ∉ {dot, s, r, d}.
    exfalso
    simp only [PBP.doubleDescent_B_paintR] at h₁
    by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
    · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
    · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.Q (j+1)
      · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg hb] at h₁
        -- h₁ : Q.paint(i₁, j+1) = c. But Q ∈ {dot, s, r, d} for B type.
        have hmem : (i₁, j + 1) ∈ τ.Q.shape := by
          by_contra hout; exact absurd (τ.Q.paint_outside i₁ (j+1) hout) (by rw [h₁]; decide)
        have hsym := τ.sym_Q i₁ (j + 1) hmem
        rcases hγ with hγ' | hγ' <;> rw [hγ'] at hsym <;> simp [DRCSymbol.allowed] at hsym <;>
          rcases hsym with h' | h' | h' | h' <;> rw [h'] at h₁ <;> exact absurd h₁ (by decide)
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    -- d in P' from paintL: P.paint = d. But P ∈ {dot, c} for B type. Impossible.
    simp only [PBP.doubleDescent_B_paintL] at h₁
    by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
    · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
    · rw [if_neg ha] at h₁
      have hmem : (i₁, j + 1) ∈ τ.P.shape := by
        by_contra hout; exact absurd (τ.P.paint_outside i₁ (j+1) hout) (by rw [h₁]; decide)
      have := PBP.P_nonDot_eq_c_of_B τ hγ i₁ (j+1) hmem (by rw [h₁]; decide)
      rw [this] at h₁; exact absurd h₁ (by decide)
  col_d_Q := by
    intro j i₁ i₂ h₁ h₂
    -- d from paintR zone 3: Q.paint(i₁, j+1) = d and Q.paint(i₂, j+1) = d
    have hd₁ : τ.Q.paint i₁ (j+1) = .d := by
      simp only [PBP.doubleDescent_B_paintR] at h₁
      by_cases ha : i₁ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.Q (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hd₂ : τ.Q.paint i₂ (j+1) = .d := by
      simp only [PBP.doubleDescent_B_paintR] at h₂
      by_cases ha : i₂ < PBP.dotScolLen τ.P (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.Q (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_d_Q (j+1) i₁ i₂ hd₁ hd₂

/-- Double descent map for B-type: B→M→B on PBPSet. -/
noncomputable def doubleDescent_B_map (μP μQ : YoungDiagram)
    (τ : PBPSet .Bplus μP μQ ⊕ PBPSet .Bminus μP μQ) :
    PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft) ⊕
    PBPSet .Bminus (μP.shiftLeft) (μQ.shiftLeft) := by
  rcases τ with ⟨τval, hγ, hP, hQ⟩ | ⟨τval, hγ, hP, hQ⟩
  · exact Sum.inl ⟨doubleDescent_B_PBP τval (Or.inl hγ), rfl,
      congrArg YoungDiagram.shiftLeft hP,
      congrArg YoungDiagram.shiftLeft hQ⟩
  · exact Sum.inl ⟨doubleDescent_B_PBP τval (Or.inr hγ), rfl,
      congrArg YoungDiagram.shiftLeft hP,
      congrArg YoungDiagram.shiftLeft hQ⟩

/-! ## Recursive step infrastructure -/

/-- tripleSum(tailCoeffs k).1 = 4k for k ≥ 1. -/
theorem tripleSum_tailCoeffs_fst_eq (k : ℕ) (hk : k ≥ 1) :
    tripleSum (tailCoeffs k).1 = 4 * k := by
  simp only [tripleSum, tailCoeffs, nu]
  split <;> omega

/-- The restricted double descent map B⁺ → B⁺(shiftLeft). -/
noncomputable def doubleDescent_Bplus_map (μP μQ : YoungDiagram)
    (τ : PBPSet .Bplus μP μQ) :
    PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft) :=
  ⟨doubleDescent_B_PBP τ.val (Or.inl τ.prop.1), rfl,
   congrArg YoungDiagram.shiftLeft τ.prop.2.1,
   congrArg YoungDiagram.shiftLeft τ.prop.2.2⟩

/-- Fiber of the B⁺ double descent map. -/
def doubleDescent_Bplus_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) :=
  {τ : PBPSet .Bplus μP μQ // doubleDescent_Bplus_map μP μQ τ = σ}

instance {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) :
    Finite (doubleDescent_Bplus_fiber σ) :=
  Finite.of_injective (fun x => x.val) (fun _ _ h => Subtype.ext h)

noncomputable instance {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) :
    Fintype (doubleDescent_Bplus_fiber σ) :=
  Fintype.ofFinite _

/-- |PBPSet B⁺| = Σ_σ |fiber(σ)|. -/
theorem card_PBPSet_Bplus_eq_sum_fiber {μP μQ : YoungDiagram} :
    Fintype.card (PBPSet .Bplus μP μQ) =
      Finset.sum Finset.univ (fun σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft) =>
        Fintype.card (doubleDescent_Bplus_fiber σ)) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (doubleDescent_Bplus_map μP μQ)).symm

/-! ### Valid column 0 painting for B type

For B type with `r₁ :: r₂ :: rest`:
- P col 0 (height r₂/2): from {•, c}, monotone, at most 1 c
  → All dots, or all dots then 1 c at bottom. 2 choices if height > 0.
- Q col 0 (height r₁/2): from {•, s, r, d}, monotone, at most 1 d
  → dot_match forces: Q(i) = • iff P(i) = • (for i < P.colLen 0)
  → For i ≥ P.colLen 0: Q(i) ∈ {s,r,d} (forced non-dot by dot_match)

Decomposition:
  Case 1 (P all dots): Q tail is DSeq(Q.colLen(0) - P.colLen(0))
  Case 2 (P has c): Q extended tail is DSeq(Q.colLen(0) - P.colLen(0) + 1)

|ValidCol0_B(hP, hQ)| = |DSeq(hQ-hP)| + |DSeq(hQ-hP+1)| = (2(hQ-hP)+1) + (2(hQ-hP)+3) = 4k
where k = hQ - hP + 1.
-/

/-- Valid column 0 paintings for B type.
    Parameterized by the P and Q column 0 heights.
    Sum.inl = P all dots, Q tail is DSeq(hQ-hP).
    Sum.inr = P has c at bottom, Q extended tail is DSeq(hQ-hP+1). -/
private def ValidCol0_B (hP : ℕ) (hQ : ℕ) :=
  DSeq (hQ - hP) ⊕ DSeq (hQ - hP + 1)

private noncomputable instance (hP hQ : ℕ) : Fintype (ValidCol0_B hP hQ) := by
  unfold ValidCol0_B; infer_instance

/-- |ValidCol0_B| = 4k when k = hQ - hP + 1. -/
private theorem validCol0_B_card (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card (ValidCol0_B hP hQ) = 4 * k := by
  simp only [ValidCol0_B, Fintype.card_sum, DSeq_card]
  omega

/-- The top Q symbol of a ValidCol0_B, i.e., the symbol at row μQ.colLen 0 - 1
    of the lifted Q col 0. For inl (P all dots), this is the last DSeq entry
    when the tail is non-empty; otherwise .dot (P extends to the top, forcing
    Q = dot by dot_match). For inr (P has c), this is always the last DSeq entry. -/
private noncomputable def topSym_B (hP hQ : ℕ) (v : ValidCol0_B hP hQ) : DRCSymbol :=
  match v with
  | .inl d =>
    if h : hQ - hP ≥ 1 then d.val ⟨hQ - hP - 1, by omega⟩ else .dot
  | .inr d => d.val ⟨hQ - hP, by omega⟩

/-! ### Extraction map: fiber → ValidCol0_B

For each fiber element τ, extract:
- Whether P col 0 is all dots or has c at bottom (2 choices)
- The Q col 0 tail as a DSeq

Case 1 (P all dots): Q(i,0) = dot for i < hP (by dot_match), non-dot for i ≥ hP.
  The tail Q(hP), Q(hP+1), ..., Q(hQ-1) is a DSeq(hQ - hP).
Case 2 (P has c at bottom): Q(i,0) = dot for i < hP-1, non-dot for i ≥ hP-1.
  The extended tail Q(hP-1), Q(hP), ..., Q(hQ-1) is a DSeq(hQ - hP + 1).
-/

/-- Whether P column 0 has a c at the bottom (true) or is all dots (false). -/
private noncomputable def P_col0_has_c {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) : Prop :=
  μP.colLen 0 > 0 ∧ τ.val.P.paint (μP.colLen 0 - 1) 0 = .c

private noncomputable instance {μP μQ : YoungDiagram} (τ : PBPSet .Bplus μP μQ) :
    Decidable (P_col0_has_c τ) := by
  unfold P_col0_has_c; exact inferInstance

/-- The starting row of the Q col 0 tail (= first non-dot row in Q col 0). -/
private noncomputable def Q_tail_start {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) : ℕ :=
  if P_col0_has_c τ then μP.colLen 0 - 1 else μP.colLen 0

/-- The length of the Q col 0 tail. -/
private noncomputable def Q_tail_len {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0) : ℕ :=
  if P_col0_has_c τ then μQ.colLen 0 - μP.colLen 0 + 1
  else μQ.colLen 0 - μP.colLen 0

/-- P col 0 has only dots and c's, with at most one c at the bottom. -/
private theorem P_col0_dot_below_c {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (i : ℕ) (hi : i < μP.colLen 0)
    (hnotc : ¬P_col0_has_c τ ∨ i < μP.colLen 0 - 1) :
    τ.val.P.paint i 0 = .dot := by
  by_contra hne
  have hmem : (i, 0) ∈ τ.val.P.shape := by
    rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi
  have hc := PBP.P_nonDot_eq_c_of_B τ.val (Or.inl τ.prop.1) i 0 hmem hne
  rcases hnotc with hnotc | hnotc
  · -- ¬P_col0_has_c: P.paint(hP-1,0) ≠ c, but P.paint(i,0) = c
    simp only [P_col0_has_c, not_and_or, not_lt] at hnotc
    rcases hnotc with hnotc | hnotc
    · omega
    · -- P(hP-1,0) ≠ c but P(i,0) = c
      have hmem' : (μP.colLen 0 - 1, 0) ∈ τ.val.P.shape := by
        rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hmono := τ.val.mono_P i 0 (μP.colLen 0 - 1) 0 (by omega) le_rfl hmem'
      rw [hc] at hmono; simp [DRCSymbol.layerOrd] at hmono
      have : τ.val.P.paint (μP.colLen 0 - 1) 0 = .dot ∨
             τ.val.P.paint (μP.colLen 0 - 1) 0 = .c := by
        have hsym := τ.val.sym_P _ _ hmem'
        rw [τ.prop.1] at hsym; simp [DRCSymbol.allowed] at hsym; exact hsym
      rcases this with h | h
      · simp [h, DRCSymbol.layerOrd] at hmono
      · exact hnotc h
  · -- i < hP - 1: c at (i,0) contradicts col_c_P with c at bottom
    have hmem' : (μP.colLen 0 - 1, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hmono := τ.val.mono_P i 0 (μP.colLen 0 - 1) 0 (by omega) le_rfl hmem'
    rw [hc] at hmono; simp [DRCSymbol.layerOrd] at hmono
    have : τ.val.P.paint (μP.colLen 0 - 1) 0 = .dot ∨
           τ.val.P.paint (μP.colLen 0 - 1) 0 = .c := by
      have hsym := τ.val.sym_P _ _ hmem'
      rw [τ.prop.1] at hsym; simp [DRCSymbol.allowed] at hsym; exact hsym
    rcases this with h | h
    · simp [h, DRCSymbol.layerOrd] at hmono
    · exact absurd (τ.val.col_c_P 0 i (μP.colLen 0 - 1) hc h) (by omega)

/-- Q col 0 is dot for rows below the tail start. -/
private theorem Q_col0_dot_below_tail {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (i : ℕ) (hi : i < Q_tail_start τ) :
    τ.val.Q.paint i 0 = .dot := by
  unfold Q_tail_start at hi
  split_ifs at hi with hc
  · -- P has c: tail starts at hP - 1, so i < hP - 1
    have hdot := P_col0_dot_below_c τ i (by omega) (Or.inr hi)
    have hmemP : (i, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    exact ((τ.val.dot_match i 0).mp ⟨hmemP, hdot⟩).2
  · -- P all dots: tail starts at hP
    have hdot := P_col0_dot_below_c τ i hi (Or.inl hc)
    have hmemP : (i, 0) ∈ τ.val.P.shape := by
      rw [τ.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi
    exact ((τ.val.dot_match i 0).mp ⟨hmemP, hdot⟩).2

/-- Q col 0 is non-dot for rows in the tail. -/
private theorem Q_col0_nondot_in_tail {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (i : ℕ) (hi1 : Q_tail_start τ ≤ i) (hi2 : i < μQ.colLen 0) :
    τ.val.Q.paint i 0 ≠ .dot := by
  intro hdot
  have hmemQ : (i, 0) ∈ τ.val.Q.shape := by
    rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi2
  have ⟨hmemP, _⟩ := (τ.val.dot_match i 0).mpr ⟨hmemQ, hdot⟩
  rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen] at hmemP
  unfold Q_tail_start at hi1
  split_ifs at hi1 with hc
  · -- P has c at bottom: tail starts at hP - 1
    have ⟨hpos, hpc⟩ := hc
    have hi_eq : i = μP.colLen 0 - 1 := by omega
    have hpdot := ((τ.val.dot_match i 0).mpr ⟨hmemQ, hdot⟩).2
    rw [hi_eq, hpc] at hpdot; exact DRCSymbol.noConfusion hpdot
  · -- P all dots: tail starts at hP, i ≥ hP, but (i,0) ∈ P.shape → i < hP
    omega

/-- Q col 0 tail symbols are in {s, r, d}. -/
private theorem Q_col0_tail_srd {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (i : ℕ) (hi1 : Q_tail_start τ ≤ i) (hi2 : i < μQ.colLen 0) :
    τ.val.Q.paint i 0 = .s ∨ τ.val.Q.paint i 0 = .r ∨ τ.val.Q.paint i 0 = .d := by
  have hmemQ : (i, 0) ∈ τ.val.Q.shape := by
    rw [τ.prop.2.2]; exact YoungDiagram.mem_iff_lt_colLen.mpr hi2
  have hsym := τ.val.sym_Q i 0 hmemQ
  rw [τ.prop.1] at hsym; simp [DRCSymbol.allowed] at hsym
  have hne := Q_col0_nondot_in_tail τ hle i hi1 hi2
  tauto

/-- Extract the Q col 0 tail as a DSeq from a fiber element.
    The tail length depends on whether P col 0 has c. -/
private noncomputable def extractQtail_B {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (n : ℕ) (hn : n = Q_tail_len τ hle) : DSeq n := by
  have h_start_bound : Q_tail_start τ + n = μQ.colLen 0 := by
    rw [hn]; unfold Q_tail_len Q_tail_start
    split_ifs with hc
    · have := hc.1; omega
    · have := hle; omega
  refine ⟨fun ⟨k, hk⟩ => τ.val.Q.paint (Q_tail_start τ + k) 0, ?_, ?_, ?_⟩
  · intro ⟨k, hk⟩; exact Q_col0_tail_srd τ hle _ (by omega) (by omega)
  · intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ (hle' : k₁ ≤ k₂)
    have hmem : (Q_tail_start τ + k₂, 0) ∈ τ.val.Q.shape := by
      rw [τ.prop.2.2, YoungDiagram.mem_iff_lt_colLen]
      exact by omega
    exact τ.val.mono_Q _ 0 _ 0 (by omega : Q_tail_start τ + k₁ ≤ Q_tail_start τ + k₂) le_rfl hmem
  · intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ hd₁ hd₂
    have h_eq := τ.val.col_d_Q 0 (Q_tail_start τ + k₁) (Q_tail_start τ + k₂) hd₁ hd₂
    exact Fin.ext (show k₁ = k₂ by omega)

/-- Extract column 0 data from a B⁺-fiber element as a ValidCol0_B. -/
private noncomputable def extractCol0_B {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0) :
    ValidCol0_B (μP.colLen 0) (μQ.colLen 0) :=
  if hc : P_col0_has_c τ then
    Sum.inr (extractQtail_B τ hle _ (by simp [Q_tail_len, if_pos hc]))
  else
    Sum.inl (extractQtail_B τ hle _ (by simp [Q_tail_len, if_neg hc]))

/-- extractCol0_B is injective on the fiber over σ.

    Proof outline:
    1. From fiber membership: both τ₁, τ₂ map to σ under doubleDescent_Bplus_map.
    2. By ddescent_B_determines_colsGe1: P and Q agree on columns ≥ 1.
    3. From extractCol0_B equality:
       - Same Sum branch → same P_col0_has_c → same P col 0 painting.
       - Same DSeq → same Q col 0 tail painting.
       - Below-tail Q rows are forced to dots by dot_match.
    4. Assemble: P and Q agree everywhere → τ₁ = τ₂.

    The proof is structurally identical to extractCol0_D_injective_on_fiber
    in Fiber.lean, adapted for B-type's two-column extraction. -/
private theorem extractCol0_B_injective_on_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0) :
    Function.Injective (fun τ : doubleDescent_Bplus_fiber σ =>
      extractCol0_B τ.val hle) := by
  intro ⟨τ₁, hτ₁⟩ ⟨τ₂, hτ₂⟩ h
  have hshapeP : τ₁.val.P.shape = τ₂.val.P.shape := by
    rw [τ₁.prop.2.1, τ₂.prop.2.1]
  have hshapeQ : τ₁.val.Q.shape = τ₂.val.Q.shape := by
    rw [τ₁.prop.2.2, τ₂.prop.2.2]
  have hdd_eq : doubleDescent_B_PBP τ₁.val (Or.inl τ₁.prop.1) =
                doubleDescent_B_PBP τ₂.val (Or.inl τ₂.prop.1) :=
    congrArg Subtype.val (hτ₁.trans hτ₂.symm)
  have hddL : ∀ i j, PBP.doubleDescent_B_paintL τ₁.val i j =
                      PBP.doubleDescent_B_paintL τ₂.val i j := by
    intro i j; exact congr_fun (congr_fun (congrArg (fun d => d.P.paint) hdd_eq) i) j
  have hddR : ∀ i j, PBP.doubleDescent_B_paintR τ₁.val i j =
                      PBP.doubleDescent_B_paintR τ₂.val i j := by
    intro i j; exact congr_fun (congr_fun (congrArg (fun d => d.Q.paint) hdd_eq) i) j
  have ⟨hP_ge1, hQ_ge1⟩ := PBP.ddescent_B_determines_colsGe1 τ₁.val τ₂.val
    (Or.inl τ₁.prop.1) (Or.inl τ₂.prop.1) hshapeP hshapeQ hddL hddR
  -- extractCol0_B encodes: (a) P col 0 c-status via Sum branch, (b) Q col 0 tail via DSeq.
  -- Same extractCol0_B → same (a) and (b) → same col 0 paint.
  -- P col 0: either all dot or dots+c, determined by the Sum branch.
  -- Q col 0: below tail = dot (by dot_match), tail = DSeq data.
  -- Assemble full paint equality → Subtype.ext.
  have hP0 : ∀ i, τ₁.val.P.paint i 0 = τ₂.val.P.paint i 0 := by
    intro i
    by_cases hi : i < μP.colLen 0
    · -- P col 0 agreement via extractCol0_B → same Sum branch → same c-status
      -- First establish same P_col0_has_c
      have hP_c_eq : P_col0_has_c τ₁ ↔ P_col0_has_c τ₂ := by
        simp only [extractCol0_B] at h
        constructor
        · intro hc₁; by_contra hc₂
          simp [dif_pos hc₁, dif_neg hc₂] at h
        · intro hc₂; by_contra hc₁
          simp [dif_neg hc₁, dif_pos hc₂] at h
      -- Case: i is the bottom row and P has c
      by_cases hbot : i = μP.colLen 0 - 1 ∧ μP.colLen 0 > 0
      · rcases hbot with ⟨rfl, hpos⟩
        -- Both have {dot, c} here. Same P_col0_has_c → same paint.
        have hmem₁ : (μP.colLen 0 - 1, 0) ∈ τ₁.val.P.shape := by
          rw [τ₁.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem₂ : (μP.colLen 0 - 1, 0) ∈ τ₂.val.P.shape := by
          rw [τ₂.prop.2.1]; exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hsym₁ := τ₁.val.sym_P _ _ hmem₁
        rw [τ₁.prop.1] at hsym₁; simp [DRCSymbol.allowed] at hsym₁
        have hsym₂ := τ₂.val.sym_P _ _ hmem₂
        rw [τ₂.prop.1] at hsym₂; simp [DRCSymbol.allowed] at hsym₂
        rcases hsym₁ with h₁ | h₁ <;> rcases hsym₂ with h₂ | h₂
        · rw [h₁, h₂]
        · exfalso; exact (hP_c_eq.not.mp (by simp [P_col0_has_c, h₁, hpos]))
            ⟨hpos, h₂⟩
        · exfalso; exact (hP_c_eq.mp ⟨hpos, h₁⟩ |>.2 |> fun hc₂ => by
            rw [h₂] at hc₂; exact DRCSymbol.noConfusion hc₂)
        · rw [h₁, h₂]
      · -- Not bottom row (or hP = 0): both are dots
        have not_bottom : ∀ (τ' : PBPSet .Bplus μP μQ),
            ¬P_col0_has_c τ' ∨ i < μP.colLen 0 - 1 := by
          intro τ'; push_neg at hbot
          by_cases hc : P_col0_has_c τ'
          · exact Or.inr (by rcases hc with ⟨hpos, _⟩; omega)
          · exact Or.inl hc
        rw [P_col0_dot_below_c τ₁ i hi (not_bottom τ₁),
            P_col0_dot_below_c τ₂ i hi (not_bottom τ₂)]
    · -- Outside P shape
      rw [τ₁.val.P.paint_outside i 0 (by rw [τ₁.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega),
          τ₂.val.P.paint_outside i 0 (by rw [τ₂.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; omega)]
  have hQ0 : ∀ i, τ₁.val.Q.paint i 0 = τ₂.val.Q.paint i 0 := by
    intro i
    by_cases hi : i < μQ.colLen 0
    · -- Q col 0 agreement: below tail = both dot, in tail = same DSeq data
      -- First, same P_col0_has_c → same Q_tail_start
      have hP_c_eq : P_col0_has_c τ₁ ↔ P_col0_has_c τ₂ := by
        simp only [extractCol0_B] at h
        constructor
        · intro hc₁; by_contra hc₂; simp [dif_pos hc₁, dif_neg hc₂] at h
        · intro hc₂; by_contra hc₁; simp [dif_neg hc₁, dif_pos hc₂] at h
      have hts_eq : Q_tail_start τ₁ = Q_tail_start τ₂ := by
        unfold Q_tail_start
        split_ifs with h₁ h₂ h₂ <;> try rfl
        · exact absurd (hP_c_eq.mp h₁) h₂
        · exact absurd (hP_c_eq.mpr h₂) h₁
      by_cases htail : Q_tail_start τ₁ ≤ i
      · -- In the tail: same DSeq → same paint
        -- Extract DSeq equality from h
        have h_start_bound₁ : Q_tail_start τ₁ + Q_tail_len τ₁ hle = μQ.colLen 0 := by
          unfold Q_tail_len Q_tail_start
          split_ifs with hc
          · have := hc.1; omega
          · omega
        have hfin : i - Q_tail_start τ₁ < Q_tail_len τ₁ hle := by omega
        -- Extract that the DSeq values agree
        -- Extract DSeq function equality from extractCol0_B equality
        -- Same P_col0_has_c → same Sum branch → same DSeq → same Q.paint on tail
        simp only [extractCol0_B] at h
        -- Split on P_col0_has_c for both τ₁ and τ₂
        -- extractQtail_B stores Q.paint(tail_start + k) for each k.
        -- Same extractCol0_B → same DSeq → function values agree at each index.
        -- At index (i - tail_start), both sides give Q.paint(i, 0).
        by_cases hc₁ : P_col0_has_c τ₁
        · have hc₂ := hP_c_eq.mp hc₁
          rw [dif_pos hc₁, dif_pos hc₂] at h
          have hds := Sum.inr.inj h
          have hv := congrArg Subtype.val hds
          have hfin' : i - Q_tail_start τ₁ < μQ.colLen 0 - μP.colLen 0 + 1 := by
            unfold Q_tail_start; rw [if_pos hc₁]; have := hc₁.1; omega
          -- extractQtail_B with subst: the Subtype val is (fun k => Q.paint(start + k))
          -- but wrapped in a `subst` transport. Use `show` to unwrap.
          have key₁ : (extractQtail_B τ₁ hle _ (by simp [Q_tail_len, if_pos hc₁])).val
              ⟨i - Q_tail_start τ₁, hfin'⟩ =
              τ₁.val.Q.paint i 0 := by
            show τ₁.val.Q.paint (Q_tail_start τ₁ + (i - Q_tail_start τ₁)) 0 = _
            congr 1; omega
          have key₂ : (extractQtail_B τ₂ hle _ (by simp [Q_tail_len, if_pos hc₂])).val
              ⟨i - Q_tail_start τ₁, hfin'⟩ =
              τ₂.val.Q.paint i 0 := by
            show τ₂.val.Q.paint (Q_tail_start τ₂ + (i - Q_tail_start τ₁)) 0 = _
            congr 1; omega
          rw [← key₁, ← key₂]
          exact congr_fun hv ⟨i - Q_tail_start τ₁, hfin'⟩
        · have hc₂ : ¬P_col0_has_c τ₂ := fun h₂ => hc₁ (hP_c_eq.mpr h₂)
          rw [dif_neg hc₁, dif_neg hc₂] at h
          have hds := Sum.inl.inj h
          have hv := congrArg Subtype.val hds
          have hfin' : i - Q_tail_start τ₁ < μQ.colLen 0 - μP.colLen 0 := by
            unfold Q_tail_start at htail ⊢; rw [if_neg hc₁] at htail ⊢; omega
          have key₁ : (extractQtail_B τ₁ hle _ (by simp [Q_tail_len, if_neg hc₁])).val
              ⟨i - Q_tail_start τ₁, hfin'⟩ =
              τ₁.val.Q.paint i 0 := by
            show τ₁.val.Q.paint (Q_tail_start τ₁ + (i - Q_tail_start τ₁)) 0 = _
            congr 1; omega
          have key₂ : (extractQtail_B τ₂ hle _ (by simp [Q_tail_len, if_neg hc₂])).val
              ⟨i - Q_tail_start τ₁, hfin'⟩ =
              τ₂.val.Q.paint i 0 := by
            show τ₂.val.Q.paint (Q_tail_start τ₂ + (i - Q_tail_start τ₁)) 0 = _
            congr 1; omega
          rw [← key₁, ← key₂]
          exact congr_fun hv ⟨i - Q_tail_start τ₁, hfin'⟩
      · -- Below tail: both are dots
        push_neg at htail
        rw [Q_col0_dot_below_tail τ₁ i htail,
            Q_col0_dot_below_tail τ₂ i (by omega)]
    · -- Outside Q shape
      rw [τ₁.val.Q.paint_outside i 0 (by rw [τ₁.prop.2.2, YoungDiagram.mem_iff_lt_colLen]; omega),
          τ₂.val.Q.paint_outside i 0 (by rw [τ₂.prop.2.2, YoungDiagram.mem_iff_lt_colLen]; omega)]
  have hPeq : τ₁.val.P = τ₂.val.P := PaintedYoungDiagram.ext' hshapeP (by
    ext i j; cases j with
    | zero => exact hP0 i
    | succ j => exact hP_ge1 i (j + 1) (by omega))
  have hQeq : τ₁.val.Q = τ₂.val.Q := PaintedYoungDiagram.ext' hshapeQ (by
    ext i j; cases j with
    | zero => exact hQ0 i
    | succ j => exact hQ_ge1 i (j + 1) (by omega))
  exact Subtype.ext (Subtype.ext (PBP.ext'' (by rw [τ₁.prop.1, τ₂.prop.1]) hPeq hQeq))

/-! ### Fiber cardinality for B-type primitive step

In the primitive case, the fiber of each sub-PBP has uniform size 4k.
The proof uses a sandwich argument:
  fiber ↪ ValidCol0_B (extraction of col 0 paintings)
  ValidCol0_B ↪ fiber (lift construction, valid in primitive case)
-/

/-- Upper bound: |fiber| ≤ |ValidCol0_B|.
    Proof: extract col 0 of P and Q from a fiber element. The extraction map
    is injective because ∇² determines cols ≥ 1 (ddescent_B_determines_colsGe1)
    and the ValidCol0_B encoding determines col 0. -/
private theorem fiber_le_validCol0_B {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0) :
    Fintype.card (doubleDescent_Bplus_fiber σ) ≤
    Fintype.card (ValidCol0_B (μP.colLen 0) (μQ.colLen 0)) := by
  exact Fintype.card_le_of_injective _ (extractCol0_B_injective_on_fiber σ hle)

/-! ### B-type lift construction

Given σ : PBPSet .Bplus (shiftLeft μP) (shiftLeft μQ) and v : ValidCol0_B,
construct a PBP τ : PBPSet .Bplus μP μQ such that doubleDescent_Bplus_map τ = σ.

The lift uses the simple column shift (same as liftPaint_D for D-type):
  τ.P.paint(i, 0) = col0P(i),  τ.P.paint(i, j+1) = σ.P.paint(i, j)
  τ.Q.paint(i, 0) = col0Q(i),  τ.Q.paint(i, j+1) = σ.Q.paint(i, j)

The round-trip works because for B type, σ's dotScolLen zones are self-consistent:
  σ.P below dotScolLen is .dot (B-type P ∈ {dot, c})
  σ.Q below dotScolLen(P) is .dot (by dot_match + P dots)
  σ.Q in [dotScolLen(P), dotScolLen(Q)) is .s (layerOrd ≤ 1, non-dot)
-/

/-- P column 0 paint from ValidCol0_B.
    inl _: all dots.  inr _: dots + c at bottom (row hP - 1). -/
private def liftCol0P_B (hP : ℕ) (v : ValidCol0_B hP hQ) : ℕ → DRCSymbol :=
  fun i => match v with
  | .inl _ => .dot
  | .inr _ => if i = hP - 1 ∧ hP > 0 then .c else .dot

/-- Q column 0 paint from ValidCol0_B.
    inl d: dots for i < hP, then DSeq(hQ-hP) for i ∈ [hP, hQ).
    inr d: dots for i < hP-1, then DSeq(hQ-hP+1) for i ∈ [hP-1, hQ). -/
private def liftCol0Q_B (hP hQ : ℕ) (v : ValidCol0_B hP hQ) : ℕ → DRCSymbol :=
  fun i => match v with
  | .inl d =>
    if h : hP ≤ i ∧ i < hQ then d.val ⟨i - hP, by omega⟩ else .dot
  | .inr d =>
    if h : hP - 1 ≤ i ∧ i < hQ ∧ hP > 0 then d.val ⟨i - (hP - 1), by omega⟩ else .dot

/-- Lift P paint: column 0 from v, columns ≥ 1 from σ.P (simple column shift). -/
private def liftPaint_B_P (σ : PBP) (hP : ℕ) {hQ : ℕ} (v : ValidCol0_B hP hQ) :
    ℕ → ℕ → DRCSymbol :=
  fun i j => match j with
  | 0 => liftCol0P_B hP v i
  | j + 1 => σ.P.paint i j

/-- Lift Q paint: column 0 from v, columns ≥ 1 from σ.Q (simple column shift). -/
private def liftPaint_B_Q (σ : PBP) (hP hQ : ℕ) (v : ValidCol0_B hP hQ) :
    ℕ → ℕ → DRCSymbol :=
  fun i j => match j with
  | 0 => liftCol0Q_B hP hQ v i
  | j + 1 => σ.Q.paint i j

/-- The B-type lift construction: from σ and v, produce a valid PBP with shapes μP, μQ.

    Construction: P col 0 from v (all dots or dots + c at bottom),
    Q col 0 from v (dots then DSeq tail), cols ≥ 1 from σ.

    13 PBP constraints verified per blueprint Section 1.5:
    - sym_P, sym_Q: by construction (P ∈ {dot, c}, Q ∈ {dot, s, r, d})
    - dot_match: dot regions match by construction
    - mono_P: col 0 dot/c monotone; col0→col1 needs primitive condition (vacuous)
    - mono_Q: col 0 DSeq monotone; col0→col1 needs primitive condition (vacuous)
    - row_s, row_r: no s/r in P; Q col 0 vs cols ≥ 1 disjoint in primitive case
    - col_c_P: at most one c in col 0; cols ≥ 1 from σ
    - col_c_Q: DSeq has no c
    - col_d_P: P has no d
    - col_d_Q: DSeq has at most one d; cols ≥ 1 from σ

    All 13 PBP constraints verified. Requires primitive conditions (hprimP, hprimQ). -/
private noncomputable def liftPBP_B {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    PBPSet .Bplus μP μQ := by
  have hpoP : ∀ i j, (i, j) ∉ μP → liftPaint_B_P σ.val (μP.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero =>
      simp only [liftPaint_B_P, liftCol0P_B]
      cases v with
      | inl _ => rfl
      | inr _ =>
        split_ifs with hc
        · exfalso; apply hmem; rw [YoungDiagram.mem_iff_lt_colLen]; omega
        · rfl
    | succ j =>
      simp only [liftPaint_B_P]
      exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  have hpoQ : ∀ i j, (i, j) ∉ μQ → liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero =>
      have hi : ¬(i < μQ.colLen 0) := by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega
      unfold liftPaint_B_Q liftCol0Q_B
      cases v with
      | inl _ => simp; intro hp hq; omega
      | inr _ => simp; intro hp hq; omega
    | succ j =>
      simp only [liftPaint_B_Q]
      exact σ.val.Q.paint_outside i j (by
        rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft]; exact hmem)
  refine ⟨⟨.Bplus,
    ⟨μP, liftPaint_B_P σ.val (μP.colLen 0) v, hpoP⟩,
    ⟨μQ, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v, hpoQ⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P =>
    intro i j hmem
    show (liftPaint_B_P σ.val (μP.colLen 0) v i j).allowed .Bplus .L
    cases j with
    | zero =>
      simp only [liftPaint_B_P, liftCol0P_B]
      cases v with
      | inl _ => simp [DRCSymbol.allowed]
      | inr _ => split_ifs <;> simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_P]
      have := σ.val.sym_P i j (by rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
      rw [σ.prop.1] at this; exact this
  case sym_Q =>
    intro i j hmem
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j).allowed .Bplus .R
    cases j with
    | zero =>
      unfold liftPaint_B_Q liftCol0Q_B
      cases v with
      | inl d =>
        simp only
        split_ifs with hc
        · simp [DRCSymbol.allowed]
          rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h]
        · simp [DRCSymbol.allowed]
      | inr d =>
        simp only
        split_ifs with hc
        · simp [DRCSymbol.allowed]
          rcases d.prop.1 ⟨i - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h]
        · simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_Q]
      have := σ.val.sym_Q i j (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
      rw [σ.prop.1] at this; exact this
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        have hi : i < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        cases v with
        | inl d =>
          -- P(i,0) = dot always; Q(i,0) = dot because i < hP
          constructor
          · exact YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hi hle)
          · change liftCol0Q_B _ _ (.inl d) i = .dot
            simp only [liftCol0Q_B]; exact dif_neg (by omega)
        | inr d =>
          -- P(i,0) = dot requires ¬(i = hP-1 ∧ hP > 0)
          simp only [liftPaint_B_P, liftCol0P_B] at hpaint
          split_ifs at hpaint with hc
          -- neg branch only (pos closes by .c ≠ .dot)
          push_neg at hc
          -- i ≠ hP-1 (by hc + hP_pos), so i < hP-1, so Q(i,0) = dot
          refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hi hle), ?_⟩
          change liftCol0Q_B _ _ (.inr d) i = .dot
          simp only [liftCol0Q_B]
          exact dif_neg (by push_neg; intro h1 h2; exact absurd hP_pos (not_lt.mpr (hc (by omega))))
      | succ j =>
        simp only [liftPaint_B_P] at hpaint
        have hmemP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemQ, hQdot⟩ := (σ.val.dot_match i j).mp ⟨hmemP, hpaint⟩
        exact ⟨by rw [σ.prop.2.2] at hmemQ; exact YoungDiagram.mem_shiftLeft.mp hmemQ,
               by simp only [liftPaint_B_Q]; exact hQdot⟩
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        unfold liftPaint_B_Q liftCol0Q_B at hpaint
        have hi : i < μQ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        cases v with
        | inl d =>
          dsimp at hpaint
          split_ifs at hpaint with hc
          · rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at hpaint
          · have hiP : i < μP.colLen 0 := by omega
            exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hiP,
                   by unfold liftPaint_B_P liftCol0P_B; dsimp⟩
        | inr d =>
          dsimp at hpaint
          split_ifs at hpaint with hc
          · rcases d.prop.1 ⟨i - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h] at hpaint
          · have hiP : i < μP.colLen 0 := by
              simp only [not_and, not_lt] at hc
              by_contra hge; push_neg at hge; exact absurd (hc (by omega) hi) (by omega)
            refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr hiP, ?_⟩
            unfold liftPaint_B_P liftCol0P_B; dsimp
            split_ifs with h1
            · exfalso; simp only [not_and, not_lt] at hc; exact absurd (hc (by omega) hi) (by omega)
            · rfl
      | succ j =>
        simp only [liftPaint_B_Q] at hpaint
        have hmemQ : (i, j) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemP, hPdot⟩ := (σ.val.dot_match i j).mpr ⟨hmemQ, hpaint⟩
        exact ⟨by rw [σ.prop.2.1] at hmemP; exact YoungDiagram.mem_shiftLeft.mp hmemP,
               by simp only [liftPaint_B_P]; exact hPdot⟩
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_P σ.val (μP.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_P σ.val (μP.colLen 0) v i₂ j₂).layerOrd
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero =>
        -- col 0 vs col 0: dot (0) or c (3) at bottom; monotone since i₁ ≤ i₂
        simp only [liftPaint_B_P, liftCol0P_B]
        cases v with
        | inl _ => simp [DRCSymbol.layerOrd]
        | inr _ =>
          split_ifs with hc1 hc2
          · simp [DRCSymbol.layerOrd]
          · -- i₁ = hP-1, paint(i₁) = c, paint(i₂) = dot. But i₂ ≥ i₁ = hP-1 and i₂ < hP.
            -- So i₂ = hP-1, contradicting hc2.
            exfalso
            have hi₂ : i₂ < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
            exact hc2 ⟨by omega, hc1.2⟩
          · simp [DRCSymbol.layerOrd]  -- dot ≤ c
          · simp [DRCSymbol.layerOrd]
      | succ j₂ =>
        -- col 0 vs col ≥ 1: paint(i₁, 0) vs σ.P.paint(i₂, j₂)
        simp only [liftPaint_B_P, liftCol0P_B]
        cases v with
        | inl _ => simp [DRCSymbol.layerOrd]
        | inr _ =>
          split_ifs with hc
          · -- i₁ = hP-1, paint = c (layerOrd 3). But (i₂, j₂+1) ∈ μP with
            -- i₂ ≥ hP-1 and μP.colLen(j₂+1) < hP gives hP-1 < μP.colLen(j₂+1) < hP. Impossible.
            exfalso
            have h₂mem : i₂ < μP.colLen (j₂ + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
            have := hprimP (j₂ + 1) (by omega)
            omega
          · simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega  -- j₁+1 ≤ 0 is impossible
      | succ j₂ =>
        -- both cols ≥ 1: from σ.mono_P
        simp only [liftPaint_B_P]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case mono_Q =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ j₂).layerOrd
    have hi₂ : i₂ < μQ.colLen j₂ := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero =>
        -- col 0 vs col 0: dot region then DSeq tail. DSeq monotone.
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (liftCol0Q_B _ _ v i₂).layerOrd
        unfold liftCol0Q_B; cases v with
        | inl d =>
          simp only
          by_cases hc1 : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
          · have hb1 : i₁ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right hc1.1 hc1.2
            have hb2 : i₂ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right (by omega) hi₂
            rw [dif_pos hc1, dif_pos ⟨by omega, hi₂⟩]
            exact d.prop.2.1 ⟨_, hb1⟩ ⟨_, hb2⟩ (by simp; omega)
          · rw [dif_neg hc1]; simp [DRCSymbol.layerOrd]
        | inr d =>
          simp only
          by_cases hc1 : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
          · have hb1 : i₁ - (μP.colLen 0 - 1) < μQ.colLen 0 - μP.colLen 0 + 1 := by omega
            have hb2 : i₂ - (μP.colLen 0 - 1) < μQ.colLen 0 - μP.colLen 0 + 1 := by omega
            rw [dif_pos hc1, dif_pos ⟨by omega, hi₂, hc1.2.2⟩]
            exact d.prop.2.1 ⟨_, hb1⟩ ⟨_, hb2⟩ (by simp; omega)
          · rw [dif_neg hc1]; simp [DRCSymbol.layerOrd]
      | succ j₂ =>
        -- col 0 vs col ≥ 1. Non-dot Q(i₁,0) implies i₁ in tail region, but (i₂,j₂+1)∈μQ
        -- means i₂ < μQ.colLen(j₂+1) ≤ hP-1 (by hprimQ). i₂ ≥ i₁ contradicts.
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (σ.val.Q.paint i₂ j₂).layerOrd
        unfold liftCol0Q_B; cases v with
        | inl d =>
          simp only
          by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
          · exfalso; have := hprimQ (j₂ + 1) (by omega); omega
          · rw [dif_neg hc]; simp [DRCSymbol.layerOrd]
        | inr d =>
          simp only
          by_cases hc : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
          · exfalso; have := hprimQ (j₂ + 1) (by omega); omega
          · rw [dif_neg hc]; simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [liftPaint_B_Q]
        exact σ.val.mono_Q i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case row_s =>
    -- P ∈ {dot, c} for B+ type → P has no s. So s can only appear on Q side.
    -- Helper: P paint is never s
    have hP_no_s : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .s := by
      intro i j; cases j with
      | zero =>
        simp only [liftPaint_B_P]; unfold liftCol0P_B; cases v with
        | inl _ => simp
        | inr _ => split_ifs <;> simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    -- Eliminate L (P) cases using hP_no_s
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₂ (hP_no_s i j₂)
    · -- Both R (Q): Q col 0 non-dot rows don't overlap with cols ≥ 1
      -- Helper: Q col 0 non-dot means i ≥ hP - 1
      -- Helper: Q col 0 non-dot implies in tail region
      have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 - 1 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        cases v with
        | inl d => simp only at hne; split_ifs at hne with hc <;> first | omega | exact absurd rfl hne
        | inr d => simp only at hne; split_ifs at hne with hc <;> first | exact hc.1 | exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have := hprimQ (j₂ + 1) (by omega); omega
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have := hprimQ (j₁ + 1) (by omega); omega
        | succ j₂ =>
          have := σ.val.row_s i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .s by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .s by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case row_r =>
    -- Same as row_s but for r. P has no r.
    have hP_no_r : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .r := by
      intro i j; cases j with
      | zero =>
        simp only [liftPaint_B_P]; unfold liftCol0P_B; cases v with
        | inl _ => simp
        | inr _ => split_ifs <;> simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₂ (hP_no_r i j₂)
    · have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 - 1 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        cases v with
        | inl d => simp only at hne; split_ifs at hne with hc <;> first | omega | exact absurd rfl hne
        | inr d => simp only at hne; split_ifs at hne with hc <;> first | exact hc.1 | exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have := hprimQ (j₂ + 1) (by omega); omega
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have := hprimQ (j₁ + 1) (by omega); omega
        | succ j₂ =>
          have := σ.val.row_r i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .r by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .r by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    show i₁ = i₂
    simp only [liftPaint_B_P] at h₁ h₂
    cases j with
    | zero =>
      -- col 0: only inr case can produce c, and only at row hP-1
      cases v with
      | inl _ => simp [liftCol0P_B] at h₁
      | inr _ =>
        simp only [liftCol0P_B] at h₁ h₂
        split_ifs at h₁ with h1
        split_ifs at h₂ with h2
        omega
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      -- Q col 0 uses DSeq values in {s,r,d} or dot; no c possible
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .c at h₁
      simp only [liftPaint_B_Q] at h₁
      cases v with
      | inl d =>
        simp only [liftCol0Q_B] at h₁
        split_ifs at h₁ with hc
        rcases d.prop.1 ⟨i₁ - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at h₁
      | inr d =>
        simp only [liftCol0Q_B] at h₁
        split_ifs at h₁ with hc
        rcases d.prop.1 ⟨i₁ - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h] at h₁
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_c_Q j i₁ i₂ h₁ h₂
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      -- P col 0 only has dot or c, no d possible
      change liftPaint_B_P σ.val (μP.colLen 0) v i₁ 0 = .d at h₁
      simp only [liftPaint_B_P] at h₁
      cases v with
      | inl _ => exact absurd (show (DRCSymbol.dot : DRCSymbol) = .d from h₁) (by decide)
      | inr _ => simp only [liftCol0P_B] at h₁; split_ifs at h₁
    | succ j =>
      simp only [liftPaint_B_P] at h₁ h₂
      exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .d at h₁
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ 0 = .d at h₂
      simp only [liftPaint_B_Q] at h₁ h₂
      cases v with
      | inl d =>
        simp only [liftCol0Q_B] at h₁ h₂
        split_ifs at h₁ with hc₁
        split_ifs at h₂ with hc₂
        have heq := d.prop.2.2 ⟨i₁ - μP.colLen 0, by omega⟩ ⟨i₂ - μP.colLen 0, by omega⟩ h₁ h₂
        have := congr_arg Fin.val heq; simp at this; omega
      | inr d =>
        simp only [liftCol0Q_B] at h₁ h₂
        split_ifs at h₁ with hc₁
        split_ifs at h₂ with hc₂
        have heq := d.prop.2.2 ⟨i₁ - (μP.colLen 0 - 1), by omega⟩ ⟨i₂ - (μP.colLen 0 - 1), by omega⟩ h₁ h₂
        have := congr_arg Fin.val heq; simp at this; omega
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_d_Q j i₁ i₂ h₁ h₂

/-- Round-trip: doubleDescent_Bplus_map (liftPBP_B σ v) = σ.
    For B-type P ∈ {dot, c}, dotScolLen only counts dots (layerOrd(c) = 3 > 1).
    So dotScolLen(liftedP, j+1) = dotScolLen(σ.P, j) and the paint shifts cancel. -/
private theorem liftPBP_B_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    doubleDescent_Bplus_map μP μQ (liftPBP_B σ v hle hP_pos hprimP hprimQ) = σ := by
  set τ := liftPBP_B σ v hle hP_pos hprimP hprimQ
  apply Subtype.ext
  apply PBP_eq_of_data
  · -- γ: doubleDescent_B_PBP sets γ = Bplus, σ.prop.1 says σ.val.γ = Bplus
    simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]; exact σ.prop.1.symm
  · -- P equality
    apply PaintedYoungDiagram.ext'
    · -- P shape: shiftLeft of lifted P shape = σ P shape
      simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.1]; rfl
    · -- P paint: doubleDescent_B_paintL(lifted)(i,j) = σ.P.paint(i,j)
      funext i j
      show PBP.doubleDescent_B_paintL τ.val i j = σ.val.P.paint i j
      simp only [PBP.doubleDescent_B_paintL]
      by_cases hds : i < PBP.dotScolLen τ.val.P (j + 1)
      · -- In dotScolLen zone: lifted P paint has layerOrd ≤ 1, so it's dot (B-type)
        rw [if_pos hds]
        -- τ.val.P.paint(i, j+1) has layerOrd ≤ 1
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hds)
        -- τ.val.P.paint(i, j+1) = liftPaint_B_P σ.val ... i (j+1) = σ.val.P.paint i j
        have hpaint : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        rw [hpaint] at hlo
        -- σ is B+ type, so σ.P symbols ∈ {dot, c}. layerOrd(dot)=0, layerOrd(c)=3.
        -- layerOrd ≤ 1 forces dot.
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σ : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσ_sym := σ.val.sym_P i j hmem_σ
        rw [σ.prop.1] at hσ_sym
        simp only [DRCSymbol.allowed] at hσ_sym
        rcases hσ_sym with h | h <;> rw [h] at hlo ⊢ <;>
          simp [DRCSymbol.layerOrd] at hlo ⊢
      · -- Outside dotScolLen: result is τ.val.P.paint(i, j+1) = σ.val.P.paint(i,j)
        rw [if_neg hds]; rfl
  · -- Q equality
    apply PaintedYoungDiagram.ext'
    · -- Q shape
      simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.2]; rfl
    · -- Q paint: doubleDescent_B_paintR(lifted)(i,j) = σ.Q.paint(i,j)
      funext i j
      show PBP.doubleDescent_B_paintR τ.val i j = σ.val.Q.paint i j
      simp only [PBP.doubleDescent_B_paintR]
      by_cases hdsP : i < PBP.dotScolLen τ.val.P (j + 1)
      · -- dot zone of P: result is .dot, need σ.Q.paint = .dot
        rw [if_pos hdsP]
        have hpaintP : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsP)
        rw [hpaintP] at hlo
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσP_sym := σ.val.sym_P i j hmem_σP
        rw [σ.prop.1] at hσP_sym
        simp only [DRCSymbol.allowed] at hσP_sym
        have hσP_dot : σ.val.P.paint i j = .dot := by
          rcases hσP_sym with h | h <;> rw [h] at hlo <;>
            simp [DRCSymbol.layerOrd] at hlo ⊢ <;> exact h
        have ⟨_, hQd⟩ := (σ.val.dot_match i j).mp ⟨hmem_σP, hσP_dot⟩
        exact hQd.symm
      · rw [if_neg hdsP]
        by_cases hdsQ : i < PBP.dotScolLen τ.val.Q (j + 1)
        · -- s zone: dotScolLen(P) ≤ i < dotScolLen(Q). Result is .s, need σ.Q.paint = .s
          rw [if_pos hdsQ]
          have hpaintQ : τ.val.Q.paint i (j + 1) = σ.val.Q.paint i j := rfl
          have hloQ := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.Q τ.val.mono_Q
            (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsQ)
          rw [hpaintQ] at hloQ
          have hmemQ : (i, j + 1) ∈ τ.val.Q.shape := by
            have := PBP.dotScolLen_le_colLen τ.val.Q τ.val.mono_Q (j + 1)
            exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
          have hmem_σQ : (i, j) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
            exact YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have hQ_ne_dot : σ.val.Q.paint i j ≠ .dot := by
            intro hQd
            have ⟨hmemP, hPd⟩ := (σ.val.dot_match i j).mpr ⟨hmem_σQ, hQd⟩
            have hlo_σP : (σ.val.P.paint i j).layerOrd ≤ 1 := by rw [hPd]; decide
            have hP_in_shape : (i, j + 1) ∈ τ.val.P.shape := by
              have : i < σ.val.P.shape.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hmemP
              rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft] at this
              exact YoungDiagram.mem_iff_lt_colLen.mpr this
            have hlo_τP : (τ.val.P.paint i (j + 1)).layerOrd ≤ 1 := hlo_σP
            have h_in_dsdiag : (i, j + 1) ∈ PBP.dotSdiag τ.val.P τ.val.mono_P := by
              simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
                YoungDiagram.mem_cells]
              exact ⟨hP_in_shape, hlo_τP⟩
            have := YoungDiagram.mem_iff_lt_colLen.mp h_in_dsdiag
            rw [← PBP.dotScolLen_eq_dotSdiag_colLen] at this
            exact hdsP this
          have hσQ_sym := σ.val.sym_Q i j hmem_σQ
          rw [σ.prop.1] at hσQ_sym
          simp only [DRCSymbol.allowed] at hσQ_sym
          rcases hσQ_sym with h | h | h | h <;> rw [h] at hloQ hQ_ne_dot ⊢ <;>
            simp [DRCSymbol.layerOrd] at hloQ hQ_ne_dot ⊢
        · -- Pass-through zone: result is τ.Q.paint(i,j+1) = σ.Q.paint(i,j)
          rw [if_neg hdsQ]; rfl

/-- liftPBP_B is injective: different v give different PBPs.
    The P and Q column 0 paints are determined by v, so equal PBPs imply equal v. -/
private theorem liftPBP_B_injective {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    Function.Injective (fun v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) =>
      liftPBP_B σ v hle hP_pos hprimP hprimQ) := by
  intro v₁ v₂ h
  -- h : liftPBP_B σ v₁ = liftPBP_B σ v₂ (as PBPSet elements)
  have hval : (liftPBP_B σ v₁ hle hP_pos hprimP hprimQ).val =
              (liftPBP_B σ v₂ hle hP_pos hprimP hprimQ).val :=
    congrArg Subtype.val h
  -- Extract PBP equality (PBPSet.val : PBP)
  have hPBP : (liftPBP_B σ v₁ hle hP_pos hprimP hprimQ).val =
              (liftPBP_B σ v₂ hle hP_pos hprimP hprimQ).val := hval
  -- P.paint and Q.paint agree at all (i, 0)
  have hPeq : ∀ i, liftPaint_B_P σ.val (μP.colLen 0) v₁ i 0 =
                    liftPaint_B_P σ.val (μP.colLen 0) v₂ i 0 := by
    intro i
    exact congr_fun (congr_fun (congrArg (fun d => d.P.paint) hPBP) i) 0
  have hQeq : ∀ i, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v₁ i 0 =
                    liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v₂ i 0 := by
    intro i
    exact congr_fun (congr_fun (congrArg (fun d => d.Q.paint) hPBP) i) 0
  -- P col 0 determines the Sum branch (inl vs inr)
  simp only [liftPaint_B_P, liftCol0P_B] at hPeq
  -- Q col 0 determines the DSeq within that branch
  simp only [liftPaint_B_Q, liftCol0Q_B] at hQeq
  -- Case split on v₁ and v₂
  match v₁, v₂ with
  | .inl d₁, .inl d₂ =>
    -- Both P all dots. DSeq from Q determines v.
    congr 1; apply Subtype.ext; funext ⟨k, hk⟩
    have hq := hQeq (μP.colLen 0 + k)
    have hlt : μP.colLen 0 + k < μQ.colLen 0 := by omega
    simp only [dif_pos (show μP.colLen 0 ≤ μP.colLen 0 + k ∧ μP.colLen 0 + k < μQ.colLen 0
      from ⟨by omega, hlt⟩)] at hq
    have hfin : (⟨μP.colLen 0 + k - μP.colLen 0, by omega⟩ : Fin _) = ⟨k, hk⟩ :=
      Fin.ext (by simp)
    rw [hfin] at hq; exact hq
  | .inr d₁, .inr d₂ =>
    -- Both P have c. DSeq from Q determines v.
    congr 1; apply Subtype.ext; funext ⟨k, hk⟩
    have hq := hQeq (μP.colLen 0 - 1 + k)
    have hlt : μP.colLen 0 - 1 + k < μQ.colLen 0 := by omega
    simp only [dif_pos (show μP.colLen 0 - 1 ≤ μP.colLen 0 - 1 + k ∧
      μP.colLen 0 - 1 + k < μQ.colLen 0 ∧ μP.colLen 0 > 0
      from ⟨by omega, hlt, hP_pos⟩)] at hq
    have hfin : (⟨μP.colLen 0 - 1 + k - (μP.colLen 0 - 1), by omega⟩ : Fin _) = ⟨k, hk⟩ :=
      Fin.ext (by simp)
    rw [hfin] at hq; exact hq
  | .inl _, .inr _ =>
    -- v₁ is inl (P all dots), v₂ is inr (P has c). P paints differ.
    exfalso
    have hp := hPeq (μP.colLen 0 - 1)
    simp only [show (μP.colLen 0 - 1 = μP.colLen 0 - 1 ∧ μP.colLen 0 > 0) from
      ⟨rfl, hP_pos⟩, ite_true] at hp
    exact DRCSymbol.noConfusion hp
  | .inr _, .inl _ =>
    -- v₁ is inr (P has c), v₂ is inl (P all dots). P paints differ.
    exfalso
    have hp := hPeq (μP.colLen 0 - 1)
    simp only [show (μP.colLen 0 - 1 = μP.colLen 0 - 1 ∧ μP.colLen 0 > 0) from
      ⟨rfl, hP_pos⟩, ite_true] at hp
    exact DRCSymbol.noConfusion hp.symm

/-- Lower bound: |ValidCol0_B| ≤ |fiber|, via the lift injection.
    Requires primitive case conditions to construct valid lifts. -/
private theorem validCol0_B_le_fiber' {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    Fintype.card (ValidCol0_B (μP.colLen 0) (μQ.colLen 0)) ≤
    Fintype.card (doubleDescent_Bplus_fiber σ) := by
  apply Fintype.card_le_of_injective
    (fun v => ⟨liftPBP_B σ v hle hP_pos hprimP hprimQ,
              liftPBP_B_round_trip σ v hle hP_pos hprimP hprimQ⟩)
  intro v₁ v₂ h
  exact liftPBP_B_injective σ hle hP_pos hprimP hprimQ
    (congrArg (fun x => x.val) h)

/-- Key counting lemma (primitive case, B type):
    Every sub-PBP σ has fiber size = tripleSum(tailCoeffs k).1 = 4k. -/
private theorem fiber_card_B_primitive {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (k : ℕ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hk : k = μQ.colLen 0 - μP.colLen 0 + 1) (hk_pos : k ≥ 1)
    (hP_pos : 0 < μP.colLen 0)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    Fintype.card (doubleDescent_Bplus_fiber σ) = tripleSum (tailCoeffs k).1 := by
  rw [tripleSum_tailCoeffs_fst_eq k hk_pos]
  have hcard := validCol0_B_card (μP.colLen 0) (μQ.colLen 0) hle k hk hk_pos
  have h_le := fiber_le_validCol0_B σ hle
  have h_ge := validCol0_B_le_fiber' σ hle hP_pos hprimP hprimQ
  omega

/-- r₁ ≥ r₂ from SortedGE. -/
private theorem sortedGE_head_ge {r₁ r₂ : ℕ} {rest : List ℕ}
    (h : (r₁ :: r₂ :: rest).SortedGE) : r₁ ≥ r₂ := by
  have : Antitone (r₁ :: r₂ :: rest).get := h
  have := @this ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp)
  simp at this
  exact this

/-! ### Top-Q preservation for extract / lift -/

/-- `extractCol0_B` preserves the top-Q symbol at row μQ.colLen 0 - 1.
    Requires μQ.colLen 0 ≥ 1. -/
private theorem extractCol0_B_preserves_top_Q {μP μQ : YoungDiagram}
    (τ : PBPSet .Bplus μP μQ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hQ_pos : μQ.colLen 0 ≥ 1) :
    topSym_B (μP.colLen 0) (μQ.colLen 0) (extractCol0_B τ hle) =
      τ.val.Q.paint (μQ.colLen 0 - 1) 0 := by
  unfold extractCol0_B
  split_ifs with hc
  · -- Sum.inr (extractQtail_B): topSym = d.val ⟨hQ-hP, _⟩
    simp only [topSym_B]
    -- The DSeq underlying function: ⟨k, _⟩ ↦ τ.Q.paint (Q_tail_start + k) 0
    -- where Q_tail_start = hP - 1 (since has c).
    have hts : Q_tail_start τ = μP.colLen 0 - 1 := by
      unfold Q_tail_start; rw [if_pos hc]
    show (extractQtail_B τ hle _ (by simp [Q_tail_len, if_pos hc])).val
        ⟨μQ.colLen 0 - μP.colLen 0, by omega⟩ = _
    -- Unfold extractQtail_B.val : the val of the subtype is fun ⟨k, _⟩ => τ.Q.paint (tail_start + k) 0
    show τ.val.Q.paint (Q_tail_start τ + (μQ.colLen 0 - μP.colLen 0)) 0 = _
    rw [hts]
    have hpos : μP.colLen 0 ≥ 1 := hc.1
    congr 1; omega
  · -- Sum.inl (extractQtail_B): topSym = dif on hQ-hP ≥ 1
    simp only [topSym_B]
    split_ifs with h
    · -- hQ-hP ≥ 1: topSym = d.val ⟨hQ-hP-1, _⟩
      show (extractQtail_B τ hle _ (by simp [Q_tail_len, if_neg hc])).val
          ⟨μQ.colLen 0 - μP.colLen 0 - 1, by omega⟩ = _
      show τ.val.Q.paint (Q_tail_start τ + (μQ.colLen 0 - μP.colLen 0 - 1)) 0 = _
      have hts : Q_tail_start τ = μP.colLen 0 := by
        unfold Q_tail_start; rw [if_neg hc]
      rw [hts]; congr 1; omega
    · -- hQ-hP = 0, i.e., hP = hQ: top Q = .dot (by Q_col0_dot_below_tail with hQ-1 < hP)
      -- In this case, the row hQ-1 is in P shape (since hQ = hP and hQ-1 < hP).
      -- Not has-c in P, so P.paint(hQ-1, 0) = dot, dot_match forces Q.paint(hQ-1, 0) = dot.
      have hP_eq : μQ.colLen 0 = μP.colLen 0 := by omega
      have hdot : τ.val.Q.paint (μQ.colLen 0 - 1) 0 = .dot := by
        apply Q_col0_dot_below_tail
        unfold Q_tail_start; rw [if_neg hc]; omega
      exact hdot.symm

/-- `liftPBP_B` preserves the top-Q symbol at row μQ.colLen 0 - 1.
    Requires μQ.colLen 0 ≥ 1. -/
private theorem liftPBP_B_preserves_top_Q {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hQ_pos : μQ.colLen 0 ≥ 1)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1) :
    (liftPBP_B σ v hle hP_pos hprimP hprimQ).val.Q.paint (μQ.colLen 0 - 1) 0 =
      topSym_B (μP.colLen 0) (μQ.colLen 0) v := by
  -- The paint at col 0 is liftCol0Q_B (by definition of liftPaint_B_Q at j=0).
  show liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v (μQ.colLen 0 - 1) 0 =
      topSym_B (μP.colLen 0) (μQ.colLen 0) v
  simp only [liftPaint_B_Q, liftCol0Q_B]
  rcases v with d | d
  · -- .inl d: liftCol0Q_B = if hP ≤ hQ-1 ∧ hQ-1 < hQ then d.val ⟨hQ-1-hP, _⟩ else .dot
    simp only [topSym_B]
    by_cases h_ge_1 : μQ.colLen 0 - μP.colLen 0 ≥ 1
    · -- hQ - hP ≥ 1, so hP < hQ, so hP ≤ hQ-1.
      rw [dif_pos h_ge_1]
      have hcond : μP.colLen 0 ≤ μQ.colLen 0 - 1 ∧ μQ.colLen 0 - 1 < μQ.colLen 0 := ⟨by omega, by omega⟩
      rw [dif_pos hcond]
      have hfin : (⟨μQ.colLen 0 - 1 - μP.colLen 0, by omega⟩ : Fin (μQ.colLen 0 - μP.colLen 0)) =
          ⟨μQ.colLen 0 - μP.colLen 0 - 1, by omega⟩ := by
        apply Fin.ext; show μQ.colLen 0 - 1 - μP.colLen 0 = μQ.colLen 0 - μP.colLen 0 - 1; omega
      rw [hfin]
    · -- hQ - hP = 0, so hP = hQ, so ¬(hP ≤ hQ-1).
      rw [dif_neg h_ge_1]
      have hcond : ¬ (μP.colLen 0 ≤ μQ.colLen 0 - 1 ∧ μQ.colLen 0 - 1 < μQ.colLen 0) := by
        intro ⟨h1, _⟩; omega
      rw [dif_neg hcond]
  · -- .inr d
    simp only [topSym_B]
    have hcond : μP.colLen 0 - 1 ≤ μQ.colLen 0 - 1 ∧ μQ.colLen 0 - 1 < μQ.colLen 0 ∧
        μP.colLen 0 > 0 := ⟨by omega, by omega, hP_pos⟩
    rw [dif_pos hcond]
    have hfin : (⟨μQ.colLen 0 - 1 - (μP.colLen 0 - 1), by omega⟩ : Fin (μQ.colLen 0 - μP.colLen 0 + 1)) =
        ⟨μQ.colLen 0 - μP.colLen 0, by omega⟩ := by
      apply Fin.ext
      show μQ.colLen 0 - 1 - (μP.colLen 0 - 1) = μQ.colLen 0 - μP.colLen 0; omega
    rw [hfin]

/-- Primitive per-top-Q-sym step for B+ only:
    |{τ : B+ | Q_bot = sym}| = |B+ shift| · |ValidCol0_B | topSym = sym|. -/
private theorem card_PBPSet_Bplus_primitive_step_top_Q {μP μQ : YoungDiagram}
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (hQ_pos : μQ.colLen 0 ≥ 1)
    (hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0)
    (hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1)
    (sym : DRCSymbol) :
    Fintype.card {τ : PBPSet .Bplus μP μQ //
      τ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym} =
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) *
        Fintype.card {v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) //
          topSym_B (μP.colLen 0) (μQ.colLen 0) v = sym} := by
  apply le_antisymm
  · -- Upper bound: fiber with Q_bot = sym ↪ (sub × ValidCol0_B with topSym = sym).
    rw [← Fintype.card_prod]
    apply Fintype.card_le_of_injective
      (fun (x : {τ : PBPSet .Bplus μP μQ //
          τ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym}) =>
        ((doubleDescent_Bplus_map μP μQ x.val,
          ⟨extractCol0_B x.val hle, by
            rw [extractCol0_B_preserves_top_Q x.val hle hQ_pos]
            exact x.prop⟩) :
          PBPSet .Bplus μP.shiftLeft μQ.shiftLeft ×
          {v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) //
            topSym_B (μP.colLen 0) (μQ.colLen 0) v = sym}))
    intro ⟨τ₁, _⟩ ⟨τ₂, _⟩ heq
    simp only [Prod.mk.injEq] at heq
    have h_σ := heq.1
    have h_v_sub := Subtype.ext_iff.mp heq.2
    -- Use extractCol0_B_injective_on_fiber with both τ₁, τ₂ as fiber elements over σ := doubleDescent τ₁
    have h_fib_eq : (⟨τ₁, rfl⟩ : doubleDescent_Bplus_fiber (doubleDescent_Bplus_map μP μQ τ₁)) =
        ⟨τ₂, h_σ.symm⟩ := by
      apply extractCol0_B_injective_on_fiber (μP := μP) (μQ := μQ)
        (doubleDescent_Bplus_map μP μQ τ₁) hle
      exact h_v_sub
    -- Extract τ₁ = τ₂ from the fiber equality.
    have : τ₁ = τ₂ := by
      have := congrArg (fun x : doubleDescent_Bplus_fiber _ => x.val) h_fib_eq
      exact this
    exact Subtype.ext this
  · -- Lower bound: sub × ValidCol0_B with topSym = sym ↪ fiber with Q_bot = sym.
    rw [← Fintype.card_prod]
    apply Fintype.card_le_of_injective
      (fun (p : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft ×
          {v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) //
            topSym_B (μP.colLen 0) (μQ.colLen 0) v = sym}) =>
        (⟨liftPBP_B p.1 p.2.1 hle hP_pos hprimP hprimQ, by
          rw [liftPBP_B_preserves_top_Q p.1 p.2.1 hle hP_pos hQ_pos hprimP hprimQ]
          exact p.2.prop⟩ :
          {τ : PBPSet .Bplus μP μQ //
            τ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym}))
    intro ⟨σ₁, v₁, _⟩ ⟨σ₂, v₂, _⟩ heq
    -- Extract that liftPBP_B are equal on values
    have h_lift_eq : liftPBP_B σ₁ v₁ hle hP_pos hprimP hprimQ =
        liftPBP_B σ₂ v₂ hle hP_pos hprimP hprimQ := Subtype.ext_iff.mp heq
    -- Round-trip: doubleDescent_Bplus_map (liftPBP_B σ v) = σ
    have hrt₁ := liftPBP_B_round_trip σ₁ v₁ hle hP_pos hprimP hprimQ
    have hrt₂ := liftPBP_B_round_trip σ₂ v₂ hle hP_pos hprimP hprimQ
    have hσ_eq : σ₁ = σ₂ := by
      rw [← hrt₁, ← hrt₂, h_lift_eq]
    subst hσ_eq
    -- Now σ₁ = σ₂; need v₁ = v₂. Use liftPBP_B_injective.
    have hv_eq := liftPBP_B_injective σ₁ hle hP_pos hprimP hprimQ h_lift_eq
    exact Prod.ext rfl (Subtype.ext hv_eq)

/-! ## Recursive step -/

/-- Primitive case (r₂ > r₃): fiber is uniform across all tail classes. -/
theorem card_PBPSet_B_primitive_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hprim : r₂ > rest.head?.getD 0) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    (Fintype.card (PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) +
     Fintype.card (PBPSet .Bminus (μP.shiftLeft) (μQ.shiftLeft))) *
    tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
  -- Use B⁺/B⁻ symmetry to reduce to B⁺ only
  have h_sym := card_Bplus_eq_Bminus μP μQ
  have h_sym_sh := card_Bplus_eq_Bminus (μP.shiftLeft) (μQ.shiftLeft)
  -- Suffices to show card(B⁺) = card(B⁺ shift) × tripleSum(tailCoeffs k).1
  suffices h : Fintype.card (PBPSet .Bplus μP μQ) =
      Fintype.card (PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft)) *
        tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 by
    rw [← h_sym, h, h_sym_sh, Nat.add_mul]
  -- Decompose card(B⁺) as sum of fiber sizes
  rw [card_PBPSet_Bplus_eq_sum_fiber]
  -- Each fiber has the same size
  have hk_pos : (r₁ - r₂) / 2 + 1 ≥ 1 := by omega
  -- Compute column lengths
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  -- k = Q.colLen(0) - P.colLen(0) + 1 = r₁/2 - r₂/2 + 1
  have hk_eq : (r₁ - r₂) / 2 + 1 = μQ.colLen 0 - μP.colLen 0 + 1 := by
    rw [hP0, hQ0]
    have heven₁ := heven r₁ (by simp)
    have heven₂ := heven r₂ (by simp)
    obtain ⟨a, rfl⟩ := heven₁; obtain ⟨b, rfl⟩ := heven₂
    simp [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    omega
  -- Derive primitivity conditions for the lift construction
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  -- μP.shiftLeft.colLens = dpartColLensP_B rest
  have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
  -- μQ.shiftLeft.colLens = dpartColLensQ_B rest
  have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
  -- colLen 0 of shiftLeft = colLen 1
  -- Key: μP.colLen 1 = μP.shiftLeft.colLen 0, and colLen 0 ≤ head of colLens (if nonempty)
  -- or 0 (if empty). All entries of dpartColLensP_B rest are < r₂/2.
  have hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0 := by
    intro j hj
    have h1 : μP.colLen j ≤ μP.colLen 1 := μP.colLen_anti 1 j (by omega)
    suffices hsuff : μP.colLen 1 < μP.colLen 0 from lt_of_le_of_lt h1 hsuff
    rw [← YoungDiagram.colLen_shiftLeft, hP0]
    -- μP.shiftLeft.colLen 0 < r₂/2
    -- From μP.shiftLeft.colLens = dpartColLensP_B rest:
    -- if list is empty, colLen 0 = 0 < r₂/2
    -- if nonempty, colLen 0 = head of list, which is some rₖ/2 < r₂/2
    by_cases hemp : μP.shiftLeft.colLens = []
    · -- empty: colLen 0 = 0
      have hrl : μP.shiftLeft.rowLen 0 = 0 := by
        rw [← YoungDiagram.length_colLens]; simp [hemp]
      have : μP.shiftLeft.colLen 0 = 0 := by
        by_contra hne; push_neg at hne
        have : 0 < μP.shiftLeft.colLen 0 := Nat.pos_of_ne_zero hne
        have hmem := YoungDiagram.mem_iff_lt_colLen.mpr this
        have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
        omega
      omega
    · -- nonempty: colLen 0 = first element
      obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil (by exact hemp)
      have h0 : μP.shiftLeft.colLen 0 = hd :=
        colLen_0_eq_of_colLens_cons heq
      rw [h0]
      -- hd is the first entry of dpartColLensP_B rest
      have heq' := hP_sh.symm.trans heq
      -- Case analysis on rest
      match rest, heq' with
      | r₃ :: r₄ :: rest', heq'' =>
        simp only [dpartColLensP_B] at heq''
        have hhd : r₄ / 2 = hd := (List.cons.inj heq'').1
        rw [← hhd, hb]
        have hr₃_lt : r₃ < r₂ := by
          have : r₂ > (r₃ :: r₄ :: rest').head?.getD 0 := hprim
          simp at this; omega
        have hr₄_le_r₃ : r₄ ≤ r₃ := by
          have : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
          have := @this ⟨2, by simp⟩ ⟨3, by simp⟩ (by simp)
          simp at this; exact this
        have heven₄ := heven r₄ (by simp)
        obtain ⟨d, hd⟩ := heven₄; rw [hd]; omega
      | [r₃], heq'' =>
        simp [dpartColLensP_B] at heq''
      | [], heq'' =>
        simp [dpartColLensP_B] at heq''
  have hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1 := by
    intro j hj
    have h1 : μQ.colLen j ≤ μQ.colLen 1 := μQ.colLen_anti 1 j (by omega)
    suffices hsuff : μQ.colLen 1 ≤ μP.colLen 0 - 1 from le_trans h1 hsuff
    rw [← YoungDiagram.colLen_shiftLeft, hP0]
    by_cases hemq : μQ.shiftLeft.colLens = []
    · have hrl : μQ.shiftLeft.rowLen 0 = 0 := by
        rw [← YoungDiagram.length_colLens]; simp [hemq]
      have : μQ.shiftLeft.colLen 0 = 0 := by
        by_contra hne; push_neg at hne
        have : 0 < μQ.shiftLeft.colLen 0 := Nat.pos_of_ne_zero hne
        have hmem := YoungDiagram.mem_iff_lt_colLen.mpr this
        have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
        omega
      omega
    · obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil (by exact hemq)
      have h0 : μQ.shiftLeft.colLen 0 = hd :=
        colLen_0_eq_of_colLens_cons heq
      rw [h0]
      have heq' := hQ_sh.symm.trans heq
      match rest, heq' with
      | r₃ :: r₄ :: rest', heq'' =>
        simp only [dpartColLensQ_B] at heq''
        have hhd : r₃ / 2 = hd := (List.cons.inj heq'').1
        rw [← hhd, hb]
        have hr₃_lt : r₃ < r₂ := by
          have : r₂ > (r₃ :: r₄ :: rest').head?.getD 0 := hprim
          simp at this; omega
        have heven₃ := heven r₃ (by simp)
        obtain ⟨c, hc⟩ := heven₃; rw [hc]; omega
      | [r₃], heq'' =>
        simp only [dpartColLensQ_B] at heq''
        by_cases hr₃ : r₃ > 0
        · rw [if_pos hr₃] at heq''
          have hhd : r₃ / 2 = hd := (List.cons.inj heq'').1
          rw [← hhd, hb]
          have hr₃_lt : r₃ < r₂ := by simp at hprim; exact hprim
          have heven₃ := heven r₃ (by simp)
          obtain ⟨c, hc⟩ := heven₃; rw [hc]; omega
        · rw [if_neg (by omega)] at heq''; exact absurd heq'' (List.cons_ne_nil _ _).symm
      | [], heq'' =>
        simp [dpartColLensQ_B] at heq''
  have hfiber : ∀ σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft),
      Fintype.card (doubleDescent_Bplus_fiber σ) =
      tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
    intro σ
    rw [hk_eq]
    exact fiber_card_B_primitive σ _ hle rfl (by omega) hP_pos hprimP hprimQ
  rw [Finset.sum_congr rfl (fun σ _ => hfiber σ)]
  rw [Finset.sum_const, Finset.card_univ]
  rfl

/-! ## α-Class Count Identities

Reference: `lean/docs/blueprints/B_balanced_fiber_structure.md`.

For B-type PBPs on dp shape, `countPBP_B(dp) = (dd_α, rc_α, ss_α)` where:
- `dd_α = |{σ ∈ B⁺ ∪ B⁻ : Q_bot σ = d}|`
- `rc_α = |{σ ∈ B⁺ : Q_bot σ ≠ d}| + |{σ ∈ B⁻ : Q_bot σ = r}|`
- `ss_α = |{σ ∈ B⁻ : (Q_bot σ).layerOrd ≤ 1}|`  (i.e., Q_bot ∈ {•, s})

These identities (A1, A2, A3 below) are admitted; numerically verified for dp up to size 24.
See `tools/verify_countB_components.py`. -/

/-! ### γ-swap symmetries for Q_bot predicates

Since `PBP.swapBplusBminus` preserves both P and Q, any predicate on `σ.val.Q`
is invariant under the swap. This gives bijections on filtered subtypes. -/

/-- **γ-swap for Q_bot = d**: B⁺ and B⁻ have the same count of PBPs with `Q_bot = d`. -/
private theorem card_Bplus_Qbot_d_eq_Bminus_Qbot_d (μP μQ : YoungDiagram) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card := by
  rw [show (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bplus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm]
  rw [show (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bminus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm]
  apply Fintype.card_congr
  refine {
    toFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inl σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    invFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inr σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    left_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
    right_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
  }

/-! ### DSeq enumeration helpers for singleton base cases

For k ≥ 1, we count DSeqs of length k by the value at last position. A DSeq is
a sorted (by layerOrd) sequence in {s, r, d} with at most one d. The counts are:
- last = .s → all s (by monotonicity), count = 1
- last = .r → choose the s|r boundary in [0, k], count = k
- last = .d → d at last (forced by uniqueness + mono), then s|r boundary, count = k

Since `Fintype.card (DSeq k) = 2k+1` and the three classes partition DSeq k
into disjoint subsets (by last-entry trichotomy in {s, r, d}), and the last=s
class has card 1 by A3's argument, we can derive the other two counts by
symmetry if we can establish one directly.

Strategy: exhibit an explicit injection `Fin k ↪ {DSeq k, last = r}` and
similarly for last = d, then count = 2k gives both = k by the total constraint. -/

/-- Build the specific DSeq v_m (indexed by m ∈ Fin k, k ≥ 1) with
    - v_m i = .s  if i.val < m.val
    - v_m i = .r  otherwise.
    This has last entry .r (since m.val ≤ k-1 < k-1+1 = k, so k-1 ≥ m.val).
    The hypothesis `hk` is used by downstream lemmas (e.g. `DSeq_sr_last`). -/
private def DSeq_sr {k : ℕ} (hk : k ≥ 1) (m : Fin k) : DSeq k :=
  ⟨fun i => if i.val < m.val then .s else .r,
    ⟨fun i => by by_cases h : i.val < m.val <;> simp [h],
     fun i j hij => by
       by_cases hi : i.val < m.val
       · by_cases hj : j.val < m.val
         · simp [hi, hj]
         · simp [hi, hj, DRCSymbol.layerOrd]
       · have hj : ¬ j.val < m.val := by omega
         simp [hi, hj],
     fun i j hdi hdj => by
       simp only at hdi hdj
       split_ifs at hdi⟩⟩

/-- Build the specific DSeq w_m (indexed by m ∈ Fin k, k ≥ 1) with
    - w_m i = .s  if i.val < m.val
    - w_m i = .r  if m.val ≤ i.val and i.val < k - 1
    - w_m i = .d  if i.val = k - 1.
    This has last entry .d. -/
private def DSeq_srd {k : ℕ} (hk : k ≥ 1) (m : Fin k) : DSeq k :=
  ⟨fun i =>
      if i.val = k - 1 then .d
      else if i.val < m.val then .s
      else .r,
    ⟨fun i => by
       by_cases h₁ : i.val = k - 1
       · simp [h₁]
       · by_cases h₂ : i.val < m.val
         · simp [h₁, h₂]
         · simp [h₁, h₂],
     fun i j hij => by
       by_cases hj : j.val = k - 1
       · simp only [hj, if_true]
         by_cases hi : i.val = k - 1
         · simp [hi, DRCSymbol.layerOrd]
         · simp only [hi, if_false]
           by_cases hi_m : i.val < m.val
           · simp [hi_m, DRCSymbol.layerOrd]
           · simp [hi_m, DRCSymbol.layerOrd]
       · have hi : i.val ≠ k - 1 := by have := j.isLt; omega
         simp only [hi, if_false, hj, if_false]
         by_cases hi_m : i.val < m.val
         · by_cases hj_m : j.val < m.val
           · simp [hi_m, hj_m]
           · simp [hi_m, hj_m, DRCSymbol.layerOrd]
         · have hj_m : ¬ j.val < m.val := by omega
           simp [hi_m, hj_m],
     fun i j hdi hdj => by
       have hi : i.val = k - 1 := by
         by_contra h
         simp only [h, if_false] at hdi
         split_ifs at hdi
       have hj : j.val = k - 1 := by
         by_contra h
         simp only [h, if_false] at hdj
         split_ifs at hdj
       exact Fin.ext (hi.trans hj.symm)⟩⟩

/-- DSeq_sr m has last entry = .r. -/
private lemma DSeq_sr_last {k : ℕ} (hk : k ≥ 1) (m : Fin k) :
    (DSeq_sr hk m).val ⟨k - 1, by omega⟩ = .r := by
  unfold DSeq_sr
  simp only
  have hm := m.isLt
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

/-- DSeq_srd m has last entry = .d. -/
private lemma DSeq_srd_last {k : ℕ} (hk : k ≥ 1) (m : Fin k) :
    (DSeq_srd hk m).val ⟨k - 1, by omega⟩ = .d := by
  unfold DSeq_srd
  simp

/-- DSeq_sr is injective. -/
private lemma DSeq_sr_injective {k : ℕ} (hk : k ≥ 1) :
    Function.Injective (DSeq_sr hk) := by
  intro m₁ m₂ h
  -- Extract the underlying function equality.
  have hfun : (fun i : Fin k => if i.val < m₁.val then DRCSymbol.s else DRCSymbol.r) =
              (fun i : Fin k => if i.val < m₂.val then DRCSymbol.s else DRCSymbol.r) :=
    congrArg Subtype.val h
  -- Show m₁.val = m₂.val by comparing evaluations.
  apply Fin.ext
  rcases lt_trichotomy m₁.val m₂.val with hlt | heq | hgt
  · -- m₁.val < m₂.val: at position ⟨m₁.val, m₁.isLt⟩, LHS = r, RHS = s. Contradiction.
    exfalso
    have heval := congrFun hfun ⟨m₁.val, m₁.isLt⟩
    simp only [lt_irrefl, if_false, hlt, if_true] at heval
    exact absurd heval (by decide)
  · exact heq
  · -- Symmetric: m₂.val < m₁.val. At ⟨m₂.val, m₂.isLt⟩, LHS = s, RHS = r.
    exfalso
    have heval := congrFun hfun ⟨m₂.val, m₂.isLt⟩
    simp only [hgt, if_true, lt_irrefl, if_false] at heval
    exact absurd heval (by decide)

/-- DSeq_srd is injective. -/
private lemma DSeq_srd_injective {k : ℕ} (hk : k ≥ 1) :
    Function.Injective (DSeq_srd hk) := by
  intro m₁ m₂ h
  have hfun : (fun i : Fin k => if i.val = k - 1 then DRCSymbol.d
                                else if i.val < m₁.val then DRCSymbol.s else DRCSymbol.r) =
              (fun i : Fin k => if i.val = k - 1 then DRCSymbol.d
                                else if i.val < m₂.val then DRCSymbol.s else DRCSymbol.r) :=
    congrArg Subtype.val h
  apply Fin.ext
  rcases lt_trichotomy m₁.val m₂.val with hlt | heq | hgt
  · exfalso
    have hm₁_ne : m₁.val ≠ k - 1 := by have := m₂.isLt; omega
    have heval := congrFun hfun ⟨m₁.val, m₁.isLt⟩
    simp only [hm₁_ne, if_false, lt_irrefl, hlt, if_true] at heval
    exact absurd heval (by decide)
  · exact heq
  · exfalso
    have hm₂_ne : m₂.val ≠ k - 1 := by have := m₁.isLt; omega
    have heval := congrFun hfun ⟨m₂.val, m₂.isLt⟩
    simp only [hm₂_ne, if_false, hgt, lt_irrefl, if_true] at heval
    exact absurd heval (by decide)

/-- All last = .s DSeqs are forced to be constant .s. -/
private lemma DSeq_last_s_eq {k : ℕ} (hk : k ≥ 1) (d : DSeq k)
    (hlast : d.val ⟨k - 1, by omega⟩ = .s) : ∀ i, d.val i = .s := by
  intro i
  have hi : i.val ≤ k - 1 := by have := i.isLt; omega
  have hmono := d.prop.2.1 i ⟨k - 1, by omega⟩ hi
  rw [hlast] at hmono
  rcases d.prop.1 i with h | h | h
  · exact h
  · rw [h, DRCSymbol.layerOrd] at hmono
    simp [DRCSymbol.layerOrd] at hmono
  · rw [h, DRCSymbol.layerOrd] at hmono
    simp [DRCSymbol.layerOrd] at hmono

/-- Constant DSeq .s sequence. -/
private def DSeq_const_s {k : ℕ} : DSeq k :=
  ⟨fun _ => .s,
   ⟨fun _ => Or.inl rfl,
    fun _ _ _ => le_refl _,
    fun _ _ hi _ => by simp at hi⟩⟩

/-- Card of DSeqs with last = .s is 1 (all s). -/
private theorem card_DSeq_last_s {k : ℕ} (hk : k ≥ 1) :
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .s} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨DSeq_const_s, rfl⟩, ?_⟩
  rintro ⟨d, hlast⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact DSeq_last_s_eq hk d hlast i

/-- DSeq k partitions into last=s, last=r, last=d (using the s/r/d trichotomy
    from DSeq.prop.1), so |DSeq k| = |last=s| + |last=r| + |last=d|.
    Uses Finset.card partition into three filters. -/
private theorem card_DSeq_partition {k : ℕ} (hk : k ≥ 1) :
    Fintype.card (DSeq k) =
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .s} +
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .r} +
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .d} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
  -- Abbreviate the three filter sets.
  set Fs := (Finset.univ.filter (fun d : DSeq k => d.val ⟨k - 1, by omega⟩ = .s)) with hFs
  set Fr := (Finset.univ.filter (fun d : DSeq k => d.val ⟨k - 1, by omega⟩ = .r)) with hFr
  set Fd := (Finset.univ.filter (fun d : DSeq k => d.val ⟨k - 1, by omega⟩ = .d)) with hFd
  have hcov : (Finset.univ : Finset (DSeq k)) = Fs ∪ Fr ∪ Fd := by
    ext d
    simp only [hFs, hFr, hFd, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
      true_iff]
    rcases d.prop.1 ⟨k - 1, by omega⟩ with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hdisj_sr : Disjoint Fs Fr := by
    rw [hFs, hFr, Finset.disjoint_filter]
    intro d _ h₁ h₂; rw [h₁] at h₂; exact DRCSymbol.noConfusion h₂
  have hdisj_sd : Disjoint (Fs ∪ Fr) Fd := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, ?_⟩
    · rw [hFs, hFd, Finset.disjoint_filter]
      intro d _ h₁ h₂; rw [h₁] at h₂; exact DRCSymbol.noConfusion h₂
    · rw [hFr, hFd, Finset.disjoint_filter]
      intro d _ h₁ h₂; rw [h₁] at h₂; exact DRCSymbol.noConfusion h₂
  rw [show Fintype.card (DSeq k) = (Finset.univ : Finset (DSeq k)).card from
    (Finset.card_univ).symm, hcov,
    Finset.card_union_of_disjoint hdisj_sd, Finset.card_union_of_disjoint hdisj_sr]

/-- Count of DSeq of length k with last = .r is ≥ k. -/
private theorem card_DSeq_last_r_ge {k : ℕ} (hk : k ≥ 1) :
    k ≤ Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .r} := by
  have : Fintype.card (Fin k) ≤
      Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .r} := by
    apply Fintype.card_le_of_injective
      (fun m => ⟨DSeq_sr hk m, DSeq_sr_last hk m⟩)
    intro m₁ m₂ h
    exact DSeq_sr_injective hk (Subtype.ext_iff.mp h)
  rw [Fintype.card_fin] at this
  exact this

/-- Count of DSeq of length k with last = .d is ≥ k. -/
private theorem card_DSeq_last_d_ge {k : ℕ} (hk : k ≥ 1) :
    k ≤ Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .d} := by
  have : Fintype.card (Fin k) ≤
      Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .d} := by
    apply Fintype.card_le_of_injective
      (fun m => ⟨DSeq_srd hk m, DSeq_srd_last hk m⟩)
    intro m₁ m₂ h
    exact DSeq_srd_injective hk (Subtype.ext_iff.mp h)
  rw [Fintype.card_fin] at this
  exact this

/-- Count of DSeq of length k with last = .r equals k. -/
private theorem card_DSeq_last_r {k : ℕ} (hk : k ≥ 1) :
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .r} = k := by
  have htotal := DSeq_card k
  have hpart := card_DSeq_partition hk
  have hs := card_DSeq_last_s hk
  have h_r_ge := card_DSeq_last_r_ge hk
  have h_d_ge := card_DSeq_last_d_ge hk
  omega

/-- Count of DSeq of length k with last = .d equals k. -/
private theorem card_DSeq_last_d {k : ℕ} (hk : k ≥ 1) :
    Fintype.card {d : DSeq k // d.val ⟨k - 1, by omega⟩ = .d} = k := by
  have htotal := DSeq_card k
  have hpart := card_DSeq_partition hk
  have hs := card_DSeq_last_s hk
  have h_r_ge := card_DSeq_last_r_ge hk
  have h_d_ge := card_DSeq_last_d_ge hk
  omega

/-- Sum decomposition for ValidCol0_B top-symbol subtype card. -/
private theorem validCol0_B_card_top_split (hP hQ : ℕ) (sym : DRCSymbol) :
    Fintype.card {v : ValidCol0_B hP hQ // topSym_B hP hQ v = sym} =
    Fintype.card {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = sym} +
    Fintype.card {v : DSeq (hQ - hP + 1) // topSym_B hP hQ (Sum.inr v) = sym} := by
  -- Use Equiv between {v : A ⊕ B // P v} and {v : A // P (inl v)} ⊕ {v : B // P (inr v)}.
  have : {v : ValidCol0_B hP hQ // topSym_B hP hQ v = sym} ≃
      {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = sym} ⊕
      {v : DSeq (hQ - hP + 1) // topSym_B hP hQ (Sum.inr v) = sym} := by
    refine {
      toFun := fun ⟨v, hv⟩ => match v, hv with
        | Sum.inl a, hv => Sum.inl ⟨a, hv⟩
        | Sum.inr b, hv => Sum.inr ⟨b, hv⟩
      invFun := fun v => match v with
        | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a, ha⟩
        | Sum.inr ⟨b, hb⟩ => ⟨Sum.inr b, hb⟩
      left_inv := ?_
      right_inv := ?_
    }
    · rintro ⟨v, hv⟩
      rcases v with a | b <;> rfl
    · rintro (⟨a, ha⟩ | ⟨b, hb⟩) <;> rfl
  rw [Fintype.card_congr this, Fintype.card_sum]

/-- |ValidCol0_B with top Q = d| = 2k - 1, where k = hQ - hP + 1.
    (Agrees with tDD = `nu(k-1) + (if k≥2 then nu(k-2) else 0)` for k ≥ 1.) -/
private theorem validCol0_B_card_top_d (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card {v : ValidCol0_B hP hQ // topSym_B hP hQ v = .d} =
      2 * k - 1 := by
  -- Sum decomposition.
  rw [validCol0_B_card_top_split]
  -- inr side: subtype reformulation.
  have h_idx_eq : (hQ - hP + 1) - 1 = hQ - hP := by omega
  have h_inr_eq : Fintype.card
      {v : DSeq (hQ - hP + 1) // topSym_B hP hQ (Sum.inr v) = .d} =
      Fintype.card {v : DSeq (hQ - hP + 1) //
        v.val ⟨(hQ - hP + 1) - 1, by omega⟩ = .d} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro v
    show v.val ⟨hQ - hP, _⟩ = .d ↔ v.val ⟨(hQ - hP + 1) - 1, _⟩ = .d
    have hfin : (⟨hQ - hP, by omega⟩ : Fin (hQ - hP + 1)) =
        ⟨(hQ - hP + 1) - 1, by omega⟩ := Fin.ext h_idx_eq.symm
    rw [hfin]
  -- inr side card.
  have h_inr_card := card_DSeq_last_d (k := hQ - hP + 1) (by omega)
  -- Now case split on k.
  by_cases h_k_eq_1 : k = 1
  · -- k = 1: hQ - hP = 0.
    -- inl side: DSeq(0) with top via dif_neg → .dot ≠ .d → 0.
    have h_inl_zero : Fintype.card
        {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = .d} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun ⟨v, hv⟩ => ?_⟩
      simp only [topSym_B] at hv
      split_ifs at hv with h
      · omega
    rw [h_inl_zero, h_inr_eq, h_inr_card]
    omega
  · -- k ≥ 2: hQ - hP ≥ 1.
    have hKm : hQ - hP ≥ 1 := by omega
    -- inl: DSeq(hQ-hP) last=d = hQ-hP = k-1.
    have h_inl_eq : Fintype.card
        {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = .d} =
        Fintype.card {v : DSeq (hQ - hP) //
          v.val ⟨(hQ - hP) - 1, by omega⟩ = .d} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro v
      show (dite (hQ - hP ≥ 1) (fun h => v.val ⟨hQ - hP - 1, by omega⟩)
          (fun _ => DRCSymbol.dot)) = .d ↔ v.val ⟨(hQ - hP) - 1, by omega⟩ = .d
      rw [dif_pos hKm]
    have h_inl_card := card_DSeq_last_d (k := hQ - hP) hKm
    rw [h_inl_eq, h_inr_eq, h_inl_card, h_inr_card]
    omega

/-- |ValidCol0_B with top Q = r| = 2k - 1, where k = hQ - hP + 1.
    Proof mirrors `validCol0_B_card_top_d` but uses `card_DSeq_last_r`. -/
private theorem validCol0_B_card_top_r (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card {v : ValidCol0_B hP hQ // topSym_B hP hQ v = .r} =
      2 * k - 1 := by
  -- Sum decomposition.
  rw [validCol0_B_card_top_split]
  -- inr side: subtype reformulation.
  have h_idx_eq : (hQ - hP + 1) - 1 = hQ - hP := by omega
  have h_inr_eq : Fintype.card
      {v : DSeq (hQ - hP + 1) // topSym_B hP hQ (Sum.inr v) = .r} =
      Fintype.card {v : DSeq (hQ - hP + 1) //
        v.val ⟨(hQ - hP + 1) - 1, by omega⟩ = .r} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro v
    show v.val ⟨hQ - hP, _⟩ = .r ↔ v.val ⟨(hQ - hP + 1) - 1, _⟩ = .r
    have hfin : (⟨hQ - hP, by omega⟩ : Fin (hQ - hP + 1)) =
        ⟨(hQ - hP + 1) - 1, by omega⟩ := Fin.ext h_idx_eq.symm
    rw [hfin]
  -- inr side card.
  have h_inr_card := card_DSeq_last_r (k := hQ - hP + 1) (by omega)
  -- Now case split on k.
  by_cases h_k_eq_1 : k = 1
  · -- k = 1: hQ - hP = 0.
    -- inl side: DSeq(0) with top via dif_neg → .dot ≠ .r → 0.
    have h_inl_zero : Fintype.card
        {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = .r} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun ⟨v, hv⟩ => ?_⟩
      simp only [topSym_B] at hv
      split_ifs at hv with h
      · omega
    rw [h_inl_zero, h_inr_eq, h_inr_card]
    omega
  · -- k ≥ 2: hQ - hP ≥ 1.
    have hKm : hQ - hP ≥ 1 := by omega
    -- inl: DSeq(hQ-hP) last=r = hQ-hP = k-1.
    have h_inl_eq : Fintype.card
        {v : DSeq (hQ - hP) // topSym_B hP hQ (Sum.inl v) = .r} =
        Fintype.card {v : DSeq (hQ - hP) //
          v.val ⟨(hQ - hP) - 1, by omega⟩ = .r} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro v
      show (dite (hQ - hP ≥ 1) (fun h => v.val ⟨hQ - hP - 1, by omega⟩)
          (fun _ => DRCSymbol.dot)) = .r ↔ v.val ⟨(hQ - hP) - 1, by omega⟩ = .r
      rw [dif_pos hKm]
    have h_inl_card := card_DSeq_last_r (k := hQ - hP) hKm
    rw [h_inl_eq, h_inr_eq, h_inl_card, h_inr_card]
    omega

/-- |ValidCol0_B with topSym.layerOrd ≤ 1| = 2.
    Exactly 2 paintings have `topSym ∈ {•, s}`, irrespective of k.

    Derived from `validCol0_B_card` (total = 4k), minus top=r and top=d counts
    (both 2k-1 via `validCol0_B_card_top_r` and `validCol0_B_card_top_d`):
    `4k - (2k-1) - (2k-1) = 2`. -/
private theorem validCol0_B_card_top_lo_le_one (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card {v : ValidCol0_B hP hQ // (topSym_B hP hQ v).layerOrd ≤ 1} = 2 := by
  -- Partition ValidCol0_B into classes by topSym: .d, .r, lo≤1.
  have h_total := validCol0_B_card hP hQ hle k hk hk_pos
  have h_top_d := validCol0_B_card_top_d hP hQ hle k hk hk_pos
  have h_top_r := validCol0_B_card_top_r hP hQ hle k hk hk_pos
  -- Convert subtype cards to filter cards.
  rw [show (Fintype.card {v : ValidCol0_B hP hQ //
      (topSym_B hP hQ v).layerOrd ≤ 1}) =
      (Finset.univ.filter fun v : ValidCol0_B hP hQ =>
        (topSym_B hP hQ v).layerOrd ≤ 1).card from (Fintype.card_subtype _)]
  rw [show (Fintype.card {v : ValidCol0_B hP hQ // topSym_B hP hQ v = .d}) =
      (Finset.univ.filter fun v : ValidCol0_B hP hQ =>
        topSym_B hP hQ v = .d).card from (Fintype.card_subtype _)] at h_top_d
  rw [show (Fintype.card {v : ValidCol0_B hP hQ // topSym_B hP hQ v = .r}) =
      (Finset.univ.filter fun v : ValidCol0_B hP hQ =>
        topSym_B hP hQ v = .r).card from (Fintype.card_subtype _)] at h_top_r
  rw [show (Fintype.card (ValidCol0_B hP hQ)) =
      (Finset.univ : Finset (ValidCol0_B hP hQ)).card from Finset.card_univ.symm] at h_total
  -- The union filter: univ = {top=d} ∪ {top=r} ∪ {top.lo≤1} (pairwise disjoint).
  have h_union : (Finset.univ : Finset (ValidCol0_B hP hQ)) =
      (Finset.univ.filter fun v => topSym_B hP hQ v = .d) ∪
      (Finset.univ.filter fun v => topSym_B hP hQ v = .r) ∪
      (Finset.univ.filter fun v => (topSym_B hP hQ v).layerOrd ≤ 1) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    -- Show: ∀ v, topSym v = .d ∨ topSym v = .r ∨ topSym v.lo ≤ 1.
    rcases v with d | d
    · -- inl case
      simp only [topSym_B]
      split_ifs with h
      · -- k ≥ 1: topSym = d.val ⟨hQ-hP-1, _⟩ ∈ {s, r, d}
        rcases d.prop.1 ⟨hQ - hP - 1, by omega⟩ with h1 | h1 | h1
        · right; rw [h1]; decide
        · left; right; exact h1
        · left; left; exact h1
      · -- k = 0: topSym = .dot (layerOrd 0 ≤ 1)
        right; decide
    · -- inr case: always d.val ⟨hQ-hP, _⟩ ∈ {s, r, d}
      simp only [topSym_B]
      rcases d.prop.1 ⟨hQ - hP, by omega⟩ with h1 | h1 | h1
      · right; rw [h1]; decide
      · left; right; exact h1
      · left; left; exact h1
  -- Disjointness.
  have h_disj_dr : Disjoint
      (Finset.univ.filter fun v : ValidCol0_B hP hQ => topSym_B hP hQ v = .d)
      (Finset.univ.filter fun v => topSym_B hP hQ v = .r) := by
    rw [Finset.disjoint_filter]; intros v _ h1 h2; rw [h1] at h2; exact DRCSymbol.noConfusion h2
  have h_disj_d_lo : Disjoint
      (Finset.univ.filter fun v : ValidCol0_B hP hQ => topSym_B hP hQ v = .d)
      (Finset.univ.filter fun v => (topSym_B hP hQ v).layerOrd ≤ 1) := by
    rw [Finset.disjoint_filter]; intros v _ h1 h2; rw [h1] at h2
    simp [DRCSymbol.layerOrd] at h2
  have h_disj_r_lo : Disjoint
      (Finset.univ.filter fun v : ValidCol0_B hP hQ => topSym_B hP hQ v = .r)
      (Finset.univ.filter fun v => (topSym_B hP hQ v).layerOrd ≤ 1) := by
    rw [Finset.disjoint_filter]; intros v _ h1 h2; rw [h1] at h2
    simp [DRCSymbol.layerOrd] at h2
  have h_disj_dr_lo : Disjoint
      ((Finset.univ.filter fun v : ValidCol0_B hP hQ => topSym_B hP hQ v = .d) ∪
       (Finset.univ.filter fun v => topSym_B hP hQ v = .r))
      (Finset.univ.filter fun v => (topSym_B hP hQ v).layerOrd ≤ 1) := by
    rw [Finset.disjoint_union_left]; exact ⟨h_disj_d_lo, h_disj_r_lo⟩
  -- card univ = card({d} ∪ {r}) + card({lo≤1}) = card{d} + card{r} + card{lo≤1}
  rw [h_union, Finset.card_union_of_disjoint h_disj_dr_lo,
    Finset.card_union_of_disjoint h_disj_dr] at h_total
  omega

/-- Transfer between PBPSet .Bminus ⊥ μQ filter and DSeq last-entry filter,
    for a given DRCSymbol constant. -/
private theorem card_Bminus_Qbot_eq_DSeq_last {μQ : YoungDiagram}
    (hsc : ∀ j, j ≥ 1 → μQ.colLen j = 0) (hk_pos : μQ.colLen 0 ≥ 1) (sym : DRCSymbol) :
    (Finset.univ.filter fun σ : PBPSet .Bminus ⊥ μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym).card =
    Fintype.card {d : DSeq (μQ.colLen 0) //
      d.val ⟨μQ.colLen 0 - 1, by omega⟩ = sym} := by
  rw [show (Finset.univ.filter fun σ : PBPSet .Bminus ⊥ μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym).card =
      Fintype.card {σ : PBPSet .Bminus ⊥ μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = sym} from
    (Fintype.card_subtype _).symm]
  apply Fintype.card_congr
  refine {
    toFun := fun σ => ⟨PBPSet_Bminus_bot_to_DSeq σ.val, ?_⟩
    invFun := fun d => ⟨DSeq_to_PBP_Bminus hsc d.val, ?_⟩
    left_inv := fun σ => by
      apply Subtype.ext; exact DSeq_roundtrip_left hsc σ.val
    right_inv := fun d => by
      apply Subtype.ext; exact DSeq_roundtrip_right hsc d.val
  }
  · simp only [PBPSet_Bminus_bot_to_DSeq]
    exact σ.prop
  · have hi : μQ.colLen 0 - 1 < μQ.colLen 0 := by omega
    show mkQpaint μQ d.val (μQ.colLen 0 - 1) 0 = sym
    rw [mkQpaint_col0 hi]
    exact d.prop

/-- Singleton helper: B⁻ PBPs with Q_bot = d count is c₁ = μQ.colLen 0 = r₁/2. -/
private theorem singleton_case_B_Bminus_Qbot_d (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : ∀ r ∈ [r₁], Even r)
    (hpos : ∀ r ∈ [r₁], 0 < r) :
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card = μQ.colLen 0 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  have hr₁ : r₁ > 0 := hpos r₁ (List.mem_singleton.mpr rfl)
  have hr₁_even : Even r₁ := heven r₁ (List.mem_singleton.mpr rfl)
  have hsc := dpartColLensQ_B_singleton_singleCol hQ hr₁
  have hk_eq : μQ.colLen 0 = r₁ / 2 := dpartColLensQ_B_singleton_colLen0 hQ hr₁
  have hk_pos : μQ.colLen 0 ≥ 1 := by
    rw [hk_eq]; obtain ⟨m, rfl⟩ := hr₁_even; omega
  rw [card_Bminus_Qbot_eq_DSeq_last hsc hk_pos .d]
  exact card_DSeq_last_d hk_pos

/-- Singleton helper: B⁻ PBPs with Q_bot = r count is c₁ = μQ.colLen 0 = r₁/2. -/
private theorem singleton_case_B_Bminus_Qbot_r (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : ∀ r ∈ [r₁], Even r)
    (hpos : ∀ r ∈ [r₁], 0 < r) :
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card = μQ.colLen 0 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  have hr₁ : r₁ > 0 := hpos r₁ (List.mem_singleton.mpr rfl)
  have hr₁_even : Even r₁ := heven r₁ (List.mem_singleton.mpr rfl)
  have hsc := dpartColLensQ_B_singleton_singleCol hQ hr₁
  have hk_eq : μQ.colLen 0 = r₁ / 2 := dpartColLensQ_B_singleton_colLen0 hQ hr₁
  have hk_pos : μQ.colLen 0 ≥ 1 := by
    rw [hk_eq]; obtain ⟨m, rfl⟩ := hr₁_even; omega
  rw [card_Bminus_Qbot_eq_DSeq_last hsc hk_pos .r]
  exact card_DSeq_last_r hk_pos

/-- Singleton helper: A1 for dp = [r₁]. -/
private theorem singleton_case_B_DD_alpha (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : ∀ r ∈ [r₁], Even r)
    (hpos : ∀ r ∈ [r₁], 0 < r) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      (countPBP_B [r₁]).1 := by
  have hr₁ : r₁ > 0 := hpos r₁ (List.mem_singleton.mpr rfl)
  have hr₁_even : Even r₁ := heven r₁ (List.mem_singleton.mpr rfl)
  have hk_eq : μQ.colLen 0 = r₁ / 2 := dpartColLensQ_B_singleton_colLen0 hQ hr₁
  have hc₁_ge : r₁ / 2 ≥ 1 := by obtain ⟨m, rfl⟩ := hr₁_even; omega
  -- Use γ-swap to reduce B⁺ count to B⁻ count.
  rw [card_Bplus_Qbot_d_eq_Bminus_Qbot_d]
  rw [singleton_case_B_Bminus_Qbot_d r₁ hP hQ heven hpos]
  -- Goal: μQ.colLen 0 + μQ.colLen 0 = (countPBP_B [r₁]).1
  -- = 2 * (if c₁ ≥ 1 then nu (c₁ - 1) else 0) = 2 * c₁ when c₁ ≥ 1
  simp only [countPBP_B, hc₁_ge, ite_true, nu]
  rw [hk_eq]
  omega

/-- Singleton helper: A2 for dp = [r₁]. -/
private theorem singleton_case_B_RC_alpha (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : ∀ r ∈ [r₁], Even r)
    (hpos : ∀ r ∈ [r₁], 0 < r) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card =
      (countPBP_B [r₁]).2.1 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  have hr₁ : r₁ > 0 := hpos r₁ (List.mem_singleton.mpr rfl)
  have hr₁_even : Even r₁ := heven r₁ (List.mem_singleton.mpr rfl)
  have hsc := dpartColLensQ_B_singleton_singleCol hQ hr₁
  have hk_eq : μQ.colLen 0 = r₁ / 2 := dpartColLensQ_B_singleton_colLen0 hQ hr₁
  have hc₁_ge : r₁ / 2 ≥ 1 := by obtain ⟨m, rfl⟩ := hr₁_even; omega
  have hk_pos : μQ.colLen 0 ≥ 1 := by rw [hk_eq]; exact hc₁_ge
  -- Step 1: |B⁺ Q_bot ≠ d| = |B⁺ total| - |B⁺ Q_bot = d|.
  -- |B⁺ total| = 2c₁ + 1 (by card_PBPSet_Bminus_bot_singleCol + γ-swap).
  -- |B⁺ Q_bot = d| = c₁ (by γ-swap and Bminus analysis).
  -- So |B⁺ Q_bot ≠ d| = 2c₁ + 1 - c₁ = c₁ + 1.
  have h_Bp_total : Fintype.card (PBPSet .Bplus ⊥ μQ) = 2 * (μQ.colLen 0) + 1 := by
    rw [card_Bplus_eq_Bminus]
    exact card_PBPSet_Bminus_bot_singleCol hsc
  have h_Bp_d : (Finset.univ.filter fun σ : PBPSet .Bplus ⊥ μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card = μQ.colLen 0 := by
    rw [card_Bplus_Qbot_d_eq_Bminus_Qbot_d]
    exact singleton_case_B_Bminus_Qbot_d r₁ hP hQ heven hpos
  -- |B⁺ total| = |B⁺ Q_bot = d| + |B⁺ Q_bot ≠ d|
  have h_Bp_split : Fintype.card (PBPSet .Bplus ⊥ μQ) =
      (Finset.univ.filter fun σ : PBPSet .Bplus ⊥ μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
      (Finset.univ.filter fun σ : PBPSet .Bplus ⊥ μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card := by
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (p := fun σ : PBPSet .Bplus ⊥ μQ => σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d)]
  have h_Bp_nonD : (Finset.univ.filter fun σ : PBPSet .Bplus ⊥ μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card = μQ.colLen 0 + 1 := by
    have := h_Bp_split
    rw [h_Bp_total, h_Bp_d] at this
    omega
  rw [h_Bp_nonD]
  -- |B⁻ Q_bot = r| = c₁ via singleton_case_B_Bminus_Qbot_r.
  rw [singleton_case_B_Bminus_Qbot_r r₁ hP hQ heven hpos]
  -- Goal: (μQ.colLen 0 + 1) + μQ.colLen 0 = (countPBP_B [r₁]).2.1 = 2c₁ + 1
  simp only [countPBP_B, hc₁_ge, ite_true, nu]
  rw [hk_eq]
  omega

/-- Primitive-case step for α-class DD count.
    |B+ Q=d new| + |B- Q=d new| = (countPBP_B new).1 when new = r₁::r₂::rest is primitive.
    Requires `h_total_rest`: Total(B at shift level) = tripleSum(countPBP_B rest). -/
private theorem card_B_DD_alpha_primitive_step (r₁ r₂ : ℕ) (rest : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (hQ_pos : μQ.colLen 0 > 0)
    (h_prim : r₂ > rest.head?.getD 0)
    (h_total_rest :
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) +
      Fintype.card (PBPSet .Bminus μP.shiftLeft μQ.shiftLeft) =
      tripleSum (countPBP_B rest)) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      (countPBP_B (r₁ :: r₂ :: rest)).1 := by
  -- Setup: compute colLens, shifts, primitivity conditions.
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hr₂_pos : r₂ > 0 := hpos r₂ (by simp)
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  have hQ_pos' : μQ.colLen 0 ≥ 1 := hQ_pos
  have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
  have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
  have hprimP : ∀ j, j ≥ 1 → μP.colLen j < μP.colLen 0 := by
    intro j hj
    have h1 : μP.colLen j ≤ μP.colLen 1 := μP.colLen_anti 1 j (by omega)
    suffices hsuff : μP.colLen 1 < μP.colLen 0 from lt_of_le_of_lt h1 hsuff
    rw [← YoungDiagram.colLen_shiftLeft, hP0]
    by_cases hemp : μP.shiftLeft.colLens = []
    · have hrl : μP.shiftLeft.rowLen 0 = 0 := by
        rw [← YoungDiagram.length_colLens]; simp [hemp]
      have : μP.shiftLeft.colLen 0 = 0 := by
        by_contra hne; push_neg at hne
        have : 0 < μP.shiftLeft.colLen 0 := Nat.pos_of_ne_zero hne
        have hmem := YoungDiagram.mem_iff_lt_colLen.mpr this
        have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
        omega
      omega
    · obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil (by exact hemp)
      have h0 : μP.shiftLeft.colLen 0 = hd :=
        colLen_0_eq_of_colLens_cons heq
      rw [h0]
      have heq' := hP_sh.symm.trans heq
      match rest, heq' with
      | r₃ :: r₄ :: rest', heq'' =>
        simp only [dpartColLensP_B] at heq''
        have hhd : r₄ / 2 = hd := (List.cons.inj heq'').1
        rw [← hhd, hb]
        have hr₃_lt : r₃ < r₂ := by
          have : r₂ > (r₃ :: r₄ :: rest').head?.getD 0 := h_prim
          simp at this; omega
        have hr₄_le_r₃ : r₄ ≤ r₃ := by
          have : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
          have := @this ⟨2, by simp⟩ ⟨3, by simp⟩ (by simp)
          simp at this; exact this
        have heven₄ := heven r₄ (by simp)
        obtain ⟨d, hd⟩ := heven₄; rw [hd]; omega
      | [r₃], heq'' =>
        simp [dpartColLensP_B] at heq''
      | [], heq'' =>
        simp [dpartColLensP_B] at heq''
  have hprimQ : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 - 1 := by
    intro j hj
    have h1 : μQ.colLen j ≤ μQ.colLen 1 := μQ.colLen_anti 1 j (by omega)
    suffices hsuff : μQ.colLen 1 ≤ μP.colLen 0 - 1 from le_trans h1 hsuff
    rw [← YoungDiagram.colLen_shiftLeft, hP0]
    by_cases hemq : μQ.shiftLeft.colLens = []
    · have hrl : μQ.shiftLeft.rowLen 0 = 0 := by
        rw [← YoungDiagram.length_colLens]; simp [hemq]
      have : μQ.shiftLeft.colLen 0 = 0 := by
        by_contra hne; push_neg at hne
        have : 0 < μQ.shiftLeft.colLen 0 := Nat.pos_of_ne_zero hne
        have hmem := YoungDiagram.mem_iff_lt_colLen.mpr this
        have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
        omega
      omega
    · obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil (by exact hemq)
      have h0 : μQ.shiftLeft.colLen 0 = hd :=
        colLen_0_eq_of_colLens_cons heq
      rw [h0]
      have heq' := hQ_sh.symm.trans heq
      match rest, heq' with
      | r₃ :: r₄ :: rest', heq'' =>
        simp only [dpartColLensQ_B] at heq''
        have hhd : r₃ / 2 = hd := (List.cons.inj heq'').1
        rw [← hhd, hb]
        have hr₃_lt : r₃ < r₂ := by
          have : r₂ > (r₃ :: r₄ :: rest').head?.getD 0 := h_prim
          simp at this; omega
        have heven₃ := heven r₃ (by simp)
        obtain ⟨c, hc⟩ := heven₃; rw [hc]; omega
      | [r₃], heq'' =>
        simp only [dpartColLensQ_B] at heq''
        by_cases hr₃ : r₃ > 0
        · rw [if_pos hr₃] at heq''
          have hhd : r₃ / 2 = hd := (List.cons.inj heq'').1
          rw [← hhd, hb]
          have hr₃_lt : r₃ < r₂ := by simp at h_prim; exact h_prim
          have heven₃ := heven r₃ (by simp)
          obtain ⟨c, hc⟩ := heven₃; rw [hc]; omega
        · rw [if_neg (by omega)] at heq''; exact absurd heq'' (List.cons_ne_nil _ _).symm
      | [], heq'' =>
        simp [dpartColLensQ_B] at heq''
  -- k = Q.colLen(0) - P.colLen(0) + 1 = r₁/2 - r₂/2 + 1
  set k := (r₁ - r₂) / 2 + 1 with hk_def
  have hk_pos : k ≥ 1 := by rw [hk_def]; omega
  have hk_eq : k = μQ.colLen 0 - μP.colLen 0 + 1 := by
    rw [hk_def, hP0, hQ0]
    have heven₁ := heven r₁ (by simp)
    obtain ⟨a, ha⟩ := heven₁
    rw [ha, hb]; omega
  -- Convert filter.card to Fintype.card subtype.
  rw [show (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bplus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm,
    show (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bminus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm]
  -- γ-swap: B- count equals B+ count.
  have h_swap := card_Bplus_Qbot_d_eq_Bminus_Qbot_d μP μQ
  rw [show (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bplus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm,
    show (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      Fintype.card {σ : PBPSet .Bminus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d} from
    (Fintype.card_subtype _).symm] at h_swap
  rw [← h_swap]
  -- Apply primitive_step_top_Q for top Q = .d.
  rw [card_PBPSet_Bplus_primitive_step_top_Q hle hP_pos hQ_pos' hprimP hprimQ .d]
  rw [validCol0_B_card_top_d _ _ hle k hk_eq hk_pos]
  -- Now: |B+shift| * (2k-1) + |B+shift| * (2k-1) = (countPBP_B (r₁::r₂::rest)).1
  -- Use γ-swap at shift: |B+ shift| = |B- shift|.
  have h_sh_sym := card_Bplus_eq_Bminus μP.shiftLeft μQ.shiftLeft
  have h_total_sh : 2 * Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) =
      tripleSum (countPBP_B rest) := by
    rw [← h_total_rest, h_sh_sym]; ring
  -- Unfold countPBP_B primitive manually.
  have h_unfold : (countPBP_B (r₁ :: r₂ :: rest)).1 = tripleSum (countPBP_B rest) * (2 * k - 1) := by
    show (countPBP_B (r₁ :: r₂ :: rest)).1 = _
    simp only [countPBP_B, h_prim, ite_true]
    rcases h_ct : countPBP_B rest with ⟨dd', rc', ss'⟩
    simp only [tripleSum]
    rw [show (tailCoeffs ((r₁ - r₂) / 2 + 1)).1.1 = 2 * ((r₁ - r₂) / 2 + 1) - 1 from
      tailCoeffs_tDD _ (by omega)]
  rw [h_unfold]
  -- Goal: |B+shift| * (2k-1) + |B+shift| * (2k-1) = Total(rest) * (2k-1)
  -- Use h_total_sh: 2 * |B+shift| = Total(rest).
  rw [← h_total_sh]; ring

/-- **α-class DD count**: combined B⁺ ∪ B⁻ PBPs with Q column 0 bottom = d
    equals `countPBP_B(dp).1`.

    Structural induction on dp:
    - Empty: hQ_pos false (vacuous, closed).
    - Singleton: closed via `singleton_case_B_DD_alpha` (γ-swap + DSeq enumeration).
    - Inductive:
      - Primitive (r₂ > rest.head?.getD 0): closed via
        `card_B_DD_alpha_primitive_step`, supplying `h_total_rest` derived
        from `h_total` (Total at the current level) through the primitive-step
        identity `card_PBPSet_B_primitive_step`.
      - Balanced (r₂ ≤ rest.head?.getD 0): admitted as scoped sorry; requires
        per-Q_bot-class fiber refinement to relate `new Q_bot = d` to the
        per-sub-class counts (`dd'`, `rc'`).

    Takes `h_total` as hypothesis (Total at the current level) so the primitive
    inductive case can derive the shift-level Total needed for
    `card_B_DD_alpha_primitive_step`. This creates a harmless joint induction
    with `card_PBPSet_B_eq_tripleSum_countPBP_B`: A1(new, primitive) needs
    Total(rest); Total(new, balanced) needs A1(rest). -/
private theorem card_B_DD_alpha_eq_countB_dd (dp : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r)
    (hQ_pos : μQ.colLen 0 > 0)
    (h_total :
      Fintype.card (PBPSet .Bplus μP μQ) +
      Fintype.card (PBPSet .Bminus μP μQ) =
      tripleSum (countPBP_B dp)) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      (countPBP_B dp).1 := by
  match dp, hP, hQ, hsort, heven, hpos, hQ_pos, h_total with
  | [], _, hQ, _, _, _, hQ_pos, _ =>
    have hQ_bot : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    exfalso
    rw [hQ_bot] at hQ_pos
    have : ¬ (⊥ : YoungDiagram).colLen 0 > 0 := by
      intro h
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr h
      simp at hmem
    exact this hQ_pos
  | [r₁], hP, hQ, _, heven, hpos, _, _ =>
    exact singleton_case_B_DD_alpha r₁ hP hQ heven hpos
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos, hQ_pos, h_total =>
    -- Inductive case: split into primitive (r₂ > r₃) and balanced (r₂ ≤ r₃).
    by_cases h_prim : r₂ > rest.head?.getD 0
    · -- Primitive branch: derive h_total_rest from h_total and apply primitive step.
      have h_prim_step :
          Fintype.card (PBPSet .Bplus μP μQ) +
          Fintype.card (PBPSet .Bminus μP μQ) =
          (Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) +
           Fintype.card (PBPSet .Bminus μP.shiftLeft μQ.shiftLeft)) *
          tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 :=
        card_PBPSet_B_primitive_step r₁ r₂ rest μP μQ hP hQ hsort heven h_prim
      -- Compute tripleSum (tailCoeffs k).1 = 4k, with k ≥ 1.
      have hk_pos : (r₁ - r₂) / 2 + 1 ≥ 1 := by omega
      have h_ts := tripleSum_tailCoeffs_fst_eq ((r₁ - r₂) / 2 + 1) hk_pos
      -- countPBP_B (r₁::r₂::rest) primitive unfold and tripleSum:
      -- tripleSum(countPBP_B (r₁::r₂::rest)) = tripleSum(countPBP_B rest) * 4k.
      have h_unfold :
          tripleSum (countPBP_B (r₁ :: r₂ :: rest)) =
          tripleSum (countPBP_B rest) *
          tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
        simp only [countPBP_B, h_prim, ite_true]
        rcases h_ct : countPBP_B rest with ⟨dd', rc', ss'⟩
        simp only [tripleSum, tailCoeffs, nu]
        split <;> ring
      -- Combine: (|B+sh|+|B-sh|) * 4k = tripleSum(countPBP_B rest) * 4k.
      have h_eq :
          (Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) +
           Fintype.card (PBPSet .Bminus μP.shiftLeft μQ.shiftLeft)) *
          tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 =
          tripleSum (countPBP_B rest) *
          tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
        rw [← h_prim_step, h_total, h_unfold]
      -- Cancel the common factor 4k > 0.
      have h_ts_pos : tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 > 0 := by
        rw [h_ts]; omega
      have h_total_rest :
          Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) +
          Fintype.card (PBPSet .Bminus μP.shiftLeft μQ.shiftLeft) =
          tripleSum (countPBP_B rest) :=
        Nat.eq_of_mul_eq_mul_right h_ts_pos h_eq
      -- Apply the primitive step lemma.
      exact card_B_DD_alpha_primitive_step r₁ r₂ rest hP hQ hsort heven hpos hQ_pos
        h_prim h_total_rest
    · -- Balanced case: requires per-Q_bot-class fiber refinement to relate
      -- `new Q_bot = d` count to the per-sub-class counts `dd'` and `rc'`.
      --
      -- Target: A1_new = dd' · tDD + rc' · scDD, where
      --   tDD = ν(k-1) + [k≥2→ν(k-2)]  (balanced tail coefficient, sub.Q=d class)
      --   scDD = 2 · [k≥2→ν(k-2)]      (balanced sub-correction, sub.Q=r class)
      --
      -- **Required infrastructure** (not yet built):
      --   * `fiber_alpha_dd_count_bal_Qd σ : |{τ ∈ fiber(σ) | τ.new_Q_bot = .d}| = tDD`
      --     when σ.Q_bot = .d in the balanced case.
      --   * `fiber_alpha_dd_count_bal_Qr σ : |{τ ∈ fiber(σ) | τ.new_Q_bot = .d}| = scDD`
      --     when σ.Q_bot = .r in the balanced case.
      --   * `fiber_alpha_dd_count_bal_Qlow σ : |{τ ∈ fiber(σ) | τ.new_Q_bot = .d}| = 0`
      --     when σ.Q_bot.layerOrd ≤ 1 (Qlow) in the balanced case.
      -- Then A1_new sum decomposes by σ.Q_bot class (parallel to
      -- `card_B_bal_grouped_fiber`) and gives dd'·tDD + rc'·scDD (using
      -- A1(rest) and RC-class partition derivation).
      --
      -- Blocker: fiber-α refinement requires a `ValidCol0_B_bal_α` subtype
      -- keyed on τ.new_Q_bot, parallel to existing `ValidCol0_B_Qr`/
      -- `ValidCol0_B_Qlow` (which are keyed on σ.Q_bot).
      --
      -- **Status**: admitted as bare sorry until fiber-α refinement is built.
      -- Numerically verified via `tools/verify_all_B_lemmas.py` (82 dp cases).
      sorry

/-- Singleton case helper for `card_B_SS_alpha_eq_countB_ss`.
    For dp = [r₁] with r₁ > 0 Even, the B⁻ PBPs over (⊥, μQ) are in bijection
    with DSeq(μQ.colLen 0) (single-column Q). The filter {σ | Q col-0 bottom
    has layerOrd ≤ 1} corresponds to DSeqs whose last entry has layerOrd ≤ 1.
    Since DSeq entries are in {s, r, d} (layerOrds 1, 2, 4), monotonicity
    forces all entries to be s. Count = 1 = (countPBP_B [r₁]).2.2. -/
private theorem singleton_case_B_SS_alpha (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B [r₁])
    (hQ : μQ.colLens = dpartColLensQ_B [r₁])
    (heven : ∀ r ∈ [r₁], Even r)
    (hpos : ∀ r ∈ [r₁], 0 < r) :
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
      (countPBP_B [r₁]).2.2 := by
  -- Reduce μP = ⊥.
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  -- r₁ > 0 and Even r₁, hence r₁ ≥ 2, so μQ.colLen 0 = r₁/2 ≥ 1.
  have hr₁ : r₁ > 0 := hpos r₁ (List.mem_singleton.mpr rfl)
  have hr₁_even : Even r₁ := heven r₁ (List.mem_singleton.mpr rfl)
  have hr₁_ge_two : r₁ ≥ 2 := by
    obtain ⟨m, rfl⟩ := hr₁_even; omega
  -- Single-column Q description.
  have hsc := dpartColLensQ_B_singleton_singleCol hQ hr₁
  have hk_eq : μQ.colLen 0 = r₁ / 2 := dpartColLensQ_B_singleton_colLen0 hQ hr₁
  have hk_pos : μQ.colLen 0 ≥ 1 := by rw [hk_eq]; omega
  -- (countPBP_B [r₁]).2.2 = 1.
  show _ = 1
  -- Convert filter.card to Fintype.card subtype.
  rw [show (Finset.univ.filter fun σ : PBPSet .Bminus ⊥ μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
      Fintype.card {σ : PBPSet .Bminus ⊥ μQ //
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1} from
    (Fintype.card_subtype _).symm]
  -- Transfer through the equiv PBPSet .Bminus ⊥ μQ ≃ DSeq (μQ.colLen 0).
  -- The predicate σ.val.Q.paint (k-1) 0 corresponds to (d.val ⟨k-1, _⟩) under
  -- the forward map PBPSet_Bminus_bot_to_DSeq.
  have key : Fintype.card {σ : PBPSet .Bminus ⊥ μQ //
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1} =
      Fintype.card {d : DSeq (μQ.colLen 0) //
        (d.val ⟨μQ.colLen 0 - 1, by omega⟩).layerOrd ≤ 1} := by
    apply Fintype.card_congr
    refine {
      toFun := fun σ => ⟨PBPSet_Bminus_bot_to_DSeq σ.val, ?_⟩
      invFun := fun d => ⟨DSeq_to_PBP_Bminus hsc d.val, ?_⟩
      left_inv := fun σ => by
        apply Subtype.ext; exact DSeq_roundtrip_left hsc σ.val
      right_inv := fun d => by
        apply Subtype.ext; exact DSeq_roundtrip_right hsc d.val
    }
    · -- Forward direction on predicate.
      simp only [PBPSet_Bminus_bot_to_DSeq]
      exact σ.prop
    · -- Backward direction on predicate.
      have hi : μQ.colLen 0 - 1 < μQ.colLen 0 := by omega
      show (mkQpaint μQ d.val (μQ.colLen 0 - 1) 0).layerOrd ≤ 1
      rw [mkQpaint_col0 hi]
      exact d.prop
  rw [key]
  -- Now goal: card {d : DSeq k // (d.val ⟨k-1, _⟩).layerOrd ≤ 1} = 1.
  -- Unique such d: the constant s function.
  rw [Fintype.card_eq_one_iff]
  -- Build witness: constant s DSeq.
  refine ⟨⟨⟨fun _ => DRCSymbol.s,
    ⟨fun _ => Or.inl rfl,
     fun _ _ _ => le_refl _,
     fun _ _ hi _ => by simp at hi⟩⟩, ?_⟩, ?_⟩
  · -- The witness satisfies v (k-1) has layerOrd ≤ 1.
    simp [DRCSymbol.layerOrd]
  · -- Uniqueness.
    rintro ⟨⟨v, hv_srd, hv_mono, hv_d⟩, hv_last⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    -- Need v i = s. We know v i ∈ {s, r, d} and v (k-1) has layerOrd ≤ 1.
    -- By mono, v i.layerOrd ≤ v (k-1).layerOrd ≤ 1.
    -- Since v i ∈ {s, r, d} (layerOrds 1, 2, 4), only s has layerOrd ≤ 1.
    have hi : i.val ≤ μQ.colLen 0 - 1 := by
      have := i.isLt; omega
    have hmono := hv_mono i ⟨μQ.colLen 0 - 1, by omega⟩ hi
    have hle : (v i).layerOrd ≤ 1 := le_trans hmono hv_last
    rcases hv_srd i with h | h | h
    · exact h
    · rw [h] at hle; simp [DRCSymbol.layerOrd] at hle
    · rw [h] at hle; simp [DRCSymbol.layerOrd] at hle

/-- **α-class SS count**: B⁻ PBPs with Q column 0 bottom ∈ {•, s}
    (i.e., layerOrd ≤ 1) equals `countPBP_B(dp).2.2`.
    This is the "tail-s ⟹ γ=B⁻" identity.
    Used by Prop10_8_M.lean's `card_Bminus_bottom_lo_le_one_eq_ss` for M balanced.

    Proof by induction on dp:
    - Empty: vacuous (hQ_pos requires μQ.colLen 0 > 0, but μQ = ⊥ has 0).
    - Singleton + Inductive: sub-sorry for fiber refinement. -/
theorem card_B_SS_alpha_eq_countB_ss (dp : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r)
    (hQ_pos : μQ.colLen 0 > 0) :
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
      (countPBP_B dp).2.2 := by
  match dp, hP, hQ, hsort, heven, hpos, hQ_pos with
  | [], _, hQ, _, _, _, hQ_pos =>
    -- Empty case: vacuous (μQ = ⊥ has colLen 0 = 0, contradicting hQ_pos).
    have hQ_bot : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    exfalso
    rw [hQ_bot] at hQ_pos
    -- μQ.colLen 0 = 0 for μQ = ⊥, so hQ_pos : 0 < 0 is false.
    have : ¬ (⊥ : YoungDiagram).colLen 0 > 0 := by
      intro h
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr h
      simp at hmem
    exact this hQ_pos
  | [r₁], hP, hQ, _, heven, hpos, _ =>
    -- Singleton case: direct computation via DSeq enumeration.
    exact singleton_case_B_SS_alpha r₁ hP hQ heven hpos
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos, hQ_pos =>
    -- Inductive case: split into primitive (r₂ > r₃) and balanced (r₂ ≤ r₃).
    -- In both cases, need refined fiber analysis: per sub-PBP σ, determine how many
    -- of the variable-size new fibers have new Q_bot.lo ≤ 1 (i.e., ∈ {•, s}).
    --
    -- Primitive: per sub has 4k fibers; `tSS = 1` of them has Q_bot.lo≤1 (specifically
    --            the all-s fiber). So ss_new = total_rest · 1 = total_rest.
    -- Balanced: `ss_new = dd' · tSS + rc' · scSS = dd' · 1 + rc' · 1 = dd' + rc'`.
    --
    -- Both cases require the lo≤1-class fiber-α lemma (parallel to Phase 3's
    -- `fiber_card_B_bal_Qlow` but refining to new-level Q_bot.lo≤1):
    --   * `fiber_alpha_ss_count_primitive σ : |{τ ∈ fiber(σ) | τ.new_Q_bot.lo ≤ 1}| = 1`
    --   * `fiber_alpha_ss_count_balanced σ : depends on σ.Q_bot class`
    --
    -- Cannot be derived from Total + A1 + A2 + γ-swap alone (A2 circularly depends on A3).
    -- **Status**: admitted as bare sorry until fiber-α refinement infrastructure
    -- is built. Numerically verified for 82 dp cases via `tools/verify_countB_components.py`.
    sorry

/-- **γ-swap SS symmetry**: B⁺ and B⁻ have the same number of PBPs with
    Q column 0 bottom ∈ {•, s}. The swap `swapBplusBminus` preserves P and Q,
    so the Q_bot predicate is invariant under swap.

    Proof: build an Equiv between the filtered subtypes via `swapBplusBminus`. -/
private theorem card_Bplus_SS_eq_Bminus_SS (μP μQ : YoungDiagram) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card := by
  -- Convert filter.card to subtype card
  rw [show (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
      Fintype.card {σ : PBPSet .Bplus μP μQ //
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1} from
    (Fintype.card_subtype _).symm]
  rw [show (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card =
      Fintype.card {σ : PBPSet .Bminus μP μQ //
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1} from
    (Fintype.card_subtype _).symm]
  -- Construct the Equiv via swapBplusBminus
  apply Fintype.card_congr
  refine {
    toFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inl σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    invFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inr σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    left_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
    right_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
  }

/-! ### Per-class fiber sizes for balanced step

In the balanced case (r₂ ≤ r₃), each sub-PBP σ at rest level has a fiber at the new
level whose size depends on `σ.Q_bot` (the top entry of Q col 0):

| σ.Q_bot class     | fiber size |
|-------------------|------------|
| .d (layerOrd 4)   | 4k         |
| .r (layerOrd 2)   | 4k - 2     |
| .lo ≤ 1 ({•, s})  | 2k - 1     |

where k = (r₁ - r₂) / 2 + 1. These are empirically verified for all tested dp cases
(`tools/verify_all_B_lemmas.py`, 82 cases). See blueprint
`lean/docs/blueprints/B_balanced_fiber_structure.md`.

Building each per-class fiber lemma requires a `ValidCol0_B_balanced` refinement
of the primitive case's `ValidCol0_B`, parameterized by the boundary Q_bot value.
The primitive case's infrastructure (lines 885-1930) is ~700 lines; the balanced
refinement would be of comparable size.

**Status**: Per-class fiber lemmas admitted as focused axioms
(`fiber_card_B_bal_Qd`, `fiber_card_B_bal_Qr`, `fiber_card_B_bal_Qlow`).
The Phase 3 aggregate theorem `card_B_bal_grouped_fiber` is DERIVED from these
three fiber lemmas via combinatorial decomposition (Finset.sum split by Q_bot class).
-/

/-- **γ-swap for Q_bot = r**: B⁺ and B⁻ have the same count of PBPs with `Q_bot = r`.
    Mirrors `card_Bplus_Qbot_d_eq_Bminus_Qbot_d`; proof is identical modulo the
    predicate. -/
private theorem card_Bplus_Qbot_r_eq_Bminus_Qbot_r (μP μQ : YoungDiagram) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card =
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card := by
  rw [show (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card =
      Fintype.card {σ : PBPSet .Bplus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r} from
    (Fintype.card_subtype _).symm]
  rw [show (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card =
      Fintype.card {σ : PBPSet .Bminus μP μQ //
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r} from
    (Fintype.card_subtype _).symm]
  apply Fintype.card_congr
  refine {
    toFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inl σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    invFun := fun σ => ⟨⟨σ.val.val.swapBplusBminus (Or.inr σ.val.prop.1),
        by simp [PBP.swapBplusBminus, σ.val.prop.1],
        σ.val.prop.2.1, σ.val.prop.2.2⟩, σ.prop⟩
    left_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
    right_inv := fun σ => by
      apply Subtype.ext; apply Subtype.ext
      apply PBP_eq_of_data
      · simp [PBP.swapBplusBminus, σ.val.prop.1]
      · simp [PBP.swapBplusBminus]
      · simp [PBP.swapBplusBminus]
  }

/-! ### Balanced case fiber closure path

In balanced (r₂ ≤ r₃), the primitive lemma `fiber_card_B_primitive` does NOT apply:
its hypothesis `hprimQ : ∀ j ≥ 1, μQ.colLen j ≤ μP.colLen 0 - 1` is FALSE because
μQ.shiftLeft.colLen 0 = r₃/2 ≥ r₂/2 = μP.colLen 0.

The closure path for each Qd/Qr/Qlow lemma requires:

**Step 1**: Define `ValidCol0_B_bal (σ) (Q_bot)` = a subtype of `ValidCol0_B hP hQ`
  (where hP = μP.colLen 0 = r₂/2, hQ = μQ.colLen 0 = r₁/2), whose elements `v`
  also satisfy mono_Q against σ's col 0 in the overlap region:
    ∀ i < min(hP, σ.Q.colLen 0), (liftCol0Q_B hP hQ v i).layerOrd ≤ σ.Q.paint i 0.layerOrd

**Step 2**: Prove fiber ≤ ValidCol0_B_bal via col-0 extraction + mono_Q on τ.
  Requires showing that for any τ ∈ fiber(σ), the extracted v satisfies the
  balanced admissibility (from τ.mono_Q applied to new col 0 vs col 1 = σ.col 0).

**Step 3**: Prove ValidCol0_B_bal ≤ fiber via a balanced lift construction
  `liftPBP_B_bal σ v (h_adm : admissible)`. Parallel to `liftPBP_B` but uses
  h_adm to handle mono_Q between col 0 and col 1. Also needs row_s, row_r
  handling: in balanced case, non-dot rows in Q col 0 CAN overlap with col ≥ 1,
  so `row_s` (equal non-dot rows must have equal j's) may fire. Requires
  additional constraints: if σ.Q(i, 0) = .s, then v's col 0 at row i must NOT be .s
  (since v.Q(i, 0) = σ.Q(i, 0) = .s would contradict row_s). Similarly for .r.
  These row_s/row_r constraints further restrict ValidCol0_B_bal.

**Step 4**: Count |ValidCol0_B_bal (σ) (Q_bot)| by Q_bot trichotomy:
  - Q_bot = d: max layerOrd cap, row_s/row_r trivially satisfied (no s/r below d
    row by mono). Count = 4k. Admissibility vacuous for rows below d.
  - Q_bot = r: cap layerOrd at 2 for overlap rows. Count = 4k - 2 (2 exclusions:
    d and c at the boundary row).
  - Q_bot ∈ {•, s}: heavy cap (layerOrd ≤ 1). Count = 2k - 1.

The DSeq enumeration machinery at lines ~2150-2500 (`DSeq_sr`, `DSeq_srd`, `DSeq_last_s_eq`,
etc.) would be extended with `DSeq_bal_{d,r,low}` variants tracking admissibility.

Each lemma requires ~500 lines; full Phase 3 infrastructure ~1500 lines total.
Parallels the primitive case's ~650-line infrastructure at lines 880-1930.

Status: all three lemmas admitted as focused sorries. Numerically verified for
all 82 dp cases up to size 24 via `tools/verify_all_B_lemmas.py`.
-/

/-! ### Qd balanced case: key helper lemmas

These helper lemmas encode the key insight: when `σ.Q_bot = d` and
`σ.Q.colLen 0 = μP.colLen 0` (which holds in balanced case, since
`r₂ = r₃` by SortedGE + balanced), then:
- `σ.Q(hP-1, j) = .d` for all j with `(hP-1, j) ∈ σ.Q.shape`
- `σ.P(hP-1, j) = .c` for all j with `(hP-1, j) ∈ σ.P.shape` (assuming shape inclusion)

These make the lift's mono_P, mono_Q, row_s, row_r constraints discharge
in balanced case without needing `hprimQ` / `hprimP`. -/

/-- Given σ with Q_bot = d at row `hQ_σ - 1 = μP.colLen 0 - 1` (true in balanced),
    by σ.mono_Q, σ.Q(hP-1, j) = d for any j with (hP-1, j) ∈ σ.Q.shape. -/
private theorem sigma_Q_eq_d_of_Qbot_d_bal {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d)
    (j : ℕ) (hmem : (μP.colLen 0 - 1, j) ∈ σ.val.Q.shape) :
    σ.val.Q.paint (μP.colLen 0 - 1) j = .d := by
  -- First: rewrite h_Qd to row (μP.colLen 0 - 1)
  have h_Qd' : σ.val.Q.paint (μP.colLen 0 - 1) 0 = .d := by
    rw [← h_hQσ_eq]; exact h_Qd
  -- σ.mono_Q: σ.Q(hP-1, 0).layerOrd ≤ σ.Q(hP-1, j).layerOrd (since 0 ≤ j, same row)
  have hmono := σ.val.mono_Q (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) j le_rfl (Nat.zero_le _) hmem
  rw [h_Qd'] at hmono
  -- layerOrd(d) = 4, and Q ∈ {•, s, r, d} for B+, layerOrds ∈ {0, 1, 2, 4}
  have hsym := σ.val.sym_Q (μP.colLen 0 - 1) j hmem
  rw [σ.prop.1] at hsym
  simp [DRCSymbol.allowed] at hsym
  rcases hsym with h | h | h | h
  · rw [h] at hmono; simp [DRCSymbol.layerOrd] at hmono
  · rw [h] at hmono; simp [DRCSymbol.layerOrd] at hmono
  · rw [h] at hmono; simp [DRCSymbol.layerOrd] at hmono
  · exact h

/-- List-level helper: for a SortedGE list `dp`, `dpartColLensP_B dp` is pointwise
    ≤ `dpartColLensQ_B dp` at each index. -/
private theorem dpartColLens_P_le_Q : ∀ (dp : DualPart), dp.SortedGE → ∀ (j : ℕ),
    (dpartColLensP_B dp).getD j 0 ≤ (dpartColLensQ_B dp).getD j 0
  | [], _, j => by simp [dpartColLensP_B, dpartColLensQ_B]
  | [_], _, j => by simp [dpartColLensP_B, dpartColLensQ_B]
  | r₁ :: r₂ :: rest', hsort, j => by
    simp only [dpartColLensP_B, dpartColLensQ_B]
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      have h12 : r₁ ≥ r₂ := by
        have : Antitone (r₁ :: r₂ :: rest').get := hsort
        have := @this ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp)
        simp at this; exact this
      exact Nat.div_le_div_right h12
    | succ j' =>
      simp only [List.getD_cons_succ]
      exact dpartColLens_P_le_Q rest' (sorted_tail₂ hsort) j'

/-- `colLen j = colLens.getD j 0`. -/
private theorem colLen_eq_getD (μ : YoungDiagram) (j : ℕ) :
    μ.colLen j = μ.colLens.getD j 0 := by
  by_cases hj : j < μ.colLens.length
  · -- In-range: colLens[j] = colLen j by getElem_colLens
    have h1 : μ.colLens.getD j 0 = μ.colLens[j] := by
      simp [List.getD, List.getElem?_eq_getElem hj]
    rw [h1]; exact (YoungDiagram.getElem_colLens hj).symm
  · push_neg at hj
    -- Out of range: colLens.getD = 0 by default
    have h1 : μ.colLens.getD j 0 = 0 := by
      simp [List.getD, List.getElem?_eq_none hj]
    rw [h1]
    rw [YoungDiagram.length_colLens] at hj
    by_contra hne
    have hpos : 0 < μ.colLen j := Nat.pos_of_ne_zero hne
    have hmem : (0, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hpos
    have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    omega

/-- Shape inclusion helper: derive `μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j`
    from the B-type dp structure. -/
private theorem sigma_shape_inc_of_dp {r₁ r₂ : ℕ} {rest : DualPart}
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (j : ℕ) : μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j := by
  have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
  have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
  rw [colLen_eq_getD, colLen_eq_getD, hP_sh, hQ_sh]
  exact dpartColLens_P_le_Q rest (sorted_tail₂ hsort) j

/-- Given σ with Q_bot = d at (hP - 1, 0) (via h_hQσ_eq + h_Qd), and P shape
    contains (hP-1, j), then σ.P(hP-1, j) = .c. Assumes shape inclusion
    `σ.P.shape ≤ σ.Q.shape` (provable from dp structure). -/
private theorem sigma_P_eq_c_of_Qbot_d_bal {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d)
    (j : ℕ) (hmemP : (μP.colLen 0 - 1, j) ∈ σ.val.P.shape) :
    σ.val.P.paint (μP.colLen 0 - 1) j = .c := by
  -- First derive (hP-1, j) ∈ σ.Q.shape from shape inclusion
  have hmemQ : (μP.colLen 0 - 1, j) ∈ σ.val.Q.shape := by
    rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen] at hmemP
    rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen]
    exact lt_of_lt_of_le hmemP (h_shape_inc j)
  have hQd := sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j hmemQ
  have hPne : σ.val.P.paint (μP.colLen 0 - 1) j ≠ .dot := by
    intro hPdot
    have := (σ.val.dot_match _ _).mp ⟨hmemP, hPdot⟩
    rw [hQd] at this
    exact DRCSymbol.noConfusion this.2
  exact PBP.P_nonDot_eq_c_of_B σ.val (Or.inl σ.prop.1) _ _ hmemP hPne

/-! ### Qr balanced case: key helper lemmas

When `σ.Q_bot = r` (at (hP-1, 0)) and `σ.Q.colLen 0 = μP.colLen 0` (balanced),
by `σ.mono_Q` + `σ.row_r` + sym_Q, for j ≥ 1 with (hP-1, j) ∈ σ.Q.shape:
  σ.Q(hP-1, j) = .d
(mono_Q gives ≥ r, sym_Q gives ∈ {s,r,d} (nondot, from mono_Q ≥ r excludes s/dot),
 row_r excludes another r, so = d.)
-/

/-- Given σ with Q_bot = r at (hP - 1, 0), for j ≥ 1 with (hP-1, j) ∈ σ.Q.shape,
    σ.Q(hP-1, j) = d. -/
private theorem sigma_Q_eq_d_of_Qbot_r_bal_j_pos {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qr : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r)
    (j : ℕ) (hj : j ≥ 1) (hmem : (μP.colLen 0 - 1, j) ∈ σ.val.Q.shape) :
    σ.val.Q.paint (μP.colLen 0 - 1) j = .d := by
  -- First: rewrite h_Qr to row (μP.colLen 0 - 1)
  have h_Qr' : σ.val.Q.paint (μP.colLen 0 - 1) 0 = .r := by
    rw [← h_hQσ_eq]; exact h_Qr
  -- σ.mono_Q: σ.Q(hP-1, 0).layerOrd ≤ σ.Q(hP-1, j).layerOrd
  have hmono := σ.val.mono_Q (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) j le_rfl (Nat.zero_le _) hmem
  rw [h_Qr'] at hmono
  -- layerOrd(r) = 2, Q ∈ {•, s, r, d} with layerOrds {0, 1, 2, 4}
  have hsym := σ.val.sym_Q (μP.colLen 0 - 1) j hmem
  rw [σ.prop.1] at hsym
  simp [DRCSymbol.allowed] at hsym
  rcases hsym with h | h | h | h
  · rw [h] at hmono; simp [DRCSymbol.layerOrd] at hmono
  · rw [h] at hmono; simp [DRCSymbol.layerOrd] at hmono
  · -- σ.Q(hP-1, j) = r: row_r forces j = 0, but hj says j ≥ 1. Contradiction.
    exfalso
    have := σ.val.row_r (μP.colLen 0 - 1) .R .R 0 j
      (by simp [paintBySide]; exact h_Qr')
      (by simp [paintBySide]; exact h)
    omega
  · exact h

/-! ### Balanced-Qd lift construction

Parallel to `liftPBP_B` (primitive case), but uses:
- `h_hQσ_eq`: μQ.shiftLeft.colLen 0 = μP.colLen 0 (balanced: r₂ = r₃ ⇒ r₃/2 = r₂/2)
- `h_weak`: ∀ j ≥ 1, μQ.colLen j ≤ μP.colLen 0 (balanced weaker than primitive)
- `h_Qd`: σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d

The 5 `hprimQ` uses in the primitive lift become uses of:
- `sigma_Q_eq_d_of_Qbot_d_bal`: σ.Q(hP-1, j) = .d for j in σ.Q.shape
- `sigma_P_eq_c_of_Qbot_d_bal` (indirect): σ.P(hP-1, j) = .c where relevant
-/

/-- B-type lift construction for balanced case with Q_bot = d.
    Parallel to `liftPBP_B` but replaces `hprimQ` with `h_weak` + `h_Qd`,
    and uses `h_shape_inc` + `h_weakP` (instead of `hprimP`) for the mono_P case
    where P col 0 has c at bottom. -/
private noncomputable def liftPBP_B_bal_Qd {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_weakP : ∀ j, j ≥ 1 → μP.colLen j ≤ μP.colLen 0)
    (h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    PBPSet .Bplus μP μQ := by
  have hpoP : ∀ i j, (i, j) ∉ μP → liftPaint_B_P σ.val (μP.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero =>
      simp only [liftPaint_B_P, liftCol0P_B]
      cases v with
      | inl _ => rfl
      | inr _ =>
        split_ifs with hc
        · exfalso; apply hmem; rw [YoungDiagram.mem_iff_lt_colLen]; omega
        · rfl
    | succ j =>
      simp only [liftPaint_B_P]
      exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  have hpoQ : ∀ i j, (i, j) ∉ μQ → liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero =>
      have hi : ¬(i < μQ.colLen 0) := by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega
      unfold liftPaint_B_Q liftCol0Q_B
      cases v with
      | inl _ => simp; intro hp hq; omega
      | inr _ => simp; intro hp hq; omega
    | succ j =>
      simp only [liftPaint_B_Q]
      exact σ.val.Q.paint_outside i j (by
        rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft]; exact hmem)
  refine ⟨⟨.Bplus,
    ⟨μP, liftPaint_B_P σ.val (μP.colLen 0) v, hpoP⟩,
    ⟨μQ, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v, hpoQ⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P =>
    intro i j hmem
    show (liftPaint_B_P σ.val (μP.colLen 0) v i j).allowed .Bplus .L
    cases j with
    | zero =>
      simp only [liftPaint_B_P, liftCol0P_B]
      cases v with
      | inl _ => simp [DRCSymbol.allowed]
      | inr _ => split_ifs <;> simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_P]
      have := σ.val.sym_P i j (by rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
      rw [σ.prop.1] at this; exact this
  case sym_Q =>
    intro i j hmem
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j).allowed .Bplus .R
    cases j with
    | zero =>
      unfold liftPaint_B_Q liftCol0Q_B
      cases v with
      | inl d =>
        simp only
        split_ifs with hc
        · simp [DRCSymbol.allowed]
          rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h]
        · simp [DRCSymbol.allowed]
      | inr d =>
        simp only
        split_ifs with hc
        · simp [DRCSymbol.allowed]
          rcases d.prop.1 ⟨i - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h]
        · simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_Q]
      have := σ.val.sym_Q i j (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
      rw [σ.prop.1] at this; exact this
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        have hi : i < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        cases v with
        | inl d =>
          constructor
          · exact YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hi hle)
          · change liftCol0Q_B _ _ (.inl d) i = .dot
            simp only [liftCol0Q_B]; exact dif_neg (by omega)
        | inr d =>
          simp only [liftPaint_B_P, liftCol0P_B] at hpaint
          split_ifs at hpaint with hc
          push_neg at hc
          refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hi hle), ?_⟩
          change liftCol0Q_B _ _ (.inr d) i = .dot
          simp only [liftCol0Q_B]
          exact dif_neg (by push_neg; intro h1 h2; exact absurd hP_pos (not_lt.mpr (hc (by omega))))
      | succ j =>
        simp only [liftPaint_B_P] at hpaint
        have hmemP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemQ, hQdot⟩ := (σ.val.dot_match i j).mp ⟨hmemP, hpaint⟩
        exact ⟨by rw [σ.prop.2.2] at hmemQ; exact YoungDiagram.mem_shiftLeft.mp hmemQ,
               by simp only [liftPaint_B_Q]; exact hQdot⟩
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        unfold liftPaint_B_Q liftCol0Q_B at hpaint
        have hi : i < μQ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        cases v with
        | inl d =>
          dsimp at hpaint
          split_ifs at hpaint with hc
          · rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at hpaint
          · have hiP : i < μP.colLen 0 := by omega
            exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hiP,
                   by unfold liftPaint_B_P liftCol0P_B; dsimp⟩
        | inr d =>
          dsimp at hpaint
          split_ifs at hpaint with hc
          · rcases d.prop.1 ⟨i - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h] at hpaint
          · have hiP : i < μP.colLen 0 := by
              simp only [not_and, not_lt] at hc
              by_contra hge; push_neg at hge; exact absurd (hc (by omega) hi) (by omega)
            refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr hiP, ?_⟩
            unfold liftPaint_B_P liftCol0P_B; dsimp
            split_ifs with h1
            · exfalso; simp only [not_and, not_lt] at hc; exact absurd (hc (by omega) hi) (by omega)
            · rfl
      | succ j =>
        simp only [liftPaint_B_Q] at hpaint
        have hmemQ : (i, j) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemP, hPdot⟩ := (σ.val.dot_match i j).mpr ⟨hmemQ, hpaint⟩
        exact ⟨by rw [σ.prop.2.1] at hmemP; exact YoungDiagram.mem_shiftLeft.mp hmemP,
               by simp only [liftPaint_B_P]; exact hPdot⟩
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_P σ.val (μP.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_P σ.val (μP.colLen 0) v i₂ j₂).layerOrd
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero =>
        simp only [liftPaint_B_P, liftCol0P_B]
        cases v with
        | inl _ => simp [DRCSymbol.layerOrd]
        | inr _ =>
          split_ifs with hc1 hc2
          · simp [DRCSymbol.layerOrd]
          · exfalso
            have hi₂ : i₂ < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
            exact hc2 ⟨by omega, hc1.2⟩
          · simp [DRCSymbol.layerOrd]
          · simp [DRCSymbol.layerOrd]
      | succ j₂ =>
        simp only [liftPaint_B_P, liftCol0P_B]
        cases v with
        | inl _ => simp [DRCSymbol.layerOrd]
        | inr _ =>
          split_ifs with hc
          · -- i₁ = hP-1, paint = c (layerOrd 3). In balanced case, must show τ.P(i₂, j₂+1) = c.
            -- i₁ = hP-1, i₂ ≥ i₁ = hP-1, (i₂, j₂+1) ∈ μP with μP.colLen(j₂+1) ≤ hP.
            -- So i₂ < hP. Combined with i₂ ≥ hP-1, we get i₂ = hP-1.
            have h₂mem : i₂ < μP.colLen (j₂ + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
            have h_wp := h_weakP (j₂ + 1) (by omega)
            have hi₂_lt : i₂ < μP.colLen 0 := lt_of_lt_of_le h₂mem h_wp
            have hi₂_eq : i₂ = μP.colLen 0 - 1 := by omega
            -- (hP-1, j₂) ∈ σ.P.shape because (i₂, j₂+1) ∈ μP.
            have hmem_σP : (μP.colLen 0 - 1, j₂) ∈ σ.val.P.shape := by
              rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft, ← hi₂_eq]; exact hmem₂
            -- σ.P(hP-1, j₂) = c. Rewrite i₂ = hP-1 then use the lemma.
            rw [hi₂_eq, sigma_P_eq_c_of_Qbot_d_bal σ h_hQσ_eq h_shape_inc h_Qd j₂ hmem_σP]
          · simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [liftPaint_B_P]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case mono_Q =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ j₂).layerOrd
    have hi₂ : i₂ < μQ.colLen j₂ := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero =>
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (liftCol0Q_B _ _ v i₂).layerOrd
        unfold liftCol0Q_B; cases v with
        | inl d =>
          simp only
          by_cases hc1 : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
          · have hb1 : i₁ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right hc1.1 hc1.2
            have hb2 : i₂ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right (by omega) hi₂
            rw [dif_pos hc1, dif_pos ⟨by omega, hi₂⟩]
            exact d.prop.2.1 ⟨_, hb1⟩ ⟨_, hb2⟩ (by simp; omega)
          · rw [dif_neg hc1]; simp [DRCSymbol.layerOrd]
        | inr d =>
          simp only
          by_cases hc1 : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
          · have hb1 : i₁ - (μP.colLen 0 - 1) < μQ.colLen 0 - μP.colLen 0 + 1 := by omega
            have hb2 : i₂ - (μP.colLen 0 - 1) < μQ.colLen 0 - μP.colLen 0 + 1 := by omega
            rw [dif_pos hc1, dif_pos ⟨by omega, hi₂, hc1.2.2⟩]
            exact d.prop.2.1 ⟨_, hb1⟩ ⟨_, hb2⟩ (by simp; omega)
          · rw [dif_neg hc1]; simp [DRCSymbol.layerOrd]
      | succ j₂ =>
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (σ.val.Q.paint i₂ j₂).layerOrd
        unfold liftCol0Q_B; cases v with
        | inl d =>
          simp only
          by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
          · exfalso
            have hi₂_bound : i₂ < μQ.colLen (j₂+1) := hi₂
            have := h_weak (j₂ + 1) (by omega); omega
          · rw [dif_neg hc]; simp [DRCSymbol.layerOrd]
        | inr d =>
          simp only
          by_cases hc : μP.colLen 0 - 1 ≤ i₁ ∧ i₁ < μQ.colLen 0 ∧ μP.colLen 0 > 0
          · -- Balanced case: i₁ could be hP-1. Use h_Qd to show σ.Q(hP-1, j₂) = d.
            have h_weak_j : μQ.colLen (j₂+1) ≤ μP.colLen 0 := h_weak (j₂+1) (by omega)
            have hi₂_lt : i₂ < μP.colLen 0 := lt_of_lt_of_le hi₂ h_weak_j
            have hi_eq : i₁ = μP.colLen 0 - 1 := by omega
            have hi₂_eq : i₂ = μP.colLen 0 - 1 := by omega
            have hmemσ : (μP.colLen 0 - 1, j₂) ∈ σ.val.Q.shape := by
              rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft, ← hi₂_eq]; exact hmem₂
            rw [hi₂_eq, sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₂ hmemσ]
            -- Now goal: (liftCol0Q_B hP hQ (.inr d) i₁).layerOrd ≤ layerOrd(d) = 4
            rw [dif_pos hc]
            rcases d.prop.1 ⟨i₁ - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;>
              simp [h, DRCSymbol.layerOrd]
          · rw [dif_neg hc]; simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [liftPaint_B_Q]
        exact σ.val.mono_Q i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case row_s =>
    have hP_no_s : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .s := by
      intro i j; cases j with
      | zero =>
        simp only [liftPaint_B_P]; unfold liftCol0P_B; cases v with
        | inl _ => simp
        | inr _ => split_ifs <;> simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₂ (hP_no_s i j₂)
    · have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 - 1 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        cases v with
        | inl d => simp only at hne; split_ifs at hne with hc <;> first | omega | exact absurd rfl hne
        | inr d => simp only at hne; split_ifs at hne with hc <;> first | exact hc.1 | exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          -- balanced: μQ.colLen(j₂+1) ≤ μP.colLen 0, so i < μP.colLen 0, so i = μP.colLen 0 - 1.
          have h_weak_j : μQ.colLen (j₂+1) ≤ μP.colLen 0 := h_weak (j₂+1) (by omega)
          have hi_bound : i < μP.colLen 0 := lt_of_lt_of_le hi₂ h_weak_j
          have hi_eq : i = μP.colLen 0 - 1 := by omega
          have hmemσ : (μP.colLen 0 - 1, j₂) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft, ← hi_eq]; exact hmemQ
          simp only [liftPaint_B_Q] at h₂
          rw [hi_eq, sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₂ hmemσ] at h₂
          exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₁+1) ≤ μP.colLen 0 := h_weak (j₁+1) (by omega)
          have hi_bound : i < μP.colLen 0 := lt_of_lt_of_le hi₁ h_weak_j
          have hi_eq : i = μP.colLen 0 - 1 := by omega
          have hmemσ : (μP.colLen 0 - 1, j₁) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft, ← hi_eq]; exact hmemQ
          simp only [liftPaint_B_Q] at h₁
          rw [hi_eq, sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₁ hmemσ] at h₁
          exact absurd h₁ (by decide)
        | succ j₂ =>
          have := σ.val.row_s i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .s by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .s by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case row_r =>
    have hP_no_r : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .r := by
      intro i j; cases j with
      | zero =>
        simp only [liftPaint_B_P]; unfold liftCol0P_B; cases v with
        | inl _ => simp
        | inr _ => split_ifs <;> simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₂ (hP_no_r i j₂)
    · have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 - 1 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        cases v with
        | inl d => simp only at hne; split_ifs at hne with hc <;> first | omega | exact absurd rfl hne
        | inr d => simp only at hne; split_ifs at hne with hc <;> first | exact hc.1 | exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₂+1) ≤ μP.colLen 0 := h_weak (j₂+1) (by omega)
          have hi_bound : i < μP.colLen 0 := lt_of_lt_of_le hi₂ h_weak_j
          have hi_eq : i = μP.colLen 0 - 1 := by omega
          have hmemσ : (μP.colLen 0 - 1, j₂) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft, ← hi_eq]; exact hmemQ
          simp only [liftPaint_B_Q] at h₂
          rw [hi_eq, sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₂ hmemσ] at h₂
          exact absurd h₂ (by decide)
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_tail := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₁+1) ≤ μP.colLen 0 := h_weak (j₁+1) (by omega)
          have hi_bound : i < μP.colLen 0 := lt_of_lt_of_le hi₁ h_weak_j
          have hi_eq : i = μP.colLen 0 - 1 := by omega
          have hmemσ : (μP.colLen 0 - 1, j₁) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft, ← hi_eq]; exact hmemQ
          simp only [liftPaint_B_Q] at h₁
          rw [hi_eq, sigma_Q_eq_d_of_Qbot_d_bal σ h_hQσ_eq h_Qd j₁ hmemσ] at h₁
          exact absurd h₁ (by decide)
        | succ j₂ =>
          have := σ.val.row_r i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .r by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .r by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    show i₁ = i₂
    simp only [liftPaint_B_P] at h₁ h₂
    cases j with
    | zero =>
      cases v with
      | inl _ => simp [liftCol0P_B] at h₁
      | inr _ =>
        simp only [liftCol0P_B] at h₁ h₂
        split_ifs at h₁ with h1
        split_ifs at h₂ with h2
        omega
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .c at h₁
      simp only [liftPaint_B_Q] at h₁
      cases v with
      | inl d =>
        simp only [liftCol0Q_B] at h₁
        split_ifs at h₁ with hc
        rcases d.prop.1 ⟨i₁ - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at h₁
      | inr d =>
        simp only [liftCol0Q_B] at h₁
        split_ifs at h₁ with hc
        rcases d.prop.1 ⟨i₁ - (μP.colLen 0 - 1), by omega⟩ with h | h | h <;> simp [h] at h₁
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_c_Q j i₁ i₂ h₁ h₂
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_P σ.val (μP.colLen 0) v i₁ 0 = .d at h₁
      simp only [liftPaint_B_P] at h₁
      cases v with
      | inl _ => exact absurd (show (DRCSymbol.dot : DRCSymbol) = .d from h₁) (by decide)
      | inr _ => simp only [liftCol0P_B] at h₁; split_ifs at h₁
    | succ j =>
      simp only [liftPaint_B_P] at h₁ h₂
      exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .d at h₁
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ 0 = .d at h₂
      simp only [liftPaint_B_Q] at h₁ h₂
      cases v with
      | inl d =>
        simp only [liftCol0Q_B] at h₁ h₂
        split_ifs at h₁ with hc₁
        split_ifs at h₂ with hc₂
        have heq := d.prop.2.2 ⟨i₁ - μP.colLen 0, by omega⟩ ⟨i₂ - μP.colLen 0, by omega⟩ h₁ h₂
        have := congr_arg Fin.val heq; simp at this; omega
      | inr d =>
        simp only [liftCol0Q_B] at h₁ h₂
        split_ifs at h₁ with hc₁
        split_ifs at h₂ with hc₂
        have heq := d.prop.2.2 ⟨i₁ - (μP.colLen 0 - 1), by omega⟩ ⟨i₂ - (μP.colLen 0 - 1), by omega⟩ h₁ h₂
        have := congr_arg Fin.val heq; simp at this; omega
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_d_Q j i₁ i₂ h₁ h₂

/-- Round-trip: doubleDescent_Bplus_map (liftPBP_B_bal_Qd σ v) = σ.
    Identical to `liftPBP_B_round_trip` (just passes through σ column data). -/
private theorem liftPBP_B_bal_Qd_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_weakP : ∀ j, j ≥ 1 → μP.colLen j ≤ μP.colLen 0)
    (h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    doubleDescent_Bplus_map μP μQ
      (liftPBP_B_bal_Qd σ v hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd) = σ := by
  set τ := liftPBP_B_bal_Qd σ v hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd
  apply Subtype.ext
  apply PBP_eq_of_data
  · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]; exact σ.prop.1.symm
  · apply PaintedYoungDiagram.ext'
    · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.1]; rfl
    · funext i j
      show PBP.doubleDescent_B_paintL τ.val i j = σ.val.P.paint i j
      simp only [PBP.doubleDescent_B_paintL]
      by_cases hds : i < PBP.dotScolLen τ.val.P (j + 1)
      · rw [if_pos hds]
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hds)
        have hpaint : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        rw [hpaint] at hlo
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σ : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσ_sym := σ.val.sym_P i j hmem_σ
        rw [σ.prop.1] at hσ_sym
        simp only [DRCSymbol.allowed] at hσ_sym
        rcases hσ_sym with h | h <;> rw [h] at hlo ⊢ <;>
          simp [DRCSymbol.layerOrd] at hlo ⊢
      · rw [if_neg hds]; rfl
  · apply PaintedYoungDiagram.ext'
    · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.2]; rfl
    · funext i j
      show PBP.doubleDescent_B_paintR τ.val i j = σ.val.Q.paint i j
      simp only [PBP.doubleDescent_B_paintR]
      by_cases hdsP : i < PBP.dotScolLen τ.val.P (j + 1)
      · rw [if_pos hdsP]
        have hpaintP : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsP)
        rw [hpaintP] at hlo
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσP_sym := σ.val.sym_P i j hmem_σP
        rw [σ.prop.1] at hσP_sym
        simp only [DRCSymbol.allowed] at hσP_sym
        have hσP_dot : σ.val.P.paint i j = .dot := by
          rcases hσP_sym with h | h <;> rw [h] at hlo <;>
            simp [DRCSymbol.layerOrd] at hlo ⊢ <;> exact h
        have ⟨_, hQd'⟩ := (σ.val.dot_match i j).mp ⟨hmem_σP, hσP_dot⟩
        exact hQd'.symm
      · rw [if_neg hdsP]
        by_cases hdsQ : i < PBP.dotScolLen τ.val.Q (j + 1)
        · rw [if_pos hdsQ]
          have hpaintQ : τ.val.Q.paint i (j + 1) = σ.val.Q.paint i j := rfl
          have hloQ := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.Q τ.val.mono_Q
            (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsQ)
          rw [hpaintQ] at hloQ
          have hmemQ : (i, j + 1) ∈ τ.val.Q.shape := by
            have := PBP.dotScolLen_le_colLen τ.val.Q τ.val.mono_Q (j + 1)
            exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
          have hmem_σQ : (i, j) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
            exact YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have hQ_ne_dot : σ.val.Q.paint i j ≠ .dot := by
            intro hQd'
            have ⟨hmemP, hPd⟩ := (σ.val.dot_match i j).mpr ⟨hmem_σQ, hQd'⟩
            have hlo_σP : (σ.val.P.paint i j).layerOrd ≤ 1 := by rw [hPd]; decide
            have hP_in_shape : (i, j + 1) ∈ τ.val.P.shape := by
              have : i < σ.val.P.shape.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hmemP
              rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft] at this
              exact YoungDiagram.mem_iff_lt_colLen.mpr this
            have hlo_τP : (τ.val.P.paint i (j + 1)).layerOrd ≤ 1 := hlo_σP
            have h_in_dsdiag : (i, j + 1) ∈ PBP.dotSdiag τ.val.P τ.val.mono_P := by
              simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
                YoungDiagram.mem_cells]
              exact ⟨hP_in_shape, hlo_τP⟩
            have := YoungDiagram.mem_iff_lt_colLen.mp h_in_dsdiag
            rw [← PBP.dotScolLen_eq_dotSdiag_colLen] at this
            exact hdsP this
          have hσQ_sym := σ.val.sym_Q i j hmem_σQ
          rw [σ.prop.1] at hσQ_sym
          simp only [DRCSymbol.allowed] at hσQ_sym
          rcases hσQ_sym with h | h | h | h <;> rw [h] at hloQ hQ_ne_dot ⊢ <;>
            simp [DRCSymbol.layerOrd] at hloQ hQ_ne_dot ⊢
        · rw [if_neg hdsQ]; rfl

/-- liftPBP_B_bal_Qd is injective: different v give different PBPs. -/
private theorem liftPBP_B_bal_Qd_injective {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_weakP : ∀ j, j ≥ 1 → μP.colLen j ≤ μP.colLen 0)
    (h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    Function.Injective (fun v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) =>
      liftPBP_B_bal_Qd σ v hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd) := by
  intro v₁ v₂ h
  have hval : (liftPBP_B_bal_Qd σ v₁ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd).val =
              (liftPBP_B_bal_Qd σ v₂ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd).val :=
    congrArg Subtype.val h
  have hPBP : (liftPBP_B_bal_Qd σ v₁ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd).val =
              (liftPBP_B_bal_Qd σ v₂ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd).val := hval
  have hPeq : ∀ i, liftPaint_B_P σ.val (μP.colLen 0) v₁ i 0 =
                    liftPaint_B_P σ.val (μP.colLen 0) v₂ i 0 := by
    intro i
    exact congr_fun (congr_fun (congrArg (fun d => d.P.paint) hPBP) i) 0
  have hQeq : ∀ i, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v₁ i 0 =
                    liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v₂ i 0 := by
    intro i
    exact congr_fun (congr_fun (congrArg (fun d => d.Q.paint) hPBP) i) 0
  simp only [liftPaint_B_P, liftCol0P_B] at hPeq
  simp only [liftPaint_B_Q, liftCol0Q_B] at hQeq
  match v₁, v₂ with
  | .inl d₁, .inl d₂ =>
    congr 1; apply Subtype.ext; funext ⟨k, hk⟩
    have hq := hQeq (μP.colLen 0 + k)
    have hlt : μP.colLen 0 + k < μQ.colLen 0 := by omega
    simp only [dif_pos (show μP.colLen 0 ≤ μP.colLen 0 + k ∧ μP.colLen 0 + k < μQ.colLen 0
      from ⟨by omega, hlt⟩)] at hq
    have hfin : (⟨μP.colLen 0 + k - μP.colLen 0, by omega⟩ : Fin _) = ⟨k, hk⟩ :=
      Fin.ext (by simp)
    rw [hfin] at hq; exact hq
  | .inr d₁, .inr d₂ =>
    congr 1; apply Subtype.ext; funext ⟨k, hk⟩
    have hq := hQeq (μP.colLen 0 - 1 + k)
    have hlt : μP.colLen 0 - 1 + k < μQ.colLen 0 := by omega
    simp only [dif_pos (show μP.colLen 0 - 1 ≤ μP.colLen 0 - 1 + k ∧
      μP.colLen 0 - 1 + k < μQ.colLen 0 ∧ μP.colLen 0 > 0
      from ⟨by omega, hlt, hP_pos⟩)] at hq
    have hfin : (⟨μP.colLen 0 - 1 + k - (μP.colLen 0 - 1), by omega⟩ : Fin _) = ⟨k, hk⟩ :=
      Fin.ext (by simp)
    rw [hfin] at hq; exact hq
  | .inl _, .inr _ =>
    exfalso
    have hp := hPeq (μP.colLen 0 - 1)
    simp only [show (μP.colLen 0 - 1 = μP.colLen 0 - 1 ∧ μP.colLen 0 > 0) from
      ⟨rfl, hP_pos⟩, ite_true] at hp
    exact DRCSymbol.noConfusion hp
  | .inr _, .inl _ =>
    exfalso
    have hp := hPeq (μP.colLen 0 - 1)
    simp only [show (μP.colLen 0 - 1 = μP.colLen 0 - 1 ∧ μP.colLen 0 > 0) from
      ⟨rfl, hP_pos⟩, ite_true] at hp
    exact DRCSymbol.noConfusion hp.symm

/-- Lower bound in balanced-Qd case: |ValidCol0_B| ≤ |fiber|, via the lift injection. -/
private theorem validCol0_B_le_fiber_bal_Qd {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_weakP : ∀ j, j ≥ 1 → μP.colLen j ≤ μP.colLen 0)
    (h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    Fintype.card (ValidCol0_B (μP.colLen 0) (μQ.colLen 0)) ≤
    Fintype.card (doubleDescent_Bplus_fiber σ) := by
  apply Fintype.card_le_of_injective
    (fun v => ⟨liftPBP_B_bal_Qd σ v hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd,
              liftPBP_B_bal_Qd_round_trip σ v hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd⟩)
  intro v₁ v₂ h
  exact liftPBP_B_bal_Qd_injective σ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd
    (congrArg (fun x => x.val) h)

/-! ### Qr balanced case: ValidCol0_B_Qr subtype

For Q_bot = r, the admissibility constraint on v ∈ ValidCol0_B is:
- `inl d` (P col 0 all dots): τ.Q(hP-1, 0) = dot, always admissible.
- `inr d` (P col 0 has c at bottom): τ.Q(hP-1, 0) = d.val(0).
  By τ.mono_Q (τ.Q(hP-1, 0).layerOrd ≤ τ.Q(hP-1, 1).layerOrd = σ.Q(hP-1, 0).layerOrd = 2),
  d.val(0).layerOrd ≤ 2. And by τ.row_r (τ.Q(hP-1, 0) = r AND τ.Q(hP-1, 1) = r ⇒ 0 = 1),
  d.val(0) ≠ r. So d.val(0) ∈ {s} only (since d.val(0) ∈ {s, r, d} by DSeq).

Exclusions: `inr d` with d.val(0) ∈ {r, d}. Count of exclusions = 2 (for k ≥ 1).
Net count: 4k - 2. -/

/-- ValidCol0_B configs admissible for Qr case: excludes `inr d` with d.val(0) ∈ {r, d}. -/
private def ValidCol0_B_Qr (hP hQ : ℕ) :=
  { v : ValidCol0_B hP hQ //
    match v with
    | .inl _ => True
    | .inr d => ∀ h : hQ - hP + 1 ≥ 1, d.val ⟨0, by omega⟩ ≠ .r ∧ d.val ⟨0, by omega⟩ ≠ .d }

private noncomputable instance (hP hQ : ℕ) : Fintype (ValidCol0_B_Qr hP hQ) := by
  unfold ValidCol0_B_Qr; infer_instance

/-- The all-.r DSeq of length k. -/
private def DSeq_allR {k : ℕ} : DSeq k :=
  ⟨fun _ => .r,
    ⟨fun _ => Or.inr (Or.inl rfl),
     fun _ _ _ => le_refl _,
     fun _ _ hi _ => by simp at hi⟩⟩

/-- The DSeq of length k ≥ 1 with r everywhere except d at the last position.
    For k = 1, this is just [d]. -/
private def DSeq_Rd {k : ℕ} (hk : k ≥ 1) : DSeq k :=
  ⟨fun i => if i.val = k - 1 then .d else .r,
    ⟨fun i => by
       by_cases h : i.val = k - 1
       · simp [h]
       · simp [h],
     fun i j hij => by
       by_cases hj : j.val = k - 1
       · simp only [hj, if_true]
         by_cases hi : i.val = k - 1
         · simp [hi]
         · simp [hi, DRCSymbol.layerOrd]
       · have hi : i.val ≠ k - 1 := by have := j.isLt; omega
         simp [hi, hj],
     fun i j hdi hdj => by
       have hi : i.val = k - 1 := by by_contra h; simp [h] at hdi
       have hj : j.val = k - 1 := by by_contra h; simp [h] at hdj
       exact Fin.ext (hi.trans hj.symm)⟩⟩

/-- DSeq_allR has first = r. -/
private lemma DSeq_allR_first {k : ℕ} (hk : k ≥ 1) :
    (DSeq_allR (k := k)).val ⟨0, by omega⟩ = .r := rfl

/-- DSeq_Rd has first = r if k ≥ 2, else first = d (when k = 1). -/
private lemma DSeq_Rd_first {k : ℕ} (hk : k ≥ 1) (hk2 : k ≥ 2) :
    (DSeq_Rd (k := k) hk).val ⟨0, by omega⟩ = .r := by
  unfold DSeq_Rd; simp
  intro h; omega

/-- Key lemma: a DSeq(k) with first entry = r has either all r's or r^(k-1) then d. -/
private lemma DSeq_first_r_struct {k : ℕ} (hk : k ≥ 1) (d : DSeq k)
    (h : d.val ⟨0, by omega⟩ = .r) :
    d = DSeq_allR ∨ d = DSeq_Rd hk := by
  by_cases hd_exists : ∃ i : Fin k, d.val i = .d
  · right
    obtain ⟨p, hp⟩ := hd_exists
    apply Subtype.ext; funext i
    by_cases hi : i.val = k - 1
    · -- At position k-1: must be d (since d is monotone, at most 1 d).
      -- If p = k-1, then d.val(k-1) = d. Goal: d.val i = .d (since hi).
      have : d.val i = .d := by
        -- If d.val(p) = d, monotone: d.val(i) ≥ d.val(p) when i ≥ p. Since d.val ∈ {s,r,d}.
        -- d.val(i) for i ≥ p has layerOrd ≥ 4 = d.layerOrd. So d.val(i) = d.
        have hip : p.val ≤ i.val := by
          have := p.isLt; omega
        have hmono := d.prop.2.1 p i hip
        rw [hp] at hmono
        -- hmono: (.d).layerOrd ≤ (d.val i).layerOrd. .d.layerOrd = 4.
        -- d.val i ∈ {s,r,d}.
        rcases d.prop.1 i with h1 | h1 | h1
        · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
        · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
        · exact h1
      unfold DSeq_Rd; simp [hi, this]
    · -- At position i ≠ k-1: first derive p = k-1 by col_d_Q constraint.
      -- d.val(0) = r, d.val(p) = d. So p ≠ 0.
      have hp_ne_0 : p ≠ ⟨0, by omega⟩ := by
        intro he; rw [he] at hp
        simp [h] at hp
      -- By monotonicity from p to i or i to p.
      -- Actually, we need: d is monotone, d.val(p) = d (layerOrd 4). For i < p: d.val(i) ≤ 4.
      -- For i > p: d.val(i) ≥ 4, so d.val(i) = d, so i = p (by col_d_Q).
      -- So i ≤ p. For i < p, d.val(i) ∈ {s,r,d}; at most 1 d so d.val(i) = s or r.
      -- Given d.val(0) = r, monotonicity: d.val(i) ≥ r for i ≥ 0. So d.val(i) ∈ {r, d}.
      -- Combined: d.val(i) = r (for i < p). And p must equal k-1.
      have hp_is_kmin1 : p.val = k - 1 := by
        -- We need to show p = k - 1. If p < k-1, consider j = ⟨k-1, ...⟩.
        -- d.val(j).layerOrd ≥ d.val(p).layerOrd = 4. So d.val(j) = d. Then col_d_Q: p = j.
        by_contra hp_ne
        have hp_lt : p.val < k - 1 := by
          have := p.isLt; omega
        let j : Fin k := ⟨k - 1, by omega⟩
        have hmono := d.prop.2.1 p j (by show p.val ≤ k - 1; omega)
        rw [hp] at hmono
        rcases d.prop.1 j with h1 | h1 | h1
        · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
        · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
        · have := d.prop.2.2 p j hp h1
          exact absurd (congr_arg Fin.val this) (by simp [j]; omega)
      -- Now p.val = k-1 and i.val ≠ k-1, so i.val < k-1 < p.val is NOT correct; i.val ≤ k-2 and p.val = k-1.
      have hi_lt_p : i.val < p.val := by rw [hp_is_kmin1]; have := i.isLt; omega
      have hmono := d.prop.2.1 ⟨0, by omega⟩ i (Nat.zero_le _)
      rw [h] at hmono
      have h_i : d.val i = .r := by
        rcases d.prop.1 i with h1 | h1 | h1
        · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
        · exact h1
        · -- d.val i = d, but d at p; i < p, col_d_Q.
          exfalso
          have := d.prop.2.2 i p h1 hp
          exact absurd (congr_arg Fin.val this) (by omega)
      unfold DSeq_Rd; simp [hi, h_i]
  · left
    push_neg at hd_exists
    apply Subtype.ext; funext i
    -- d.val(i) ∈ {s, r, d}, no d by hd_exists. So d.val(i) ∈ {s, r}.
    -- Monotone from 0: d.val(i) ≥ r, so ≠ s. Therefore d.val(i) = r.
    have hmono := d.prop.2.1 ⟨0, by omega⟩ i (Nat.zero_le _)
    rw [h] at hmono
    rcases d.prop.1 i with h1 | h1 | h1
    · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
    · show d.val i = (DSeq_allR (k := k)).val i
      unfold DSeq_allR; exact h1
    · exact absurd h1 (hd_exists i)

/-- Key lemma: a DSeq(k) with first entry = d has all d's (only possible for k = 1). -/
private lemma DSeq_first_d_struct {k : ℕ} (hk : k ≥ 1) (d : DSeq k)
    (h : d.val ⟨0, by omega⟩ = .d) :
    k = 1 ∧ d = DSeq_Rd hk := by
  -- col_d_Q: at most 1 d. Monotone: d.val(i) ≥ d.val(0) = d. So all d's. Need k = 1.
  have hall_d : ∀ i : Fin k, d.val i = .d := by
    intro i
    have hmono := d.prop.2.1 ⟨0, by omega⟩ i (Nat.zero_le _)
    rw [h] at hmono
    rcases d.prop.1 i with h1 | h1 | h1
    · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
    · rw [h1] at hmono; simp [DRCSymbol.layerOrd] at hmono
    · exact h1
  -- If k ≥ 2, we have at least 2 d's at position 0 and 1. col_d_Q: contradiction.
  have hk_eq : k = 1 := by
    by_contra hne
    have hk2 : k ≥ 2 := by omega
    have hd0 : d.val ⟨0, by omega⟩ = .d := h
    have hd1 : d.val ⟨1, by omega⟩ = .d := hall_d ⟨1, by omega⟩
    have := d.prop.2.2 ⟨0, by omega⟩ ⟨1, by omega⟩ hd0 hd1
    exact absurd (congr_arg Fin.val this) (by simp)
  refine ⟨hk_eq, ?_⟩
  apply Subtype.ext; funext i
  have hi : i.val = 0 := by have := i.isLt; omega
  unfold DSeq_Rd; simp
  have : i.val = k - 1 := by omega
  rw [if_pos this]
  rw [show i = ⟨0, by omega⟩ from Fin.ext hi]
  exact h

/-- |DSeq(k) with first ∈ {r, d}| = 2 uniformly (for k ≥ 1). -/
private theorem card_DSeq_first_rd {k : ℕ} (hk : k ≥ 1) :
    Fintype.card {d : DSeq k // d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d} = 2 := by
  -- Show Equiv with Bool via: tt ↦ DSeq_allR, ff ↦ DSeq_Rd.
  have hDSeq_allR_in : (DSeq_allR (k := k)).val ⟨0, by omega⟩ = .r ∨
      (DSeq_allR (k := k)).val ⟨0, by omega⟩ = .d := Or.inl (DSeq_allR_first hk)
  have hDSeq_Rd_in : (DSeq_Rd (k := k) hk).val ⟨0, by omega⟩ = .r ∨
      (DSeq_Rd (k := k) hk).val ⟨0, by omega⟩ = .d := by
    by_cases hk2 : k ≥ 2
    · exact Or.inl (DSeq_Rd_first hk hk2)
    · have hk1 : k = 1 := by omega
      subst hk1
      right
      show (if (0 : ℕ) = 1 - 1 then DRCSymbol.d else DRCSymbol.r) = .d
      simp
  have hne : (⟨DSeq_allR, hDSeq_allR_in⟩ : {d : DSeq k //
      d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d}) ≠
    ⟨DSeq_Rd hk, hDSeq_Rd_in⟩ := by
    intro heq
    have hsub : (DSeq_allR (k := k)) = DSeq_Rd (k := k) hk := Subtype.ext_iff.mp heq
    have hval_eq : (DSeq_allR (k := k)).val = (DSeq_Rd (k := k) hk).val :=
      congrArg Subtype.val hsub
    have hlast := congr_fun hval_eq ⟨k - 1, by omega⟩
    have hfalse : (DRCSymbol.r : DRCSymbol) = .d := by
      have : (DSeq_Rd (k := k) hk).val ⟨k - 1, by omega⟩ = .d := by
        unfold DSeq_Rd; simp
      rw [this] at hlast
      exact hlast
    exact absurd hfalse (by decide)
  -- Now use card_eq_two (for Finset or via univ_eq)
  have : (Finset.univ : Finset {d : DSeq k //
      d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d}).card = 2 := by
    apply Finset.card_eq_two.mpr
    refine ⟨⟨DSeq_allR, hDSeq_allR_in⟩, ⟨DSeq_Rd hk, hDSeq_Rd_in⟩, hne, ?_⟩
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases x with ⟨d, hd | hd⟩
    · rcases DSeq_first_r_struct hk d hd with h | h
      · left; apply Subtype.ext; exact h
      · right; apply Subtype.ext; exact h
    · rcases DSeq_first_d_struct hk d hd with ⟨_, h⟩
      right; apply Subtype.ext; exact h
  rw [← Finset.card_univ]; exact this

/-- |ValidCol0_B_Qr| = 4k - 2 where k = hQ - hP + 1.
    ValidCol0_B = DSeq(k-1) ⊕ DSeq(k), and ValidCol0_B_Qr restricts `inr d` to d.val(0) ∉ {r,d}.
    So ValidCol0_B_Qr = DSeq(k-1) + (DSeq(k) \ {first in {r,d}}). Since DSeq(k-1) ≃ first=s side,
    and DSeq(k) partitions by first s/r/d. -/
private theorem validCol0_B_Qr_card (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card (ValidCol0_B_Qr hP hQ) = 4 * k - 2 := by
  -- Unfold ValidCol0_B_Qr to subtype of sum.
  -- ValidCol0_B_Qr = {v : DSeq(k-1) ⊕ DSeq(k) // if inr then first not in {r,d}}
  -- ≃ DSeq(k-1) ⊕ {d : DSeq(k) // d.val 0 ∉ {r, d}}
  have hK : hQ - hP + 1 ≥ 1 := by omega
  -- Equiv: ValidCol0_B_Qr hP hQ ≃ DSeq(hQ - hP) ⊕ {d : DSeq(hQ-hP+1) // d.val 0 ∉ {r, d}}
  have hequiv : ValidCol0_B_Qr hP hQ ≃ DSeq (hQ - hP) ⊕
      {d : DSeq (hQ - hP + 1) // ¬(d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d)} := by
    refine {
      toFun := fun v => match v with
        | ⟨Sum.inl d, _⟩ => Sum.inl d
        | ⟨Sum.inr d, hp⟩ => Sum.inr ⟨d, fun h => by
            have := hp hK
            rcases h with h | h
            · exact absurd h this.1
            · exact absurd h this.2⟩
      invFun := fun e => match e with
        | Sum.inl d => ⟨Sum.inl d, trivial⟩
        | Sum.inr ⟨d, hd⟩ => ⟨Sum.inr d, fun _ => by
            push_neg at hd
            exact hd⟩
      left_inv := ?_
      right_inv := ?_
    }
    · rintro ⟨v, hp⟩
      cases v <;> rfl
    · rintro (d | ⟨d, hd⟩) <;> rfl
  rw [Fintype.card_congr hequiv, Fintype.card_sum]
  -- Now compute DSeq(k-1) + {d : DSeq(k) // first ∉ {r,d}} = (2(k-1)+1) + (DSeq(k).card - 2)
  -- DSeq(k-1) = 2k-1 (card from DSeq_card: 2n+1)
  have hDSeq_km1 : Fintype.card (DSeq (hQ - hP)) = 2 * (hQ - hP) + 1 := DSeq_card _
  -- DSeq(k) = 2k+1
  have hDSeq_k : Fintype.card (DSeq (hQ - hP + 1)) = 2 * (hQ - hP + 1) + 1 := DSeq_card _
  -- {d : DSeq(k) // first ∉ {r,d}} = DSeq(k) - {first ∈ {r,d}}, with card = (2k+1) - 2 = 2k-1
  have hneg_card : Fintype.card
      {d : DSeq (hQ - hP + 1) // ¬(d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d)} =
      2 * (hQ - hP + 1) + 1 - 2 := by
    have hpos_card : Fintype.card
        {d : DSeq (hQ - hP + 1) // d.val ⟨0, by omega⟩ = .r ∨ d.val ⟨0, by omega⟩ = .d} = 2 :=
      card_DSeq_first_rd hK
    -- Use subtype complement: card({x // ¬ p x}) = card(α) - card({x // p x}).
    rw [Fintype.card_subtype_compl]
    rw [hpos_card, hDSeq_k]
  rw [hDSeq_km1, hneg_card]
  omega

/-- Key admissibility lemma: for τ in fiber of σ with σ.Q_bot = r and P_col0_has_c τ,
    τ.Q(hP-1, 0) ∉ {r, d}.

    Proof outline:
    - τ in fiber of σ: doubleDescent_Bplus_map τ = σ, so σ.Q = doubleDescent_B_paintR τ.
    - σ.Q(hP-1, 0) = r. By dd_paintR def (≠ dot, ≠ s), τ.Q(hP-1, 1) = r.
    - τ.mono_Q: τ.Q(hP-1, 0).layerOrd ≤ τ.Q(hP-1, 1).layerOrd = 2, so ≠ d (layerOrd 4).
    - τ.row_r: τ.Q(hP-1, 0) = r AND τ.Q(hP-1, 1) = r ⇒ 0 = 1, contradiction. So ≠ r. -/
private theorem fiber_Q_hPm1_nrd_of_Qr {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qr : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r)
    (τ : doubleDescent_Bplus_fiber σ) (hPc : P_col0_has_c τ.val) :
    τ.val.val.Q.paint (μP.colLen 0 - 1) 0 ≠ .r ∧
    τ.val.val.Q.paint (μP.colLen 0 - 1) 0 ≠ .d := by
  have hddmap : doubleDescent_Bplus_map μP μQ τ.val = σ := τ.prop
  have hσ_eq : σ.val = doubleDescent_B_PBP τ.val.val (Or.inl τ.val.prop.1) :=
    congrArg Subtype.val hddmap.symm
  have hσ_Q_eq : σ.val.Q.paint (μP.colLen 0 - 1) 0 =
      PBP.doubleDescent_B_paintR τ.val.val (μP.colLen 0 - 1) 0 := by
    rw [hσ_eq]; rfl
  have h_Qr' : σ.val.Q.paint (μP.colLen 0 - 1) 0 = .r := by
    rw [← h_hQσ_eq]; exact h_Qr
  have h_paintR : PBP.doubleDescent_B_paintR τ.val.val (μP.colLen 0 - 1) 0 = .r := by
    rw [← hσ_Q_eq]; exact h_Qr'
  simp only [PBP.doubleDescent_B_paintR] at h_paintR
  split_ifs at h_paintR with h1 h2
  have hτQ1 : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 = .r := h_paintR
  have hmemQ_1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.Q.shape := by
    by_contra hne
    rw [τ.val.val.Q.paint_outside _ _ hne] at hτQ1
    exact absurd hτQ1 (by decide)
  have hmono := τ.val.val.mono_Q (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) 1
    le_rfl (by omega) hmemQ_1
  rw [hτQ1] at hmono
  refine ⟨?_, ?_⟩
  · intro hr
    have := τ.val.val.row_r (μP.colLen 0 - 1) .R .R 0 1
      (by simp [paintBySide]; exact hr)
      (by simp [paintBySide]; exact hτQ1)
    omega
  · intro hd
    rw [hd] at hmono
    simp [DRCSymbol.layerOrd] at hmono

/-- Upper bound for Qr balanced case: fiber ↪ ValidCol0_B_Qr. -/
private theorem fiber_le_validCol0_B_Qr {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qr : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r) :
    Fintype.card (doubleDescent_Bplus_fiber σ) ≤
    Fintype.card (ValidCol0_B_Qr (μP.colLen 0) (μQ.colLen 0)) := by
  apply Fintype.card_le_of_injective (fun τ => (⟨extractCol0_B τ.val hle, ?_⟩ :
    ValidCol0_B_Qr (μP.colLen 0) (μQ.colLen 0)))
  · intro τ₁ τ₂ heq
    have := Subtype.ext_iff.mp heq
    exact extractCol0_B_injective_on_fiber σ hle this
  · -- Show extractCol0_B τ is in ValidCol0_B_Qr.
    unfold extractCol0_B
    split_ifs with hPc
    · intro hK
      -- Need: (extractQtail_B τ.val hle ...).val ⟨0, _⟩ ≠ .r ∧ ≠ .d.
      -- Reduce to τ.Q(hP-1, 0) via Q_tail_start τ = μP.colLen 0 - 1 (from hPc).
      have hqs : Q_tail_start τ.val = μP.colLen 0 - 1 := by
        unfold Q_tail_start; rw [if_pos hPc]
      have hpt : (extractQtail_B τ.val hle (μQ.colLen 0 - μP.colLen 0 + 1)
          (by simp [Q_tail_len, if_pos hPc])).val ⟨0, by omega⟩ =
          τ.val.val.Q.paint (μP.colLen 0 - 1) 0 := by
        show τ.val.val.Q.paint (Q_tail_start τ.val + 0) 0 = _
        rw [hqs]; simp
      rw [hpt]
      exact fiber_Q_hPm1_nrd_of_Qr σ hP_pos h_hQσ_eq h_Qr τ hPc
    · trivial

/-- Lower bound for Qr balanced case: ValidCol0_B_Qr ↪ fiber.

    **Closure plan**: Build `liftPBP_B_bal_Qr σ v hle hP_pos h_weakP h_shape_inc
    h_hQσ_eq h_weak h_Qr` parallel to `liftPBP_B_bal_Qd`, replacing the 5 uses
    of `sigma_Q_eq_d_of_Qbot_d_bal` with `sigma_Q_eq_d_of_Qbot_r_bal_j_pos` for
    j ≥ 1 (i.e. in the `| succ j₂ =>` / `| j + 1` branches for Q). The
    ValidCol0_B_Qr constraint excludes `inr d` with `d.val(0) ∈ {r, d}`, so
    the boundary row τ.Q(hP-1, 0) is always in {•, s} (layerOrd ≤ 1 ≤ 2),
    making `mono_Q` from τ.Q(hP-1, 0) to τ.Q(hP-1, 1) = σ.Q(hP-1, 0) = .r
    automatically satisfied. `row_r` is automatic since τ.Q(hP-1, 0) ≠ .r.

    **Status**: admitted as bare sorry; the Qd template (~450 lines) needs
    structural copy with targeted replacements. Numerically verified: 82 dp
    cases via `tools/verify_all_B_lemmas.py`. -/
private theorem validCol0_B_Qr_le_fiber {r₁ r₂ : ℕ} {rest : DualPart} {μP μQ : YoungDiagram}
    (_hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (_hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (_hsort : (r₁ :: r₂ :: rest).SortedGE)
    (_heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (_hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (_h_bal : ¬(r₂ > rest.head?.getD 0))
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (_h_Qr : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r) :
    Fintype.card (ValidCol0_B_Qr (μP.colLen 0) (μQ.colLen 0)) ≤
    Fintype.card (doubleDescent_Bplus_fiber σ) := by
  sorry

/-- **Per-class fiber size (Q_bot = d)**: In balanced case, a sub-PBP σ with
    Q_bot = d has a fiber of size 4k in the new level.

    **Numerical verification**: 82 dp cases via `tools/verify_all_B_lemmas.py`. -/
private theorem fiber_card_B_bal_Qd {r₁ r₂ : ℕ} {rest : DualPart}
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_Qd : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) :
    Fintype.card (doubleDescent_Bplus_fiber σ) = 4 * ((r₁ - r₂) / 2 + 1) := by
  -- Compute column lengths from dp structure.
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hpos₂ := hpos r₂ (by simp)
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  have hk_eq : (r₁ - r₂) / 2 + 1 = μQ.colLen 0 - μP.colLen 0 + 1 := by
    rw [hP0, hQ0]
    have heven₁ := heven r₁ (by simp)
    obtain ⟨a, ha⟩ := heven₁
    rw [ha, hb]
    -- r₁ = a + a, r₂ = b + b.
    -- (a+a - (b+b))/2 + 1 = (a+a)/2 - (b+b)/2 + 1
    -- Note Even.add_self: a+a = 2*a, (a+a)/2 = a.
    have : a + a = 2 * a := by ring
    have : b + b = 2 * b := by ring
    have h1 : (a + a) / 2 = a := by omega
    have h2 : (b + b) / 2 = b := by omega
    rw [h1, h2]
    have h_ge' : a + a ≥ b + b := by rw [← ha, ← hb]; exact h_ge
    have : (a + a - (b + b)) / 2 = a - b := by omega
    omega
  have hk_pos : (r₁ - r₂) / 2 + 1 ≥ 1 := by omega
  -- Shape relations for shiftLeft.
  have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
  have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
  -- Balanced: r₂ ≤ rest.head?.getD 0 (from ¬(r₂ > ...)) and r₂ ≥ rest.head?.getD 0 (from sorted).
  -- So rest starts with r₃ = r₂ (at least in head). We need μQ.shiftLeft.colLen 0 = μP.colLen 0.
  have h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0 := by
    push_neg at h_bal
    -- rest.head?.getD 0 ≥ r₂
    have hr₂ := sortedGE_head_ge hsort  -- r₁ ≥ r₂
    rw [hP0]
    -- Case on rest.
    match rest, hQ_sh with
    | [], heq =>
      -- rest = []: h_bal says r₂ ≤ 0, but hpos says r₂ > 0. Contradiction.
      simp at h_bal; omega
    | [r₃], heq =>
      -- rest = [r₃]: h_bal says r₂ ≤ r₃. Sort: r₂ ≥ r₃. So r₂ = r₃.
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: [r₃]).get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm (by omega) hr₃_le
      have hpos₃ := hpos r₃ (by simp)
      -- μQ.shiftLeft.colLens = [r₃/2]. colLen 0 = r₃/2 = r₂/2.
      have h : μQ.shiftLeft.colLens = [r₃/2] := by
        rw [heq]; simp [dpartColLensQ_B, hpos₃]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
    | r₃ :: r₄ :: rest', heq =>
      -- rest = r₃ :: r₄ :: rest'. h_bal says r₂ ≤ r₃. Sort: r₂ ≥ r₃. So r₂ = r₃.
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp : (⟨1, by simp⟩ : Fin 4) ≤ ⟨2, by simp⟩)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm h_bal hr₃_le
      have h : μQ.shiftLeft.colLens = r₃/2 :: dpartColLensQ_B rest' := by
        rw [heq, dpartColLensQ_B_cons₂]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
  -- h_weak: μQ.colLen j ≤ μP.colLen 0 for j ≥ 1, which is μQ.shiftLeft.colLen (j-1) ≤ μP.colLen 0.
  have h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 := by
    intro j hj
    -- μQ.colLen j ≤ μQ.colLen 1 = μQ.shiftLeft.colLen 0 = μP.colLen 0
    have h1 : μQ.colLen j ≤ μQ.colLen 1 := μQ.colLen_anti 1 j (by omega)
    rw [show μQ.colLen 1 = μQ.shiftLeft.colLen 0 from
      (YoungDiagram.colLen_shiftLeft μQ 0).symm] at h1
    omega
  -- h_weakP: μP.colLen j ≤ μP.colLen 0 for j ≥ 1 (always holds by mono).
  have h_weakP : ∀ j, j ≥ 1 → μP.colLen j ≤ μP.colLen 0 := by
    intro j _
    exact μP.colLen_anti 0 j (by omega)
  -- h_shape_inc: μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j (from dp structure).
  have h_shape_inc : ∀ j, μP.shiftLeft.colLen j ≤ μQ.shiftLeft.colLen j :=
    sigma_shape_inc_of_dp hP hQ hsort
  apply le_antisymm
  · -- Upper bound: |fiber σ| ≤ |ValidCol0_B hP hQ| = 4k.
    have h_le := fiber_le_validCol0_B σ hle
    have hcard := validCol0_B_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_le; omega
  · -- Lower bound: |ValidCol0_B hP hQ| ≤ |fiber σ|.
    have h_ge := validCol0_B_le_fiber_bal_Qd σ hle hP_pos h_weakP h_shape_inc h_hQσ_eq h_weak h_Qd
    have hcard := validCol0_B_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_ge; omega

/-- **Per-class fiber size (Q_bot = r)**: In balanced case, a sub-PBP σ with
    Q_bot = r has a fiber of size 4k - 2 in the new level.

    **Closure path**: Parallel to `fiber_card_B_bal_Qd`, but the admissibility
    constraint `(τ.Q col 0 at row < hP_σ).layerOrd ≤ 2` excludes 2 col-0 paintings
    from the `ValidCol0_B hP hQ` = 4k count: those that would paint the boundary
    row as `c` (layerOrd 3) or `d` (layerOrd 4). Net fiber = 4k - 2.

    **Numerical verification**: 82 dp cases via `tools/verify_all_B_lemmas.py`. -/
private theorem fiber_card_B_bal_Qr {r₁ r₂ : ℕ} {rest : DualPart}
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_Qr : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r) :
    Fintype.card (doubleDescent_Bplus_fiber σ) = 4 * ((r₁ - r₂) / 2 + 1) - 2 := by
  -- Compute column lengths from dp structure (parallel to fiber_card_B_bal_Qd).
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hpos₂ := hpos r₂ (by simp)
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  have hk_eq : (r₁ - r₂) / 2 + 1 = μQ.colLen 0 - μP.colLen 0 + 1 := by
    rw [hP0, hQ0]
    have heven₁ := heven r₁ (by simp)
    obtain ⟨a, ha⟩ := heven₁
    rw [ha, hb]
    have h1 : (a + a) / 2 = a := by omega
    have h2 : (b + b) / 2 = b := by omega
    rw [h1, h2]
    have h_ge' : a + a ≥ b + b := by rw [← ha, ← hb]; exact h_ge
    have : (a + a - (b + b)) / 2 = a - b := by omega
    omega
  have hk_pos : (r₁ - r₂) / 2 + 1 ≥ 1 := by omega
  -- Balanced: μQ.shiftLeft.colLen 0 = μP.colLen 0.
  have h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0 := by
    push_neg at h_bal
    rw [hP0]
    match rest, show μQ.shiftLeft.colLens = dpartColLensQ_B rest from
      (by rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]) with
    | [], heq => simp at h_bal; omega
    | [r₃], heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: [r₃]).get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm (by omega) hr₃_le
      have hpos₃ := hpos r₃ (by simp)
      have h : μQ.shiftLeft.colLens = [r₃/2] := by
        rw [heq]; simp [dpartColLensQ_B, hpos₃]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
    | r₃ :: r₄ :: rest', heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp : (⟨1, by simp⟩ : Fin 4) ≤ ⟨2, by simp⟩)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm h_bal hr₃_le
      have h : μQ.shiftLeft.colLens = r₃/2 :: dpartColLensQ_B rest' := by
        rw [heq, dpartColLensQ_B_cons₂]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
  apply le_antisymm
  · -- Upper bound: |fiber σ| ≤ |ValidCol0_B_Qr| = 4k - 2.
    have h_le := fiber_le_validCol0_B_Qr σ hle hP_pos h_hQσ_eq h_Qr
    have hcard := validCol0_B_Qr_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_le; omega
  · -- Lower bound: |ValidCol0_B_Qr| ≤ |fiber σ|.
    have h_ge := validCol0_B_Qr_le_fiber hP hQ hsort heven hpos h_bal σ h_Qr
    have hcard := validCol0_B_Qr_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_ge; omega

/-! ### Qlow balanced case: ValidCol0_B_Qlow subtype

For Q_bot.layerOrd ≤ 1 (σ.Q_bot ∈ {•, s}), the admissibility constraint on
v ∈ ValidCol0_B is much stricter:
- `inl d` (P col 0 all dots): τ.Q(i, 0) = dot for i < hP, layerOrd 0 ≤ σ.Q(i, 0).
  No admissibility on d. All DSeq(hQ-hP) valid. Count: 2k - 1 (where k = hQ-hP+1).
- `inr d` (P col 0 has c at bottom): τ.P(hP-1, 0) = c. By mono_P, σ.P(hP-1, 0) ≥ c,
  so σ.P(hP-1, 0) = c. By dot_match, σ.Q(hP-1, 0) = non-dot. Combined with
  layerOrd ≤ 1, σ.Q(hP-1, 0) = s. Then τ.Q(hP-1, 0) must satisfy:
  - layerOrd ≤ σ.Q(hP-1, 0).layerOrd = 1, so τ.Q(hP-1, 0) ∈ {dot, s}.
  - non-dot (by dot_match at (hP-1, 0) with τ.P = c), so τ.Q(hP-1, 0) = s.
  - But σ.Q(hP-1, 0) = s too, so by row_s, 0 = 1, contradiction.
  Hence inr case is entirely excluded.

Net count: 2k - 1. -/

/-- ValidCol0_B configs admissible for Qlow case: only `inl d` variants. -/
private def ValidCol0_B_Qlow (hP hQ : ℕ) :=
  { v : ValidCol0_B hP hQ //
    match v with
    | .inl _ => True
    | .inr _ => False }

private noncomputable instance (hP hQ : ℕ) : Fintype (ValidCol0_B_Qlow hP hQ) := by
  unfold ValidCol0_B_Qlow; infer_instance

/-- |ValidCol0_B_Qlow| = 2k - 1 where k = hQ - hP + 1.
    Reason: only inl branch valid; DSeq(hQ - hP) has 2(hQ - hP) + 1 = 2k - 1 elements. -/
private theorem validCol0_B_Qlow_card (hP hQ : ℕ) (hle : hP ≤ hQ)
    (k : ℕ) (hk : k = hQ - hP + 1) (hk_pos : k ≥ 1) :
    Fintype.card (ValidCol0_B_Qlow hP hQ) = 2 * k - 1 := by
  -- ValidCol0_B_Qlow ≃ DSeq(hQ - hP): inl branch only.
  have hequiv : ValidCol0_B_Qlow hP hQ ≃ DSeq (hQ - hP) := by
    refine {
      toFun := fun ⟨v, hv⟩ => ?_
      invFun := fun d => ⟨Sum.inl d, trivial⟩
      left_inv := ?_
      right_inv := ?_
    }
    · cases v with
      | inl d => exact d
      | inr _ => exact absurd hv (by simp [ValidCol0_B_Qlow])
    · rintro ⟨v, hv⟩
      cases v with
      | inl d => rfl
      | inr _ => exact absurd hv (by simp [ValidCol0_B_Qlow])
    · intro d; rfl
  rw [Fintype.card_congr hequiv, DSeq_card]; omega

/-- Key admissibility lemma: for τ in fiber of σ with σ.Q_bot.layerOrd ≤ 1,
    ¬ P_col0_has_c τ (i.e., τ.P col 0 is all dots).

    Reasoning detailed in `ValidCol0_B_Qlow` docblock: inr case leads to
    row_s contradiction because τ.Q(hP-1, 0) and σ.Q(hP-1, 0) both end up as s,
    violating row_s uniqueness. -/
private theorem fiber_P_col0_no_c_of_Qlow {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qlow : (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1)
    (τ : doubleDescent_Bplus_fiber σ) :
    ¬ P_col0_has_c τ.val := by
  -- Assume for contradiction τ.P(hP-1, 0) = c.
  rintro ⟨_, hPc⟩
  -- τ in fiber of σ: σ.Q = doubleDescent_B_paintR τ.
  have hddmap : doubleDescent_Bplus_map μP μQ τ.val = σ := τ.prop
  have hσ_eq : σ.val = doubleDescent_B_PBP τ.val.val (Or.inl τ.val.prop.1) :=
    congrArg Subtype.val hddmap.symm
  have hσ_Q_eq : σ.val.Q.paint (μP.colLen 0 - 1) 0 =
      PBP.doubleDescent_B_paintR τ.val.val (μP.colLen 0 - 1) 0 := by
    rw [hσ_eq]; rfl
  -- Rewrite h_Qlow using h_hQσ_eq so the index matches (hP-1, 0).
  have h_Qlow' : (PBP.doubleDescent_B_paintR τ.val.val (μP.colLen 0 - 1) 0).layerOrd ≤ 1 := by
    rw [← hσ_Q_eq, ← h_hQσ_eq]; exact h_Qlow
  -- Cell (hP-1, 0) ∈ τ.P.shape.
  have hmemP0 : (μP.colLen 0 - 1, 0) ∈ τ.val.val.P.shape := by
    rw [τ.val.prop.2.1]
    exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  -- Case split on the three branches of doubleDescent_B_paintR.
  simp only [PBP.doubleDescent_B_paintR] at h_Qlow'
  split_ifs at h_Qlow' with h1 h2
  · -- Branch 1: hP-1 < dotScolLen τ.P 1 ⇒ σ.Q = dot.
    -- Then (hP-1, 1) ∈ dotSdiag P, so τ.P(hP-1, 1) has layerOrd ≤ 1.
    -- mono_P: τ.P(hP-1, 0).layerOrd ≤ 1. But = c (layerOrd 3). Contradiction.
    have h_mem_sd : (μP.colLen 0 - 1, 1) ∈
        PBP.dotSdiag τ.val.val.P τ.val.val.mono_P := by
      rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.val.mono_P] at h1
      exact YoungDiagram.mem_iff_lt_colLen.mpr h1
    have h_memP1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.P.shape :=
      PBP.dotSdiag_le_shape τ.val.val.P τ.val.val.mono_P h_mem_sd
    have h_layer_P1 : (τ.val.val.P.paint (μP.colLen 0 - 1) 1).layerOrd ≤ 1 := by
      rw [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
          YoungDiagram.mem_cells] at h_mem_sd
      exact h_mem_sd.2
    have hmonoP := τ.val.val.mono_P (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) 1
      le_rfl (by omega) h_memP1
    rw [hPc] at hmonoP
    -- hmonoP: (c).layerOrd ≤ (P(hP-1, 1)).layerOrd, but layer ≤ 1.
    rcases hP1 : τ.val.val.P.paint (μP.colLen 0 - 1) 1 with _ | _ | _ | _ | _ <;>
      rw [hP1] at hmonoP h_layer_P1 <;>
      simp only [DRCSymbol.layerOrd] at hmonoP h_layer_P1 <;> omega
  · -- Branch 2: σ.Q(hP-1, 0) = s (middle branch). Requires dotSdiag Q membership.
    -- Then derive τ.Q(hP-1, 1) = s (only non-dot layer-1 symbol).
    -- Also τ.Q(hP-1, 0) = s (via dot_match, mono, sym). Apply row_s ⇒ contradiction.
    have h_mem_sd_Q : (μP.colLen 0 - 1, 1) ∈
        PBP.dotSdiag τ.val.val.Q τ.val.val.mono_Q := by
      rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.val.mono_Q] at h2
      exact YoungDiagram.mem_iff_lt_colLen.mpr h2
    have h_memQ1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.Q.shape :=
      PBP.dotSdiag_le_shape τ.val.val.Q τ.val.val.mono_Q h_mem_sd_Q
    have h_layer_Q1 : (τ.val.val.Q.paint (μP.colLen 0 - 1) 1).layerOrd ≤ 1 := by
      rw [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
          YoungDiagram.mem_cells] at h_mem_sd_Q
      exact h_mem_sd_Q.2
    -- τ.Q(hP-1, 1) ≠ dot: else dot_match gives (hP-1, 1) ∈ dotDiag ⊆ dotSdiag (P), contradicting h1.
    have hQ1_ne_dot : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 ≠ .dot := by
      intro hd
      have h_eqv := (τ.val.val.dot_match (μP.colLen 0 - 1) 1).mpr ⟨h_memQ1, hd⟩
      have h_memP1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.P.shape := h_eqv.1
      have hPd : τ.val.val.P.paint (μP.colLen 0 - 1) 1 = .dot := h_eqv.2
      -- (hP-1, 1) ∈ dotSdiag P: P = dot with layerOrd 0 ≤ 1.
      have h_dotS : (μP.colLen 0 - 1, 1) ∈ PBP.dotSdiag τ.val.val.P τ.val.val.mono_P := by
        rw [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
            YoungDiagram.mem_cells]
        exact ⟨h_memP1, by rw [hPd]; decide⟩
      rw [PBP.dotScolLen_eq_dotSdiag_colLen _ τ.val.val.mono_P] at h1
      exact absurd (YoungDiagram.mem_iff_lt_colLen.mp h_dotS) h1
    -- From sym_Q and layer ≤ 1 and ≠ dot: τ.Q(hP-1, 1) = s.
    have hQ1_s : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 = .s := by
      have hsym := τ.val.val.sym_Q _ _ h_memQ1
      rw [τ.val.prop.1] at hsym
      simp only [DRCSymbol.allowed] at hsym
      rcases hsym with h | h | h | h
      · exact absurd h hQ1_ne_dot
      · exact h
      · rw [h] at h_layer_Q1; simp only [DRCSymbol.layerOrd] at h_layer_Q1; omega
      · rw [h] at h_layer_Q1; simp only [DRCSymbol.layerOrd] at h_layer_Q1; omega
    -- (hP-1, 0) ∈ τ.Q.shape: Q.colLen 1 ≤ Q.colLen 0.
    have h_memQ0 : (μP.colLen 0 - 1, 0) ∈ τ.val.val.Q.shape := by
      rw [YoungDiagram.mem_iff_lt_colLen] at h_memQ1 ⊢
      have := τ.val.val.Q.shape.colLen_anti 0 1 (by omega)
      omega
    have hmonoQ := τ.val.val.mono_Q (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) 1
      le_rfl (by omega) h_memQ1
    rw [hQ1_s] at hmonoQ
    have hQ0_nd : τ.val.val.Q.paint (μP.colLen 0 - 1) 0 ≠ .dot := by
      intro hd
      have h_eqv := (τ.val.val.dot_match (μP.colLen 0 - 1) 0).mpr ⟨h_memQ0, hd⟩
      have hPd : τ.val.val.P.paint (μP.colLen 0 - 1) 0 = .dot := h_eqv.2
      rw [hPc] at hPd
      exact absurd hPd (by decide)
    have hQ0_s : τ.val.val.Q.paint (μP.colLen 0 - 1) 0 = .s := by
      have hsym := τ.val.val.sym_Q _ _ h_memQ0
      rw [τ.val.prop.1] at hsym
      simp only [DRCSymbol.allowed] at hsym
      rcases hsym with h | h | h | h
      · exact absurd h hQ0_nd
      · exact h
      · rw [h] at hmonoQ; simp only [DRCSymbol.layerOrd] at hmonoQ; omega
      · rw [h] at hmonoQ; simp only [DRCSymbol.layerOrd] at hmonoQ; omega
    -- Apply row_s.
    have h_rows := τ.val.val.row_s (μP.colLen 0 - 1) .R .R 0 1
      (by simp [paintBySide]; exact hQ0_s)
      (by simp [paintBySide]; exact hQ1_s)
    omega
  · -- Branch 3: σ.Q(hP-1, 0) = τ.Q(hP-1, 1); layerOrd ≤ 1 directly.
    by_cases h_memQ1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.Q.shape
    · by_cases hQ1_dot : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 = .dot
      · -- Case 3a: τ.Q(hP-1, 1) = dot. dot_match: τ.P(hP-1, 1) = dot.
        have h_eqv := (τ.val.val.dot_match (μP.colLen 0 - 1) 1).mpr ⟨h_memQ1, hQ1_dot⟩
        have h_memP1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.P.shape := h_eqv.1
        have hPd : τ.val.val.P.paint (μP.colLen 0 - 1) 1 = .dot := h_eqv.2
        have hmonoP := τ.val.val.mono_P (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) 1
          le_rfl (by omega) h_memP1
        rw [hPc, hPd] at hmonoP
        simp only [DRCSymbol.layerOrd] at hmonoP
        omega
      · -- Case 3b: τ.Q(hP-1, 1) ≠ dot; layer ≤ 1 forces = s.
        have hQ1_s : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 = .s := by
          have hsym := τ.val.val.sym_Q _ _ h_memQ1
          rw [τ.val.prop.1] at hsym
          simp only [DRCSymbol.allowed] at hsym
          rcases hsym with h | h | h | h
          · exact absurd h hQ1_dot
          · exact h
          · rw [h] at h_Qlow'; simp only [DRCSymbol.layerOrd] at h_Qlow'; omega
          · rw [h] at h_Qlow'; simp only [DRCSymbol.layerOrd] at h_Qlow'; omega
        -- Now derive τ.Q(hP-1, 0) = s and apply row_s.
        have h_memQ0 : (μP.colLen 0 - 1, 0) ∈ τ.val.val.Q.shape := by
          rw [YoungDiagram.mem_iff_lt_colLen] at h_memQ1 ⊢
          have := τ.val.val.Q.shape.colLen_anti 0 1 (by omega)
          omega
        have hmonoQ := τ.val.val.mono_Q (μP.colLen 0 - 1) 0 (μP.colLen 0 - 1) 1
          le_rfl (by omega) h_memQ1
        rw [hQ1_s] at hmonoQ
        have hQ0_nd : τ.val.val.Q.paint (μP.colLen 0 - 1) 0 ≠ .dot := by
          intro hd
          have h_eqv := (τ.val.val.dot_match (μP.colLen 0 - 1) 0).mpr ⟨h_memQ0, hd⟩
          have hPd : τ.val.val.P.paint (μP.colLen 0 - 1) 0 = .dot := h_eqv.2
          rw [hPc] at hPd
          exact absurd hPd (by decide)
        have hQ0_s : τ.val.val.Q.paint (μP.colLen 0 - 1) 0 = .s := by
          have hsym := τ.val.val.sym_Q _ _ h_memQ0
          rw [τ.val.prop.1] at hsym
          simp only [DRCSymbol.allowed] at hsym
          rcases hsym with h | h | h | h
          · exact absurd h hQ0_nd
          · exact h
          · rw [h] at hmonoQ; simp only [DRCSymbol.layerOrd] at hmonoQ; omega
          · rw [h] at hmonoQ; simp only [DRCSymbol.layerOrd] at hmonoQ; omega
        have h_rows := τ.val.val.row_s (μP.colLen 0 - 1) .R .R 0 1
          (by simp [paintBySide]; exact hQ0_s)
          (by simp [paintBySide]; exact hQ1_s)
        omega
    · -- (hP-1, 1) ∉ τ.Q.shape: τ.Q(hP-1, 1) = dot (paint_outside).
      -- By dot_match iff: not(P(hP-1,1) ∈ shape ∧ P(hP-1,1) = dot). So either (hP-1,1) ∉ P.shape
      -- or P(hP-1, 1) ≠ dot. In both subcases use the rich structure:
      --   Subcase A: (hP-1, 1) ∉ P.shape. Then P.colLen 1 ≤ hP-1. Combined with
      --     P(hP-1, 0) = c (so ∈ P.shape, hP-1 < P.colLen 0 = hP), this means P.shape at
      --     col 1 stops at or before hP-1. Use col_c_P: in col 0, there's only ONE c row.
      --     Actually the c constraint is per column. No direct contradiction.
      --   Use that σ.Q(hP-1, 0) = dot also means (hP-1, 0) is a dot in σ.Q? By dot_match
      --     on σ (applied to σ at (hP-1, 0)): σ.Q(hP-1, 0) = dot ↔ σ.P(hP-1, 0) ∈ shape ∧ = dot
      --     (if (hP-1, 0) ∈ σ.Q.shape).
      --   σ.Q.shape = μQ.shiftLeft, and hP-1 < μP.colLen 0 = μQ.shiftLeft.colLen 0, so
      --     (hP-1, 0) ∈ σ.Q.shape. By dot_match (on σ, at (hP-1, 0)): σ.P(hP-1, 0) ∈ σ.P.shape
      --     AND σ.P(hP-1, 0) = dot.
      --   σ.P.shape = μP.shiftLeft. For (hP-1, 0) to be in μP.shiftLeft, we need
      --     hP-1 < μP.shiftLeft.colLen 0 = μP.colLen 1 (by shiftLeft definition).
      --   So μP.colLen 1 > hP-1, i.e., (hP-1, 1) ∈ μP = τ.P.shape. This CONTRADICTS h_memQ1's
      --     being false (since (hP-1, 1) ∈ τ.P.shape implies it's in τ.Q.shape if P ⊆ Q...).
      --     Wait, we don't yet know P ⊆ Q. But we have σ.P(hP-1, 0) = dot and from doubleDescent,
      --     that's τ.P(hP-1, 1) (when hP-1 ≥ dotScolLen(P,1), which is h1's negation).
      --     Hmm, actually doubleDescent_B_paintL gives σ.P(i,0) as τ.P(i, 1) (for non-dot zone)
      --     or dot (dot zone). Negation of h1 means hP-1 ≥ dotScolLen τ.P 1, non-dot zone for L.
      --     So σ.P(hP-1, 0) = τ.P(hP-1, 1). And σ.P(hP-1, 0) = dot means τ.P(hP-1, 1) = dot.
      --     Then by dot_match on τ at (hP-1, 1): (hP-1, 1) ∈ τ.Q.shape ∧ τ.Q(hP-1, 1) = dot.
      --     This gives h_memQ1 contradiction! So Subcase A is impossible.
      --
      -- Establishing σ.Q(hP-1, 0) = dot here: σ.Q layerOrd ≤ 1 and from third branch def,
      --   σ.Q(hP-1, 0) = τ.Q(hP-1, 1). Since (hP-1, 1) ∉ τ.Q.shape, τ.Q.paint_outside gives
      --   τ.Q(hP-1, 1) = dot. So σ.Q(hP-1, 0) = dot. ✓
      --
      -- Deriving contradiction:
      have hτQ1_dot : τ.val.val.Q.paint (μP.colLen 0 - 1) 1 = .dot :=
        τ.val.val.Q.paint_outside _ _ h_memQ1
      -- Need to show that τ.P(hP-1, 1) = dot, then use dot_match to put (hP-1, 1) ∈ τ.Q.shape.
      -- Get σ.P(hP-1, 0) — σ.Q(hP-1, 0) = dot; by dot_match on σ, we have σ.P(hP-1, 0) = dot.
      -- σ's dot_match uses σ's shapes.
      -- σ.Q.shape = μQ.shiftLeft: (hP-1, 0) ∈ iff hP-1 < μQ.shiftLeft.colLen 0 = μP.colLen 0, yes.
      have hσ_memQ0 : (μP.colLen 0 - 1, 0) ∈ σ.val.Q.shape := by
        rw [σ.prop.2.2]
        exact YoungDiagram.mem_iff_lt_colLen.mpr (by rw [h_hQσ_eq]; omega)
      -- σ.Q(hP-1, 0) = τ.Q(hP-1, 1) = dot.
      have hσQ_dot : σ.val.Q.paint (μP.colLen 0 - 1) 0 = .dot := by
        rw [hσ_Q_eq]
        simp [PBP.doubleDescent_B_paintR, h1, h2, hτQ1_dot]
      -- By σ's dot_match: (hP-1, 0) ∈ σ.P.shape ∧ σ.P(hP-1, 0) = dot.
      have h_σ_eqv := (σ.val.dot_match (μP.colLen 0 - 1) 0).mpr ⟨hσ_memQ0, hσQ_dot⟩
      have hσ_memP0 : (μP.colLen 0 - 1, 0) ∈ σ.val.P.shape := h_σ_eqv.1
      have hσ_Pdot : σ.val.P.paint (μP.colLen 0 - 1) 0 = .dot := h_σ_eqv.2
      -- (hP-1, 0) ∈ σ.P.shape = μP.shiftLeft → hP-1 < μP.shiftLeft.colLen 0 = μP.colLen 1.
      -- So (hP-1, 1) ∈ μP = τ.P.shape.
      have h_memP1 : (μP.colLen 0 - 1, 1) ∈ τ.val.val.P.shape := by
        rw [τ.val.prop.2.1]
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft] at hσ_memP0
        exact hσ_memP0
      -- σ.P = doubleDescent_B_paintL τ: σ.P(hP-1, 0) = τ.P(hP-1, 1) (non-dot zone).
      have hσ_P_eq : σ.val.P.paint (μP.colLen 0 - 1) 0 =
          PBP.doubleDescent_B_paintL τ.val.val (μP.colLen 0 - 1) 0 := by
        rw [hσ_eq]; rfl
      have hτP1_dot : τ.val.val.P.paint (μP.colLen 0 - 1) 1 = .dot := by
        rw [hσ_Pdot] at hσ_P_eq
        simp only [PBP.doubleDescent_B_paintL, if_neg h1] at hσ_P_eq
        exact hσ_P_eq.symm
      -- By dot_match: τ.P(hP-1, 1) = dot and ∈ P.shape ⇒ (hP-1, 1) ∈ τ.Q.shape.
      have h_memQ1' : (μP.colLen 0 - 1, 1) ∈ τ.val.val.Q.shape :=
        ((τ.val.val.dot_match _ _).mp ⟨h_memP1, hτP1_dot⟩).1
      exact absurd h_memQ1' h_memQ1

/-- Upper bound for Qlow balanced case: fiber ↪ ValidCol0_B_Qlow.
    Uses `extractCol0_B` from the primitive-step upper bound, and the Qlow
    admissibility lemma `fiber_P_col0_no_c_of_Qlow`. -/
private theorem fiber_le_validCol0_B_Qlow {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_Qlow : (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) :
    Fintype.card (doubleDescent_Bplus_fiber σ) ≤
    Fintype.card (ValidCol0_B_Qlow (μP.colLen 0) (μQ.colLen 0)) := by
  apply Fintype.card_le_of_injective (fun τ => (⟨extractCol0_B τ.val hle, ?_⟩ :
    ValidCol0_B_Qlow (μP.colLen 0) (μQ.colLen 0)))
  · intro τ₁ τ₂ heq
    have := Subtype.ext_iff.mp heq
    exact extractCol0_B_injective_on_fiber σ hle this
  · -- Show extractCol0_B τ is inl (P col 0 all dots), i.e., in ValidCol0_B_Qlow.
    unfold extractCol0_B
    split_ifs with hPc
    · -- P_col0_has_c τ.val: contradiction via fiber_P_col0_no_c_of_Qlow.
      exact absurd hPc (fiber_P_col0_no_c_of_Qlow σ hP_pos h_hQσ_eq h_Qlow τ)
    · trivial

/-- **Specialized balanced lift for Qlow case**: takes a DSeq (no `h_Qd` needed).
    Constructs a PBPSet using `Sum.inl d : ValidCol0_B` internally. In the balanced
    case, the 5 sites in `liftPBP_B_bal_Qd` that use `sigma_Q_eq_d_of_Qbot_d_bal`
    (reachable only for `inr`) become unreachable here, and the balanced constraints
    (`mono_P/Q`, `row_s/r` at the col-0 boundary) discharge via the inl structure
    (col 0 P is all dots; col 0 Q has non-dot only at rows ≥ hP). -/
private noncomputable def liftPBP_B_bal_Qlow {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (d : DSeq (μQ.colLen 0 - μP.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0) :
    PBPSet .Bplus μP μQ := by
  -- Use Sum.inl d as the underlying ValidCol0_B witness.
  let v : ValidCol0_B (μP.colLen 0) (μQ.colLen 0) := Sum.inl d
  have hpoP : ∀ i j, (i, j) ∉ μP → liftPaint_B_P σ.val (μP.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero => simp only [liftPaint_B_P, liftCol0P_B, v]
    | succ j =>
      simp only [liftPaint_B_P]
      exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  have hpoQ : ∀ i j, (i, j) ∉ μQ → liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j = .dot := by
    intro i j hmem; cases j with
    | zero =>
      have hi : ¬(i < μQ.colLen 0) := by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega
      unfold liftPaint_B_Q liftCol0Q_B
      simp only [v]
      split_ifs with hc
      · exact absurd hc.2 hi
      · rfl
    | succ j =>
      simp only [liftPaint_B_Q]
      exact σ.val.Q.paint_outside i j (by
        rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft]; exact hmem)
  refine ⟨⟨.Bplus,
    ⟨μP, liftPaint_B_P σ.val (μP.colLen 0) v, hpoP⟩,
    ⟨μQ, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v, hpoQ⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P =>
    intro i j _
    show (liftPaint_B_P σ.val (μP.colLen 0) v i j).allowed .Bplus .L
    cases j with
    | zero => simp only [liftPaint_B_P, liftCol0P_B, v]; simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_P]
      have hmem' : (i, j) ∈ σ.val.P.shape := by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]
        have hinμP : (i, j + 1) ∈ μP := by
          rename_i hmem
          exact hmem
        exact hinμP
      have := σ.val.sym_P i j hmem'
      rw [σ.prop.1] at this; exact this
  case sym_Q =>
    intro i j _
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i j).allowed .Bplus .R
    cases j with
    | zero =>
      unfold liftPaint_B_Q liftCol0Q_B
      simp only [v]
      split_ifs with hc
      · simp [DRCSymbol.allowed]
        rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h]
      · simp [DRCSymbol.allowed]
    | succ j =>
      simp only [liftPaint_B_Q]
      rename_i hmem
      have := σ.val.sym_Q i j (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
      rw [σ.prop.1] at this; exact this
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        have hi : i < μP.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hi hle), ?_⟩
        change liftCol0Q_B _ _ v i = .dot
        simp only [liftCol0Q_B, v]; exact dif_neg (by omega)
      | succ j =>
        simp only [liftPaint_B_P] at hpaint
        have hmemP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemQ, hQdot⟩ := (σ.val.dot_match i j).mp ⟨hmemP, hpaint⟩
        exact ⟨by rw [σ.prop.2.2] at hmemQ; exact YoungDiagram.mem_shiftLeft.mp hmemQ,
               by simp only [liftPaint_B_Q]; exact hQdot⟩
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        unfold liftPaint_B_Q liftCol0Q_B at hpaint
        have hi : i < μQ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
        simp only [v] at hpaint
        split_ifs at hpaint with hc
        · rcases d.prop.1 ⟨i - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at hpaint
        · have hiP : i < μP.colLen 0 := by omega
          exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr hiP,
                 by unfold liftPaint_B_P liftCol0P_B; simp only [v]⟩
      | succ j =>
        simp only [liftPaint_B_Q] at hpaint
        have hmemQ : (i, j) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hmemP, hPdot⟩ := (σ.val.dot_match i j).mpr ⟨hmemQ, hpaint⟩
        exact ⟨by rw [σ.prop.2.1] at hmemP; exact YoungDiagram.mem_shiftLeft.mp hmemP,
               by simp only [liftPaint_B_P]; exact hPdot⟩
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_P σ.val (μP.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_P σ.val (μP.colLen 0) v i₂ j₂).layerOrd
    cases j₁ with
    | zero =>
      -- LHS: liftCol0P_B .inl d = .dot (layerOrd 0).
      have hLHS : liftPaint_B_P σ.val (μP.colLen 0) v i₁ 0 = .dot := by
        simp only [liftPaint_B_P, liftCol0P_B, v]
      rw [hLHS]; simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [liftPaint_B_P]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case mono_Q =>
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ j₁).layerOrd ≤
         (liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ j₂).layerOrd
    have hi₂ : i₂ < μQ.colLen j₂ := YoungDiagram.mem_iff_lt_colLen.mp hmem₂
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero =>
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (liftCol0Q_B _ _ v i₂).layerOrd
        unfold liftCol0Q_B; simp only [v]
        by_cases hc1 : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
        · have hb1 : i₁ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right hc1.1 hc1.2
          have hb2 : i₂ - μP.colLen 0 < μQ.colLen 0 - μP.colLen 0 := Nat.sub_lt_sub_right (by omega) hi₂
          rw [dif_pos hc1, dif_pos ⟨by omega, hi₂⟩]
          exact d.prop.2.1 ⟨_, hb1⟩ ⟨_, hb2⟩ (by simp; omega)
        · rw [dif_neg hc1]; simp [DRCSymbol.layerOrd]
      | succ j₂ =>
        change (liftCol0Q_B _ _ v i₁).layerOrd ≤ (σ.val.Q.paint i₂ j₂).layerOrd
        unfold liftCol0Q_B; simp only [v]
        by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
        · exfalso
          have hi₂_bound : i₂ < μQ.colLen (j₂+1) := hi₂
          have := h_weak (j₂ + 1) (by omega); omega
        · rw [dif_neg hc]; simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => omega
      | succ j₂ =>
        simp only [liftPaint_B_Q]
        exact σ.val.mono_Q i₁ j₁ i₂ j₂ hi (by omega)
          (by rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem₂)
  case row_s =>
    have hP_no_s : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .s := by
      intro i j; cases j with
      | zero => simp only [liftPaint_B_P, liftCol0P_B, v]; simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₁ (hP_no_s i j₁)
    · exact absurd h₂ (hP_no_s i j₂)
    · -- For v = inl d, liftCol0Q_B at row i = .s forces hP ≤ i.
      have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        simp only [v] at hne
        split_ifs at hne with hc
        · exact hc.1
        · exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_lb := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₂+1) ≤ μP.colLen 0 := h_weak (j₂+1) (by omega)
          omega
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_lb := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₁+1) ≤ μP.colLen 0 := h_weak (j₁+1) (by omega)
          omega
        | succ j₂ =>
          have := σ.val.row_s i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .s by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .s by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case row_r =>
    have hP_no_r : ∀ i j, liftPaint_B_P σ.val (μP.colLen 0) v i j ≠ .r := by
      intro i j; cases j with
      | zero => simp only [liftPaint_B_P, liftCol0P_B, v]; simp
      | succ j =>
        simp only [liftPaint_B_P]
        intro heq
        by_cases hmem : (i, j) ∈ σ.val.P.shape
        · have := σ.val.sym_P i j hmem; rw [σ.prop.1] at this
          simp [DRCSymbol.allowed] at this; rcases this with h | h <;> simp [h] at heq
        · simp [σ.val.P.paint_outside i j hmem] at heq
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    rcases s₁ with _ | _ <;> rcases s₂ with _ | _ <;> simp only at h₁ h₂
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₁ (hP_no_r i j₁)
    · exact absurd h₂ (hP_no_r i j₂)
    · have hQ0_nondot : ∀ x, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v x 0 ≠ .dot →
          μP.colLen 0 ≤ x := by
        intro x hne; simp only [liftPaint_B_Q] at hne; unfold liftCol0Q_B at hne
        simp only [v] at hne
        split_ifs at hne with hc
        · exact hc.1
        · exact absurd rfl hne
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => exact ⟨rfl, rfl⟩
        | succ j₂ =>
          exfalso
          have hi_lb := hQ0_nondot i (by rw [h₁]; decide)
          have hmemQ : (i, j₂ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₂ + 1) hout] at h₂; exact absurd h₂ (by decide)
          have hi₂ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₂+1) ≤ μP.colLen 0 := h_weak (j₂+1) (by omega)
          omega
      | succ j₁ =>
        cases j₂ with
        | zero =>
          exfalso
          have hi_lb := hQ0_nondot i (by rw [h₂]; decide)
          have hmemQ : (i, j₁ + 1) ∈ μQ := by
            by_contra hout; rw [hpoQ i (j₁ + 1) hout] at h₁; exact absurd h₁ (by decide)
          have hi₁ := YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have h_weak_j : μQ.colLen (j₁+1) ≤ μP.colLen 0 := h_weak (j₁+1) (by omega)
          omega
        | succ j₂ =>
          have := σ.val.row_r i .R .R j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .R i j₁ = .r by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .R i j₂ = .r by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    show i₁ = i₂
    simp only [liftPaint_B_P] at h₁ h₂
    cases j with
    | zero =>
      -- v = .inl d ⇒ liftCol0P_B = .dot ≠ .c.
      simp only [liftCol0P_B, v] at h₁
      exact absurd h₁ (by decide)
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .c at h₁
      simp only [liftPaint_B_Q] at h₁
      simp only [liftCol0Q_B, v] at h₁
      split_ifs at h₁ with hc
      rcases d.prop.1 ⟨i₁ - μP.colLen 0, by omega⟩ with h | h | h <;> simp [h] at h₁
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_c_Q j i₁ i₂ h₁ h₂
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_P σ.val (μP.colLen 0) v i₁ 0 = .d at h₁
      simp only [liftPaint_B_P, liftCol0P_B, v] at h₁
      exact absurd (show (DRCSymbol.dot : DRCSymbol) = .d from h₁) (by decide)
    | succ j =>
      simp only [liftPaint_B_P] at h₁ h₂
      exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q =>
    intro j i₁ i₂ h₁ h₂
    cases j with
    | zero =>
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₁ 0 = .d at h₁
      change liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) v i₂ 0 = .d at h₂
      simp only [liftPaint_B_Q] at h₁ h₂
      simp only [liftCol0Q_B, v] at h₁ h₂
      split_ifs at h₁ with hc₁
      split_ifs at h₂ with hc₂
      have heq := d.prop.2.2 ⟨i₁ - μP.colLen 0, by omega⟩ ⟨i₂ - μP.colLen 0, by omega⟩ h₁ h₂
      have := congr_arg Fin.val heq; simp at this; omega
    | succ j =>
      simp only [liftPaint_B_Q] at h₁ h₂
      exact σ.val.col_d_Q j i₁ i₂ h₁ h₂

/-- Round-trip: doubleDescent_Bplus_map (liftPBP_B_bal_Qlow σ d) = σ. -/
private theorem liftPBP_B_bal_Qlow_round_trip {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (d : DSeq (μQ.colLen 0 - μP.colLen 0))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0) :
    doubleDescent_Bplus_map μP μQ
      (liftPBP_B_bal_Qlow σ d hle hP_pos h_hQσ_eq h_weak) = σ := by
  set τ := liftPBP_B_bal_Qlow σ d hle hP_pos h_hQσ_eq h_weak
  apply Subtype.ext
  apply PBP_eq_of_data
  · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]; exact σ.prop.1.symm
  · apply PaintedYoungDiagram.ext'
    · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.1]; rfl
    · funext i j
      show PBP.doubleDescent_B_paintL τ.val i j = σ.val.P.paint i j
      simp only [PBP.doubleDescent_B_paintL]
      by_cases hds : i < PBP.dotScolLen τ.val.P (j + 1)
      · rw [if_pos hds]
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hds)
        have hpaint : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        rw [hpaint] at hlo
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σ : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσ_sym := σ.val.sym_P i j hmem_σ
        rw [σ.prop.1] at hσ_sym
        simp only [DRCSymbol.allowed] at hσ_sym
        rcases hσ_sym with h | h <;> rw [h] at hlo ⊢ <;>
          simp [DRCSymbol.layerOrd] at hlo ⊢
      · rw [if_neg hds]; rfl
  · apply PaintedYoungDiagram.ext'
    · simp only [doubleDescent_Bplus_map, doubleDescent_B_PBP]
      rw [σ.prop.2.2]; rfl
    · funext i j
      show PBP.doubleDescent_B_paintR τ.val i j = σ.val.Q.paint i j
      simp only [PBP.doubleDescent_B_paintR]
      by_cases hdsP : i < PBP.dotScolLen τ.val.P (j + 1)
      · rw [if_pos hdsP]
        have hpaintP : τ.val.P.paint i (j + 1) = σ.val.P.paint i j := rfl
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.P τ.val.mono_P
          (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsP)
        rw [hpaintP] at hlo
        have hmem_shape : (i, j + 1) ∈ τ.val.P.shape := by
          have := PBP.dotScolLen_le_colLen τ.val.P τ.val.mono_P (j + 1)
          exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have hmem_σP : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
          exact YoungDiagram.mem_iff_lt_colLen.mp hmem_shape
        have hσP_sym := σ.val.sym_P i j hmem_σP
        rw [σ.prop.1] at hσP_sym
        simp only [DRCSymbol.allowed] at hσP_sym
        have hσP_dot : σ.val.P.paint i j = .dot := by
          rcases hσP_sym with h | h <;> rw [h] at hlo <;>
            simp [DRCSymbol.layerOrd] at hlo ⊢ <;> exact h
        have ⟨_, hQd'⟩ := (σ.val.dot_match i j).mp ⟨hmem_σP, hσP_dot⟩
        exact hQd'.symm
      · rw [if_neg hdsP]
        by_cases hdsQ : i < PBP.dotScolLen τ.val.Q (j + 1)
        · rw [if_pos hdsQ]
          have hpaintQ : τ.val.Q.paint i (j + 1) = σ.val.Q.paint i j := rfl
          have hloQ := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.val.Q τ.val.mono_Q
            (by rwa [PBP.dotScolLen_eq_dotSdiag_colLen] at hdsQ)
          rw [hpaintQ] at hloQ
          have hmemQ : (i, j + 1) ∈ τ.val.Q.shape := by
            have := PBP.dotScolLen_le_colLen τ.val.Q τ.val.mono_Q (j + 1)
            exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
          have hmem_σQ : (i, j) ∈ σ.val.Q.shape := by
            rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen, YoungDiagram.colLen_shiftLeft]
            exact YoungDiagram.mem_iff_lt_colLen.mp hmemQ
          have hQ_ne_dot : σ.val.Q.paint i j ≠ .dot := by
            intro hQd'
            have ⟨hmemP, hPd⟩ := (σ.val.dot_match i j).mpr ⟨hmem_σQ, hQd'⟩
            have hlo_σP : (σ.val.P.paint i j).layerOrd ≤ 1 := by rw [hPd]; decide
            have hP_in_shape : (i, j + 1) ∈ τ.val.P.shape := by
              have : i < σ.val.P.shape.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hmemP
              rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft] at this
              exact YoungDiagram.mem_iff_lt_colLen.mpr this
            have hlo_τP : (τ.val.P.paint i (j + 1)).layerOrd ≤ 1 := hlo_σP
            have h_in_dsdiag : (i, j + 1) ∈ PBP.dotSdiag τ.val.P τ.val.mono_P := by
              simp only [PBP.dotSdiag, YoungDiagram.mem_mk, Finset.mem_filter,
                YoungDiagram.mem_cells]
              exact ⟨hP_in_shape, hlo_τP⟩
            have := YoungDiagram.mem_iff_lt_colLen.mp h_in_dsdiag
            rw [← PBP.dotScolLen_eq_dotSdiag_colLen] at this
            exact hdsP this
          have hσQ_sym := σ.val.sym_Q i j hmem_σQ
          rw [σ.prop.1] at hσQ_sym
          simp only [DRCSymbol.allowed] at hσQ_sym
          rcases hσQ_sym with h | h | h | h <;> rw [h] at hloQ hQ_ne_dot ⊢ <;>
            simp [DRCSymbol.layerOrd] at hloQ hQ_ne_dot ⊢
        · rw [if_neg hdsQ]; rfl

/-- liftPBP_B_bal_Qlow is injective: different d give different PBPs. -/
private theorem liftPBP_B_bal_Qlow_injective {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hP_pos : 0 < μP.colLen 0)
    (h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0)
    (h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0) :
    Function.Injective (fun d : DSeq (μQ.colLen 0 - μP.colLen 0) =>
      liftPBP_B_bal_Qlow σ d hle hP_pos h_hQσ_eq h_weak) := by
  intro d₁ d₂ h
  have hval : (liftPBP_B_bal_Qlow σ d₁ hle hP_pos h_hQσ_eq h_weak).val =
              (liftPBP_B_bal_Qlow σ d₂ hle hP_pos h_hQσ_eq h_weak).val :=
    congrArg Subtype.val h
  have hQeq : ∀ i, liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) (Sum.inl d₁) i 0 =
                    liftPaint_B_Q σ.val (μP.colLen 0) (μQ.colLen 0) (Sum.inl d₂) i 0 := by
    intro i
    exact congr_fun (congr_fun (congrArg (fun d => d.Q.paint) hval) i) 0
  simp only [liftPaint_B_Q, liftCol0Q_B] at hQeq
  apply Subtype.ext; funext ⟨k, hk⟩
  have hq := hQeq (μP.colLen 0 + k)
  have hlt : μP.colLen 0 + k < μQ.colLen 0 := by omega
  simp only [dif_pos (show μP.colLen 0 ≤ μP.colLen 0 + k ∧ μP.colLen 0 + k < μQ.colLen 0
    from ⟨by omega, hlt⟩)] at hq
  have hfin : (⟨μP.colLen 0 + k - μP.colLen 0, by omega⟩ : Fin _) = ⟨k, hk⟩ :=
    Fin.ext (by simp)
  rw [hfin] at hq; exact hq

/-- Lower bound for Qlow balanced case: ValidCol0_B_Qlow ↪ fiber.
    Reasoning: For v = Sum.inl d (ValidCol0_B_Qlow element), the balanced
    lift `liftPBP_B_bal_Qlow` produces a valid τ. Injectivity via DSeq distinctness. -/
private theorem validCol0_B_Qlow_le_fiber {r₁ r₂ : ℕ} {rest : DualPart} {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (_h_Qlow : (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) :
    Fintype.card (ValidCol0_B_Qlow (μP.colLen 0) (μQ.colLen 0)) ≤
    Fintype.card (doubleDescent_Bplus_fiber σ) := by
  -- Extract shape relations (parallel to fiber_card_B_bal_Qd).
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hpos₂ := hpos r₂ (by simp)
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  -- h_hQσ_eq: μQ.shiftLeft.colLen 0 = μP.colLen 0 (from balanced).
  have h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0 := by
    push_neg at h_bal
    rw [hP0]
    match rest, show μQ.shiftLeft.colLens = dpartColLensQ_B rest from
      (by rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]) with
    | [], heq => simp at h_bal; omega
    | [r₃], heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: [r₃]).get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm (by omega) hr₃_le
      have hpos₃ := hpos r₃ (by simp)
      have h : μQ.shiftLeft.colLens = [r₃/2] := by
        rw [heq]; simp [dpartColLensQ_B, hpos₃]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
    | r₃ :: r₄ :: rest', heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp : (⟨1, by simp⟩ : Fin 4) ≤ ⟨2, by simp⟩)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm h_bal hr₃_le
      have h : μQ.shiftLeft.colLens = r₃/2 :: dpartColLensQ_B rest' := by
        rw [heq, dpartColLensQ_B_cons₂]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
  -- h_weak: μQ.colLen j ≤ μP.colLen 0 for j ≥ 1.
  have h_weak : ∀ j, j ≥ 1 → μQ.colLen j ≤ μP.colLen 0 := by
    intro j hj
    have h1 : μQ.colLen j ≤ μQ.colLen 1 := μQ.colLen_anti 1 j (by omega)
    rw [show μQ.colLen 1 = μQ.shiftLeft.colLen 0 from
      (YoungDiagram.colLen_shiftLeft μQ 0).symm] at h1
    omega
  -- Go via DSeq: ValidCol0_B_Qlow ≃ DSeq (μQ.colLen 0 - μP.colLen 0) ↪ fiber.
  have hcongr : Fintype.card (ValidCol0_B_Qlow (μP.colLen 0) (μQ.colLen 0)) =
      Fintype.card (DSeq (μQ.colLen 0 - μP.colLen 0)) := by
    apply Fintype.card_congr
    refine {
      toFun := fun ⟨v, hv⟩ => ?_
      invFun := fun d => ⟨Sum.inl d, trivial⟩
      left_inv := ?_
      right_inv := ?_
    }
    · cases v with
      | inl d => exact d
      | inr _ => exact absurd hv (by simp [ValidCol0_B_Qlow])
    · rintro ⟨v, hv⟩
      cases v with
      | inl d => rfl
      | inr _ => exact absurd hv (by simp [ValidCol0_B_Qlow])
    · intro d; rfl
  rw [hcongr]
  exact Fintype.card_le_of_injective
    (fun d : DSeq (μQ.colLen 0 - μP.colLen 0) =>
      (⟨liftPBP_B_bal_Qlow σ d hle hP_pos h_hQσ_eq h_weak,
        liftPBP_B_bal_Qlow_round_trip σ d hle hP_pos h_hQσ_eq h_weak⟩ :
       doubleDescent_Bplus_fiber σ))
    (fun d₁ d₂ hEq =>
      liftPBP_B_bal_Qlow_injective σ hle hP_pos h_hQσ_eq h_weak
        (congrArg Subtype.val hEq))

/-- **Per-class fiber size (Q_bot ∈ {•, s})**: In balanced case, a sub-PBP σ with
    Q_bot.layerOrd ≤ 1 has a fiber of size 2k - 1 in the new level.

    **Structural closure**: matches `fiber_card_B_bal_Qr` pattern.
    - Upper bound via `fiber_le_validCol0_B_Qlow`.
    - Lower bound via `validCol0_B_Qlow_le_fiber`.
    - Cardinality of `ValidCol0_B_Qlow` = 2k - 1.

    **Numerical verification**: 82 dp cases via `tools/verify_all_B_lemmas.py`. -/
private theorem fiber_card_B_bal_Qlow {r₁ r₂ : ℕ} {rest : DualPart}
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)
    (h_Qlow : (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) :
    Fintype.card (doubleDescent_Bplus_fiber σ) = 2 * ((r₁ - r₂) / 2 + 1) - 1 := by
  -- Compute column lengths from dp structure (parallel to fiber_card_B_bal_Qd/Qr).
  have hP0 : μP.colLen 0 = r₂ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hP, dpartColLensP_B_cons₂])
  have hQ0 : μQ.colLen 0 = r₁ / 2 :=
    colLen_0_eq_of_colLens_cons (by rw [hQ, dpartColLensQ_B_cons₂])
  have h_ge := sortedGE_head_ge hsort
  have hle : μP.colLen 0 ≤ μQ.colLen 0 := by
    rw [hP0, hQ0]; exact Nat.div_le_div_right h_ge
  have heven₂ := heven r₂ (by simp)
  obtain ⟨b, hb⟩ := heven₂
  have hpos₂ := hpos r₂ (by simp)
  have hP_pos : 0 < μP.colLen 0 := by rw [hP0, hb]; omega
  have hk_eq : (r₁ - r₂) / 2 + 1 = μQ.colLen 0 - μP.colLen 0 + 1 := by
    rw [hP0, hQ0]
    have heven₁ := heven r₁ (by simp)
    obtain ⟨a, ha⟩ := heven₁
    rw [ha, hb]
    have h1 : (a + a) / 2 = a := by omega
    have h2 : (b + b) / 2 = b := by omega
    rw [h1, h2]
    have h_ge' : a + a ≥ b + b := by rw [← ha, ← hb]; exact h_ge
    have : (a + a - (b + b)) / 2 = a - b := by omega
    omega
  have hk_pos : (r₁ - r₂) / 2 + 1 ≥ 1 := by omega
  -- Balanced: μQ.shiftLeft.colLen 0 = μP.colLen 0.
  have h_hQσ_eq : μQ.shiftLeft.colLen 0 = μP.colLen 0 := by
    push_neg at h_bal
    rw [hP0]
    match rest, show μQ.shiftLeft.colLens = dpartColLensQ_B rest from
      (by rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]) with
    | [], heq => simp at h_bal; omega
    | [r₃], heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: [r₃]).get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm (by omega) hr₃_le
      have hpos₃ := hpos r₃ (by simp)
      have h : μQ.shiftLeft.colLens = [r₃/2] := by
        rw [heq]; simp [dpartColLensQ_B, hpos₃]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
    | r₃ :: r₄ :: rest', heq =>
      simp at h_bal
      have hr₃_le : r₃ ≤ r₂ := by
        have hsort' : Antitone (r₁ :: r₂ :: r₃ :: r₄ :: rest').get := hsort
        have h12 := @hsort' ⟨1, by simp⟩ ⟨2, by simp⟩ (by simp : (⟨1, by simp⟩ : Fin 4) ≤ ⟨2, by simp⟩)
        simpa using h12
      have hr₂_eq : r₂ = r₃ := le_antisymm h_bal hr₃_le
      have h : μQ.shiftLeft.colLens = r₃/2 :: dpartColLensQ_B rest' := by
        rw [heq, dpartColLensQ_B_cons₂]
      have hcl : μQ.shiftLeft.colLen 0 = r₃/2 := colLen_0_eq_of_colLens_cons h
      rw [hcl, hr₂_eq]
  apply le_antisymm
  · -- Upper bound: |fiber σ| ≤ |ValidCol0_B_Qlow| = 2k - 1.
    have h_le := fiber_le_validCol0_B_Qlow σ hle hP_pos h_hQσ_eq h_Qlow
    have hcard := validCol0_B_Qlow_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_le; omega
  · -- Lower bound: |ValidCol0_B_Qlow| ≤ |fiber σ|.
    have h_ge := validCol0_B_Qlow_le_fiber hP hQ hsort heven hpos h_bal σ h_Qlow
    have hcard := validCol0_B_Qlow_card (μP.colLen 0) (μQ.colLen 0) hle _ hk_eq hk_pos
    rw [hcard] at h_ge; omega

/-! ### Target: balanced double descent theorem

The theorem below is the **structural target** that, once proven, closes the three
`fiber_card_B_bal_*` lemmas uniformly. It mirrors `card_PBPSet_Bplus_primitive_step_top_Q`
at line ~2040.

**Differences from primitive**:
1. `hprimQ` is replaced by the balanced-case shape constraint h_bal.
2. The RHS is a **sum over σ** (not a product), because the fiber size varies by σ.
3. A per-σ `ValidCol0_B_bal σ sym` subtype replaces the uniform `ValidCol0_B` with topSym.

**Numerical uniformity**: 82 dp cases verify that for any σ₁, σ₂ with the same
`Q_bot.layerOrd`-class, `|ValidCol0_B_bal σ₁ sym| = |ValidCol0_B_bal σ₂ sym|`. So the
per-σ sum collapses to (q_d_comb · 4k + q_r_comb · (4k-2) + q_low_comb · (2k-1)) style.

**Infrastructure needed**:
- `ValidCol0_B_bal σ sym` type (~50 lines, subtype of ValidCol0_B with admissibility).
- `liftPBP_B_bal σ v h_adm` construction (~400 lines, balanced version of liftPBP_B).
- Round-trip + injectivity (~300 lines).
- Per-class card (~300 lines, three instances).

See `lean/docs/blueprints/balanced_double_descent_theorem.md` for full outline.

**Status**: Not yet implemented. The three fiber sorries above (`fiber_card_B_bal_Qd`,
`fiber_card_B_bal_Qr`, `fiber_card_B_bal_Qlow`) stand in for this theorem. -/

/-- **Balanced fiber identity**: in balanced case, the total count of
    new B⁺ ∪ B⁻ PBPs decomposes as a sum over sub-PBPs grouped by their Q_bot:
    each sub contributes `4k` (if Q_bot=d), `4k-2` (if Q_bot=r), or `2k-1` (if Q_bot.lo≤1).

    Proof: use the B⁺ ↔ B⁻ bijection (card_Bplus_eq_Bminus) and
    `card_PBPSet_Bplus_eq_sum_fiber` to reduce to a sum over B⁺ sub-PBPs.
    Split the B⁺ sub-PBPs by Q_bot class (trichotomy from `sym_Q`: ∈ {•, s, r, d}).
    Apply the three per-class fiber lemmas to each class.
    Then use γ-swap (B⁺ = B⁻) to reassemble the combined counts. -/
private theorem card_B_bal_grouped_fiber (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0)) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
      let k := (r₁ - r₂) / 2 + 1
      let q_d_comb := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card +
        (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card
      let q_r_comb := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card +
        (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card
      let q_low_comb := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card +
        (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
          (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card
      q_d_comb * (4 * k) + q_r_comb * (4 * k - 2) + q_low_comb * (2 * k - 1) := by
  -- Unfold the let-bindings and rewrite using γ-swap symmetries.
  simp only
  -- Step 1: By γ-swap, B⁻ filtered counts equal B⁺ filtered counts for each class.
  have h_swap_d := card_Bplus_Qbot_d_eq_Bminus_Qbot_d μP.shiftLeft μQ.shiftLeft
  have h_swap_r := card_Bplus_Qbot_r_eq_Bminus_Qbot_r μP.shiftLeft μQ.shiftLeft
  have h_swap_low := card_Bplus_SS_eq_Bminus_SS μP.shiftLeft μQ.shiftLeft
  -- Step 2: By γ-swap, |B⁻_new| = |B⁺_new|, so LHS = 2 * |B⁺_new|.
  have h_sym := (card_Bplus_eq_Bminus μP μQ).symm
  -- Step 3: Decompose |B⁺_new| = Σ_σ |fiber(σ)| (sum over rest B⁺).
  rw [h_sym, card_PBPSet_Bplus_eq_sum_fiber]
  -- Now goal: |B⁻_new| + Σ_σ fiber = q_d_comb * 4k + q_r_comb * (4k-2) + q_low_comb * (2k-1)
  -- where we rewrote the LHS. Actually goal is Σ + Σ = ..., so let's rewrite other summand too.
  -- Switch LHS to 2 * (Σ)
  set Bp_d := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card
  set Bp_r := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card
  set Bp_low := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card
  set Bm_d := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card
  set Bm_r := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card
  set Bm_low := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card
  set k := (r₁ - r₂) / 2 + 1 with hk_def
  -- Now goal: Σ_σ fiber + Σ_σ fiber = (Bp_d + Bm_d)*4k + (Bp_r + Bm_r)*(4k-2) + (Bp_low + Bm_low)*(2k-1)
  -- Use swap: Bm_d = Bp_d, Bm_r = Bp_r, Bm_low = Bp_low.
  have hBm_d : Bm_d = Bp_d := h_swap_d.symm
  have hBm_r : Bm_r = Bp_r := h_swap_r.symm
  have hBm_low : Bm_low = Bp_low := h_swap_low.symm
  rw [hBm_d, hBm_r, hBm_low]
  -- Now goal: Σ_σ fiber + Σ_σ fiber = (Bp_d + Bp_d)*4k + ... = 2·(Bp_d·4k + Bp_r·(4k-2) + Bp_low·(2k-1))
  -- Suffices to show Σ_σ fiber = Bp_d·4k + Bp_r·(4k-2) + Bp_low·(2k-1), then ring.
  suffices h : (∑ σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft,
      Fintype.card (doubleDescent_Bplus_fiber σ)) =
      Bp_d * (4 * k) + Bp_r * (4 * k - 2) + Bp_low * (2 * k - 1) by
    rw [h]; ring
  -- Step 5: Partition sum by Q_bot class using Finset.sum_filter + exhaustive split.
  -- σ.Q_bot ∈ {•, s, r, d} (allowed for B⁺).
  -- Q_bot = d: fiber = 4k
  -- Q_bot = r: fiber = 4k-2
  -- Q_bot.lo ≤ 1 ({•, s}): fiber = 2k-1
  -- Partition: Σ = Σ_{Qbot=d} + Σ_{Qbot=r} + Σ_{Qbot.lo≤1}.
  -- Each partial sum = |class| · constant (per-class fiber lemma).
  rw [show Bp_d = (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
      σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card from rfl,
      show Bp_r = (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
      σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card from rfl,
      show Bp_low = (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
      (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card from rfl]
  -- Split Finset.univ into three disjoint pieces by Q_bot class.
  -- Predicate trichotomy (for B+): Q_bot ∈ {•, s, r, d}.
  -- Note Q=• has layerOrd 0, Q=s has layerOrd 1, Q=r has layerOrd 2, Q=d has layerOrd 4.
  -- So "low = {•, s}" = "layerOrd ≤ 1" is disjoint from "Q=r" and "Q=d".
  -- Combined with .r and .d, this is a full partition of Q_bot values.
  have h_partition : (Finset.univ : Finset (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft)) =
      (Finset.univ.filter fun σ => σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) ∪
      (Finset.univ.filter fun σ => σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r) ∪
      (Finset.univ.filter fun σ =>
          (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    -- Show: true ↔ (Q=d ∨ Q=r ∨ Q.lo≤1)
    constructor
    · intro _
      -- Need to establish σ.val.Q.paint ∈ {•, s, r, d} via sym_Q.
      -- For balanced case, μQ.shiftLeft.colLen 0 > 0 (since rest non-empty).
      -- But we need this fact. Use the hQ info to derive it.
      -- Actually, σ is a subtype over the shifted Q; σ's existence already implies
      -- the shape is valid. But we need to know the (colLen 0 - 1, 0) cell exists in σ's Q shape.
      -- Here's the subtle point: if μQ.shiftLeft.colLen 0 = 0, then (colLen 0 - 1, 0) = (-1 mod _, 0)
      -- via Nat subtraction giving 0; the cell may or may not be in the shape.
      -- If μQ.shiftLeft.colLen 0 = 0, then there's NO cell at row 0 col 0, so Q.paint(0,0) = •
      -- by paint_outside. So Q_bot = •, which has layerOrd 0 ≤ 1 → Q.lo≤1 branch.
      by_cases h_Qs_pos : μQ.shiftLeft.colLen 0 > 0
      · -- Cell exists: use sym_Q.
        have hmem : (μQ.shiftLeft.colLen 0 - 1, 0) ∈ μQ.shiftLeft := by
          rw [YoungDiagram.mem_iff_lt_colLen]; omega
        have hmemQ : (μQ.shiftLeft.colLen 0 - 1, 0) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact hmem
        have hsym := σ.val.sym_Q _ _ hmemQ
        rw [σ.prop.1] at hsym
        simp [DRCSymbol.allowed] at hsym
        rcases hsym with h | h | h | h
        · right; rw [h]; decide
        · right; rw [h]; decide
        · left; right; exact h
        · left; left; exact h
      · -- μQ.shiftLeft.colLen 0 = 0 → cell not in shape → Q.paint = dot → Q.lo ≤ 1.
        push_neg at h_Qs_pos
        have h0 : μQ.shiftLeft.colLen 0 = 0 := by omega
        have hnmem : (μQ.shiftLeft.colLen 0 - 1, 0) ∉ σ.val.Q.shape := by
          rw [σ.prop.2.2, YoungDiagram.mem_iff_lt_colLen]; omega
        have hdot : σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .dot :=
          σ.val.Q.paint_outside _ _ hnmem
        right; rw [hdot]; decide
    · intro _; trivial
  -- The three sets are pairwise disjoint.
  have h_disj_dr : Disjoint
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d)
      (Finset.univ.filter fun σ => σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r) := by
    rw [Finset.disjoint_filter]
    intros _ _ h1 h2; rw [h1] at h2; exact DRCSymbol.noConfusion h2
  have h_disj_dl : Disjoint
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d)
      (Finset.univ.filter fun σ =>
        (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) := by
    rw [Finset.disjoint_filter]
    intros _ _ h1 h2; rw [h1] at h2; simp [DRCSymbol.layerOrd] at h2
  have h_disj_rl : Disjoint
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r)
      (Finset.univ.filter fun σ =>
        (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) := by
    rw [Finset.disjoint_filter]
    intros _ _ h1 h2; rw [h1] at h2; simp [DRCSymbol.layerOrd] at h2
  -- Apply partition to the sum.
  have h_sum_split : (∑ σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft,
      Fintype.card (doubleDescent_Bplus_fiber σ)) =
      (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d,
        Fintype.card (doubleDescent_Bplus_fiber σ)) +
      (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r,
        Fintype.card (doubleDescent_Bplus_fiber σ)) +
      (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1,
        Fintype.card (doubleDescent_Bplus_fiber σ)) := by
    conv_lhs => rw [show (Finset.univ : Finset _) =
      ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d) ∪
        (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
          σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r)) ∪
        (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
            (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1) from h_partition]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_union_left]
      exact ⟨h_disj_dl, h_disj_rl⟩)]
    rw [Finset.sum_union h_disj_dr]
  rw [h_sum_split]
  -- Apply per-class fiber lemmas to each sum.
  -- For the Q=d class: all fibers are 4k.
  have h_sum_d : (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d,
      Fintype.card (doubleDescent_Bplus_fiber σ)) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card * (4 * k) := by
    trans ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).sum (fun _ => 4 * k))
    · apply Finset.sum_congr rfl
      intros σ hσ
      simp only [Finset.mem_filter] at hσ
      exact fiber_card_B_bal_Qd hP hQ hsort heven hpos h_bal σ hσ.2
    · simp [Finset.sum_const, mul_comm]
  have h_sum_r : (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r,
      Fintype.card (doubleDescent_Bplus_fiber σ)) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card * (4 * k - 2) := by
    trans ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).sum (fun _ => 4 * k - 2))
    · apply Finset.sum_congr rfl
      intros σ hσ
      simp only [Finset.mem_filter] at hσ
      exact fiber_card_B_bal_Qr hP hQ hsort heven hpos h_bal σ hσ.2
    · simp [Finset.sum_const, mul_comm]
  have h_sum_low : (∑ σ ∈ Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1,
      Fintype.card (doubleDescent_Bplus_fiber σ)) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card * (2 * k - 1) := by
    trans ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).sum (fun _ => 2 * k - 1))
    · apply Finset.sum_congr rfl
      intros σ hσ
      simp only [Finset.mem_filter] at hσ
      exact fiber_card_B_bal_Qlow hP hQ hsort heven hpos h_bal σ hσ.2
    · simp [Finset.sum_const, mul_comm]
  rw [h_sum_d, h_sum_r, h_sum_low]

/-- **B⁺ set partition**: for σ ∈ B⁺, σ.Q_bot ∈ {•, s, r, d}. So the predicates
    `Q_bot ≠ d`, `Q_bot.lo ≤ 1`, `Q_bot = r` partition via
    `|Q_bot ≠ d| = |Q_bot.lo ≤ 1| + |Q_bot = r|`.

    This is a direct DRCSymbol case analysis using `sym_Q` for B⁺. -/
private theorem card_Bplus_nonD_eq_low_plus_r (μP μQ : YoungDiagram)
    (hQ_pos : μQ.colLen 0 > 0) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card =
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card +
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card := by
  -- Partition |Q_bot ≠ d| = |Q_bot.lo ≤ 1| + |Q_bot = r| for B⁺.
  -- The two subsets are disjoint and cover Q_bot ≠ d (since Q_bot ∈ {•, s, r, d}).
  -- Step 1: Split as disjoint union {Q.lo≤1} ∪ {Q=r}
  have h_union : (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d) =
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1) ∪
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h_ne_d
      -- σ.val.Q.paint ∈ {•, s, r, d} by sym_Q for B+; ≠ d means ∈ {•, s, r}
      have hmem : (μQ.colLen 0 - 1, 0) ∈ μQ := by
        rw [YoungDiagram.mem_iff_lt_colLen]; omega
      have hmemQ : (μQ.colLen 0 - 1, 0) ∈ σ.val.Q.shape := by
        rw [σ.prop.2.2]; exact hmem
      have hsym := σ.val.sym_Q _ _ hmemQ
      simp [σ.prop.1, DRCSymbol.allowed] at hsym
      -- hsym: Q_bot = dot ∨ Q_bot = s ∨ Q_bot = r ∨ Q_bot = d
      rcases hsym with h | h | h | h
      · left; rw [h]; decide
      · left; rw [h]; decide
      · right; exact h
      · exact absurd h h_ne_d
    · rintro (h | h)
      · intro heq; rw [heq] at h; exact absurd h (by decide)
      · intro heq; rw [heq] at h; exact absurd h (by decide)
  rw [h_union, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro σ _ hlow heq
  rw [heq] at hlow
  exact absurd hlow (by decide)

/-- **B⁻ full partition by Q_bot**: every σ ∈ B⁻ has Q_bot ∈ {•, s, r, d}, so
    `|B⁻| = |Q_bot = d| + |Q_bot = r| + |Q_bot.lo ≤ 1|` (the three cells are disjoint
    and exhaustive). -/
private theorem card_Bminus_partition_Qbot (μP μQ : YoungDiagram)
    (hQ_pos : μQ.colLen 0 > 0) :
    Fintype.card (PBPSet .Bminus μP μQ) =
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card := by
  -- Step 1: |B⁻| = |B⁻ Q=d| + |B⁻ Q≠d| by filter/not split.
  have h_split1 : Fintype.card (PBPSet .Bminus μP μQ) =
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card := by
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (p := fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d)]
  -- Step 2: |B⁻ Q≠d| = |B⁻ Q=r| + |B⁻ Q.lo≤1| (B⁻ Q ∈ {•,s,r,d}).
  have h_split2 : (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card =
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card +
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1).card := by
    -- Mirror of `card_Bplus_nonD_eq_low_plus_r` but for B⁻ with Q=r listed first.
    have h_union : (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d) =
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r) ∪
      (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
        (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd ≤ 1) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h_ne_d
        have hmem : (μQ.colLen 0 - 1, 0) ∈ μQ := by
          rw [YoungDiagram.mem_iff_lt_colLen]; omega
        have hmemQ : (μQ.colLen 0 - 1, 0) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact hmem
        have hsym := σ.val.sym_Q _ _ hmemQ
        simp [σ.prop.1, DRCSymbol.allowed] at hsym
        -- hsym: Q_bot ∈ {dot, s, r, d}; ≠ d means ∈ {dot, s, r}
        rcases hsym with h | h | h | h
        · right; rw [h]; decide
        · right; rw [h]; decide
        · left; exact h
        · exact absurd h h_ne_d
      · rintro (h | h)
        · intro heq; rw [heq] at h; exact absurd h (by decide)
        · intro heq; rw [heq] at h; exact absurd h (by decide)
    rw [h_union]
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_filter]
    intro σ _ heq hlow
    rw [heq] at hlow
    exact absurd hlow (by decide)
  -- Combine.
  rw [h_split1, h_split2, Nat.add_assoc]

/-- **B balanced step identity** — Task #12 main goal.
    Derived from `card_B_bal_grouped_fiber` + A1, A3, Total(rest), γ-swap, partitions.

    Algebra: `card(new) = dd'·4k + (rc'-ss')·(4k-2) + 2·ss'·(2k-1)`,
    and `2·(2k-1) = 4k-2`, so this equals `dd'·4k + rc'·(4k-2)`.

    Takes `h_total_rest` as a parameter (Total at rest) to derive the RC-class count
    via partitions instead of A2. -/
private theorem card_PBPSet_B_balanced_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0))
    (h_total_rest :
      Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) +
      Fintype.card (PBPSet .Bminus μP.shiftLeft μQ.shiftLeft) =
      tripleSum (countPBP_B rest)) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
      let k := (r₁ - r₂) / 2 + 1
      let (dd', rc', _) := countPBP_B rest
      dd' * (4 * k) + rc' * (4 * k - 2) := by
  -- Shape info at rest level
  have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
  have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
    rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
  have hsort_rest : rest.SortedGE := sorted_tail₂ hsort
  have heven_rest : ∀ r ∈ rest, Even r :=
    fun r hr => heven r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  have hpos_rest : ∀ r ∈ rest, 0 < r :=
    fun r hr => hpos r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  -- Q_pos at rest level: rest non-empty (balanced requires r₂ ≤ r₃ with r₃ ∈ rest).
  have h_rest_pos : rest ≠ [] := by
    intro h_nil
    rw [h_nil] at h_bal
    simp at h_bal
    have : r₂ > 0 := hpos r₂ (by simp)
    omega
  have hQ_sh_pos : μQ.shiftLeft.colLen 0 > 0 := by
    -- μQ.shiftLeft.colLens = dpartColLensQ_B rest. Rest non-empty + positive ⇒ colLen 0 > 0.
    obtain ⟨r₃, rest', h_rest_eq⟩ := List.exists_cons_of_ne_nil h_rest_pos
    have hQs0 : μQ.shiftLeft.colLen 0 = r₃ / 2 := by
      apply colLen_0_eq_of_colLens_cons (tail := dpartColLensQ_B rest'.tail)
      rw [hQ_sh, h_rest_eq]
      cases rest' with
      | nil =>
        have h_r₃pos : r₃ > 0 := hpos r₃ (by rw [h_rest_eq]; simp)
        simp [dpartColLensQ_B, h_r₃pos]
      | cons r₄ rest'' =>
        simp [dpartColLensQ_B]
    rw [hQs0]
    have h_r₃_even : Even r₃ := heven_rest r₃ (by rw [h_rest_eq]; simp)
    have h_r₃_pos : r₃ > 0 := hpos_rest r₃ (by rw [h_rest_eq]; simp)
    obtain ⟨a, ha⟩ := h_r₃_even
    omega
  -- Apply fiber identity
  have h_fiber := card_B_bal_grouped_fiber r₁ r₂ rest μP μQ hP hQ hsort heven hpos h_bal
  -- A1, A3 at rest level (A2 replaced by Total+partitions+γ-swap derivation).
  have h_A1 := card_B_DD_alpha_eq_countB_dd rest hP_sh hQ_sh hsort_rest heven_rest hpos_rest
    hQ_sh_pos h_total_rest
  have h_A3 := card_B_SS_alpha_eq_countB_ss rest hP_sh hQ_sh hsort_rest heven_rest hpos_rest hQ_sh_pos
  -- γ-swap at rest level
  have h_swap := card_Bplus_SS_eq_Bminus_SS μP.shiftLeft μQ.shiftLeft
  have h_swap_d := card_Bplus_Qbot_d_eq_Bminus_Qbot_d μP.shiftLeft μQ.shiftLeft
  -- B+ set partition at rest level
  have h_part := card_Bplus_nonD_eq_low_plus_r μP.shiftLeft μQ.shiftLeft hQ_sh_pos
  -- B⁻ set partition at rest level: |B⁻_rest| = Bm_d + Bm_r + Bm_low
  have h_part_Bm := card_Bminus_partition_Qbot μP.shiftLeft μQ.shiftLeft hQ_sh_pos
  -- B⁺ split by Q=d: |B⁺_rest| = Bp_d + |B⁺_rest Q≠d|
  have h_split_Bp : Fintype.card (PBPSet .Bplus μP.shiftLeft μQ.shiftLeft) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card +
      (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 ≠ .d).card := by
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (p := fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
        σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d)]
  -- Destructure countPBP_B rest
  rcases h_ct : countPBP_B rest with ⟨dd', rc', ss'⟩
  rw [h_ct] at h_A1 h_A3 h_total_rest
  simp only at h_A1 h_A3 h_total_rest
  have h_ts : tripleSum (dd', rc', ss') = dd' + rc' + ss' := rfl
  rw [h_ts] at h_total_rest
  -- Unfold let-bindings in the goal
  show _ = dd' * (4 * ((r₁ - r₂) / 2 + 1)) + rc' * (4 * ((r₁ - r₂) / 2 + 1) - 2)
  -- h_fiber's let/have bindings need the same destructuring.
  -- h_fiber was stated using μQ.shiftLeft forms; let me evaluate it now.
  have h_fiber' : Fintype.card (PBPSet .Bplus μP μQ) +
      Fintype.card (PBPSet .Bminus μP μQ) =
    ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
         σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card +
     (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
         σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card) *
      (4 * ((r₁ - r₂) / 2 + 1)) +
    ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
         σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card +
     (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
         σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card) *
      (4 * ((r₁ - r₂) / 2 + 1) - 2) +
    ((Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
         (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card +
     (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
         (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card) *
      (2 * ((r₁ - r₂) / 2 + 1) - 1) := h_fiber
  rw [h_fiber']
  -- Abbreviate card expressions
  set Bp_d := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card
  set Bm_d := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .d).card
  set Bp_r := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card
  set Bm_r := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 = .r).card
  set Bp_low := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card
  set Bm_low := (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ.shiftLeft =>
    (σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0).layerOrd ≤ 1).card
  set Bp_nonD := (Finset.univ.filter fun σ : PBPSet .Bplus μP.shiftLeft μQ.shiftLeft =>
    σ.val.Q.paint (μQ.shiftLeft.colLen 0 - 1) 0 ≠ .d).card
  set k := (r₁ - r₂) / 2 + 1 with hk_def
  have hk_pos : k ≥ 1 := by rw [hk_def]; omega
  have h_2km1 : 2 * (2 * k - 1) = 4 * k - 2 := by omega
  have h_Bp_low_eq : Bp_low = ss' := h_swap.trans h_A3
  -- Derive h_rc_sum from h_total_rest + partitions + γ-swap + A1 + A3 (no A2 needed).
  -- h_total_rest: |B⁺_rest| + |B⁻_rest| = dd' + rc' + ss'
  -- h_split_Bp: |B⁺_rest| = Bp_d + Bp_nonD
  -- h_part: Bp_nonD = Bp_low + Bp_r
  -- h_part_Bm: |B⁻_rest| = Bm_d + Bm_r + Bm_low
  -- h_swap_d: Bp_d = Bm_d, hence 2·Bp_d = dd' (from h_A1)
  -- h_swap: Bp_low = Bm_low = ss' (from h_A3)
  -- Sum: Bp_d + Bp_low + Bp_r + Bm_d + Bm_r + Bm_low = dd' + rc' + ss'
  --    = dd' + 2·ss' + Bp_r + Bm_r (using A1, γ-swap, A3)
  -- So Bp_r + Bm_r = rc' - ss', hence Bp_r + Bm_r + ss' = rc'.
  have h_rc_sum : Bp_r + Bm_r + ss' = rc' := by
    have h_part' : Bp_nonD = Bp_low + Bp_r := h_part
    rw [h_part'] at h_split_Bp
    -- h_split_Bp: |B⁺_rest| = Bp_d + (Bp_low + Bp_r)
    rw [h_split_Bp, h_part_Bm] at h_total_rest
    -- h_total_rest: Bp_d + (Bp_low + Bp_r) + (Bm_d + Bm_r + Bm_low) = dd' + rc' + ss'
    rw [h_Bp_low_eq, h_swap_d] at h_total_rest
    -- h_total_rest: Bp_d + (ss' + Bp_r) + (Bp_d + Bm_r + Bm_low) = dd' + rc' + ss'
    -- (Note h_swap_d rewrites Bm_d to Bp_d; Bp_d + Bm_d = 2·Bp_d = dd' by h_A1.)
    rw [show Bm_low = ss' from h_swap.symm.trans h_Bp_low_eq] at h_total_rest
    -- h_total_rest: Bp_d + (ss' + Bp_r) + (Bp_d + Bm_r + ss') = dd' + rc' + ss'
    -- And h_A1: Bp_d + Bm_d = dd', with h_swap_d (Bp_d = Bm_d) gives 2·Bp_d = dd'.
    -- But we might need it cleaner; let's just use h_A1 directly.
    -- h_A1 originally: Bp_d + Bm_d = dd'. After rw h_swap_d on h_A1: 2·Bp_d = dd'.
    -- Actually h_swap_d is symmetric; h_A1 still holds. Use omega with both.
    omega
  -- Goal: (Bp_d + Bm_d)·4k + (Bp_r + Bm_r)·(4k-2) + (Bp_low + Bm_low)·(2k-1)
  --       = dd'·4k + rc'·(4k-2)
  rw [h_A1, h_Bp_low_eq, h_A3]
  -- Goal: dd'·4k + (Bp_r + Bm_r)·(4k-2) + (ss' + ss')·(2k-1) = dd'·4k + rc'·(4k-2)
  have h_double : (ss' + ss') * (2 * k - 1) = ss' * (4 * k - 2) := by
    have : (ss' + ss') * (2 * k - 1) = ss' * (2 * (2 * k - 1)) := by ring
    rw [this, h_2km1]
  rw [h_double]
  have h_combine : (Bp_r + Bm_r) * (4 * k - 2) + ss' * (4 * k - 2) = rc' * (4 * k - 2) := by
    rw [← Nat.add_mul, h_rc_sum]
  omega

/-- **Proposition 10.11 for B type:**
    card(PBPSet .Bplus μP μQ) + card(PBPSet .Bminus μP μQ) = tripleSum(countPBP_B dp).

    Proved by structural induction on `dp`.
    - Empty base case: trivial.
    - Singleton `[r₁]`: via `card_PBPSet_B_singleton`.
    - `r₁ :: r₂ :: rest`:
      - Primitive (r₂ > rest.head?.getD 0): via `card_PBPSet_B_primitive_step`.
      - Balanced (r₂ ≤ rest.head?.getD 0): **admitted** — requires per-tail-class
        fiber analysis with corrected α-dependent tail classes (Prop 10.9(b)). -/
theorem card_PBPSet_B_eq_tripleSum_countPBP_B (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B dp) := by
  match dp, hP, hQ, hsort, heven, hpos with
  | [], hP, hQ, _, _, _ =>
    -- Empty base case
    have h1 := yd_of_colLens_nil (by rw [hP]; rfl)
    have h2 := yd_of_colLens_nil (by rw [hQ]; rfl)
    subst h1; subst h2
    simp [card_PBPSet_bot, tripleSum, countPBP_B]
  | [r₁], hP, hQ, _, heven, hpos =>
    -- Singleton base case
    exact card_PBPSet_B_singleton r₁ μP μQ hP hQ (heven r₁ (by simp)) (hpos r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos =>
    -- Inductive step: two or more rows
    have hP_sh : μP.shiftLeft.colLens = dpartColLensP_B rest := by
      rw [YoungDiagram.colLens_shiftLeft, hP]; simp [dpartColLensP_B]
    have hQ_sh : μQ.shiftLeft.colLens = dpartColLensQ_B rest := by
      rw [YoungDiagram.colLens_shiftLeft, hQ]; simp [dpartColLensQ_B]
    have hsort' := sorted_tail₂ hsort
    have heven' : ∀ r ∈ rest, Even r :=
      fun r hr => heven r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have hpos' : ∀ r ∈ rest, 0 < r :=
      fun r hr => hpos r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    have h_ih := card_PBPSet_B_eq_tripleSum_countPBP_B rest
      μP.shiftLeft μQ.shiftLeft hP_sh hQ_sh hsort' heven' hpos'
    by_cases h_prim : r₂ > rest.head?.getD 0
    · -- Primitive case: all fibers uniform, total = total(rest) × fiber_size
      have := card_PBPSet_B_primitive_step r₁ r₂ rest μP μQ hP hQ hsort heven h_prim
      rw [this, h_ih]
      simp only [countPBP_B, h_prim, ite_true, tripleSum]; ring
    · -- Balanced case: delegate to `card_PBPSet_B_balanced_step` (focused sorry).
      have h_step := card_PBPSet_B_balanced_step r₁ r₂ rest μP μQ hP hQ hsort heven hpos h_prim h_ih
      rw [h_step]
      -- Unfold tripleSum of countPBP_B's balanced formula
      simp only [countPBP_B, h_prim, ite_false, tripleSum]
      rcases h_ct : countPBP_B rest with ⟨dd', rc', ss'⟩
      simp only [tailCoeffs, nu]
      -- Show the two forms of the balanced RHS are equal algebraically.
      -- tailCoeffs(k) entries sum to 4k and 4k-2.
      set k := (r₁ - r₂) / 2 + 1 with hk_def
      have hk_pos : k ≥ 1 := by rw [hk_def]; omega
      by_cases hk : k ≥ 2
      · simp only [if_pos hk]
        -- Expand k - 1 + 1 = k, k - 2 + 1 = k - 1
        have e1 : k - 1 + 1 = k := by omega
        have e2 : k - 2 + 1 = k - 1 := by omega
        rw [e1, e2]
        -- Goal: dd'·4k + rc'·(4k-2) = dd'·(k + (k-1)) + rc'·(2·(k-1)) + (dd'·(2k) + rc'·(k + (k-1))) + (dd'·1 + rc'·1)
        -- Simplify: dd'·(3k-1+1) + rc'·(2k-2 + k+k-1 + 1) = dd'·4k + rc'·(4k-2)
        have hk1 : k - 1 + 1 = k := by omega
        generalize hkm1 : k - 1 = m at *
        -- Now k = m + 1, m ≥ 1
        have hk_eq : k = m + 1 := by omega
        rw [hk_eq]
        have hm_sub : 4 * (m + 1) - 2 = 4 * m + 2 := by omega
        rw [hm_sub]
        ring
      · simp only [if_neg hk]
        push_neg at hk
        have hk1 : k = 1 := by omega
        rw [hk1]
        simp
        ring

/-- Corollary: each of B⁺ and B⁻ has half the total. -/
theorem card_PBPSet_Bplus_eq (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) = tripleSum (countPBP_B dp) / 2 := by
  have h_eq := card_Bplus_eq_Bminus μP μQ
  have h_total := card_PBPSet_B_eq_tripleSum_countPBP_B dp μP μQ hP hQ hsort heven hpos
  omega

/-- **α-class RC count** (γ-asymmetric): B⁺ with Q_bot ≠ d, plus B⁻ with Q_bot = r
    equals `countPBP_B(dp).2.1`. The asymmetry reflects the tail correction:
    B⁺ with natural Q_bot ∈ {•, s} gets corrected x_τ = c (RC), while B⁻ stays SS.

    Structural proof:
    - Empty: hQ_pos false (vacuous).
    - Singleton: via `singleton_case_B_RC_alpha` (|B⁺| - |B⁺ Q=d| + |B⁻ Q=r|).
    - Inductive: algebraic derivation from Total + A1 + A3 + γ-swap + partitions:
      `|B⁺ Q≠d| + |B⁻ Q=r|`
      `= (|B⁺| - |B⁺ Q=d|) + (|B⁻| - |B⁻ Q=d| - |B⁻ Q.lo≤1|)`  (partitions)
      `= (|B⁺| + |B⁻|) - (|B⁺ Q=d| + |B⁻ Q=d|) - |B⁻ Q.lo≤1|`
      `= tripleSum - dd - ss = rc`                              (Total, A1, A3).

    This theorem is declared after `card_PBPSet_B_eq_tripleSum_countPBP_B` because its
    inductive case depends on Total(dp). -/
theorem card_B_RC_alpha_eq_countB_rc (dp : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r)
    (hQ_pos : μQ.colLen 0 > 0) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .r).card =
      (countPBP_B dp).2.1 := by
  -- Derivation: |B⁺ Q≠d| + |B⁻ Q=r| = |B⁺| + |B⁻| - (|B⁺ Q=d| + |B⁻ Q=d|) - |B⁻ Q.lo≤1|
  --            = tripleSum - dd - ss = rc.
  have h_total := card_PBPSet_B_eq_tripleSum_countPBP_B dp μP μQ hP hQ hsort heven hpos
  have h_A1 := card_B_DD_alpha_eq_countB_dd dp hP hQ hsort heven hpos hQ_pos h_total
  have h_A3 := card_B_SS_alpha_eq_countB_ss dp hP hQ hsort heven hpos hQ_pos
  have h_Bp_part := card_Bplus_nonD_eq_low_plus_r μP μQ hQ_pos
  have h_Bm_part := card_Bminus_partition_Qbot μP μQ hQ_pos
  have h_swap_low := card_Bplus_SS_eq_Bminus_SS μP μQ
  -- Split B⁺ by Q=d.
  have h_Bp_split : Fintype.card (PBPSet .Bplus μP μQ) =
      (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
      (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 ≠ .d).card := by
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (p := fun σ : PBPSet .Bplus μP μQ =>
        σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d)]
  -- Destructure countPBP_B dp.
  rcases h_ct : countPBP_B dp with ⟨dd, rc, ss⟩
  rw [h_ct] at h_A1 h_A3 h_total
  simp only at h_A1 h_A3 h_total
  -- tripleSum = dd + rc + ss.
  have h_ts : tripleSum (dd, rc, ss) = dd + rc + ss := rfl
  rw [h_ts] at h_total
  show _ = rc
  -- Goal: |B⁺ Q≠d| + |B⁻ Q=r| = rc.
  -- Use partitions + A1 + A3 + swaps + total to derive.
  omega

/-! ## Structural theorems for Counting.lean -/

theorem countPBP_B_primitive {r₁ r₂ : ℕ} {rest : DualPart}
    (h : r₂ > rest.head?.getD 0) :
    countPBP_B (r₁ :: r₂ :: rest) =
      let k := (r₁ - r₂) / 2 + 1
      let ((tDD, tRC, tSS), _) := tailCoeffs k
      let (dd', rc', ss') := countPBP_B rest
      let total := dd' + rc' + ss'
      (total * tDD, total * tRC, total * tSS) := by
  simp only [countPBP_B, h, ite_true]

theorem countPBP_B_balanced {r₁ r₂ : ℕ} {rest : DualPart}
    (h : ¬(r₂ > rest.head?.getD 0)) :
    countPBP_B (r₁ :: r₂ :: rest) =
      let k := (r₁ - r₂) / 2 + 1
      let ((tDD, tRC, tSS), (scDD, scRC, scSS)) := tailCoeffs k
      let (dd', rc', ss') := countPBP_B rest
      (dd' * tDD + rc' * scDD,
       dd' * tRC + rc' * scRC,
       dd' * tSS + rc' * scSS) := by
  simp only [countPBP_B, h, ite_false]
