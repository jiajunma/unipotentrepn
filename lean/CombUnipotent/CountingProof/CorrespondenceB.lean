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

/-- **α-class DD count**: combined B⁺ ∪ B⁻ PBPs with Q column 0 bottom = d
    equals `countPBP_B(dp).1`.

    Structural induction on dp:
    - Empty: hQ_pos false (vacuous, now closed).
    - Singleton + Inductive: fiber analysis (admitted as focused sub-sorry). -/
private theorem card_B_DD_alpha_eq_countB_dd (dp : DualPart)
    {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r)
    (hQ_pos : μQ.colLen 0 > 0) :
    (Finset.univ.filter fun σ : PBPSet .Bplus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card +
    (Finset.univ.filter fun σ : PBPSet .Bminus μP μQ =>
      σ.val.Q.paint (μQ.colLen 0 - 1) 0 = .d).card =
      (countPBP_B dp).1 := by
  match dp, hP, hQ, hsort, heven, hpos, hQ_pos with
  | [], _, hQ, _, _, _, hQ_pos =>
    have hQ_bot : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    exfalso
    rw [hQ_bot] at hQ_pos
    have : ¬ (⊥ : YoungDiagram).colLen 0 > 0 := by
      intro h
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr h
      simp at hmem
    exact this hQ_pos
  | _, _, _, _, _, _, _ =>
    -- Singleton or inductive case: admitted as focused sub-sorry.
    sorry

/-- **α-class RC count** (γ-asymmetric): B⁺ with Q_bot ≠ d, plus B⁻ with Q_bot = r.
    equals `countPBP_B(dp).2.1`. The asymmetry reflects the tail correction:
    B⁺ with natural Q_bot ∈ {•, s} gets corrected x_τ = c (RC), while B⁻ stays SS. -/
private theorem card_B_RC_alpha_eq_countB_rc (dp : DualPart)
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
  match dp, hP, hQ, hsort, heven, hpos, hQ_pos with
  | [], _, hQ, _, _, _, hQ_pos =>
    have hQ_bot : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    exfalso
    rw [hQ_bot] at hQ_pos
    have : ¬ (⊥ : YoungDiagram).colLen 0 > 0 := by
      intro h
      have hmem := YoungDiagram.mem_iff_lt_colLen.mpr h
      simp at hmem
    exact this hQ_pos
  | _, _, _, _, _, _, _ =>
    sorry

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
  | [_], _, _, _, _, _, _ =>
    -- Singleton case: direct computation via DSeq enumeration.
    sorry
  | _ :: _ :: _, _, _, _, _, _, _ =>
    -- Inductive case: primitive uses refined fiber (new sub-sorry),
    -- balanced uses Phase 3 fiber identity.
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

/-- **Balanced fiber identity**: in balanced case, the total count of
    new B⁺ ∪ B⁻ PBPs decomposes as a sum over sub-PBPs grouped by their Q_bot:
    each sub contributes `4k` (if Q_bot=d), `4k-2` (if Q_bot=r), or `2k-1` (if Q_bot.lo≤1).

    Admitted; requires fiber analysis generalizing the primitive case's uniform fiber
    to the balanced case's Q_bot-dependent fiber. See blueprint. -/
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
  sorry

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

/-- **B balanced step identity** — Task #12 main goal.
    Derived from `card_B_bal_grouped_fiber` + A1, A2, A3, γ-swap, B⁺ set partition.

    Algebra: `card(new) = dd'·4k + (rc'-ss')·(4k-2) + 2·ss'·(2k-1)`,
    and `2·(2k-1) = 4k-2`, so this equals `dd'·4k + rc'·(4k-2)`. -/
private theorem card_PBPSet_B_balanced_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hpos : ∀ r ∈ (r₁ :: r₂ :: rest), 0 < r)
    (h_bal : ¬(r₂ > rest.head?.getD 0)) :
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
  -- A1, A2, A3 at rest level
  have h_A1 := card_B_DD_alpha_eq_countB_dd rest hP_sh hQ_sh hsort_rest heven_rest hpos_rest hQ_sh_pos
  have h_A2 := card_B_RC_alpha_eq_countB_rc rest hP_sh hQ_sh hsort_rest heven_rest hpos_rest hQ_sh_pos
  have h_A3 := card_B_SS_alpha_eq_countB_ss rest hP_sh hQ_sh hsort_rest heven_rest hpos_rest hQ_sh_pos
  -- γ-swap at rest level
  have h_swap := card_Bplus_SS_eq_Bminus_SS μP.shiftLeft μQ.shiftLeft
  -- B+ set partition at rest level
  have h_part := card_Bplus_nonD_eq_low_plus_r μP.shiftLeft μQ.shiftLeft hQ_sh_pos
  -- Destructure countPBP_B rest
  rcases h_ct : countPBP_B rest with ⟨dd', rc', ss'⟩
  rw [h_ct] at h_A1 h_A2 h_A3
  simp only at h_A1 h_A2 h_A3
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
  have h_rc_sum : Bp_r + Bm_r + ss' = rc' := by
    rw [h_Bp_low_eq] at h_part; omega
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
      have h_step := card_PBPSet_B_balanced_step r₁ r₂ rest μP μQ hP hQ hsort heven hpos h_prim
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
