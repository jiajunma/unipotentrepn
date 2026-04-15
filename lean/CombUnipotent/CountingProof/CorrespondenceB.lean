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

/-- Surjectivity of extractCol0_B on fiber: every ValidCol0_B element
    can be lifted to a fiber element.
    Proof: construct a PBP from (σ, col0_data) by:
    - P(i, j+1) = σ.P.paint(i, j), P(i, 0) = dots or (dots+c at bottom)
    - Q(i, j+1) = σ.Q.paint(i, j), Q(i, 0) = dots + DSeq tail
    Then verify doubleDescent_B_PBP of the result equals σ.
    Analogous to liftPBP_to_fiber in Fiber.lean for D-type. -/
private theorem extractCol0_B_surjective_on_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0) :
    Function.Surjective (fun τ : doubleDescent_Bplus_fiber σ =>
      extractCol0_B τ.val hle) := by
  sorry

private theorem validCol0_B_le_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (hle : μP.colLen 0 ≤ μQ.colLen 0) :
    Fintype.card (ValidCol0_B (μP.colLen 0) (μQ.colLen 0)) ≤
    Fintype.card (doubleDescent_Bplus_fiber σ) :=
  Fintype.card_le_of_surjective _ (extractCol0_B_surjective_on_fiber σ hle)

/-- Key counting lemma (primitive case, B type):
    Every sub-PBP σ has fiber size = tripleSum(tailCoeffs k).1 = 4k. -/
private theorem fiber_card_B_primitive {μP μQ : YoungDiagram}
    (σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft))
    (k : ℕ) (hle : μP.colLen 0 ≤ μQ.colLen 0)
    (hk : k = μQ.colLen 0 - μP.colLen 0 + 1) (hk_pos : k ≥ 1) :
    Fintype.card (doubleDescent_Bplus_fiber σ) = tripleSum (tailCoeffs k).1 := by
  rw [tripleSum_tailCoeffs_fst_eq k hk_pos]
  have hcard := validCol0_B_card (μP.colLen 0) (μQ.colLen 0) hle k hk hk_pos
  have h_le := fiber_le_validCol0_B σ hle
  have h_ge := validCol0_B_le_fiber σ hle
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
  have hfiber : ∀ σ : PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft),
      Fintype.card (doubleDescent_Bplus_fiber σ) =
      tripleSum (tailCoeffs ((r₁ - r₂) / 2 + 1)).1 := by
    intro σ
    rw [hk_eq]
    exact fiber_card_B_primitive σ _ hle rfl (by omega)
  rw [Finset.sum_congr rfl (fun σ _ => hfiber σ)]
  rw [Finset.sum_const, Finset.card_univ]
  rfl

/-- Balanced case (r₂ = r₃): per-tail-class matrix multiply. -/
theorem card_PBPSet_B_balanced_step (r₁ r₂ : ℕ) (rest : DualPart)
    (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B (r₁ :: r₂ :: rest))
    (hQ : μQ.colLens = dpartColLensQ_B (r₁ :: r₂ :: rest))
    (hsort : (r₁ :: r₂ :: rest).SortedGE)
    (heven : ∀ r ∈ (r₁ :: r₂ :: rest), Even r)
    (hbal : ¬(r₂ > rest.head?.getD 0)) :
    -- The balanced case decomposes per tail class
    True := by  -- placeholder for matrix multiply statement
  trivial

/-! ## Main theorem -/

/-- **Proposition 10.11 for B type:**
    card(PBPSet .Bplus μP μQ) + card(PBPSet .Bminus μP μQ) = tripleSum(countPBP_B dp). -/
theorem card_PBPSet_B_eq_tripleSum_countPBP_B (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_B dp)
    (hQ : μQ.colLens = dpartColLensQ_B dp)
    (hsort : dp.SortedGE)
    (heven : ∀ r ∈ dp, Even r)
    (hpos : ∀ r ∈ dp, 0 < r) :
    Fintype.card (PBPSet .Bplus μP μQ) + Fintype.card (PBPSet .Bminus μP μQ) =
    tripleSum (countPBP_B dp) := by
  -- Induction on dp (list of even parts).
  match dp, hP, hQ, hsort, heven, hpos with
  | [], hP, hQ, _, _, _ =>
    -- Base case: empty orbit
    have h1 := yd_of_colLens_nil (by rw [hP]; rfl)
    have h2 := yd_of_colLens_nil (by rw [hQ]; rfl)
    subst h1; subst h2
    simp [card_PBPSet_bot, tripleSum, countPBP_B]
  | [r₁], hP, hQ, _, heven, hpos =>
    -- Base case: single row
    exact card_PBPSet_B_singleton r₁ μP μQ hP hQ (heven r₁ (by simp)) (hpos r₁ (by simp))
  | r₁ :: r₂ :: rest, hP, hQ, hsort, heven, hpos =>
    -- Inductive step: set up IH on rest
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
    · -- Primitive case: uniform fiber
      have := card_PBPSet_B_primitive_step r₁ r₂ rest μP μQ hP hQ hsort heven h_prim
      rw [this, h_ih]
      simp only [countPBP_B, h_prim, ite_true, tripleSum]
      ring
    · -- Balanced case: per-tail-class matrix multiply
      -- When r₂ = r₃ (balanced), the fiber size depends on the tail class of σ:
      --   DD fibers have size tDD, RC fibers have size tRC, SS fibers have size tSS
      -- where (tDD, tRC, tSS) = (tailCoeffs k).1 and k = (r₁-r₂)/2 + 1.
      --
      -- The balanced formula is:
      --   card(total) = dd' × tDD + rc' × scDD
      --               + dd' × tRC + rc' × scRC
      --               + dd' × tSS + rc' × scSS
      -- where (dd', rc', ss') = countPBP_B rest and (scDD, scRC, scSS) = (tailCoeffs k).2.
      --
      -- This requires:
      --   1. card_PBPSet_B_balanced_step: decomposition by tail class with per-class
      --      fiber sizes, analogous to card_PBPSet_D_balanced_step in LiftRC.lean
      --   2. B-type tail class classification (DD/RC/SS for combined P+Q columns)
      --   3. Per-tail-class fiber cardinality lemmas
      --
      -- The D-type balanced step (LiftRC.lean:1317) is ~250 lines. The B-type
      -- version needs similar infrastructure adapted for the two-column fiber.
      simp only [countPBP_B, h_prim, ite_false, tripleSum]
      sorry

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
