/-
# C-type counting: Proposition 10.12

Proves `Fintype.card (PBPSet .C μP μQ) = countPBP_C dp` for all valid
C-type dual partitions dp (sorted, odd parts, dp ≠ []).

The proof reduces to D-type counting via the C→D descent:
- Primitive (r₁ > r₂): count = tripleSum(countPBP_D dp_tail) = dd + rc + ss
- Balanced (r₁ = r₂): count = dd + rc (SS excluded)

Reference: [BMSZb] Proposition 10.12.
-/
import CombUnipotent.CountingProof.Correspondence

open Classical

/-! ## C→D descent as injection

The C→D descent paint `descentPaintL_CD` maps C-type PBPs to D-type P paints
injectively (`descent_inj_CD`). We construct the full descended D-type PBP
and prove it lands in PBPSet .D μP (shiftLeft μQ). -/

/-- The C→D descent produces a D-type PBP with shapes (μP, shiftLeft μQ).
    Sorry: full 13-constraint verification (mechanical). -/
noncomputable def descentCD_PBP {μP μQ : YoungDiagram}
    (τ : PBPSet .C μP μQ) : PBPSet .D μP (YoungDiagram.shiftLeft μQ) := by
  sorry

/-- The C→D descent is injective. Uses `descent_inj_CD` from Descent.lean. -/
theorem descentCD_injective {μP μQ : YoungDiagram} :
    Function.Injective (@descentCD_PBP μP μQ) := by
  sorry

/-! ## Column length relationships

Key: C-type shapes relate to D-type shapes via:
  C-P cols = dpartColLensP_D dp_tail
  C-Q cols = [(r₁-1)/2] ++ dpartColLensQ_D dp_tail
  shiftLeft(C-Q) cols = dpartColLensQ_D dp_tail = D-Q cols -/

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

/-! ## Primitive vs balanced classification for C-type

For C-type dp = [r₁, r₂, ...rest]:
  k := μQ.colLen 0 = (r₁-1)/2  (Q col 0 length)
  c := μP.colLen 0 = (r₂+1)/2  (P col 0 length from D-type of tail)

  Primitive: r₁ > r₂ ↔ k ≥ c ↔ Q covers all P rows in col 0
  Balanced:  r₁ = r₂ ↔ k = c - 1 ↔ P extends 1 row beyond Q -/

lemma C_primitive_iff_Q_covers_P {r₁ r₂ : ℕ}
    (h₁ : Odd r₁) (h₂ : Odd r₂) (hle : r₂ ≤ r₁) :
    r₁ > r₂ ↔ (r₁ - 1) / 2 ≥ (r₂ + 1) / 2 := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; constructor <;> intro h <;> omega

lemma C_balanced_gap {r₁ r₂ : ℕ}
    (h₁ : Odd r₁) (h₂ : Odd r₂) (heq : r₁ = r₂) :
    (r₂ + 1) / 2 = (r₁ - 1) / 2 + 1 := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; omega

/-! ## Image characterization

**Primitive**: Every D-type PBP lifts to a C-type PBP.
  The extra Q col 0 covers all P col 0 rows, so the dot/s assignment is free.

**Balanced**: Only DD and RC lift. SS has tail symbol .s, but C-type P
  can't have .s in the non-Q zone, so the lift fails for SS. -/

/-- Primitive: image of descent = all of PBPSet .D. -/
theorem descentCD_image_card_primitive {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≥ μP.colLen 0) :
    Fintype.card (PBPSet .C μP μQ) =
      Fintype.card (PBPSet .D μP (YoungDiagram.shiftLeft μQ)) := by
  sorry

/-- Balanced: image of descent = DD ∪ RC of PBPSet .D.
    Card = |DD| + |RC| = Fintype.card - |SS|. -/
theorem descentCD_image_card_balanced {μP μQ : YoungDiagram}
    (h_bal : μP.colLen 0 = μQ.colLen 0 + 1)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    Fintype.card (PBPSet .C μP μQ) =
      Fintype.card (PBPSet .D μP (YoungDiagram.shiftLeft μQ)) -
        (Finset.univ.filter (fun σ : PBPSet .D μP (YoungDiagram.shiftLeft μQ) =>
          tailClass_D σ.val = .SS)).card := by
  sorry

/-! ## Base cases -/

lemma card_PBPSet_C_nil {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_C [])
    (hQ : μQ.colLens = dpartColLensQ_C []) :
    Fintype.card (PBPSet .C μP μQ) = 1 := by
  have hP' : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  have hQ' : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
  rw [hP', hQ']; exact card_PBPSet_bot .C

/-- C-type singleton dp = [r₁]: exactly 1 PBP. -/
theorem card_PBPSet_C_singleton (r₁ : ℕ) {μP μQ : YoungDiagram}
    (hP : μP.colLens = dpartColLensP_C [r₁])
    (hQ : μQ.colLens = dpartColLensQ_C [r₁])
    (hodd : Odd r₁) :
    Fintype.card (PBPSet .C μP μQ) = 1 := by
  have hP_nil : μP = ⊥ := yd_of_colLens_nil (by rw [hP]; rfl)
  subst hP_nil
  by_cases hr : r₁ > 1
  · -- Q has cells, all forced to s by dot_match (P = ⊥ → P outside shape → Q non-dot)
    sorry
  · -- r₁ = 1, Q = ⊥
    have : r₁ = 1 := by obtain ⟨m, rfl⟩ := hodd; omega
    subst this
    have hQ_nil : μQ = ⊥ := yd_of_colLens_nil (by rw [hQ]; rfl)
    rw [hQ_nil]; exact card_PBPSet_bot .C

/-! ## Main theorem -/

/-- **Proposition 10.12 (C-type)**: For all valid C-type dual partitions,
    `card(PBPSet .C μP μQ) = countPBP_C dp`. -/
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
    -- D-type dp for the descended PBP
    set dp_D := r₂ :: rest with hdpD
    have hr₁_odd := hodd r₁ (by simp)
    have hr₂_odd := hodd r₂ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))
    have hr₁_ge_r₂ : r₂ ≤ r₁ := by
      have := hsort.pairwise; rw [List.pairwise_cons] at this
      exact this.1 r₂ (List.mem_cons.mpr (Or.inl rfl))
    -- D-type shapes
    have hP_D : μP.colLens = dpartColLensP_D dp_D := by rw [hP]; rfl
    -- Sorted and odd for D-type dp
    have hsort_D : dp_D.SortedGE := by
      have hp := hsort.pairwise; rw [List.pairwise_cons] at hp; exact hp.2.sortedGE
    have hodd_D : ∀ r ∈ dp_D, Odd r :=
      fun r hr => hodd r (List.mem_cons_of_mem _ hr)
    -- Unfold countPBP_C
    simp only [countPBP_C]
    by_cases h_prim : r₁ > r₂
    · -- Primitive: count = dd + rc + ss = tripleSum
      -- Need: |PBPSet .C| = |PBPSet .D shifted|
      -- = tripleSum(countPBP_D dp_D)
      sorry
    · -- Balanced: r₁ = r₂. count = dd + rc
      push_neg at h_prim
      have hr₁_eq : r₁ = r₂ := le_antisymm h_prim hr₁_ge_r₂
      sorry
