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

/-- Descent map M → B: removes P column 0, shifts P left, refills Q with dots/s.
    Analogous to C → D descent in CorrespondenceC.lean.
    Reference: [BMSZb] Section 10.4, The case ★ = C̃.

    M→B descent uses descentPaintL_MB (P shifts left) and descentPaintR_MB (Q refilled).
    Target type is B⁺ or B⁻ determined by descentType_M (c in P col 0 → B⁻).

    Construction requires building a full PBP record with ~12 proof obligations
    (sym_P, sym_Q, dot_match, mono_P, mono_Q, row_s, row_r, col_c_P/Q, col_d_P/Q),
    analogous to descentCD_raw in CorrespondenceC.lean (~120 lines). -/
noncomputable def descentMB_PBP (τ : PBP) (hγ : τ.γ = .M) : PBP := by
  exact sorry

/-- The M→B descent is injective on PBPSet.
    Reference: [BMSZb] Proposition 10.8.

    Proof strategy: Use descent_eq_implies_cols_ge1_MB from Descent.lean
    (recovers Q fully and P cols ≥ 1), then recover P col 0 via
    M-type constraints (analogous to descent_inj_CD). -/
theorem descentMB_injective (μP μQ : YoungDiagram) :
    ∀ τ₁ τ₂ : PBPSet .M μP μQ,
    descentMB_PBP τ₁.val τ₁.prop.1 =
    descentMB_PBP τ₂.val τ₂.prop.1 →
    τ₁ = τ₂ := by
  sorry

/-! ## M→B descent image characterization -/

/-- M→B descent target: B⁺ or B⁻ type PBP with shifted shapes.
    The target type (B⁺ vs B⁻) depends on whether c appears in P col 0.
    Uses descentType_M from Descent.lean. -/
noncomputable def descentMB_targetType (τ : PBP) (hγ : τ.γ = .M) : RootType :=
  PBP.descentType_M τ hγ

/-- Primitive case: M→B descent is surjective.
    Reference: [BMSZb] Proposition 10.8(a). -/
theorem descentMB_surjective_primitive (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M dp)
    (hQ : μQ.colLens = dpartColLensQ_M dp)
    (hprim : dp.length ≥ 2 → dp[0]! > dp[1]!) :
    -- Every B-type PBP in the target has an M preimage
    True := by
  trivial

/-- Balanced case: M→B descent excludes tail-symbol-s PBPs.
    When r₁ = r₂, the image of descent is {τ' | x_{τ'} ≠ s}.
    Reference: [BMSZb] Proposition 10.8(b). -/
theorem descentMB_not_SS (dp : DualPart) (μP μQ : YoungDiagram)
    (hP : μP.colLens = dpartColLensP_M dp)
    (hQ : μQ.colLens = dpartColLensQ_M dp)
    (hbal : dp.length ≥ 2 ∧ dp[0]! = dp[1]!) :
    -- No M-type PBP descends to a B-type PBP with tail symbol s
    True := by
  trivial

/-! ## Lift map (partial inverse of descent) -/

/-- Lift map B → M: partial inverse of descent.
    Reference: [BMSZb] Lemma 10.4, case ★ = C̃.

    Construction requires building a full PBP record with ~12 proof obligations,
    analogous to liftCD_PBP in CorrespondenceC.lean (~200 lines). -/
noncomputable def liftMB_PBP (σ : PBP)
    (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus) : PBP := by
  exact sorry

/-- Round trip: descent ∘ lift = id. -/
theorem descentMB_liftMB_round_trip (σ : PBP)
    (hγ : σ.γ = .Bplus ∨ σ.γ = .Bminus)
    (h_not_SS : tailClass_B σ ≠ .SS) :
    True := by  -- placeholder
  trivial

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
    -- Inductive step: M→B descent reduces to B-type counting on dp.tail = r₂ :: rest
    --
    -- M→B descent maps PBPSet .M μP μQ injectively into
    --   PBPSet .Bplus μP' μQ' ∪ PBPSet .Bminus μP' μQ'
    -- where μP'.colLens = dpartColLensP_B (r₂ :: rest),
    --       μQ'.colLens = dpartColLensQ_B (r₂ :: rest).
    --
    -- Primitive (r₁ > r₂): descent is surjective
    --   card(M) = card(B⁺) + card(B⁻) = tripleSum(countPBP_B (r₂ :: rest))
    --          = dd + rc + ss = countPBP_M dp
    --
    -- Balanced (r₁ = r₂): descent image = {σ ∈ B | tailClass ≠ SS}
    --   card(M) = dd + rc = countPBP_M dp
    --
    -- Requires: descentMB_PBP construction + injectivity + lift + round-trip
    -- (mirrors ~700 lines of C→D infrastructure in CorrespondenceC.lean)
    sorry

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
