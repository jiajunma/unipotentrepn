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
  -- Strategy: dpartColLensP_B [r₁] = [] so μP = ⊥ (empty P diagram).
  -- dpartColLensQ_B [r₁] = [r₁/2] so Q has one column of height r₁/2.
  -- P is empty, so all PBP constraints reduce to Q-only constraints.
  -- Q cells in col 0 must be from {•,s,r,d} with layer monotonicity.
  -- Direct enumeration of valid Q-paintings gives the count.
  -- Needs: card_PBPSet_bot-like lemma for single-column case.
  sorry

/-! ## Double descent B→M→B -/

/-- Double descent map for B-type: B→M→B on PBPSet. -/
noncomputable def doubleDescent_B_map (μP μQ : YoungDiagram)
    (τ : PBPSet .Bplus μP μQ ⊕ PBPSet .Bminus μP μQ) :
    PBPSet .Bplus (μP.shiftLeft) (μQ.shiftLeft) ⊕
    PBPSet .Bminus (μP.shiftLeft) (μQ.shiftLeft) := by
  -- Strategy: compose two single descents B→M→B.
  -- Step 1 (B→M): remove Q col 0 using descent_B_to_M (strips tail from Q).
  --   This produces a PBP with γ=M, P shape=μP, Q shape=μQ.shiftLeft.
  -- Step 2 (M→B): remove P col 0 of the M-type result using descent_M_to_B.
  --   This produces a PBP with γ∈{B⁺,B⁻}, P shape=μP.shiftLeft, Q shape=μQ.shiftLeft.
  -- The B⁺/B⁻ tag of the output is determined by the painting of the removed cells.
  -- Needs: doubleDescent_B_paintL/R from Tail.lean, descent_inj_B infrastructure.
  -- See doubleDescent_D_map in Descent.lean for the D-type template.
  sorry

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
  -- Strategy: use doubleDescent_B_map + ddescent_inj_B to show the map is injective.
  -- In the primitive case (r₂ > r₃), the fiber over each image element has uniform
  -- cardinality = tripleSum(tailCoeffs k).1 where k = (r₁-r₂)/2 + 1.
  -- This is because the tail painting choices (in Q col 0 and P col 0) are
  -- independent of the base painting when the gap is strict.
  -- Needs: doubleDescent_B_map, fiber cardinality analysis from Fiber.lean.
  sorry

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
      -- Needs: card_PBPSet_B_balanced_step with per-tc counts
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
