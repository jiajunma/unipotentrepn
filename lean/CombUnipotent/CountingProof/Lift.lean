/-
# Counting Proof: Lift construction (reverse of double descent)

Extracted from the monolithic `CountingProof.lean`.
-/
import CombUnipotent.CountingProof.Descent

open Classical

/-! ### Reverse construction for primitive case

Given σ ∈ PBPSet(rest) and a column 0 painting, construct τ ∈ PBPSet(dp).
The construction uses liftPaint_D: P(i,0) = col0(i), P(i,j+1) = σ.P(i,j).

In the primitive case, all PBP constraints are automatically satisfied
because tail rows (i ≥ μQ.colLen 0) have P.paint(i, j) = .dot for j ≥ 1
(by primitive_tail_rows_outside). So no s/r row conflicts. -/

/-- A valid tail painting for column 0 of a D-type PBP.
    The painting is: dot for rows < b, then tail symbols, dot above c.
    - b = μQ.colLen 0 (dot boundary)
    - c = μP.colLen 0 (shape boundary)
    - Symbols in [b, c) are non-dot, monotone layerOrd, at most 1 c/d. -/
structure ValidCol0 (μP μQ : YoungDiagram) where
  paint : ℕ → DRCSymbol
  dot_below : ∀ i, i < μQ.colLen 0 → paint i = .dot
  nondot_tail : ∀ i, μQ.colLen 0 ≤ i → i < μP.colLen 0 → paint i ≠ .dot
  dot_above : ∀ i, μP.colLen 0 ≤ i → paint i = .dot
  mono : ∀ i₁ i₂, i₁ ≤ i₂ → i₂ < μP.colLen 0 →
    (paint i₁).layerOrd ≤ (paint i₂).layerOrd
  col_c_unique : ∀ i₁ i₂, paint i₁ = .c → paint i₂ = .c → i₁ = i₂
  col_d_unique : ∀ i₁ i₂, paint i₁ = .d → paint i₂ = .d → i₁ = i₂

/-- ValidCol0 is finite: inject into the finite type (Fin c → DRCSymbol)
    where c = μP.colLen 0 (paint outside [0, c) is determined). -/
instance {μP μQ : YoungDiagram} : Finite (ValidCol0 μP μQ) := by
  apply Finite.of_injective (fun (v : ValidCol0 μP μQ) =>
    fun (i : Fin (μP.colLen 0 + 1)) => v.paint i.val)
  intro v₁ v₂ h
  have : v₁.paint = v₂.paint := by
    ext i
    by_cases hi : i < μP.colLen 0 + 1
    · exact congr_fun h ⟨i, hi⟩
    · rw [v₁.dot_above i (by omega), v₂.dot_above i (by omega)]
  cases v₁; cases v₂; simp_all

noncomputable instance {μP μQ : YoungDiagram} : Fintype (ValidCol0 μP μQ) :=
  Fintype.ofFinite _

/-- Hypothesis used by the lift, bundling two properties of σ:
    (1) σ.P has no s or r at tail rows `i ≥ μQ.colLen 0`
       — needed for row_s/row_r uniqueness.
    (2) At "mono-conflicting" cells (i₂, j+1) ∈ μP with i₁ ≤ i₂, i₁ ≥ μQ.colLen 0,
       σ.P.paint i₂ j = .d — needed for mono_P in balanced DD case
       (vacuous in primitive case).
    Both hold in primitive and balanced DD. -/
structure LiftCondition {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) : Prop where
  no_sr : ∀ i, μQ.colLen 0 ≤ i → ∀ k,
    σ.val.P.paint i k ≠ .s ∧ σ.val.P.paint i k ≠ .r
  mono_d : ∀ i₁ i₂ j, μQ.colLen 0 ≤ i₁ → i₁ ≤ i₂ → (i₂, j + 1) ∈ μP →
    σ.val.P.paint i₂ j = .d

/-- In the primitive case, both conditions hold trivially:
    σ.P at tail rows is outside its shape → .dot → not s/r;
    mono_d is vacuous because (i₂, j+1) ∈ μP with i₁ ≥ μQ.colLen 0 is impossible. -/
theorem liftCondition_of_primitive {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0) :
    LiftCondition σ where
  no_sr := by
    intro i hi k
    have hdot : σ.val.P.paint i k = .dot := by
      apply σ.val.P.paint_outside
      rw [σ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]; push_neg
      calc (YoungDiagram.shiftLeft μP).colLen k
          ≤ (YoungDiagram.shiftLeft μP).colLen 0 :=
            YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
        _ ≤ μQ.colLen 0 := h_prim
        _ ≤ i := hi
    refine ⟨?_, ?_⟩ <;> (rw [hdot]; decide)
  mono_d := by
    intro i₁ i₂ j hi₁ hi₁₂ hmem
    exfalso
    have h1 : i₂ < μP.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem
    have h2 : μP.colLen (j + 1) ≤ μP.colLen 1 := YoungDiagram.colLen_anti μP 1 (j + 1) (by omega)
    have h3 : μP.colLen 1 ≤ μQ.colLen 0 := by
      have := h_prim; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
    omega

/-- In the balanced DD case, both conditions hold via σ's DD class analysis.

    Balanced: μP.colLen 1 = μQ.colLen 0 + 1 (i.e., σ.P.shape.colLen 0 = b + 1 where b = μQ.colLen 0).
    DD class: σ.P.paint b 0 = .d. Combined with σ.mono_P, any (b, j) ∈ σ.P.shape has
    σ.P.paint b j = .d (max layerOrd). Tail rows > b are outside σ.P.shape entirely. -/
theorem liftCondition_of_balanced_DD {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_tc : tailClass_D σ.val = .DD) :
    LiftCondition σ := by
  set b := μQ.colLen 0 with hb_def
  -- Derive σ.val.P.paint b 0 = .d from the DD class hypothesis
  have hbal' : μP.colLen 1 = b + 1 := by
    have := h_bal; rw [YoungDiagram.colLen_shiftLeft] at this; exact this
  have hσP_colLen : σ.val.P.shape.colLen 0 = b + 1 := by
    rw [σ.prop.2.1, YoungDiagram.colLen_shiftLeft]; exact hbal'
  have hσQ_le : σ.val.Q.shape.colLen 0 ≤ b := by
    rw [σ.prop.2.2, YoungDiagram.colLen_shiftLeft]
    exact μQ.colLen_anti 0 1 (by omega)
  have htailLen_pos : PBP.tailLen_D σ.val > 0 := by
    simp only [PBP.tailLen_D, hσP_colLen]; omega
  have hσ_bottom_d : PBP.tailSymbol_D σ.val = .d := by
    simp only [tailClass_D] at h_tc
    rw [if_neg (by omega : PBP.tailLen_D σ.val ≠ 0)] at h_tc
    cases hs : PBP.tailSymbol_D σ.val <;> rw [hs] at h_tc <;> first | simp at h_tc | rfl
  have hσ_b0_d : σ.val.P.paint b 0 = .d := by
    have : σ.val.P.paint (σ.val.P.shape.colLen 0 - 1) 0 = .d := hσ_bottom_d
    rw [hσP_colLen] at this; simpa using this
  -- Prepare: for any (b, j) ∈ σ.val.P.shape, σ.val.P.paint b j = .d (from mono_P)
  have hσ_row_b_d : ∀ j, (b, j) ∈ σ.val.P.shape → σ.val.P.paint b j = .d := by
    intro j hmem
    have hmono := σ.val.mono_P b 0 b j (le_refl _) (Nat.zero_le _) hmem
    rw [hσ_b0_d, DRCSymbol.layerOrd] at hmono
    cases hp : σ.val.P.paint b j <;> rw [hp, DRCSymbol.layerOrd] at hmono <;> omega
  refine ⟨?_, ?_⟩
  · -- no_sr: σ.P at tail rows has no s/r
    intro i hi k
    by_cases hi_eq : i = b
    · -- row b: σ.P.paint b k is .d (if in shape) or .dot (if not)
      subst hi_eq
      by_cases hmem : (b, k) ∈ σ.val.P.shape
      · rw [hσ_row_b_d k hmem]; refine ⟨?_, ?_⟩ <;> decide
      · rw [σ.val.P.paint_outside b k hmem]; refine ⟨?_, ?_⟩ <;> decide
    · -- row i > b: outside σ.P.shape → .dot
      have hi_gt : i > b := by omega
      have hnotmem : (i, k) ∉ σ.val.P.shape := by
        intro hmem
        have : i < σ.val.P.shape.colLen k := YoungDiagram.mem_iff_lt_colLen.mp hmem
        have hσP_k : σ.val.P.shape.colLen k ≤ σ.val.P.shape.colLen 0 :=
          YoungDiagram.colLen_anti _ 0 k (Nat.zero_le _)
        rw [hσP_colLen] at hσP_k; omega
      rw [σ.val.P.paint_outside i k hnotmem]
      refine ⟨?_, ?_⟩ <;> decide
  · -- mono_d: in the (i₂, j+1) ∈ μP case, σ.P.paint i₂ j = .d
    intro i₁ i₂ j hi₁ hi₁₂ hmem
    have hi₂_le : i₂ ≤ b := by
      have h1 : i₂ < μP.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmem
      have h2 : μP.colLen (j + 1) ≤ μP.colLen 1 := YoungDiagram.colLen_anti μP 1 (j + 1) (by omega)
      omega
    have hi₂_eq : i₂ = b := by omega
    subst hi₂_eq
    -- (b, j) ∈ σ.val.P.shape (from (b, j+1) ∈ μP)
    have hmem_σ : (b, j) ∈ σ.val.P.shape := by
      rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
    exact hσ_row_b_d j hmem_σ

/-- Lift construction: given σ ∈ PBPSet(rest) and a valid column 0 painting,
    produce a D-type PBP with the given shapes.

    P.paint = liftPaint_D σ col0.paint
    Q = all dots with shape μQ

    Takes a `LiftCondition σ` capturing "σ has no s/r at tail rows" and
    "σ is .d at mono-conflict positions". Holds in primitive and balanced DD. -/
noncomputable def liftPBP_D {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_cond : LiftCondition σ)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    PBPSet .D μP μQ := by
  have h_tail := h_cond.no_sr
  have h_mono_d := h_cond.mono_d
  -- Define P and Q as named PYDs to avoid anonymous structure issues
  have hpo : ∀ i j, (i, j) ∉ μP → liftPaint_D σ.val col0.paint i j = .dot := by
    intro i j hmem; cases j with
    | zero => exact col0.dot_above i (by rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
    | succ j => exact σ.val.P.paint_outside i j (by
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft]; exact hmem)
  refine ⟨⟨.D,
    ⟨μP, liftPaint_D σ.val col0.paint, hpo⟩,
    ⟨μQ, fun _ _ => .dot, fun _ _ _ => rfl⟩,
    ?sym_P, ?sym_Q, ?dot_match, ?mono_P, ?mono_Q,
    ?row_s, ?row_r, ?col_c_P, ?col_c_Q, ?col_d_P, ?col_d_Q⟩,
    rfl, rfl, rfl⟩
  case sym_P => intro _ _ _; trivial  -- D/L allows all
  case sym_Q => intro _ _ _; simp [DRCSymbol.allowed]
  case dot_match =>
    intro i j; constructor
    · intro ⟨hmem, hpaint⟩
      cases j with
      | zero =>
        simp only [liftPaint_D] at hpaint
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by
          by_contra h; push_neg at h
          exact col0.nondot_tail i h (YoungDiagram.mem_iff_lt_colLen.mp hmem) hpaint), rfl⟩
      | succ j =>
        simp only [liftPaint_D] at hpaint
        have hmemσ : (i, j) ∈ σ.val.P.shape := by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hq, _⟩ := (σ.val.dot_match i j).mp ⟨hmemσ, hpaint⟩
        rw [σ.prop.2.2, YoungDiagram.mem_shiftLeft] at hq; exact ⟨hq, rfl⟩
    · intro ⟨hmem, _⟩
      cases j with
      | zero =>
        have hq := YoungDiagram.mem_iff_lt_colLen.mp hmem
        exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_lt_of_le hq hQP), by
          simp only [liftPaint_D]; exact col0.dot_below i hq⟩
      | succ j =>
        have hq : (i, j) ∈ σ.val.Q.shape := by
          rw [σ.prop.2.2]; exact YoungDiagram.mem_shiftLeft.mpr hmem
        have ⟨hp, hpaint⟩ := (σ.val.dot_match i j).mpr
          ⟨hq, PBP.Q_all_dot_of_D σ.val σ.prop.1 i j hq⟩
        rw [σ.prop.2.1, YoungDiagram.mem_shiftLeft] at hp
        exact ⟨hp, by simp only [liftPaint_D]; exact hpaint⟩
  case mono_P =>
    intro i₁ j₁ i₂ j₂ hi hj hmem
    cases j₁ with
    | zero =>
      cases j₂ with
      | zero => exact col0.mono i₁ i₂ hi (YoungDiagram.mem_iff_lt_colLen.mp hmem)
      | succ j₂ =>
        by_cases h : i₁ < μQ.colLen 0
        · simp only [liftPaint_D]; rw [col0.dot_below i₁ h]; simp [DRCSymbol.layerOrd]
        · push_neg at h
          -- i₁ ≥ μQ.colLen 0, (i₂, j₂+1) ∈ μP, i₁ ≤ i₂ ⟹ σ.P.paint i₂ j₂ = .d
          simp only [liftPaint_D]
          rw [h_mono_d i₁ i₂ j₂ h hi hmem]
          -- col0.paint i₁ .layerOrd ≤ 4 = d.layerOrd; always holds
          cases col0.paint i₁ <;> simp [DRCSymbol.layerOrd]
    | succ j₁ =>
      cases j₂ with
      | zero => exact absurd hj (by omega)
      | succ j₂ =>
        simp only [liftPaint_D]
        exact σ.val.mono_P i₁ j₁ i₂ j₂ hi (by omega) (by
          rw [σ.prop.2.1]; exact YoungDiagram.mem_shiftLeft.mpr hmem)
  case mono_Q => intro _ _ _ _ _ _ _; simp [DRCSymbol.layerOrd]
  case row_s =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₁; exact absurd h₁ (by decide)
          exact absurd h₂ (h_tail i hi j₂).1
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₂; exact absurd h₂ (by decide)
          exact absurd h₁ (h_tail i hi j₁).1
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have := σ.val.row_s i .L .L j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .L i j₁ = .s by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .L i j₂ = .s by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  case row_r =>
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · cases j₁ with
      | zero =>
        cases j₂ with
        | zero => simp only [liftPaint_D] at h₁ h₂; exact ⟨rfl, rfl⟩
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₁; exact absurd h₁ (by decide)
          exact absurd h₂ (h_tail i hi j₂).2
      | succ j₁ =>
        cases j₂ with
        | zero =>
          simp only [liftPaint_D] at h₁ h₂
          have hi : μQ.colLen 0 ≤ i := by
            by_contra hh; push_neg at hh; rw [col0.dot_below i hh] at h₂; exact absurd h₂ (by decide)
          exact absurd h₁ (h_tail i hi j₁).2
        | succ j₂ =>
          simp only [liftPaint_D] at h₁ h₂
          have := σ.val.row_r i .L .L j₁ j₂
            (show paintBySide σ.val.P σ.val.Q .L i j₁ = .r by simp [paintBySide]; exact h₁)
            (show paintBySide σ.val.P σ.val.Q .L i j₂ = .r by simp [paintBySide]; exact h₂)
          exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  case col_c_P =>
    intro j i₁ i₂ h₁ h₂
    simp only [liftPaint_D] at h₁ h₂
    cases j with
    | zero => exact col0.col_c_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_c_P j i₁ i₂ h₁ h₂
  case col_c_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h
  case col_d_P =>
    intro j i₁ i₂ h₁ h₂
    simp only [liftPaint_D] at h₁ h₂
    cases j with
    | zero => exact col0.col_d_unique i₁ i₂ h₁ h₂
    | succ j => exact σ.val.col_d_P j i₁ i₂ h₁ h₂
  case col_d_Q => intro _ _ _ h; exact DRCSymbol.noConfusion h

/-- Primitive-case lift as a thin wrapper around `liftPBP_D`. -/
noncomputable def liftPBP_primitive_D {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    PBPSet .D μP μQ :=
  liftPBP_D σ col0 (liftCondition_of_primitive σ h_prim) hQP

/-- Balanced DD-case lift as a thin wrapper around `liftPBP_D`. -/
noncomputable def liftPBP_balanced_DD_D {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ))
    (col0 : ValidCol0 μP μQ)
    (h_bal : (YoungDiagram.shiftLeft μP).colLen 0 = μQ.colLen 0 + 1)
    (h_tc : tailClass_D σ.val = .DD)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    PBPSet .D μP μQ :=
  liftPBP_D σ col0 (liftCondition_of_balanced_DD σ h_bal h_tc) hQP

/-! ### ValidCol0 counting

A ValidCol0 with tail length k = μP.colLen(0) - μQ.colLen(0)
is determined by a tuple (a, b, δc, δd) with a + b + δc + δd = k,
where δc, δd ∈ {0, 1}. The painting is s^a r^b c^δc d^δd.

Count = Σ_{(δc,δd) ∈ {0,1}²} max(0, k + 1 - δc - δd)
      = (k+1) + k + k + max(0, k-1)
      = tDD + tRC + tSS from tailCoeffs k
-/

/-- First, show that the total tailCoeffs sum simplifies to 4k for k ≥ 1. -/
theorem tailCoeffs_total (k : ℕ) (hk : 1 ≤ k) :
    (tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2 = 4 * k := by
  simp only [tailCoeffs, nu]
  split_ifs with h
  · omega
  · omega

