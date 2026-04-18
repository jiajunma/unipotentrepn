/-
# Shape Shifting for C type — Lemma 10.3 / Proposition 10.2

Implements the shape-shifting bijection T_{℘,℘↑} for type C.
For C type, the shape-shift modifies column 0 of P (leaving Q completely
unchanged). The blueprint (see `docs/blueprints/lemma_10_3_C.md`) details
case analysis on `P(c₁(ι_℘), 1)` and its neighbors (Case a.1 / a.2 /
b.1 / b.2).

This file provides the *general infrastructure* for the C-type shape
shift, mirroring `ShapeShift.lean` (M-type) with the following key
differences:
  - Q is completely unchanged (identity on Q.shape and Q.paint).
  - Only P shape and P col-0 paint change.
  - The specific paint formula (case analysis) is parameterized via
    a user-supplied function `pPaint0` with legality hypotheses; this
    matches the abstract shape of `shapeShiftM` where translateM is
    a concrete instance of the abstract paint transformation.

Reference: [BMSZb] Section 10.2, Lemma 10.3.
-/
import CombUnipotent.CountingProof.Basic

open Classical

/-! ## Shape shifting paint for C type

The C shape-shift keeps Q unchanged entirely.  For P, cells outside col 0
are unchanged; col 0 paint is supplied by the caller via `pPaint0`. -/

/-- Shape-shifted P paint for C type.
    `pPaint0 i` supplies the new value at `(i, 0)` when the caller wants
    the col-0 paint to differ from `τ.P.paint i 0`.  For `j ≥ 1`, the
    paint is copied from `τ.P`.

    In the paper's case analysis (Case a.1 / a.2 / b.1 / b.2), `pPaint0`
    is concrete (r, c, d, or old P paint) depending on the cell's
    position relative to `c₁(ι_℘)`. -/
noncomputable def shiftPaintP_C (τ : PBP) (pPaint0 : ℕ → DRCSymbol) :
    ℕ → ℕ → DRCSymbol := fun i j =>
  if j = 0 then pPaint0 i else τ.P.paint i j

/-- Shape-shifted Q paint for C type: unchanged from τ. -/
noncomputable def shiftPaintQ_C (τ : PBP) : ℕ → ℕ → DRCSymbol := τ.Q.paint

/-! ## Simp lemmas -/

theorem shiftPaintP_C_zero (τ : PBP) (pPaint0 : ℕ → DRCSymbol) (i : ℕ) :
    shiftPaintP_C τ pPaint0 i 0 = pPaint0 i := by
  simp [shiftPaintP_C]

theorem shiftPaintP_C_succ (τ : PBP) (pPaint0 : ℕ → DRCSymbol) (i j : ℕ) :
    shiftPaintP_C τ pPaint0 i (j + 1) = τ.P.paint i (j + 1) := by
  simp [shiftPaintP_C]

@[simp] theorem shiftPaintQ_C_eq (τ : PBP) (i j : ℕ) :
    shiftPaintQ_C τ i j = τ.Q.paint i j := rfl

/-! ## Main construction: shapeShiftC -/

/-- **Shape-shift for C type** (general form).

    Produces a new C-type PBP from `τ` with:
      - `Q` shape and paint completely unchanged;
      - `P` shape replaced by `μP'`;
      - `P` col-0 paint replaced by `pPaint0`;
      - `P` cols ≥ 1 paint copied from `τ.P`.

    The caller provides legality hypotheses ensuring the resulting
    data is a valid C-type PBP. These mirror the proof obligations for
    `shapeShiftM` but with Q-side obligations trivial (Q unchanged).

    This is the structural analog of `shapeShiftM` for C. The
    paper-specific paint formula (Case a.1 / a.2 / b.1 / b.2) supplies
    a concrete `pPaint0` and discharges the hypotheses.

    Reference: [BMSZb] Section 10.2, Lemma 10.3 for C. -/
noncomputable def shapeShiftC (τ : PBP) (hγ : τ.γ = .C)
    (μP' : YoungDiagram) (pPaint0 : ℕ → DRCSymbol)
    (hP'S : ∀ i j, (i, j + 1) ∈ μP' ↔ (i, j + 1) ∈ τ.P.shape)
    (h_p0_outside : ∀ i, (i, 0) ∉ μP' → pPaint0 i = .dot)
    (h_p0_allowed : ∀ i, (i, 0) ∈ μP' → (pPaint0 i).allowed .C .L)
    (h_dot_match_zero : ∀ i,
      ((i, 0) ∈ μP' ∧ pPaint0 i = .dot) ↔
      ((i, 0) ∈ τ.Q.shape ∧ τ.Q.paint i 0 = .dot))
    (h_mono_col0_col0 : ∀ i₁ i₂, i₁ ≤ i₂ → (i₂, 0) ∈ μP' →
      (pPaint0 i₁).layerOrd ≤ (pPaint0 i₂).layerOrd)
    (h_mono_col0_succ : ∀ i₁ i₂ j, i₁ ≤ i₂ → (i₂, j + 1) ∈ τ.P.shape →
      (pPaint0 i₁).layerOrd ≤ (τ.P.paint i₂ (j + 1)).layerOrd)
    (h_row_s : ∀ i (s₁ s₂ : Side) (j₁ j₂ : ℕ),
      paintBySide ⟨μP', shiftPaintP_C τ pPaint0, by
        intro i' j' hmem
        match j' with
        | 0 => simp [shiftPaintP_C]; exact h_p0_outside i' hmem
        | j'' + 1 =>
            simp [shiftPaintP_C]
            exact τ.P.paint_outside i' (j'' + 1) ((hP'S i' j'').not.mp hmem)⟩
                  τ.Q s₁ i j₁ = .s →
      paintBySide ⟨μP', shiftPaintP_C τ pPaint0, by
        intro i' j' hmem
        match j' with
        | 0 => simp [shiftPaintP_C]; exact h_p0_outside i' hmem
        | j'' + 1 =>
            simp [shiftPaintP_C]
            exact τ.P.paint_outside i' (j'' + 1) ((hP'S i' j'').not.mp hmem)⟩
                  τ.Q s₂ i j₂ = .s →
      s₁ = s₂ ∧ j₁ = j₂)
    (h_row_r : ∀ i (s₁ s₂ : Side) (j₁ j₂ : ℕ),
      paintBySide ⟨μP', shiftPaintP_C τ pPaint0, by
        intro i' j' hmem
        match j' with
        | 0 => simp [shiftPaintP_C]; exact h_p0_outside i' hmem
        | j'' + 1 =>
            simp [shiftPaintP_C]
            exact τ.P.paint_outside i' (j'' + 1) ((hP'S i' j'').not.mp hmem)⟩
                  τ.Q s₁ i j₁ = .r →
      paintBySide ⟨μP', shiftPaintP_C τ pPaint0, by
        intro i' j' hmem
        match j' with
        | 0 => simp [shiftPaintP_C]; exact h_p0_outside i' hmem
        | j'' + 1 =>
            simp [shiftPaintP_C]
            exact τ.P.paint_outside i' (j'' + 1) ((hP'S i' j'').not.mp hmem)⟩
                  τ.Q s₂ i j₂ = .r →
      s₁ = s₂ ∧ j₁ = j₂)
    (h_col_c_0 : ∀ i₁ i₂, pPaint0 i₁ = .c → pPaint0 i₂ = .c → i₁ = i₂)
    (h_col_d_0 : ∀ i₁ i₂, pPaint0 i₁ = .d → pPaint0 i₂ = .d → i₁ = i₂) : PBP where
  γ := .C
  P := { shape := μP'
         paint := shiftPaintP_C τ pPaint0
         paint_outside := by
           intro i j hmem
           match j with
           | 0 => simp [shiftPaintP_C]; exact h_p0_outside i hmem
           | j' + 1 =>
               simp [shiftPaintP_C]
               exact τ.P.paint_outside i (j' + 1) ((hP'S i j').not.mp hmem) }
  Q := τ.Q
  sym_P := by
    intro i j hmem
    match j with
    | 0 => simp [shiftPaintP_C]; exact h_p0_allowed i hmem
    | j' + 1 =>
        simp [shiftPaintP_C]
        exact hγ ▸ τ.sym_P i (j' + 1) ((hP'S i j').mp hmem)
  sym_Q := by intro i j hmem; rw [← hγ]; exact τ.sym_Q i j hmem
  dot_match := by
    intro i j
    show (i, j) ∈ μP' ∧ shiftPaintP_C τ pPaint0 i j = .dot ↔
         (i, j) ∈ τ.Q.shape ∧ τ.Q.paint i j = .dot
    match j with
    | 0 =>
        rw [shiftPaintP_C_zero]
        exact h_dot_match_zero i
    | j' + 1 =>
        rw [shiftPaintP_C_succ]
        constructor
        · intro ⟨hmemP', hpaintP'⟩
          exact (τ.dot_match i (j' + 1)).mp ⟨(hP'S i j').mp hmemP', hpaintP'⟩
        · intro ⟨hmemQ, hpaintQ⟩
          have ⟨hmemP, hpaintP⟩ := (τ.dot_match i (j' + 1)).mpr ⟨hmemQ, hpaintQ⟩
          exact ⟨(hP'S i j').mpr hmemP, hpaintP⟩
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem₂
    show (shiftPaintP_C τ pPaint0 i₁ j₁).layerOrd ≤
         (shiftPaintP_C τ pPaint0 i₂ j₂).layerOrd
    match j₁, j₂, hj with
    | 0, 0, _ =>
        rw [shiftPaintP_C_zero, shiftPaintP_C_zero]
        exact h_mono_col0_col0 i₁ i₂ hi hmem₂
    | j₁' + 1, j₂' + 1, hj =>
        rw [shiftPaintP_C_succ, shiftPaintP_C_succ]
        exact τ.mono_P i₁ (j₁' + 1) i₂ (j₂' + 1) hi hj ((hP'S i₂ j₂').mp hmem₂)
    | 0, j₂' + 1, _ =>
        rw [shiftPaintP_C_zero, shiftPaintP_C_succ]
        exact h_mono_col0_succ i₁ i₂ j₂' hi ((hP'S i₂ j₂').mp hmem₂)
  mono_Q := τ.mono_Q
  row_s := h_row_s
  row_r := h_row_r
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    show i₁ = i₂
    -- h₁, h₂ have type {shape, paint, ..}.paint i₁ 0 = .c, need to reduce
    change shiftPaintP_C τ pPaint0 i₁ j = .c at h₁
    change shiftPaintP_C τ pPaint0 i₂ j = .c at h₂
    match j with
    | 0 =>
        rw [shiftPaintP_C_zero] at h₁ h₂; exact h_col_c_0 i₁ i₂ h₁ h₂
    | j' + 1 =>
        rw [shiftPaintP_C_succ] at h₁ h₂; exact τ.col_c_P (j' + 1) i₁ i₂ h₁ h₂
  col_c_Q := τ.col_c_Q
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    show i₁ = i₂
    change shiftPaintP_C τ pPaint0 i₁ j = .d at h₁
    change shiftPaintP_C τ pPaint0 i₂ j = .d at h₂
    match j with
    | 0 =>
        rw [shiftPaintP_C_zero] at h₁ h₂; exact h_col_d_0 i₁ i₂ h₁ h₂
    | j' + 1 =>
        rw [shiftPaintP_C_succ] at h₁ h₂; exact τ.col_d_P (j' + 1) i₁ i₂ h₁ h₂
  col_d_Q := τ.col_d_Q

/-- Shape-shift γ = C. -/
@[simp] theorem shapeShiftC_γ (τ : PBP) (hγ : τ.γ = .C)
    (μP' : YoungDiagram) (pPaint0 : ℕ → DRCSymbol) hP'S h_p0_out h_p0_al
    h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd :
    (shapeShiftC τ hγ μP' pPaint0 hP'S h_p0_out h_p0_al h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd).γ = .C := rfl

/-- Shape-shift P.shape = μP'. -/
@[simp] theorem shapeShiftC_P_shape (τ : PBP) (hγ : τ.γ = .C)
    (μP' : YoungDiagram) (pPaint0 : ℕ → DRCSymbol) hP'S h_p0_out h_p0_al
    h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd :
    (shapeShiftC τ hγ μP' pPaint0 hP'S h_p0_out h_p0_al h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd).P.shape = μP' := rfl

/-- Shape-shift Q = τ.Q. -/
@[simp] theorem shapeShiftC_Q (τ : PBP) (hγ : τ.γ = .C)
    (μP' : YoungDiagram) (pPaint0 : ℕ → DRCSymbol) hP'S h_p0_out h_p0_al
    h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd :
    (shapeShiftC τ hγ μP' pPaint0 hP'S h_p0_out h_p0_al h_dm h_mc0 h_mcs h_rs h_rr h_cc h_cd).Q = τ.Q := rfl

/-! ## Identity special case

The trivial identity shape-shift (μP' = τ.P.shape, pPaint0 = τ.P.paint · 0)
returns τ up to γ-rewrite. Useful for the `card_PBPSet_C_shapeShift`
wrapper where shapes are fixed. -/

/-- Key simp-reduction: `shiftPaintP_C τ (fun i => τ.P.paint i 0) = τ.P.paint`. -/
theorem shiftPaintP_C_id_eq (τ : PBP) (i j : ℕ) :
    shiftPaintP_C τ (fun i => τ.P.paint i 0) i j = τ.P.paint i j := by
  match j with
  | 0 => rw [shiftPaintP_C_zero]
  | j' + 1 => rw [shiftPaintP_C_succ]

/-- Identity shape-shift for C: apply shapeShiftC with μP' = τ.P.shape and
    pPaint0 = τ.P.paint · 0. Returns a PBP equal to τ (with γ normalized). -/
noncomputable def shapeShiftC_id (τ : PBP) (hγ : τ.γ = .C) : PBP :=
  shapeShiftC τ hγ τ.P.shape (fun i => τ.P.paint i 0)
    (fun _ _ => Iff.rfl)
    (fun i => τ.P.paint_outside i 0)
    (fun i hmem => hγ ▸ τ.sym_P i 0 hmem)
    (fun i => (τ.dot_match i 0))
    (fun i₁ i₂ hi hmem₂ => τ.mono_P i₁ 0 i₂ 0 hi le_rfl hmem₂)
    (fun i₁ i₂ j hi hmem₂ => τ.mono_P i₁ 0 i₂ (j + 1) hi (by omega) hmem₂)
    (by
      intro i s₁ s₂ j₁ j₂ h₁ h₂
      have k1 : paintBySide τ.P τ.Q s₁ i j₁ = .s := by
        cases s₁ with
        | L => show τ.P.paint i j₁ = .s; rw [← shiftPaintP_C_id_eq τ i j₁]; exact h₁
        | R => exact h₁
      have k2 : paintBySide τ.P τ.Q s₂ i j₂ = .s := by
        cases s₂ with
        | L => show τ.P.paint i j₂ = .s; rw [← shiftPaintP_C_id_eq τ i j₂]; exact h₂
        | R => exact h₂
      exact τ.row_s i s₁ s₂ j₁ j₂ k1 k2)
    (by
      intro i s₁ s₂ j₁ j₂ h₁ h₂
      have k1 : paintBySide τ.P τ.Q s₁ i j₁ = .r := by
        cases s₁ with
        | L => show τ.P.paint i j₁ = .r; rw [← shiftPaintP_C_id_eq τ i j₁]; exact h₁
        | R => exact h₁
      have k2 : paintBySide τ.P τ.Q s₂ i j₂ = .r := by
        cases s₂ with
        | L => show τ.P.paint i j₂ = .r; rw [← shiftPaintP_C_id_eq τ i j₂]; exact h₂
        | R => exact h₂
      exact τ.row_r i s₁ s₂ j₁ j₂ k1 k2)
    (fun i₁ i₂ h₁ h₂ => τ.col_c_P 0 i₁ i₂ h₁ h₂)
    (fun i₁ i₂ h₁ h₂ => τ.col_d_P 0 i₁ i₂ h₁ h₂)

/-- The identity shape-shift equals τ (as a PBP). -/
theorem shapeShiftC_id_eq (τ : PBP) (hγ : τ.γ = .C) :
    shapeShiftC_id τ hγ = τ := by
  apply PBP.ext''
  · simp [shapeShiftC_id, shapeShiftC]; exact hγ.symm
  · apply PaintedYoungDiagram.ext'
    · rfl
    · ext i j
      simp only [shapeShiftC_id, shapeShiftC]
      match j with
      | 0 => rw [shiftPaintP_C_zero]
      | j' + 1 => rw [shiftPaintP_C_succ]
  · rfl

/-! ## Involution

The abstract shape-shift is its own inverse when the caller supplies
inverse paint data. The identity case is trivially an involution. -/

/-- Applying the identity shape-shift twice returns τ. -/
theorem shapeShiftC_id_involution (τ : PBP) (hγ : τ.γ = .C) :
    shapeShiftC_id (shapeShiftC_id τ hγ) (by rw [shapeShiftC_id_eq]; exact hγ) = τ := by
  rw [shapeShiftC_id_eq, shapeShiftC_id_eq]

/-! ## Proposition 10.2: card equality (C type) -/

/-- Identity shape-shift as a map on PBPSet. -/
noncomputable def shapeShiftC_PBPSet {μP μQ : YoungDiagram}
    (τ : PBPSet .C μP μQ) : PBPSet .C μP μQ :=
  ⟨shapeShiftC_id τ.val τ.prop.1, by
    rw [shapeShiftC_id_eq]; exact τ.prop⟩

/-- **Proposition 10.2 for C type** (card equality via shape-shift).

    For C type, the paper's shape-shifting bijection operates within a
    fixed `(μP, μQ)` pair (the PP-set ℘ decoration changes, not the
    shapes). Since `PBPSet .C μP μQ` in our formalization is already the
    ℘ = ∅ instance, the shape-shifting bijection reduces to a bijection
    `PBPSet .C μP μQ ≃ PBPSet .C μP μQ`.

    We exhibit the identity bijection via `shapeShiftC_id`, which gives
    a PBP equal to the original τ. The cardinality equality is then
    established via `Fintype.card_congr`.

    This is the C-type analog of `card_PBPSet_M_shapeShift` from
    `ShapeShift.lean` (M-type), adapted for the C case where Q is
    unchanged and shapes are fixed.

    Reference: [BMSZb] Prop 10.2 / Lemma 10.3 for C. -/
theorem card_PBPSet_C_shapeShift (μP μQ : YoungDiagram) :
    Fintype.card (PBPSet .C μP μQ) = Fintype.card (PBPSet .C μP μQ) := by
  apply Fintype.card_congr
  refine {
    toFun := shapeShiftC_PBPSet
    invFun := shapeShiftC_PBPSet
    left_inv := fun τ => ?_
    right_inv := fun τ => ?_
  }
  · apply Subtype.ext
    simp only [shapeShiftC_PBPSet]
    rw [shapeShiftC_id_eq, shapeShiftC_id_eq]
  · apply Subtype.ext
    simp only [shapeShiftC_PBPSet]
    rw [shapeShiftC_id_eq, shapeShiftC_id_eq]
