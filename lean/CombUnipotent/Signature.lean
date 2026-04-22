/-
# Signature and Epsilon

Reference: [BMSZ] Equations (3.3), (3.6); [BMSZb] Equation (2.17).

The signature (p_τ, q_τ) encodes the real form of the group.
The epsilon ε_τ ∈ {0, 1} detects the presence of `d` in the first columns.
-/
import CombUnipotent.PBP

/-! ## Symbol counting -/

/-- Count cells with symbol σ in a painted Young diagram. -/
def PaintedYoungDiagram.countSym (D : PaintedYoungDiagram) (σ : DRCSymbol) : ℕ :=
  (D.shape.cells.filter (fun c => D.paint c.1 c.2 = σ)).card

/-- The sum of `countSym` over all five DRCSymbols equals the total
    number of cells in the shape. Every cell has exactly one paint
    value, so the five fibers partition the cells. -/
theorem PaintedYoungDiagram.sum_countSym (D : PaintedYoungDiagram) :
    D.countSym .dot + D.countSym .s + D.countSym .r + D.countSym .c +
      D.countSym .d = D.shape.cells.card := by
  classical
  have : D.shape.cells = D.shape.cells.filter
      (fun c => D.paint c.1 c.2 = .dot ∨ D.paint c.1 c.2 = .s ∨
        D.paint c.1 c.2 = .r ∨ D.paint c.1 c.2 = .c ∨ D.paint c.1 c.2 = .d) := by
    ext c
    refine ⟨fun hc => ?_, fun hc => (Finset.mem_filter.mp hc).1⟩
    refine Finset.mem_filter.mpr ⟨hc, ?_⟩
    rcases h : D.paint c.1 c.2 <;> tauto
  rw [this]
  unfold PaintedYoungDiagram.countSym
  -- Partition: filter (A ∨ B ∨ C ∨ D ∨ E) = filter A ∪ filter B ∪ ... with disjoint unions.
  have h_partition :
      D.shape.cells.filter
        (fun c => D.paint c.1 c.2 = .dot ∨ D.paint c.1 c.2 = .s ∨
          D.paint c.1 c.2 = .r ∨ D.paint c.1 c.2 = .c ∨ D.paint c.1 c.2 = .d) =
      (D.shape.cells.filter (fun c => D.paint c.1 c.2 = .dot)) ∪
      (D.shape.cells.filter (fun c => D.paint c.1 c.2 = .s)) ∪
      (D.shape.cells.filter (fun c => D.paint c.1 c.2 = .r)) ∪
      (D.shape.cells.filter (fun c => D.paint c.1 c.2 = .c)) ∪
      (D.shape.cells.filter (fun c => D.paint c.1 c.2 = .d)) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  rw [h_partition]
  have card_union :
      ∀ s₁ s₂ : DRCSymbol, s₁ ≠ s₂ →
        Disjoint (D.shape.cells.filter (fun c => D.paint c.1 c.2 = s₁))
                 (D.shape.cells.filter (fun c => D.paint c.1 c.2 = s₂)) := by
    intro s₁ s₂ hne
    rw [Finset.disjoint_left]
    rintro c hc₁ hc₂
    simp only [Finset.mem_filter] at hc₁ hc₂
    exact hne (hc₁.2.symm.trans hc₂.2)
  rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr
            ⟨Finset.disjoint_union_left.mpr
              ⟨card_union .dot .d (by decide), card_union .s .d (by decide)⟩,
             card_union .r .d (by decide)⟩,
           card_union .c .d (by decide)⟩),
      Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr
            ⟨card_union .dot .c (by decide), card_union .s .c (by decide)⟩,
           card_union .r .c (by decide)⟩),
      Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr
          ⟨card_union .dot .r (by decide), card_union .s .r (by decide)⟩),
      Finset.card_union_of_disjoint (card_union .dot .s (by decide))]

/-- If all five `countSym` values are zero, the shape is empty. -/
theorem PaintedYoungDiagram.shape_empty_of_countSym_all_zero
    (D : PaintedYoungDiagram)
    (h_dot : D.countSym .dot = 0) (h_s : D.countSym .s = 0)
    (h_r : D.countSym .r = 0) (h_c : D.countSym .c = 0)
    (h_d : D.countSym .d = 0) :
    D.shape = ⊥ := by
  have h_sum := D.sum_countSym
  rw [h_dot, h_s, h_r, h_c, h_d] at h_sum
  simp at h_sum
  apply YoungDiagram.ext
  rw [YoungDiagram.cells_bot]
  exact Finset.card_eq_zero.mp h_sum.symm

/-! ## Signature -/

/-- Signature (p_τ, q_τ) of a PBP.
    Reference: [BMSZ] Equation (3.3); [BMSZb] Equation (2.17).

    For B⁺/B⁻/D:
      p = n_• + 2·n_r + n_c + n_d + [1 if B⁺]
      q = n_• + 2·n_s + n_c + n_d + [1 if B⁻]

    For C/M:
      p = q = n_• + n_r + n_s + n_c + n_d -/
noncomputable def PBP.signature (τ : PBP) : ℕ × ℕ :=
  let nDot := τ.P.countSym .dot + τ.Q.countSym .dot
  let nR := τ.P.countSym .r + τ.Q.countSym .r
  let nS := τ.P.countSym .s + τ.Q.countSym .s
  let nC := τ.P.countSym .c + τ.Q.countSym .c
  let nD := τ.P.countSym .d + τ.Q.countSym .d
  match τ.γ with
  | .Bplus | .Bminus | .D =>
    let p := nDot + 2 * nR + nC + nD + (if τ.γ = .Bplus then 1 else 0)
    let q := nDot + 2 * nS + nC + nD + (if τ.γ = .Bminus then 1 else 0)
    (p, q)
  | .C | .M =>
    let n := nDot + nR + nS + nC + nD
    (n, n)

/-- For D / C / M types, `PBP.signature τ = (0, 0)` forces both shapes
    to be empty (no "+1" offset in the signature formula). -/
theorem PBP_shapes_empty_of_signature_zero_DCM (τ : PBP)
    (hγ : τ.γ = .D ∨ τ.γ = .C ∨ τ.γ = .M)
    (h_sig : PBP.signature τ = (0, 0)) :
    τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥ := by
  unfold PBP.signature at h_sig
  rcases hγ with hγ | hγ | hγ
  all_goals
    simp [hγ] at h_sig
    obtain ⟨h1, h2⟩ := h_sig
    have h_dot : τ.P.countSym .dot = 0 ∧ τ.Q.countSym .dot = 0 := by omega
    have h_r : τ.P.countSym .r = 0 ∧ τ.Q.countSym .r = 0 := by omega
    have h_s : τ.P.countSym .s = 0 ∧ τ.Q.countSym .s = 0 := by omega
    have h_c : τ.P.countSym .c = 0 ∧ τ.Q.countSym .c = 0 := by omega
    have h_d : τ.P.countSym .d = 0 ∧ τ.Q.countSym .d = 0 := by omega
    exact ⟨τ.P.shape_empty_of_countSym_all_zero h_dot.1 h_s.1 h_r.1 h_c.1 h_d.1,
           τ.Q.shape_empty_of_countSym_all_zero h_dot.2 h_s.2 h_r.2 h_c.2 h_d.2⟩

/-! ## Epsilon -/

/-- Whether `d` occurs in column 0 of a painted Young diagram. -/
def PaintedYoungDiagram.hasDInCol0 (D : PaintedYoungDiagram) : Bool :=
  (D.shape.cells.filter (fun c => c.2 = 0 ∧ D.paint c.1 c.2 = .d)).Nonempty

/-- ε_τ ∈ {0, 1}: detects whether `d` occurs in column 0 of P or Q.
    Reference: [BMSZ] Equation (3.6).

    ε_τ = 0  iff  `d` occurs in column 0 of P or column 0 of Q.
    ε_τ = 1  otherwise. -/
def PBP.epsilon (τ : PBP) : Fin 2 :=
  if τ.P.hasDInCol0 || τ.Q.hasDInCol0 then 0 else 1
