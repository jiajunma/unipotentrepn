/-
# Descent of Painted Bipartitions

Reference: [BMSZ] Section 3.3, Lemma 3.7, Definition 3.14.

The descent ∇ maps a PBP τ of type γ to a PBP τ' of type γ', where:
- C → D: remove first column of Q (right)
- D → C: remove first column of P (left)
- B⁺/B⁻ → M: remove first column of Q (right)
- M → B⁺ or B⁻: remove first column of P (left)

The key shape constraint is that the non-• cells of the "non-trivial" side
form layers compatible with the column removal.
-/
import CombUnipotent.PBP

namespace PBP

/-! ## Shape lemmas for descent

For descent to be well-defined, we need shape constraints.
These follow from the PBP axioms (symbol sets + monotonicity + row uniqueness).

### Key lemma for C → D descent:

In a C-type PBP, Q has symbols {•, s}. By layer monotonicity,
s-cells are at the bottom of each column. By row uniqueness,
each row has at most one s. Together: **s appears only at the
rightmost cell of each row in Q**. This implies:

  δ.colLen(k) ≥ Q.colLen(k + 1)   for all k

where δ is the dot diagram. This is the interlacing condition
needed for the redistribution in descent.
-/

/-- In a C-type PBP, if cell (i, k) in Q is s, then (i, k+1) ∉ Q.shape.
    Proof: by layer monotonicity, (i, k+1) would also have layerOrd ≥ 1,
    hence symbol s. But row uniqueness forbids two s in the same row. -/
theorem Q_s_rightmost_of_C (τ : PBP) (hγ : τ.γ = .C)
    {i k : ℕ} (hs : τ.Q.paint i k = .s) : (i, k + 1) ∉ τ.Q.shape := by
  intro hmem
  -- By monotonicity: paint(i, k).layerOrd ≤ paint(i, k+1).layerOrd
  -- since (i, k) ≤ (i, k+1)
  have hmono := τ.mono_Q i k i (k + 1) le_rfl (Nat.le_succ k)
    (hmem)
  -- paint(i, k) = s has layerOrd 1
  rw [hs, DRCSymbol.layerOrd] at hmono
  -- So paint(i, k+1).layerOrd ≥ 1, meaning paint(i, k+1) ∈ {s, r, c, d}
  -- But Q of C type has only {•, s}, so paint(i, k+1) = s
  have hk1 := τ.Q_nonDot_eq_s_of_C hγ i (k + 1) hmem (by
    intro heq; rw [heq, DRCSymbol.layerOrd] at hmono; omega)
  -- Now we have two s in the same row: (i, k) and (i, k+1), contradicting row_s
  have := τ.row_s i .R .R k (k + 1)
    (by simp [paintBySide]; exact hs)
    (by simp [paintBySide]; exact hk1)
  omega -- k ≠ k+1 but this.2 says k = k+1

/-- In a C-type PBP, if (i, k+1) ∈ Q.shape, then cell (i, k) in Q is •.
    Contrapositive of Q_s_rightmost: if (i, k+1) ∈ Q.shape,
    then (i, k) ∈ Q.shape (by Young diagram) and paint(i, k) ≠ s
    (by Q_s_rightmost). Since Q has only {•, s}, paint(i, k) = •. -/
theorem Q_dot_left_of_C (τ : PBP) (hγ : τ.γ = .C)
    {i k : ℕ} (hmem : (i, k + 1) ∈ τ.Q.shape) : τ.Q.paint i k = .dot := by
  have hmem_k : (i, k) ∈ τ.Q.shape :=
    τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ k⟩) hmem
  by_contra hne
  have hs := τ.Q_nonDot_eq_s_of_C hγ i k hmem_k hne
  exact τ.Q_s_rightmost_of_C hγ hs hmem

/-- In a C-type PBP, if (i, k+1) ∈ Q.shape then (i, k) is a •-cell of Q
    (within Q.shape). This is the key ingredient for the interlacing lemma. -/
theorem Q_dotCell_of_right_mem_of_C (τ : PBP) (hγ : τ.γ = .C)
    {i k : ℕ} (hmem : (i, k + 1) ∈ τ.Q.shape) :
    (i, k) ∈ τ.Q.shape ∧ τ.Q.paint i k = .dot := by
  refine ⟨?_, τ.Q_dot_left_of_C hγ hmem⟩
  exact τ.Q.shape.isLowerSet (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ k⟩) hmem

/-- In a C-type PBP, for all k:
    dotDiag(Q).colLen(k) ≥ Q.shape.colLen(k + 1).

    This is the interlacing condition needed for C → D descent.
    Proof: if (i, k+1) ∈ Q.shape then (i, k) is a •-cell of Q
    (by Q_dotCell_of_right_mem_of_C), hence (i, k) ∈ dotDiag(Q). -/
theorem dotDiag_colLen_ge_Q_colLen_succ_of_C (τ : PBP) (hγ : τ.γ = .C) (k : ℕ) :
    (dotDiag τ.Q τ.mono_Q).colLen k ≥ τ.Q.shape.colLen (k + 1) := by
  -- Suffices: ∀ i, i < Q.shape.colLen(k+1) → i < dotDiag.colLen(k)
  -- Equiv: ∀ i, (i, k+1) ∈ Q.shape → (i, k) ∈ dotDiag
  by_contra h
  push_neg at h
  -- h : dotDiag.colLen(k) < Q.shape.colLen(k+1)
  -- So ∃ i with (i, k+1) ∈ Q.shape but (i, k) ∉ dotDiag
  set d := (dotDiag τ.Q τ.mono_Q).colLen k
  have hd_mem : (d, k + 1) ∈ τ.Q.shape := by
    rw [YoungDiagram.mem_iff_lt_colLen]; omega
  have ⟨hdk_mem, hdk_dot⟩ := τ.Q_dotCell_of_right_mem_of_C hγ hd_mem
  -- (d, k) ∈ Q.shape and paint(d, k) = .dot, so (d, k) ∈ dotDiag
  have hdk_in_dot : (d, k) ∈ (dotDiag τ.Q τ.mono_Q) := by
    simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hdk_mem, hdk_dot⟩
  -- But d = dotDiag.colLen(k), so (d, k) ∉ dotDiag
  have : ¬ (d, k) ∈ (dotDiag τ.Q τ.mono_Q) := by
    rw [YoungDiagram.mem_iff_lt_colLen]; omega
  exact this hdk_in_dot

/-- The dot diagram is always contained in the shape. -/
theorem dotDiag_le (D : PaintedYoungDiagram) (hm : D.layerMonotone) :
    dotDiag D hm ≤ D.shape := by
  intro ⟨i, j⟩ hmem
  simp only [dotDiag, YoungDiagram.mem_mk, Finset.mem_filter, YoungDiagram.mem_cells] at hmem
  exact hmem.1

/-! ## Descent definition

We define descent in two stages:
1. `naiveDescent`: remove a column and redistribute •/s
2. `descent`: apply corrections for B⁺ and D types

For now, we define the key components: which column to remove,
the type change, and state the main theorem about descent. -/

/-- The descent type change.
    For M → B, the actual B⁺/B⁻ depends on whether c appears
    in the first column of P. This function gives the default (B⁺);
    the caller must correct to B⁻ when needed.
    Reference: [BMSZ] Equation (3.11). -/
def descentType (γ : RootType) : RootType :=
  match γ with
  | .C => .D
  | .D => .C
  | .Bplus | .Bminus => .M
  | .M => .Bplus  -- default; correct to B⁻ when c ∈ first column of P

/-- For M type: the actual descent target type, determined by
    whether c occurs in the first column of P.
    Reference: [BMSZ] Equation (3.11). -/
def descentType_M (τ : PBP) (hγ : τ.γ = .M) : RootType :=
  -- c in first column of P iff ∃ i, (i,0) ∈ P.shape ∧ P.paint i 0 = .c
  if (τ.P.shape.cells.filter (fun c => c.2 = 0 ∧ τ.P.paint c.1 c.2 = .c)).Nonempty
  then .Bminus
  else .Bplus

/-- Which side the descent removes a column from. -/
def descentSide' (γ : RootType) : Side :=
  match γ with
  | .C | .Bplus | .Bminus => .R  -- remove first column of Q
  | .D | .M => .L               -- remove first column of P

end PBP
