/-
# Discharge of atomic cell-count facts for Lemma 11.5

The theorem `prop_11_5_D_atomic` (in `CombUnipotent/MYD.lean`) reduces Lemma
11.5 (D-type) to three atomic integer hypotheses:

  1. `h_dsum    : p + q = 2 * tau_card`        (D-type signature-sum invariant)
  2. `h_descent : n_inner = tau_card - c₁`     (single-descent cell count)
  3. `h_residual: p_t + q_t = 2 * c₁ - c₂`     (tail-vs-col-0 balance)

This file discharges all three at the PBP level by providing concrete
parameter choices and proofs:

  - `tau_card  := PBP.cardCells τ`             (total cell count `|τ|`)
  - `n_inner   := tau_card - c₁`               (definitional)
  - `c₁        := τ.P.shape.colLen 0`          (P first-column length)
  - `c₂        := 2 * τ.Q.shape.colLen 0`      (chosen so that residual closes)
  - `p_t, q_t  := PBP.tailSignature_D τ`       (tail signature components)

Under these choices:
- `h_dsum` is a pure consequence of unfolding `PBP.signature` for D type
  (`PBP.signature_sum_D`).
- `h_descent` holds by `rfl`.
- `h_residual` reduces to `tailContrib_sum`: each tail cell's `tailContrib`
  sums to 2, so `p_t + q_t = 2 * (c₁ - τ.Q.colLen 0) = 2*c₁ - c₂` under the
  chosen `c₂` (`PBP.tailSignature_D_sum_eq`, `PBP.residual_identity_D`).

The wrapper `prop_11_5_D_atomic_pbp_discharged` packages these discharges
into a clean PBP-level interface that requires only the AC.step invariants
and per-component Prop 11.4 identifications. -/
import CombUnipotent.MYD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! ### Total cell count of a PBP -/

/-- **Total cell count** of a PBP: number of cells in P plus cells in Q.
    This is the natural integer measure of "size" `|τ|`. -/
noncomputable def PBP.cardCells (τ : PBP) : ℕ :=
  τ.P.shape.cells.card + τ.Q.shape.cells.card

/-! ### Per-symbol partition of a painted Young diagram -/

/-- The cells of a painted Young diagram split into one filtered set per
    DRC symbol (•, s, r, c, d). Hence the cell count equals the sum of the
    five `countSym` values. -/
theorem PaintedYoungDiagram.card_eq_sum_countSym (D : PaintedYoungDiagram) :
    D.shape.cells.card =
      D.countSym .dot + D.countSym .s + D.countSym .r +
      D.countSym .c + D.countSym .d := by
  -- Express both sides as `Finset.sum` of indicator functions over `D.shape.cells`,
  -- then reduce pointwise: each cell's paint matches exactly one of the 5 symbols.
  unfold PaintedYoungDiagram.countSym
  -- For each symbol σ, rewrite filter.card as a sum-with-indicator.
  have hfilter : ∀ σ : DRCSymbol,
      (D.shape.cells.filter (fun (c : ℕ × ℕ) => D.paint c.1 c.2 = σ)).card =
        ∑ c ∈ D.shape.cells, (if (D.paint c.1 c.2 = σ) then (1 : ℕ) else 0) := by
    intro σ
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hfilter .dot, hfilter .s, hfilter .r, hfilter .c, hfilter .d]
  -- Combine the 5 by-symbol sums.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- LHS: `card = ∑ 1`. Check pointwise: 5 indicators sum to 1.
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ _
  cases D.paint i j <;> simp

/-! ### Fact 1: D-type signature sum -/

/-- **Fact 1 (h_dsum discharge):** For a D-type PBP, the signature components
    sum to twice the total cell count: `p + q = 2 * |τ|`. This is the D-type
    signature-sum invariant — a pure consequence of `PBP.signature` definition
    plus the fact that Q has only `.dot` symbols for D type. -/
theorem PBP.signature_sum_D (τ : PBP) (hγ : τ.γ = .D) :
    ((PBP.signature τ).1 : ℤ) + (PBP.signature τ).2 =
      2 * (PBP.cardCells τ : ℤ) := by
  unfold PBP.signature
  simp only [hγ, show ¬(RootType.D = .Bplus) from by decide,
    show ¬(RootType.D = .Bminus) from by decide, ite_false, Nat.add_zero]
  rw [PBP.Q_countSym_eq_zero_of_D τ hγ .r (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .s (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .c (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .d (by decide)]
  unfold PBP.cardCells
  rw [PaintedYoungDiagram.card_eq_sum_countSym τ.P,
      PaintedYoungDiagram.card_eq_sum_countSym τ.Q]
  rw [PBP.Q_countSym_eq_zero_of_D τ hγ .r (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .s (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .c (by decide),
      PBP.Q_countSym_eq_zero_of_D τ hγ .d (by decide)]
  push_cast
  ring

/-- For a C-type PBP, the signature is `(n, n)` where `n` is the total
    cell count. So `signature.1 = signature.2 = |τ|` and their sum is
    `2 * |τ|`. -/
theorem PBP.signature_sum_C (τ : PBP) (hγ : τ.γ = .C) :
    ((PBP.signature τ).1 : ℤ) + (PBP.signature τ).2 =
      2 * (PBP.cardCells τ : ℤ) := by
  unfold PBP.signature
  simp only [hγ]
  -- For C, signature = (nDot + nR + nS + nC + nD, same)
  -- Q has only {dot, s}, so Q.nR = Q.nC = Q.nD = 0
  rw [PBP.Q_countSym_eq_zero_of_C τ hγ .r (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_C τ hγ .c (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_C τ hγ .d (by decide) (by decide)]
  -- P has only {dot, r, c, d}, so P.nS = 0
  rw [PBP.P_countSym_eq_zero_of_C τ hγ .s rfl]
  unfold PBP.cardCells
  rw [PaintedYoungDiagram.card_eq_sum_countSym τ.P,
      PaintedYoungDiagram.card_eq_sum_countSym τ.Q]
  rw [PBP.Q_countSym_eq_zero_of_C τ hγ .r (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_C τ hγ .c (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_C τ hγ .d (by decide) (by decide)]
  rw [PBP.P_countSym_eq_zero_of_C τ hγ .s rfl]
  push_cast
  ring

/-- For an M-type PBP: `p + q = 2 * |τ|`. Similar to C since M also has
    `p = q = n` signature form. -/
theorem PBP.signature_sum_M (τ : PBP) (hγ : τ.γ = .M) :
    ((PBP.signature τ).1 : ℤ) + (PBP.signature τ).2 =
      2 * (PBP.cardCells τ : ℤ) := by
  unfold PBP.signature
  simp only [hγ]
  -- M: signature = (nDot + nR + nS + nC + nD, same)
  -- P has only {dot, s, c}, Q has only {dot, r, d}
  rw [PBP.P_countSym_eq_zero_of_M τ hγ .r (by decide) (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_M τ hγ .d (by decide) (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_M τ hγ .s (by decide) (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_M τ hγ .c (by decide) (by decide) (by decide)]
  unfold PBP.cardCells
  rw [PaintedYoungDiagram.card_eq_sum_countSym τ.P,
      PaintedYoungDiagram.card_eq_sum_countSym τ.Q]
  rw [PBP.P_countSym_eq_zero_of_M τ hγ .r (by decide) (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_M τ hγ .d (by decide) (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_M τ hγ .s (by decide) (by decide) (by decide),
      PBP.Q_countSym_eq_zero_of_M τ hγ .c (by decide) (by decide) (by decide)]
  push_cast
  ring

/-- For a B⁺-type PBP, `p + q = 2 * |τ| + 1`. The `+1` offset comes
    from the `(if τ.γ = .Bplus then 1 else 0)` in the signature formula. -/
theorem PBP.signature_sum_Bplus (τ : PBP) (hγ : τ.γ = .Bplus) :
    ((PBP.signature τ).1 : ℤ) + (PBP.signature τ).2 =
      2 * (PBP.cardCells τ : ℤ) + 1 := by
  unfold PBP.signature
  simp only [hγ, show ¬(RootType.Bplus = .Bminus) from by decide,
    ite_true, ite_false]
  -- B⁺: P only {dot, c}, Q only {dot, s, r, d}
  rw [PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .r (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .s (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .d (by decide) (by decide)]
  unfold PBP.cardCells
  rw [PaintedYoungDiagram.card_eq_sum_countSym τ.P,
      PaintedYoungDiagram.card_eq_sum_countSym τ.Q]
  rw [PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .r (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .s (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inl hγ) .d (by decide) (by decide)]
  push_cast
  ring

/-- For a C-type PBP, `signature.1 = signature.2 = |τ|` explicitly.
    (This is stronger than `signature_sum_C` — direct equality.) -/
theorem PBP.signature_fst_C (τ : PBP) (hγ : τ.γ = .C) :
    ((PBP.signature τ).1 : ℤ) = (PBP.cardCells τ : ℤ) := by
  have h := PBP.signature_sum_C τ hγ
  have heq : (PBP.signature τ).1 = (PBP.signature τ).2 := by
    unfold PBP.signature; simp only [hγ]
  rw [← heq] at h
  omega

theorem PBP.signature_snd_C (τ : PBP) (hγ : τ.γ = .C) :
    ((PBP.signature τ).2 : ℤ) = (PBP.cardCells τ : ℤ) := by
  have heq : (PBP.signature τ).1 = (PBP.signature τ).2 := by
    unfold PBP.signature; simp only [hγ]
  rw [← heq]; exact PBP.signature_fst_C τ hγ

/-- For an M-type PBP, `signature.1 = signature.2 = |τ|`. -/
theorem PBP.signature_fst_M (τ : PBP) (hγ : τ.γ = .M) :
    ((PBP.signature τ).1 : ℤ) = (PBP.cardCells τ : ℤ) := by
  have h := PBP.signature_sum_M τ hγ
  have heq : (PBP.signature τ).1 = (PBP.signature τ).2 := by
    unfold PBP.signature; simp only [hγ]
  rw [← heq] at h
  omega

theorem PBP.signature_snd_M (τ : PBP) (hγ : τ.γ = .M) :
    ((PBP.signature τ).2 : ℤ) = (PBP.cardCells τ : ℤ) := by
  have heq : (PBP.signature τ).1 = (PBP.signature τ).2 := by
    unfold PBP.signature; simp only [hγ]
  rw [← heq]; exact PBP.signature_fst_M τ hγ

/-- For a B⁻-type PBP, `p + q = 2 * |τ| + 1`. -/
theorem PBP.signature_sum_Bminus (τ : PBP) (hγ : τ.γ = .Bminus) :
    ((PBP.signature τ).1 : ℤ) + (PBP.signature τ).2 =
      2 * (PBP.cardCells τ : ℤ) + 1 := by
  unfold PBP.signature
  simp only [hγ, show ¬(RootType.Bminus = .Bplus) from by decide,
    ite_true, ite_false]
  rw [PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .r (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .s (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .d (by decide) (by decide)]
  unfold PBP.cardCells
  rw [PaintedYoungDiagram.card_eq_sum_countSym τ.P,
      PaintedYoungDiagram.card_eq_sum_countSym τ.Q]
  rw [PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .r (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .s (by decide) (by decide),
      PBP.P_countSym_eq_zero_of_B τ (Or.inr hγ) .d (by decide) (by decide)]
  push_cast
  ring

/-! ### Fact 3: Tail signature sum -/

/-- **Tail signature sum** for a D-type PBP: each tail cell contributes
    `tailContrib` summing to 2, so the projection sum is twice the tail length
    `(P.colLen 0 - Q.colLen 0)` (truncated subtraction in ℕ, cast to ℤ). -/
theorem PBP.tailSignature_D_sum_eq (τ : PBP) :
    (PBP.tailSignature_D τ).1 + (PBP.tailSignature_D τ).2 =
      2 * ((τ.P.shape.colLen 0 - τ.Q.shape.colLen 0 : ℕ) : ℤ) := by
  unfold PBP.tailSignature_D
  -- Reduce to a generic statement about pair-folds.
  suffices h : ∀ (n : ℕ) (f : ℕ → ℤ × ℤ),
      (∀ i, (f i).1 + (f i).2 = 2) →
      ((Finset.range n).fold (fun (a b : ℤ × ℤ) => a + b) ((0, 0) : ℤ × ℤ) f).1 +
      ((Finset.range n).fold (fun (a b : ℤ × ℤ) => a + b) ((0, 0) : ℤ × ℤ) f).2 =
        2 * (n : ℤ) by
    have hf : ∀ i, ((τ.P.paint (τ.Q.shape.colLen 0 + i) 0).tailContrib.1 +
                     (τ.P.paint (τ.Q.shape.colLen 0 + i) 0).tailContrib.2) = 2 :=
      fun i => DRCSymbol.tailContrib_sum _
    exact h (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0) _ hf
  intro n f hf
  induction n with
  | zero => simp [Finset.fold]
  | succ k ih =>
    rw [Finset.range_add_one, Finset.fold_insert (by simp)]
    -- Fold over (k+1) = f k + (fold over range k); split component-wise.
    have hab : (f k).1 + (f k).2 = 2 := hf k
    -- Goal after `fold_insert`: ((f k) op (fold over range k)).1 + ... = 2*↑(k+1).
    -- Pop projections via Prod arithmetic and chain with `ih`.
    have hs := ih
    -- Use the algebraic computation; the goal has shape (a + s).1 + (a + s).2 with
    -- (a + s).1 = a.1 + s.1, (a + s).2 = a.2 + s.2.
    push_cast
    have h1 : (((f k) + (Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                  ((0, 0) : ℤ × ℤ) f).1) =
                (f k).1 + ((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                              ((0, 0) : ℤ × ℤ) f).1 := rfl
    have h2 : (((f k) + (Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                  ((0, 0) : ℤ × ℤ) f).2) =
                (f k).2 + ((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                              ((0, 0) : ℤ × ℤ) f).2 := rfl
    rw [h1, h2]
    have : (((f k).1 +
            ((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
              ((0, 0) : ℤ × ℤ) f).1) +
           ((f k).2 +
            ((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
              ((0, 0) : ℤ × ℤ) f).2)) =
            ((f k).1 + (f k).2) +
            (((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                ((0, 0) : ℤ × ℤ) f).1 +
             ((Finset.range k).fold (fun (a b : ℤ × ℤ) => a + b)
                ((0, 0) : ℤ × ℤ) f).2) := by ring
    rw [this, hab, hs]
    ring

/-- **Fact 3 (h_residual discharge, D type):** For a D-type PBP, the tail
    signature `(p_t, q_t)` satisfies `p_t + q_t = 2 * c₁ - c₂` under
    `c₁ := τ.P.shape.colLen 0` and `c₂ := 2 * τ.Q.shape.colLen 0`.
    Uses `Q_colLen0_le_P_colLen0_D` to convert ℕ truncated subtraction to ℤ. -/
theorem PBP.residual_identity_D (τ : PBP) (hγ : τ.γ = .D) :
    (PBP.tailSignature_D τ).1 + (PBP.tailSignature_D τ).2 =
      2 * (τ.P.shape.colLen 0 : ℤ) - 2 * (τ.Q.shape.colLen 0 : ℤ) := by
  rw [PBP.tailSignature_D_sum_eq]
  have hle : τ.Q.shape.colLen 0 ≤ τ.P.shape.colLen 0 :=
    PBP.Q_colLen0_le_P_colLen0_D τ hγ
  push_cast [Nat.cast_sub hle]
  ring

/-! ### Atomic discharge wrapper -/

/-- **Atomic discharge wrapper:** `prop_11_5_D_atomic` with the three atomic
    hypotheses (`h_dsum`, `h_descent`, `h_residual`) discharged automatically
    in terms of the natural PBP-derived parameter choices.

    Specifically, this wrapper instantiates:
    - `tau_card := PBP.cardCells τ`              (total cell count `|τ|`)
    - `n_inner  := tau_card - c₁`                (single-descent cell count)
    - `c₁       := τ.P.shape.colLen 0`           (P first-column length)
    - `c₂       := 2 * τ.Q.shape.colLen 0`       (so residual closes)
    - `p_t, q_t := PBP.tailSignature_D τ`        (tail signature)

    The user must still supply the AC.step invariants (`h_fc`, `h_n₀`,
    `h_sign`) and the per-component Prop 11.4 identifications
    (`h_prop_11_4_p`, `h_prop_11_4_q`). The three primitive cell-count facts
    are now fully discharged. -/
theorem prop_11_5_D_atomic_pbp_discharged
    (τ : PBP) (hγ : τ.γ = .D)
    (E : ILS) (n_prev p_prev q_prev : ℤ)
    (h_fc : ILS.firstColSign E =
              ((ILS.sign E).1 - n_prev, (ILS.sign E).2 - n_prev))
    (h_sign : ILS.sign E = (p_prev, q_prev))
    (h_prop_11_4_p :
      ((PBP.signature τ).1 : ℤ) =
        2 * (τ.Q.shape.colLen 0 : ℤ) + p_prev + (PBP.tailSignature_D τ).1)
    (h_prop_11_4_q :
      ((PBP.signature τ).2 : ℤ) =
        2 * (τ.Q.shape.colLen 0 : ℤ) + q_prev + (PBP.tailSignature_D τ).2)
    (h_n₀ : ((PBP.cardCells τ : ℤ) - τ.P.shape.colLen 0)
              - (ILS.sign E).1 - (ILS.sign E).2 + n_prev ≥ 0)
    (γ₁ : ℤ) :
    let n_inner : ℤ := (PBP.cardCells τ : ℤ) - τ.P.shape.colLen 0
    let n₀ := n_inner - (ILS.sign E).1 - (ILS.sign E).2 + n_prev
    let inner := ILS.charTwistCM (ILS.augment (n₀, n₀) E) γ₁
    ((PBP.signature τ).1 : ℤ) - (ILS.sign inner).1 - (ILS.firstColSign inner).2 =
      (PBP.tailSignature_D τ).1 ∧
    ((PBP.signature τ).2 : ℤ) - (ILS.sign inner).2 - (ILS.firstColSign inner).1 =
      (PBP.tailSignature_D τ).2 := by
  -- Discharge h_dsum.
  have h_dsum :
      ((PBP.signature τ).1 : ℤ) + ((PBP.signature τ).2 : ℤ) =
        2 * ((PBP.cardCells τ : ℤ)) := PBP.signature_sum_D τ hγ
  -- Discharge h_descent (definitional).
  have h_descent :
      ((PBP.cardCells τ : ℤ) - (τ.P.shape.colLen 0 : ℤ)) =
        ((PBP.cardCells τ : ℤ)) - (τ.P.shape.colLen 0 : ℤ) := rfl
  -- Discharge h_residual via tail sum.
  have h_residual :
      (PBP.tailSignature_D τ).1 + (PBP.tailSignature_D τ).2 =
        2 * (τ.P.shape.colLen 0 : ℤ) - 2 * (τ.Q.shape.colLen 0 : ℤ) :=
    PBP.residual_identity_D τ hγ
  -- Apply prop_11_5_D_atomic with the discharged values.
  exact prop_11_5_D_atomic E
    ((PBP.cardCells τ : ℤ) - τ.P.shape.colLen 0)
    n_prev (PBP.cardCells τ : ℤ)
    (τ.P.shape.colLen 0 : ℤ) (2 * (τ.Q.shape.colLen 0 : ℤ))
    p_prev q_prev
    ((PBP.signature τ).1 : ℤ) ((PBP.signature τ).2 : ℤ)
    (PBP.tailSignature_D τ).1 (PBP.tailSignature_D τ).2
    h_fc h_n₀ h_sign h_prop_11_4_p h_prop_11_4_q h_dsum h_descent h_residual γ₁

/-! ## Parity of signature sum -/

/-- For a B⁺-type PBP, `signature.1 + signature.2` is odd (= 2|τ| + 1). -/
theorem PBP.signature_sum_Bplus_odd (τ : PBP) (hγ : τ.γ = .Bplus) :
    Odd ((PBP.signature τ).1 + (PBP.signature τ).2) := by
  refine ⟨PBP.cardCells τ, ?_⟩
  have h := PBP.signature_sum_Bplus τ hγ
  omega

/-- For a B⁻-type PBP, `signature.1 + signature.2` is odd (= 2|τ| + 1). -/
theorem PBP.signature_sum_Bminus_odd (τ : PBP) (hγ : τ.γ = .Bminus) :
    Odd ((PBP.signature τ).1 + (PBP.signature τ).2) := by
  refine ⟨PBP.cardCells τ, ?_⟩
  have h := PBP.signature_sum_Bminus τ hγ
  omega

/-- For D/C/M-type PBP, `signature.1 + signature.2` is even. -/
theorem PBP.signature_sum_DCM_even (τ : PBP)
    (hγ : τ.γ = .D ∨ τ.γ = .C ∨ τ.γ = .M) :
    Even ((PBP.signature τ).1 + (PBP.signature τ).2) := by
  refine ⟨PBP.cardCells τ, ?_⟩
  rcases hγ with h | h | h
  · have := PBP.signature_sum_D τ h; omega
  · have := PBP.signature_sum_C τ h; omega
  · have := PBP.signature_sum_M τ h; omega
