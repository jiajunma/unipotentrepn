/-
# M1.4 Phase A: typed Φ_D : PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)

Reference: NL proof at `lean/docs/blueprints/M1_4_PhiD_typed.md`
(3-pass self-reviewed, 2026-04-19).

**Phase A (this file)**: define the descent-chain predicate
`IsDescentChain_D` and state the three interface theorems
(existence, singleton-validity, in-MYD) as `axiom`s. Assemble
`Phi_D` using the axioms.

**Current status (2026-04-21)**: All sorries closed. Paper content
that was previously sorry'd is now threaded as named Prop
hypotheses:
- `exists_descentChain_D` — fully proved
- `descentChain_D_singleton` — takes `DescentStepSingleton_D` hypothesis
- `DescentStepSingleton_D` — Prop abbrev encoding paper §11.5/§11.6

See `BijectionSig.lean` for the full hypothesis bundle per γ.
-/
import CombUnipotent.MYD.PhiD
import CombUnipotent.MYD.TypeMYD
import CombUnipotent.MYD.DPToSYD
import CombUnipotent.MYD.ShiftLeftCard
import CombUnipotent.MYD
import CombUnipotent.CountingProof.Descent
import CombUnipotent.CountingProof.Basic  -- for dpartColLensP/Q_D

open PBPInstantiation (toACStepData_D)

namespace BMSZ

/-- `chain` is the descent-chain encoding of τ's descent tower
    (inner-first ordering matching `AC.fold`'s left fold).

    Base case: τ has both shapes empty (bottom of the descent).
    Inductive step: the chain is `inner_chain ++ [outer_step]` where
    the outer step is the last in the inner-first ordering, and the
    inner chain describes the double-descent `doubleDescent_D_PBP τ`. -/
inductive IsDescentChain_D : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .D)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_D τ []
  | step {τ : PBP} (hγ : τ.γ = .D) {chain : List ACStepData}
      (h_rest : IsDescentChain_D (doubleDescent_D_PBP τ hγ) chain) :
      IsDescentChain_D τ (chain ++ [toACStepData_D τ hγ])

/-- Helper: for a D-type PBP, a descent chain exists by strong induction
    on the combined shape size. Each `doubleDescent_D_PBP` strictly
    decreases the size (via `YoungDiagram.shiftLeft_card_lt`). -/
theorem exists_descentChain_D_aux (n : ℕ) :
    ∀ (τ : PBP) (hγ : τ.γ = .D),
      τ.P.shape.cells.card + τ.Q.shape.cells.card = n →
      ∃ c : List ACStepData, IsDescentChain_D τ c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hγ hsize
    by_cases h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥
    · exact ⟨[], IsDescentChain_D.base τ hγ h_empty⟩
    · -- At least one shape is non-empty → at least one has colLen 0 > 0
      have h_decrease :
          (doubleDescent_D_PBP τ hγ).P.shape.cells.card +
          (doubleDescent_D_PBP τ hγ).Q.shape.cells.card < n := by
        -- doubleDescent_D_PBP uses shape.shiftLeft for both P and Q
        unfold doubleDescent_D_PBP
        dsimp only
        have hP_le := YoungDiagram.shiftLeft_card_le τ.P.shape
        have hQ_le := YoungDiagram.shiftLeft_card_le τ.Q.shape
        -- Not both empty: at least one has colLen 0 > 0 → its card strictly decreases
        push_neg at h_empty
        by_cases hP_empty : τ.P.shape = ⊥
        · -- P empty, so Q non-empty → Q's colLen 0 > 0 → Q's card decreases
          have hQ_ne : τ.Q.shape ≠ ⊥ := h_empty hP_empty
          have hQ_col0 : 0 < τ.Q.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hQ_ne ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hQ_lt := YoungDiagram.shiftLeft_card_lt τ.Q.shape hQ_col0
          omega
        · -- P non-empty → P's card decreases
          have hP_col0 : 0 < τ.P.shape.colLen 0 := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hP_empty ((YoungDiagram.colLen_zero_eq_zero_iff_empty _).mp h0)
          have hP_lt := YoungDiagram.shiftLeft_card_lt τ.P.shape hP_col0
          omega
      obtain ⟨c_inner, h_inner⟩ := ih _ h_decrease (doubleDescent_D_PBP τ hγ) rfl rfl
      exact ⟨c_inner ++ [toACStepData_D τ hγ], IsDescentChain_D.step hγ h_inner⟩

/-- **Theorem (M1.4.2)**: every σ ∈ PBPSet .D μP μQ admits a descent chain. -/
theorem exists_descentChain_D {μP μQ : YoungDiagram} (σ : PBPSet .D μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_D σ.val c := by
  have hγ : σ.val.γ = .D := σ.prop.1
  exact exists_descentChain_D_aux _ σ.val hγ rfl

/-- `toACStepData_D τ hγ` has non-negative `p` and `q` (signatures are nat). -/
theorem toACStepData_D_p_nonneg (τ : PBP) (hγ : τ.γ = .D) :
    0 ≤ (toACStepData_D τ hγ).p ∧ 0 ≤ (toACStepData_D τ hγ).q := by
  unfold toACStepData_D
  simp only
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩

/-- **Base case of std bound for D chain**: when E_inner = baseILS .D = [],
    the std bound at the outer step holds trivially since
    sign [] = (0, 0) and firstColSign [] = (0, 0), reducing to
    PBP signature non-negativity. -/
theorem stepStdAndAugment_D_base_nil (τ : PBP) (hγ : τ.γ = .D) :
    (toACStepData_D τ hγ).p - (ILS.sign ([] : ILS)).1 -
      (ILS.firstColSign ([] : ILS)).2 ≥ 0 ∧
    (toACStepData_D τ hγ).q - (ILS.sign ([] : ILS)).2 -
      (ILS.firstColSign ([] : ILS)).1 ≥ 0 := by
  show (_ : ℤ) ≥ 0 ∧ (_ : ℤ) ≥ 0
  obtain ⟨hp, hq⟩ := toACStepData_D_p_nonneg τ hγ
  refine ⟨?_, ?_⟩ <;> simp [ILS.sign, ILS.firstColSign] <;> omega


/-- Per-step thetaLift singleton for D chain, under std hypothesis.
    PROVED directly: given std, thetaLift_CD produces the explicit
    augment singleton. -/
theorem descent_step_thetaLift_singleton_std {τ : PBP} (hγ : τ.γ = .D)
    (E_inner : ILS)
    (h_std :
      (toACStepData_D τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2 ≥ 0 ∧
      (toACStepData_D τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1 ≥ 0) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_D τ hγ))
      (toACStepData_D τ hγ).γ
      (toACStepData_D τ hγ).p
      (toACStepData_D τ hγ).q = [E'] := by
  -- D has no pre-twist
  have h_preTwist : stepPreTwist E_inner (toACStepData_D τ hγ) = E_inner := by
    unfold stepPreTwist; simp [toACStepData_D]
  refine ⟨?_, ?_⟩
  · exact ILS.augment
      ((toACStepData_D τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2,
       (toACStepData_D τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1)
      (ILS.charTwistCM E_inner
        (((toACStepData_D τ hγ).p - (toACStepData_D τ hγ).q) / 2))
  rw [h_preTwist]
  show ILS.thetaLift E_inner _ _ _ = _
  simp only [ILS.thetaLift]
  have hγ' : (toACStepData_D τ hγ).γ = .D := rfl
  rw [hγ']
  simp only [ILS.thetaLift_CD]
  rw [if_pos h_std]

/-- **Paper §11.5/§11.6 per-step singleton hypothesis (D)**: along a
    valid D chain, each thetaLift step returns a singleton.

    CHAIN-CONDITIONAL form: `E_inner` is restricted to ILSs arising
    from an inner valid chain via `ChainSingleton`. This matches
    paper §11.5/§11.6 scope — the std sign-bound holds for
    chain-derived E_inner, not arbitrary ones. -/
abbrev DescentStepSingleton_D : Prop :=
  ∀ (τ : PBP) (hγ : τ.γ = .D)
    (chain_inner : List ACStepData) (E_inner : ILS),
    IsDescentChain_D (doubleDescent_D_PBP τ hγ) chain_inner →
    ChainSingleton (baseILS .D) chain_inner E_inner →
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_D τ hγ))
      (toACStepData_D τ hγ).γ
      (toACStepData_D τ hγ).p
      (toACStepData_D τ hγ).q = [E']

/-- Explicit std-hypothesis variant at any D-type chain step.
    Alias pattern: the _std variant is always provable; the non-std
    version assumes paper §11.5/11.6. -/
theorem descent_step_thetaLift_singleton_from_std {τ : PBP} (hγ : τ.γ = .D)
    (E_inner : ILS)
    (h_std :
      (toACStepData_D τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2 ≥ 0 ∧
      (toACStepData_D τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1 ≥ 0) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_D τ hγ))
      (toACStepData_D τ hγ).γ
      (toACStepData_D τ hγ).p
      (toACStepData_D τ hγ).q = [E'] :=
  descent_step_thetaLift_singleton_std hγ E_inner h_std

/-- **Reduction**: `DescentStepSingleton_D` follows from a
    chain-conditional std sign-bound hypothesis. -/
theorem descentStepSingleton_D_of_std
    (h_std : ∀ (τ : PBP) (hγ : τ.γ = .D)
              (chain_inner : List ACStepData) (E_inner : ILS)
              (_h_chain : IsDescentChain_D (doubleDescent_D_PBP τ hγ) chain_inner)
              (_h_sing : ChainSingleton (baseILS .D) chain_inner E_inner),
      (toACStepData_D τ hγ).p - (ILS.sign E_inner).1 - (ILS.firstColSign E_inner).2 ≥ 0 ∧
      (toACStepData_D τ hγ).q - (ILS.sign E_inner).2 - (ILS.firstColSign E_inner).1 ≥ 0) :
    DescentStepSingleton_D := by
  intro τ hγ chain_inner E_inner h_chain h_sing
  exact descent_step_thetaLift_singleton_std hγ E_inner
    (h_std τ hγ chain_inner E_inner h_chain h_sing)

/-- **Theorem (M1.4.2 partial)**: any valid descent chain for τ is
    ChainSingleton-valid.

    Proof: induction on `IsDescentChain_D`. Base case (empty chain)
    uses `ChainSingleton.nil`. Inductive step uses `ChainSingleton.snoc`
    with the per-step singleton hypothesis from
    `descent_step_thetaLift_singleton`.

    This reduces the full axiom `descentChain_D_singleton` to the
    single-step sign-bound fact (paper §11.5/11.6 content). -/
theorem descentChain_D_singleton (h_step : DescentStepSingleton_D)
    {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_D τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .D) chain E := by
  induction h_chain with
  | base τ hγ h_empty => exact ⟨baseILS .D, ChainSingleton.nil _⟩
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_inner, h_inner⟩ := ih
    obtain ⟨E', h_theta⟩ := h_step τ_outer hγ chain_inner E_inner h_rest h_inner
    exact ⟨stepPostTwist E' (toACStepData_D τ_outer hγ),
           ChainSingleton.snoc h_inner h_theta⟩

/-- Shape-dp coherence predicate at the PBP level. -/
def PBPIsCoherent_D (τ : PBP) (dp : DualPart) : Prop :=
  τ.P.shape.colLens = dpartColLensP_D dp ∧
  τ.Q.shape.colLens = dpartColLensQ_D dp

/-- External shape-dp coherence (on `μP, μQ` before a PBP is given).
    Identical to `DPCoherent_D` in `Bijection.lean` (kept here to avoid
    import cycle). -/
def PBPIsCoherent_D_ext (μP μQ : YoungDiagram) (dp : DualPart) : Prop :=
  μP.colLens = dpartColLensP_D dp ∧ μQ.colLens = dpartColLensQ_D dp

/-- `dpartColLensP_D dp = []` iff `dp = []`. (partition utility) -/
private theorem dpartColLensP_D_eq_nil_iff (dp : DualPart) :
    dpartColLensP_D dp = [] ↔ dp = [] := by
  constructor
  · intro h
    match dp with
    | [] => rfl
    | [r] => simp [dpartColLensP_D] at h
    | _ :: _ :: _ => simp [dpartColLensP_D] at h
  · intro h; subst h; rfl

/-- `(dpartColLensP_D dp).tail = dpartColLensP_D (dp.drop 2)`. -/
private theorem dpartColLensP_D_tail (dp : DualPart) :
    (dpartColLensP_D dp).tail = dpartColLensP_D (dp.drop 2) := by
  match dp with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- `SortedGE` is preserved under `List.drop`. -/
private theorem List.SortedGE.drop {l : List ℕ} (h : l.SortedGE) (n : ℕ) :
    (l.drop n).SortedGE := by
  intro i j hij
  have hi_len : n + i.val < l.length := by
    have h_i := i.isLt
    have h_dl : (l.drop n).length = l.length - n := List.length_drop
    omega
  have hj_len : n + j.val < l.length := by
    have h_j := j.isLt
    have h_dl : (l.drop n).length = l.length - n := List.length_drop
    omega
  have hij' : n + i.val ≤ n + j.val := by
    have : i.val ≤ j.val := hij
    omega
  have h_ante := h (show (⟨n + i.val, hi_len⟩ : Fin l.length) ≤
              ⟨n + j.val, hj_len⟩ from hij')
  show (l.drop n).get i ≥ (l.drop n).get j
  simp only [List.get_eq_getElem, List.getElem_drop]
  simp only [List.get_eq_getElem] at h_ante
  exact h_ante

/-- `Odd` on all members is preserved under `List.drop`. -/
private theorem drop_all_odd {l : List ℕ} (h : ∀ r ∈ l, Odd r) (n : ℕ) :
    ∀ r ∈ l.drop n, Odd r := by
  intro r hr
  exact h r (List.mem_of_mem_drop hr)

/-- **Sub-lemma 1 (P-side coherence preservation)**: P's coherence
    lifts to the doubleDescent PBP with `dp.drop 2`. -/
theorem coherence_descend_D_P {τ : PBP} (hγ : τ.γ = .D) {dp : DualPart}
    (h_coh : τ.P.shape.colLens = dpartColLensP_D dp) :
    (doubleDescent_D_PBP τ hγ).P.shape.colLens =
    dpartColLensP_D (dp.drop 2) := by
  unfold doubleDescent_D_PBP
  dsimp only
  -- The new P shape is τ.P.shape.shiftLeft
  rw [YoungDiagram.shiftLeft_colLens_eq_tail, h_coh, dpartColLensP_D_tail]

/-- Helper: `dpartColLensQ_D` on a list of all-1's is empty. -/
private theorem dpartColLensQ_D_all_ones_nil :
    ∀ (xs : List ℕ), (∀ x ∈ xs, x = 1) → dpartColLensQ_D xs = [] := by
  intro xs hall
  match xs with
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest =>
    have hy : y = 1 := hall y (by simp)
    have hrest : ∀ z ∈ rest, z = 1 := fun z hz => hall z (by simp [hz])
    simp only [dpartColLensQ_D, hy]
    simp
    exact dpartColLensQ_D_all_ones_nil rest hrest

/-- **Sub-lemma 1 (Q-side coherence preservation)**: Q's coherence
    lifts to the doubleDescent PBP with `dp.drop 2`.

    Uses sorted-descending + all-odd hypotheses to handle the `r₂ = 1`
    boundary case (where all subsequent `r_i = 1`, so Q's shape is
    unchanged under shiftLeft but `dpartColLensQ_D (dp.drop 2)` is
    also empty). -/
theorem coherence_descend_D_Q {τ : PBP} (hγ : τ.γ = .D) {dp : DualPart}
    (h_coh : τ.Q.shape.colLens = dpartColLensQ_D dp)
    (hsort : dp.SortedGE) (hodd : ∀ r ∈ dp, Odd r) :
    (doubleDescent_D_PBP τ hγ).Q.shape.colLens =
    dpartColLensQ_D (dp.drop 2) := by
  unfold doubleDescent_D_PBP
  dsimp only
  rw [YoungDiagram.shiftLeft_colLens_eq_tail, h_coh]
  -- Need: (dpartColLensQ_D dp).tail = dpartColLensQ_D (dp.drop 2)
  match dp, hsort, hodd with
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | r₁ :: r₂ :: rest, hs, ho =>
    by_cases hr₂ : r₂ > 1
    · -- Direct case: tail shifts correctly
      simp only [dpartColLensQ_D, hr₂, if_true, List.tail_cons, List.drop]
    · -- r₂ ≤ 1 AND r₂ odd (∈ dp): forces r₂ = 1 AND sorted + odd → all rest are 1
      have hr₂_odd : Odd r₂ := ho r₂ (by simp)
      have hr₂_eq : r₂ = 1 := by
        obtain ⟨k, hk⟩ := hr₂_odd; omega
      have hrest_ones : ∀ x ∈ rest, x = 1 := by
        intro x hx
        have hx_le : x ≤ r₂ := by
          -- sorted descending: r₂ ≥ x via pairwise decomposition
          obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hx
          -- x = rest[i]; in the full list r₁ :: r₂ :: rest, x is at position i+2
          have h_pos : (r₁ :: r₂ :: rest)[i + 2]'(by simp; omega) = x := by
            simp [hi_eq]
          have h_r₂_pos : (r₁ :: r₂ :: rest)[1]'(by simp) = r₂ := by simp
          have h_anti : (r₁ :: r₂ :: rest).get ⟨1, by simp⟩ ≥
              (r₁ :: r₂ :: rest).get ⟨i + 2, by simp; omega⟩ := by
            apply hs
            show (1 : ℕ) ≤ i + 2
            omega
          simp [List.get_eq_getElem] at h_anti
          rw [hi_eq] at h_anti
          exact h_anti
        have hx_odd : Odd x := ho x (by simp [hx])
        obtain ⟨k, hk⟩ := hx_odd; omega
      -- dpartColLensQ_D (r₁ :: 1 :: rest) = dpartColLensQ_D rest
      -- dp.drop 2 = rest
      -- dpartColLensQ_D rest = [] (all ones)
      -- (dpartColLensQ_D rest).tail = [].tail = []
      simp only [dpartColLensQ_D, hr₂, if_false, List.drop]
      rw [dpartColLensQ_D_all_ones_nil rest hrest_ones]
      rfl

/-- `dpartColLensQ_D` relation under `dp.drop 2`. Has a conditional case. -/
private theorem dpartColLensQ_D_drop2 (dp : DualPart) :
    ∀ r₁ r₂ rest, dp = r₁ :: r₂ :: rest →
      (r₂ > 1 → (dpartColLensQ_D dp).tail = dpartColLensQ_D (dp.drop 2)) ∧
      (r₂ ≤ 1 → dpartColLensQ_D dp = dpartColLensQ_D (dp.drop 2)) := by
  intro r₁ r₂ rest h
  subst h
  constructor
  · intro hr₂
    simp [dpartColLensQ_D, hr₂]
  · intro hr₂
    have : ¬ (r₂ > 1) := by omega
    simp [dpartColLensQ_D, this]

/-- **Sub-lemma 2**: `thetaLift_CD` output form when it's singleton.

    Definitional unfold of `ILS.thetaLift_CD` (MYD.lean:180):
    when the sign bound holds, output is `[augment (addp, addn) (charTwistCM E ((p-q)/2))]`.

    Paper ref: Eq 9.29 + Def 9.18 (augment).

    Used in `descentChain_D_in_MYD` step case to access E''s structure. -/
theorem thetaLift_CD_output_form (E : ILS) (p q : ℤ) (E' : ILS)
    (h : ILS.thetaLift_CD E p q = [E']) :
    let addp := p - (ILS.sign E).1 - (ILS.firstColSign E).2
    let addn := q - (ILS.sign E).2 - (ILS.firstColSign E).1
    addp ≥ 0 ∧ addn ≥ 0 ∧
    E' = ILS.augment (addp, addn) (ILS.charTwistCM E ((p - q) / 2)) := by
  simp only [ILS.thetaLift_CD] at h
  split_ifs at h with h_std
  · simp at h
    refine ⟨h_std.1, h_std.2, ?_⟩
    rw [← h]

/-- `⊥.colLens = []`. -/
private theorem YoungDiagram_bot_colLens : (⊥ : YoungDiagram).colLens = [] := by
  apply List.length_eq_zero_iff.mp
  rw [YoungDiagram.length_colLens]
  -- (⊥ : YoungDiagram).rowLen 0 = 0: use rowLen_transpose + colLen_zero for ⊥
  have : (⊥ : YoungDiagram).transpose = ⊥ := by ext; simp
  have : (⊥ : YoungDiagram).rowLen 0 = (⊥ : YoungDiagram).colLen 0 := by
    rw [← YoungDiagram.colLen_transpose, this]
  rw [this]
  exact (YoungDiagram.colLen_zero_eq_zero_iff_empty _).mpr rfl


/-! ## twistBD preserves MYD properties

These are small, self-contained lemmas (not paper content) needed for
the ε-twist to preserve MYD typing.
-/

/-- Helper: `|a * b| = |b|` when `a ∈ {1, -1}`. -/
private lemma natAbs_signed_mul (a b : ℤ) (ha : a = 1 ∨ a = -1) :
    (a * b).natAbs = b.natAbs := by
  rcases ha with ha | ha <;> simp [ha, Int.natAbs_mul, Int.natAbs_neg]

/-- Helper: integer power of $\pm 1$ is $\pm 1$. -/
private lemma pow_signed (a : ℤ) (ha : a = 1 ∨ a = -1) (n : ℕ) :
    a ^ n = 1 ∨ a ^ n = -1 := by
  rcases ha with ha | ha
  · left; simp [ha]
  · subst ha
    rcases Nat.even_or_odd n with hp | hp
    · left; exact hp.neg_one_pow
    · right; exact hp.neg_one_pow

/-- `twistBD` with tp, tn ∈ {1, -1} preserves row-wise absolute values.

    Proof: unfold `ILS.twistBD` to `mapIdx`; apply `List.ext_getElem`
    to reduce to per-index equality. At each index i:
    - If ℓ = i+1 is even: `twistBDRow = id`, nothing to check.
    - If ℓ is odd: row becomes `(tpp*p, tnn*q)` with tpp, tnn ∈ {1, -1}
      (via `pow_signed`), so `natAbs` is preserved on each component. -/
theorem twistBD_preserves_absValues (E : ILS) (tp tn : ℤ)
    (htp : tp = 1 ∨ tp = -1) (htn : tn = 1 ∨ tn = -1) :
    absValues (ILS.twistBD E tp tn) = absValues E := by
  unfold absValues ILS.twistBD
  apply List.ext_getElem
  · simp
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_mapIdx]
  unfold ILS.twistBDRow
  simp only
  split_ifs with hℓ
  · rfl
  · -- odd ℓ case: row is (tpp * p.1, tnn * p.2) with tpp, tnn ∈ {1, -1}
    set h := (i + 1) / 2 with hh
    have htpp : tp ^ (h + 1) * tn ^ h = 1 ∨ tp ^ (h + 1) * tn ^ h = -1 := by
      rcases pow_signed tp htp (h + 1) with h1 | h1 <;>
        rcases pow_signed tn htn h with h2 | h2 <;>
          simp [h1, h2]
    have htnn : tn ^ (h + 1) * tp ^ h = 1 ∨ tn ^ (h + 1) * tp ^ h = -1 := by
      rcases pow_signed tn htn (h + 1) with h1 | h1 <;>
        rcases pow_signed tp htp h with h2 | h2 <;>
          simp [h1, h2]
    ext
    · exact natAbs_signed_mul _ _ htpp
    · exact natAbs_signed_mul _ _ htnn

/-- `twistBD` preserves `MYDRowValid` at parity-forced positions for
    B/D types when tp = tn (matching the ⊗ (ε, ε) pattern).

    Key observation: for γ ∈ {B⁺, B⁻, D}, parity is forced at paper
    row index ℓ = j+1 even. In `twistBDRow`, the ℓ-even case returns
    the row unchanged. So MYDRowValid is trivially preserved.

    For C/M (parity at ℓ odd), the twist does modify the row; the
    argument would differ. Not needed for `Phi_D` (which is B/D-only),
    so we narrow the hypothesis to B/D here. -/
theorem twistBD_preserves_MYDRowValid (E : ILS) (γ : RootType) (t : ℤ)
    (hγ : γ = .Bplus ∨ γ = .Bminus ∨ γ = .D)
    (_ht : t = 1 ∨ t = -1)
    (h : ∀ (j : ℕ) (hj : j < E.length), MYDRowValid γ (j + 1) E[j]) :
    ∀ (j : ℕ) (hj : j < (ILS.twistBD E t t).length),
      MYDRowValid γ (j + 1) (ILS.twistBD E t t)[j] := by
  intro j hj hforced
  have hlen : (ILS.twistBD E t t).length = E.length := by
    unfold ILS.twistBD; simp
  have hj' : j < E.length := hlen ▸ hj
  -- SYDParityForced γ (j + 1) for γ ∈ {Bplus, Bminus, D} is (j+1) % 2 = 0.
  have hℓ_even : (j + 1) % 2 = 0 := by
    rcases hγ with h | h | h <;> rw [h] at hforced <;> exact hforced
  -- In twistBDRow, ℓ even means the row is unchanged.
  have heq : (ILS.twistBD E t t)[j] = E[j] := by
    unfold ILS.twistBD
    rw [List.getElem_mapIdx]
    unfold ILS.twistBDRow
    simp [hℓ_even]
  rw [heq]
  exact h j hj' hforced

/-- **Sub-lemma 4**: `twistBD E 1 (-1)` preserves `MYDRowValid γ`
    for γ ∈ {B⁺, B⁻, D}.

    At B/D parity-forced positions (paper ℓ even, Lean `(j + 1) % 2 = 0`),
    `twistBDRow` returns the row unchanged — so MYDRowValid is
    trivially preserved, regardless of (tp, tn).

    Generalises `twistBD_preserves_MYDRowValid` (which had tp = tn). -/
theorem twistBD_general_preserves_MYDRowValid_BD (E : ILS) (γ : RootType)
    (tp tn : ℤ) (hγ : γ = .Bplus ∨ γ = .Bminus ∨ γ = .D)
    (h : ∀ (j : ℕ) (hj : j < E.length), MYDRowValid γ (j + 1) E[j]) :
    ∀ (j : ℕ) (hj : j < (ILS.twistBD E tp tn).length),
      MYDRowValid γ (j + 1) (ILS.twistBD E tp tn)[j] := by
  intro j hj hforced
  have hlen : (ILS.twistBD E tp tn).length = E.length := by
    unfold ILS.twistBD; simp
  have hj' : j < E.length := hlen ▸ hj
  have hℓ_even : (j + 1) % 2 = 0 := by
    rcases hγ with h | h | h <;> rw [h] at hforced <;> exact hforced
  have heq : (ILS.twistBD E tp tn)[j] = E[j] := by
    unfold ILS.twistBD
    rw [List.getElem_mapIdx]
    unfold ILS.twistBDRow
    simp [hℓ_even]
  rw [heq]
  exact h j hj' hforced

end BMSZ
