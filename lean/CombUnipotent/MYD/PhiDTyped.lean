/-
# M1.4 Phase A: typed Φ_D : PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)

Reference: NL proof at `lean/docs/blueprints/M1_4_PhiD_typed.md`
(3-pass self-reviewed, 2026-04-19).

**Phase A (this file)**: define the descent-chain predicate
`IsDescentChain_D` and state the three interface theorems
(existence, singleton-validity, in-MYD) as `axiom`s. Assemble
`Phi_D` using the axioms.

**Phase B (future sessions, M1.4.2 and M1.4.3)**: prove the three
axioms. These are paper §11 content:
- `exists_descentChain_D`: strong induction on PBP size
- `descentChain_D_singleton`: uses paper Lemma 11.5/11.6 sign bounds
- `descentChain_D_in_MYD`: uses paper §9.4 theta-lift structural
  preservation of parity and shape.

Using `axiom` rather than `sorry` makes the phase boundary explicit
and avoids build warnings. Each axiom is paired with a concrete
proof-plan in the accompanying NL proof doc.
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

/-- **Per-step thetaLift singleton for descent chain** (paper Lem 11.5/11.6):
    each step in a descent chain has a singleton ILS-thetaLift.

    TODO: use `ILS.thetaLift_CD_nonempty` (MYD.lean:4679) — gives
    non-emptiness given `h_std` sign bound. Combined with the fact
    that `thetaLift_CD` definitionally produces at most 1 element
    (MYD.lean:180: `if h then [augment ...] else []`), we get exactly 1.
    The remaining work is proving `h_std` for descent-chain-supplied
    E_inner and (p, q) = (PBP.signature τ).

    This requires relating `sign (pre-twisted E_inner)` to τ's signature
    through the chain — paper §11.5/11.6 content. Likely connects to
    existing `ACResult.thetaLift_sign` (MYD.lean:821) and
    `AC.step_sign_D` (MYD.lean:865). -/
theorem descent_step_thetaLift_singleton {τ : PBP} (hγ : τ.γ = .D)
    (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_D τ hγ))
      (toACStepData_D τ hγ).γ
      (toACStepData_D τ hγ).p
      (toACStepData_D τ hγ).q = [E'] := by
  sorry

/-- **Theorem (M1.4.2 partial)**: any valid descent chain for τ is
    ChainSingleton-valid.

    Proof: induction on `IsDescentChain_D`. Base case (empty chain)
    uses `ChainSingleton.nil`. Inductive step uses `ChainSingleton.snoc`
    with the per-step singleton hypothesis from
    `descent_step_thetaLift_singleton`.

    This reduces the full axiom `descentChain_D_singleton` to the
    single-step sign-bound fact (paper §11.5/11.6 content). -/
theorem descentChain_D_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_D τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .D) chain E := by
  induction h_chain with
  | base τ hγ h_empty => exact ⟨baseILS .D, ChainSingleton.nil _⟩
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    obtain ⟨E_inner, h_inner⟩ := ih
    obtain ⟨E', h_theta⟩ := descent_step_thetaLift_singleton hγ E_inner
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

/-- **Theorem (M1.4.3)**: the ILS `E` extracted from a valid descent
    chain satisfies the MYD properties — parity + shape match the
    orbit `dpToSYD .D dp` whenever `dp` is coherent with `τ`'s shapes.

    Proof plan: induction on the chain tracking two invariants:
    (a) parity preservation at each theta-lift step (paper §9.4),
    (b) shape growth matching the orbit's partition transpose
    (`partTranspose dp`).

    TODO: apply `thetaLift_{CD,MB}_sign` (MYD.lean:564, 655) + sign
    preservation + parity inductive argument. -/
theorem descentChain_D_in_MYD {τ : PBP} {chain : List ACStepData}
    {E : ILS} (dp : DualPart)
    (h_coh : PBPIsCoherent_D τ dp)
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton (baseILS .D) chain E) :
    (∀ (j : ℕ) (h : j < E.length), MYDRowValid .D (j + 1) E[j])
    ∧ absValues E = (dpToSYD .D dp).rows := by
  induction h_chain generalizing E dp with
  | base τ hγ h_empty =>
    -- chain = []; ChainSingleton constraints force E = baseILS .D = []
    cases h_sing
    -- E = baseILS .D = []. From empty shapes + coherence, dp = [].
    -- Both sides become empty.
    have hdp : dp = [] := by
      have hP := h_coh.1
      rw [h_empty.1, YoungDiagram_bot_colLens] at hP
      exact (dpartColLensP_D_eq_nil_iff dp).mp hP.symm
    subst hdp
    refine ⟨?_, ?_⟩
    · -- baseILS .D = [], so E.length = 0, vacuous
      intro j h; exfalso; unfold baseILS at h; simp at h
    · -- absValues [] = [] = (SYD.empty .D).rows
      unfold absValues baseILS
      simp [dpToSYD_empty, SYD.empty_rows]
  | step hγ h_rest ih =>
    rename_i τ_outer chain_inner
    -- Decompose h_sing via snoc_inv into inner chain + end step + final.
    obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
      ChainSingleton.snoc_inv h_sing
    -- Outline (paper §9.4 structural preservation):
    -- 1. Apply IH on E_mid with a "descended" dp_inner matching
    --    (doubleDescent_D_PBP τ_outer hγ)'s shapes:
    --      have h_coh_inner : PBPIsCoherent_D (doubleDescent_D_PBP ...) dp_inner
    --      := by derive from h_coh (double-descent shifts dp by dp.drop 2)
    --      have ih_result := ih h_coh_inner h_inner_sing
    -- 2. Use h_theta (thetaLift is singleton at outer step) + the form of
    --    ILS.thetaLift_CD = [augment (charTwistCM E_mid' ...) ...] to derive:
    --    (a) parity: outer-step appends one new row with correct parity
    --        (new row's sign matches orbit's SYD row via `thetaLift_CD_sign`
    --         at MYD.lean:564; parity-forced positions have p = q ≥ 0)
    --    (b) shape: absValues E = (dpToSYD .D dp).rows follows from
    --        absValues E_mid = (dpToSYD .D dp_inner).rows (IH)
    --        + the new outer row matching (dpToSYD .D dp).rows[0]
    -- 3. stepPostTwist applies twistBD 1 (-1) for D if ε_τ = 1, else id;
    --    this preserves MYD properties via `twistBD_preserves_absValues`
    --    and `twistBD_preserves_MYDRowValid`.
    sorry

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

/-! ## Assembly: typed Phi_D -/

/-- **Typed Φ_D** (paper Prop 11.15, D type):
    $\Phi_D : \PBP_D(\mu_P, \mu_Q) \times \mathrm{Fin}\ 2 \to \MYD_D(\mathrm{dpToSYD\ .D\ dp})$,
    $(\sigma, \varepsilon) \mapsto L_\sigma \otimes (\varepsilon, \varepsilon)$.

    Constructed via the three interface axioms plus `Phi_chain` (M1.3):
    1. `exists_descentChain_D` provides a chain.
    2. `descentChain_D_singleton` extracts the unique `L_σ : ILS`.
    3. `descentChain_D_in_MYD` certifies that `L_σ ∈ MYD .D (dpToSYD .D dp)`.
    4. The ε-twist preserves MYD via `twistBD_preserves_*`. -/
noncomputable def Phi_D {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : PBPIsCoherent_D_ext μP μQ dp)
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    MYD .D (dpToSYD .D dp) :=
  let chain : List ACStepData := Classical.choose (exists_descentChain_D σ)
  let h_chain : IsDescentChain_D σ.val chain :=
    Classical.choose_spec (exists_descentChain_D σ)
  let E : ILS := Classical.choose (descentChain_D_singleton h_chain)
  let h_sing : ChainSingleton (baseILS .D) chain E :=
    Classical.choose_spec (descentChain_D_singleton h_chain)
  -- Derive per-τ coherence from the external coherence + σ's shape
  have h_coh_τ : PBPIsCoherent_D σ.val dp := by
    constructor
    · rw [σ.prop.2.1]; exact h_coh.1
    · rw [σ.prop.2.2]; exact h_coh.2
  let hMYD := descentChain_D_in_MYD dp h_coh_τ h_chain h_sing
  let h_par := hMYD.1
  let h_shape := hMYD.2
  let E' := if ε = 1 then ILS.twistBD E (-1) (-1) else E
  have h_E'_par : ∀ (j : ℕ) (hj : j < E'.length),
      MYDRowValid .D (j + 1) E'[j] := by
    by_cases hε : ε = 1
    · simp [E', hε]
      exact twistBD_preserves_MYDRowValid E .D (-1)
        (Or.inr (Or.inr rfl)) (Or.inr rfl) h_par
    · simp [E', hε]
      exact h_par
  have h_E'_shape : absValues E' = (dpToSYD .D dp).rows := by
    by_cases hε : ε = 1
    · simp [E', hε]
      rw [twistBD_preserves_absValues E (-1) (-1) (Or.inr rfl) (Or.inr rfl)]
      exact h_shape
    · simp [E', hε]
      exact h_shape
  ⟨E', h_E'_par, h_E'_shape⟩

end BMSZ
