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
import CombUnipotent.MYD
import CombUnipotent.CountingProof.Descent

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

/-- **Axiom (M1.4.2)**: every σ ∈ PBPSet .D μP μQ admits a descent chain.

    Proof plan: strong induction on `σ.val.cardCells`; each
    `doubleDescent_D_PBP` strictly decreases the size. Base case is
    `IsDescentChain_D.base` for empty shapes. -/
axiom exists_descentChain_D {μP μQ : YoungDiagram} (σ : PBPSet .D μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_D σ.val c

/-- **Per-step thetaLift singleton for descent chain** (paper Lem 11.5/11.6):
    each step in a descent chain has a singleton ILS-thetaLift.

    This is the essential sign-bound content of paper §11.5-11.6.
    Kept as axiom pending the full sign-preservation proof. -/
axiom descent_step_thetaLift_singleton {τ : PBP} (hγ : τ.γ = .D)
    (E_inner : ILS) :
    ∃ E' : ILS, ILS.thetaLift
      (stepPreTwist E_inner (toACStepData_D τ hγ))
      (toACStepData_D τ hγ).γ
      (toACStepData_D τ hγ).p
      (toACStepData_D τ hγ).q = [E']

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

/-- **Axiom (M1.4.3)**: the ILS `E` extracted from a valid descent
    chain satisfies the MYD properties.

    Proof plan: induction on the chain tracking two invariants:
    (a) parity preservation at each theta-lift step (paper §9.4),
    (b) shape growth matching the orbit's partition transpose
    (`partTranspose dp`).

    The `dp` parameter is the dual partition corresponding to τ's
    shapes; for the typed Phi_D we'll pass it explicitly. -/
axiom descentChain_D_in_MYD {τ : PBP} {chain : List ACStepData}
    {E : ILS} (dp : DualPart)
    (_h_chain : IsDescentChain_D τ chain)
    (_h_sing : ChainSingleton (baseILS .D) chain E) :
    (∀ (j : ℕ) (h : j < E.length), MYDRowValid .D (j + 1) E[j])
    ∧ absValues E = (dpToSYD .D dp).rows

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
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    MYD .D (dpToSYD .D dp) :=
  let chain : List ACStepData := Classical.choose (exists_descentChain_D σ)
  let h_chain : IsDescentChain_D σ.val chain :=
    Classical.choose_spec (exists_descentChain_D σ)
  let E : ILS := Classical.choose (descentChain_D_singleton h_chain)
  let h_sing : ChainSingleton (baseILS .D) chain E :=
    Classical.choose_spec (descentChain_D_singleton h_chain)
  let hMYD := descentChain_D_in_MYD dp h_chain h_sing
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
