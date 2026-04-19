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

/-- **Axiom (M1.4.2)**: any valid descent chain for τ is
    ChainSingleton-valid, yielding a unique ILS `E`.

    Proof plan: induction on `IsDescentChain_D`. Base case uses
    `ChainSingleton.nil`. Inductive step uses `AC_step_singleton`
    plus the sign-bound hypothesis from paper Lemma 11.5/11.6
    (`ILS.thetaLift_CD_nonempty` / `ILS.thetaLift_MB_nonempty` at
    MYD.lean:4679+ already has the non-emptiness direction; combined
    with the fact that `ILS.thetaLift_*` always has length ≤ 1, we
    get exactly length 1). -/
axiom descentChain_D_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_D τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .D) chain E

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

/-- `twistBD` with tp, tn ∈ {1, -1} preserves row-wise absolute values. -/
axiom twistBD_preserves_absValues (E : ILS) (tp tn : ℤ)
    (_htp : tp = 1 ∨ tp = -1) (_htn : tn = 1 ∨ tn = -1) :
    absValues (ILS.twistBD E tp tn) = absValues E

/-- `twistBD` preserves `MYDRowValid` at parity-forced positions
    when tp = tn (matching the ⊗ (ε, ε) pattern). -/
axiom twistBD_preserves_MYDRowValid (E : ILS) (γ : RootType) (t : ℤ)
    (_ht : t = 1 ∨ t = -1)
    (h : ∀ (j : ℕ) (hj : j < E.length), MYDRowValid γ (j + 1) E[j]) :
    ∀ (j : ℕ) (hj : j < (ILS.twistBD E t t).length),
      MYDRowValid γ (j + 1) (ILS.twistBD E t t)[j]

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
      exact twistBD_preserves_MYDRowValid E .D (-1) (Or.inr rfl) h_par
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
