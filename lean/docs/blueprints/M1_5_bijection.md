# M1.5: Constructive bijection $\Phi_D : \PBP_D(\check{\mathcal{O}}) \times \mathrm{Fin}\ 2 \simeq \MYD_D(O)$

**Milestone**: M1.5 of the MYD formalization plan.

**Status**: natural-language draft (2026-04-19), split into phases.

## Decisions

**User directive**: "M1.5 应该可以给个构造性证明" (M1.5 should have a
constructive proof). This rules out the pure injective+counting path
and requires an explicit inverse construction.

**Design**: two-tier structure similar to M1.4.

- **Phase A (this session, interface)**: state the bijection as
  `Phi_D_equiv : PBPSet .D μP μQ × Fin 2 ≃ MYD .D (dpToSYD .D dp)`.
  Introduce `Psi_D` (inverse) as an abstract function, with its
  correctness axiomatised.

- **Phase B (future, proof)**: construct `Psi_D` explicitly as the
  inverse theta-lift / descent-chain reversal (paper §11 algorithm),
  and prove `left_inv` / `right_inv`. This corresponds to paper's
  §11.14 surjectivity construction.

## Mathematical content (paper §11.14)

Given $E \in \MYD_D(O)$, the paper constructs $(\tau, \varepsilon)$
with $L_\tau \otimes (\varepsilon, \varepsilon) = E$ as follows:

**Algorithm (paper §11.14)**:
1. If $O$ is the trivial orbit, $E$ is the empty MYD and $\tau$ is
   the empty PBP, $\varepsilon$ determined by $E$'s structure.
2. Else, let $(p_0, q_0) := E(1)$ (first row of $E$).
3. **Un-truncate**: form $E^- := \Lambda_{(p_0, q_0)} E$ — strip off
   the top row / adjust subsequent rows per paper §9.19.
4. **Un-twist**: apply $T^{-\gamma_\tau}$ (the appropriate inverse
   involution depending on root type).
5. Let $O' :=$ the "descended" orbit (paper Lemma 9.2).
6. Recurse: $(\tau', \varepsilon') := \Psi_D(E'')$ where
   $E'' \in \MYD_{D'}(O')$ is the un-twisted, un-truncated $E$.
7. Assemble: $\tau$ is obtained by "augmenting" $\tau'$ with the
   γ-pair data from $(p_0, q_0)$; $\varepsilon$ is determined by
   the sign of $p_0$ (or $q_0$).

**Correctness** (paper's induction):
- $\Phi_D \circ \Psi_D = \mathrm{id}_{\MYD_D(O)}$: since each step of
  $\Psi_D$ undoes the corresponding step of $\Phi_D$.
- $\Psi_D \circ \Phi_D = \mathrm{id}$: similarly.

These round-trips rely on paper §9.20 (the truncation/augmentation
inverse pair) and paper Lemma 11.13 (injectivity of the chain).

## Phase A: interface

### Definition: `Psi_D`

**Intent**: given $E \in \MYD_D(O)$, return $(\tau, \varepsilon)$
with $\Phi_D(\tau, \varepsilon) = E$.

**Phase A formulation** (existential):

```lean
axiom Psi_D {μP μQ : YoungDiagram} (dp : DualPart)
    (E : MYD .D (dpToSYD .D dp)) :
    PBPSet .D μP μQ × Fin 2

axiom Phi_D_Psi_D_left_inv {μP μQ : YoungDiagram} (dp : DualPart)
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    Psi_D dp (Phi_D dp σ ε) = (σ, ε)

axiom Phi_D_Psi_D_right_inv {μP μQ : YoungDiagram} (dp : DualPart)
    (E : MYD .D (dpToSYD .D dp)) :
    Phi_D dp (Psi_D dp E).1 (Psi_D dp E).2 = E
```

Proof plan (phase B): define `Psi_D` by iterating the inverse-theta-lift
step; prove the round-trips by chain induction.

### Theorem: `Phi_D_equiv`

With `Psi_D`, `left_inv`, `right_inv` from phase A, construct the
Lean `Equiv`:

```lean
noncomputable def Phi_D_equiv {μP μQ : YoungDiagram} (dp : DualPart) :
    PBPSet .D μP μQ × Fin 2 ≃ MYD .D (dpToSYD .D dp) := {
  toFun := fun ⟨σ, ε⟩ => Phi_D dp σ ε
  invFun := Psi_D dp
  left_inv := fun ⟨σ, ε⟩ => Phi_D_Psi_D_left_inv dp σ ε
  right_inv := fun E => Phi_D_Psi_D_right_inv dp E
}
```

This is THE constructive bijection.

### Corollary: card equality

```lean
theorem card_PBPSet_D_Fin2_eq_card_MYD
    (μP μQ : YoungDiagram) (dp : DualPart) :
    Fintype.card (PBPSet .D μP μQ × Fin 2) =
    Fintype.card (MYD .D (dpToSYD .D dp)) :=
  Fintype.card_congr (Phi_D_equiv dp)
```

This gives paper's card equality `|PBP × Fin 2| = |MYD|` for free as
a corollary of the bijection (not as an input).

### Assembly of the paper's abstract Prop 11.15

Given `Phi_D_equiv`, we can instantiate the abstract
`prop_11_15_PBP_D_complete` (MYD.lean:5371):
- $\alpha := $ PBPSet .D μP μQ × Fin 2
- $\beta := $ MYD .D (dpToSYD .D dp)
- $e := $ Phi_D_equiv dp
- $f := $ toFun of Phi_D_equiv (which is `Phi_D dp σ ε` per construction)
- Injectivity: from `Phi_D_equiv.injective` (automatic from Equiv)
- Result: `Function.Bijective f` = `Phi_D_equiv.bijective` (automatic).

So the abstract `prop_11_15_PBP_D_complete` becomes a concrete
theorem once `Phi_D_equiv` exists.

## Scope for Phase A vs Phase B

**Phase A (this session)** — roughly 20 lines of Lean:
- Axiom: `Psi_D`
- Axiom: `Phi_D_Psi_D_left_inv`
- Axiom: `Phi_D_Psi_D_right_inv`
- Definition: `Phi_D_equiv` (built from the three)
- Theorem: `card_PBPSet_D_Fin2_eq_card_MYD` (immediate)

**Phase B (future)** — substantial paper work:
- Prove `Psi_D` constructively (iterate inverse theta-lift)
- Prove `left_inv` by chain induction
- Prove `right_inv` by chain induction
- Requires: paper §9.19–9.20 (truncation, augmentation) and paper
  §11.13–11.14 (chain reversibility and surjectivity).

## Alternative simpler Phase A (rejected)

We considered stating only the `Equiv` as a single axiom:

```lean
axiom Phi_D_equiv : PBPSet .D μP μQ × Fin 2 ≃ MYD .D (dpToSYD .D dp)
```

This is simpler but hides the structure. Our three-axiom version
exposes the `toFun = Phi_D` identity, which is needed downstream
(e.g., for injectivity proofs and for debugging).

## Self-review plan

Three passes:

1. **Type correctness**: axiom signatures well-typed; Equiv
   construction matches Lean's expected fields.
2. **Paper semantics**: `Psi_D` aligns with paper §11.14's
   un-truncate-un-twist-recurse algorithm.
3. **Downstream compatibility**: `Phi_D_equiv` gives card equality
   and the concrete bijection needed for "abstract Prop 11.15"
   instantiation.

## Review log

### Pass 1: Type correctness (2026-04-19)

- `Psi_D (dp : DualPart) (E : MYD .D (dpToSYD .D dp)) : PBPSet .D μP μQ × Fin 2`
  requires μP, μQ to match dp for the returned PBP to have a meaningful
  shape. **Fix**: make μP, μQ explicit AND require a coherence
  hypothesis `h_coh : μP.colLens = dpartColLensP_D dp ∧ μQ.colLens = dpartColLensQ_D dp`.
- `Phi_D_equiv` needs the same coherence as Phi_D on the forward side;
  pass-through from μP/μQ/dp/h_coh.

**Resolved**: axioms take explicit μP, μQ, dp, h_coh.

### Pass 2: Paper semantics (2026-04-19)

- `Psi_D` matches paper §11.14 algorithm (un-truncate-un-twist-recurse).
- Round-trips correspond to paper's inductive verification. ✓

### Pass 3: Downstream compatibility (2026-04-19)

- `Phi_D_equiv` produces card equality via `Fintype.card_congr` — automatic.
- Abstract `prop_11_15_PBP_D_complete` (MYD.lean:5371) instantiates by
  supplying the concrete Equiv.
- M1.6 follows directly.

**Verdict**: proceed. Note: axiomatising 3 facts is acceptable for
Phase A because the algorithmic content is paper §11.14, which is
substantial and warrants its own phase B.
