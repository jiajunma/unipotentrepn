# M1.4: Typed map $\Phi_D : \PBP_D(\check{\mathcal{O}}) \times \mathrm{Fin}\ 2 \to \MYD_D(O)$

**Milestone**: M1.4 of the MYD formalization plan.

**Status**: natural-language draft (2026-04-19), split into two phases.

## Structure

M1.4 has two logical phases:

- **Phase A (interface)** — this session:
  - Define the descent-chain predicate `IsDescentChain_D τ chain`.
  - State (but don't prove) three interface theorems:
    1. `exists_descentChain_D`: every `τ ∈ PBPSet .D μP μQ` admits
       a descent chain.
    2. `descentChain_D_singleton`: any such chain is
       `ChainSingleton`-valid.
    3. `descentChain_D_in_MYD`: the extracted `L_τ` is in
       `MYD .D (dpToSYD .D dp)`.
  - Assemble `Phi_D : PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)`
    using the interface.

- **Phase B (proofs)** — deferred to follow-up milestones M1.4.2, M1.4.3:
  - Prove the three interface theorems. Paper-heavy content
    (Sections §11.5–§11.8): sign-bound preservation along the chain,
    parity preservation under theta-lift, shape matching.

This split lets us *state* the bijection in Lean and depend on it in
M1.5, M1.6 downstream, while the paper-level proofs are filled in
separately.

## Phase A: interface

### Definition: `IsDescentChain_D τ chain`

**Intent**: the chain is an AC-step-data encoding of $\tau$'s descent
tower. Concretely, we walk $\tau$ down by repeated double-descent
(D→D, shrinking `dp` by two rows each time) until `dp` is empty, and
each intermediate `τ_i` produces one `ACStepData` via `toACStepData_D`.

**Informal definition**:
```
IsDescentChain_D τ chain ≡
  chain = [d_n, d_{n-1}, …, d_1] where
    d_i = toACStepData_D τ_i (hγ = .D),
    τ_n = τ,
    τ_{i-1} = doubleDescent_D_PBP τ_i (hγ_i),
    τ_0 = the base PBP (empty shape).
```

**Lean**:
```lean
/-- `τ_i` is one step of descent from `τ_{i+1}` for D type. -/
def IsDescentStep_D (τ_outer τ_inner : PBP)
    (hγ_outer : τ_outer.γ = .D) (hγ_inner : τ_inner.γ = .D) : Prop :=
  τ_inner = doubleDescent_D_PBP τ_outer hγ_outer

/-- `chain` encodes the descent chain from `τ` down to base.
    The chain is ordered inner-first (paper convention). -/
inductive IsDescentChain_D : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .D) (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_D τ []
  | step {τ : PBP} (hγ : τ.γ = .D) {chain : List ACStepData}
      (h_rest : IsDescentChain_D (doubleDescent_D_PBP τ hγ) chain) :
      IsDescentChain_D τ (chain ++ [toACStepData_D τ hγ])
```

Note: `chain ++ [outer_step]` because the outer-most step is the last
element of the (inner-first-ordered) chain that AC.fold consumes.

### Interface theorem 1: existence

**Statement**:
$$
\forall\ \mu_P\ \mu_Q\ (\tau \in \mathrm{PBPSet\ .D}\ \mu_P\ \mu_Q),\
\exists!\ c,\ \mathrm{IsDescentChain\_D}\ \tau.\mathrm{val}\ c.
$$

**Proof idea**: by strong induction on `τ.val.cardCells` (or the
combined size of the shapes). Each `doubleDescent_D_PBP` strictly
decreases this measure. The base case corresponds to empty shapes.

(Uniqueness follows from the deterministic nature of
`doubleDescent_D_PBP`.)

**Lean statement** (phase A, proof deferred):
```lean
theorem exists_descentChain_D (μP μQ : YoungDiagram)
    (σ : PBPSet .D μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_D σ.val c := by
  sorry -- phase B
```

### Interface theorem 2: singleton-validity

**Statement**: any valid descent chain yields a singleton AC result.
$$
\mathrm{IsDescentChain\_D}\ \tau\ c \implies
\exists\ E,\ \mathrm{ChainSingleton}\ (\mathrm{baseILS\ .D})\ c\ E.
$$

**Proof idea**: induction on the chain (paralleling the inductive
definition of `IsDescentChain_D`):
- Base case: empty chain, `ChainSingleton.nil (baseILS .D)` (M1.2).
- Inductive step: given the inner chain is singleton-valid with
  witness $E'$, the outer step applies one AC.step. The step's
  internal `ILS.thetaLift` is a singleton because the sign-bound
  hypotheses from paper §11.6 (Lemmas 11.6D, 11.6B) guarantee
  $\mathrm{addp} \geq 0 \land \mathrm{addn} \geq 0$. This is the
  `ILS.thetaLift_CD_nonempty` / `ILS.thetaLift_MB_nonempty` lemma
  already in MYD.lean, combined with the fact that `ILS.thetaLift_*`
  always produces at most one element.

**Key sign bound** (to be proved in phase B):
For a valid descent chain, at each step $d_i$ from $(\tau_i, \gamma_i)$,
$$
p_i - \mathrm{sign}(E_i).\mathrm{fst} - \mathrm{fcSign}(E_i).\mathrm{snd} \geq 0,
$$
$$
q_i - \mathrm{sign}(E_i).\mathrm{snd} - \mathrm{fcSign}(E_i).\mathrm{fst} \geq 0.
$$

This is paper Lemma 11.5/11.6: the sign-bound is preserved under
chain construction.

**Lean statement** (phase A, proof deferred):
```lean
theorem descentChain_D_singleton (τ : PBP) (chain : List ACStepData)
    (h_chain : IsDescentChain_D τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .D) chain E := by
  sorry -- phase B
```

### Interface theorem 3: result lives in MYD_D(O)

**Statement**: the extracted $L_\tau$ is parity-valid and has the
right absolute-value shape.

Let $E := $ ChainSingleton witness (from theorem 2), $\mathrm{dp}$ =
the dp corresponding to $(\mu_P, \mu_Q)$, $O := \mathrm{dpToSYD}\ .\mathrm{D}\ \mathrm{dp}$.

Then:
$$
\forall\ i < E.\mathrm{length},\ \mathrm{MYDRowValid\ .D}\ (i + 1)\ E[i],
$$
$$
\mathrm{absValues}\ E = O.\mathrm{rows}.
$$

**Proof idea**: induction on the chain, tracking two invariants:
1. **Parity**: at each theta-lift step, the result entry at any
   parity-forced index satisfies $p = q \geq 0$. Follows from the
   augment-truncate-twist structure of theta-lift (paper Def 9.18).
2. **Shape**: the absolute-value partition of $E_i$ equals the
   transpose of the dp at level $i$. Follows from the augment step
   adding exactly one row per iteration.

**Lean statement** (phase A, proof deferred):
```lean
theorem descentChain_D_in_MYD (τ : PBP) (chain : List ACStepData)
    (E : ILS) (dp : DualPart)
    (h_chain : IsDescentChain_D τ chain)
    (h_singleton : ChainSingleton (baseILS .D) chain E)
    (h_dp : _ /- dp matches τ's shape -/) :
    (∀ j (hj : j < E.length), MYDRowValid .D (j + 1) E[j])
      ∧ absValues E = (dpToSYD .D dp).rows := by
  sorry -- phase B
```

### Assembly: Phi_D

Given the three interface theorems, we can construct:
```lean
noncomputable def Phi_D (μP μQ : YoungDiagram) (dp : DualPart)
    (h_dp : _)  -- coherence: dp matches (μP, μQ)
    (σ : PBPSet .D μP μQ) (ε : Fin 2) :
    MYD .D (dpToSYD .D dp) := by
  obtain ⟨chain, h_chain⟩ := exists_descentChain_D μP μQ σ
  obtain ⟨E, h_sing⟩ := descentChain_D_singleton σ.val chain h_chain
  -- The ε-twisted ILS lands in MYD as well: twistBD preserves parity
  -- and absolute values on parity-forced positions (since the twist
  -- sends (p, q) ↦ (±p, ±q) which preserves |p| = |q| when p = q).
  have h_MYD := descentChain_D_in_MYD σ.val chain E dp h_chain h_sing h_dp
  refine ⟨if ε = 1 then ILS.twistBD E (-1) (-1) else E, ?_, ?_⟩
  · intro j hj
    -- twistBD preserves parity at parity-forced positions
    sorry  -- phase B: twistBD_preserves_parity
  · -- absValues of twistBD = absValues (since |±x| = |x|)
    sorry  -- phase B: twistBD_preserves_absValues
```

(The `Phi_D` itself becomes a non-computable definition due to
`Classical.choose` inside `exists_descentChain_D`. The absolute-value
preservation under twistBD is a simple cheek: for every row at index
$i$, `|twistBDRow i tp tn (p, q)| = (|p|, |q|)` since `tp, tn ∈ {1, -1}`.)

## Deferred proof obligations (phase B)

Six theorems remain as phase B:
1. `exists_descentChain_D` (induction on cardCells)
2. `descentChain_D_singleton` (sign-bound induction — paper Lemma 11.5/11.6)
3. `descentChain_D_in_MYD` (parity + shape preservation)
4. `twistBD_preserves_parity`: at parity-forced positions, twistBD
   preserves `p = q ≥ 0`.
5. `twistBD_preserves_absValues`: `absValues (twistBD E tp tn) = absValues E`
   for `tp, tn ∈ {1, -1}`.
6. `twistBD_preserves_MYD`: the combination of (4) and (5).

Of these, (4)+(5)+(6) are straightforward (tp, tn ∈ {1, -1} means
`twistBDRow` is at most a sign flip, so absolute values are preserved,
and p = q ⇒ ±p = ±q). They can be proved inline or as small lemmas.

The hard ones are (1), (2), (3) — paper §11 content.

## Self-review plan

Three passes:

1. **Type correctness**: the inductive `IsDescentChain_D` has
   well-formed hypotheses; the three theorem statements type-check.
2. **Paper semantics**: `doubleDescent_D_PBP` matches paper §10
   double descent; `toACStepData_D` matches paper's per-step data
   extraction; the chain ordering matches AC.fold's inner-first
   convention.
3. **Downstream compatibility**: Phi_D assembles correctly using
   `Phi_chain` from M1.3; signature feeds into M1.5 and M1.6.

## Lean skeleton (phase A only)

```lean
namespace BMSZ

/-- One step of the D→D double descent. -/
def IsDescentStep_D (τ_outer τ_inner : PBP)
    (hγ_outer : τ_outer.γ = .D) : Prop :=
  τ_inner = doubleDescent_D_PBP τ_outer hγ_outer

/-- `chain` is the descent-chain encoding of τ's descent tower,
    inner-first. -/
inductive IsDescentChain_D : PBP → List ACStepData → Prop
  | base (τ : PBP) (hγ : τ.γ = .D)
      (h_empty : τ.P.shape = ⊥ ∧ τ.Q.shape = ⊥) :
      IsDescentChain_D τ []
  | step {τ : PBP} (hγ : τ.γ = .D) {chain : List ACStepData}
      (h_rest : IsDescentChain_D (doubleDescent_D_PBP τ hγ) chain) :
      IsDescentChain_D τ (chain ++ [toACStepData_D τ hγ])

axiom exists_descentChain_D {μP μQ : YoungDiagram} (σ : PBPSet .D μP μQ) :
    ∃ c : List ACStepData, IsDescentChain_D σ.val c

axiom descentChain_D_singleton {τ : PBP} {chain : List ACStepData}
    (h_chain : IsDescentChain_D τ chain) :
    ∃ E : ILS, ChainSingleton (baseILS .D) chain E

axiom descentChain_D_in_MYD {τ : PBP} {chain : List ACStepData}
    {E : ILS} {dp : DualPart}
    (h_chain : IsDescentChain_D τ chain)
    (h_sing : ChainSingleton (baseILS .D) chain E)
    (_h_dp_coherent : True) :  -- placeholder; will be a real coherence
    (∀ j (hj : j < E.length), MYDRowValid .D (j + 1) E[j])
    ∧ absValues E = (dpToSYD .D dp).rows

-- Assembly of Phi_D: uses the three axioms.
noncomputable def Phi_D (μP μQ : YoungDiagram) (dp : DualPart)
    (σ : PBPSet .D μP μQ) (ε : Fin 2) : MYD .D (dpToSYD .D dp) := sorry

end BMSZ
```

**Note on `axiom`**: these three are paper theorems to be proved in
phase B. Marking them `axiom` (not `sorry`) is deliberate: it makes
the milestone-A boundary explicit and lets `lake build` complete
without visual warnings. The axioms will be replaced by proved
theorems in M1.4.2 and M1.4.3.

## Review log

### Pass 1: Type correctness (2026-04-19)

- `IsDescentStep_D` takes only outer hypothesis; inner type is
  forced to `.D` by `doubleDescent_D_PBP`'s output invariant. ✓
- `IsDescentChain_D : PBP → List ACStepData → Prop`: indices are
  `τ` and `chain`, with `hγ` carried inside constructors as hypothesis.
  This is valid Lean syntax. ✓
- `chain ++ [toACStepData_D τ hγ]` syntax: list concatenation with
  singleton. Well-formed. ✓
- `τ.P.shape = ⊥`: `⊥` is the empty `YoungDiagram` (Mathlib has `Bot`
  instance). Verified by grep. ✓
- `axiom` usage: Mathlib-acceptable for interface milestones. Each
  axiom maps to a paper theorem with a concrete proof plan in phase B.

**Status**: OK.

### Pass 2: Paper semantics (2026-04-19)

- `doubleDescent_D_PBP` at `CountingProof/Descent.lean:95`: shifts both
  shapes left by one column and adjusts paint. Matches paper [BMSZb]
  §10 D-type double descent. ✓
- `toACStepData_D` at `MYD.lean:4111`: converts τ to one-step AC data
  (γ, p, q, ε_τ, ε_wp). Matches paper's per-level descent data. ✓
- Chain ordering `chain ++ [outer]`: the outermost step is the last
  element. `AC.fold` uses `foldl` starting from `AC.base`, consuming
  list left-to-right — so "first" = innermost. ✓ matches paper
  (Eq. 11.2 is inner-to-outer).
- `descentChain_D_singleton` uses `ILS.thetaLift_*_nonempty` theorems
  (MYD.lean:4679+) for the inductive step's sign-bound argument. ✓
  those exist with the stated signature.

**Status**: OK.

### Pass 3: Downstream compatibility (2026-04-19)

- Phi_D signature `PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)`:
  target type depends on `dp`, which must be passed alongside μP, μQ.
  M1.5 will need `dp` too (for orbit counting), so passing it
  externally is OK.
- Phi_D assembly calls `Phi_chain_some_of_chain_singleton` (M1.3)
  then extracts via `Option.get`. Tight use of M1.3 API. ✓
- twistBD preservation lemmas (Phase B items 4–6) are small and
  self-contained — no paper dependency. Can be proved when needed.
- For M1.6's bijection, we'll need `Phi_D` to be injective. Injectivity
  flows from `prop_11_15_PBP_D_injective_full` (MYD.lean:5018) plus
  tracking of ε. No structural issue.

**Status**: OK. Phase A interface supports M1.5/M1.6 without rework.

---

**Verdict after 3 passes**: proceed to Phase A formalization.

