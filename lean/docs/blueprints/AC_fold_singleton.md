# AC_fold_singleton: L_τ is a single MYD with multiplicity 1

**Status**: planning (2026-04-19), milestone M1.2 of MYD_type_and_bijection

**Claim**: For every `τ ∈ PBPSet γ μP μQ` (validly descending to base), the
fold `AC.fold γ (descentChain τ)` is a single-term list of the form
`[(1, L_τ)]` for a unique `L_τ : ILS`.

## Structure of the proof

### Base case

`AC.base γ` is by definition a single-term list with multiplicity 1:

```lean
def AC.base (γ : RootType) : ACResult :=
  match γ with
  | .Bplus  => [(1, [(1, 0)])]
  | .Bminus => [(1, [(0, -1)])]
  | .C | .D | .M => [(1, [])]
```

So `AC.base γ = [(1, E_γ)]` where `E_γ = [(1,0)] / [(0,-1)] / []`
depending on γ. This is provable by `cases γ`.

### Inductive step (single step)

**Claim**: if `source = [(1, E)]` (single-term, mult 1) and the theta-lift
inputs are valid (i.e. `ILS.thetaLift (possibly_twisted E) γ p q = [E']`
for a unique `E'`), then:

```
AC.step source γ p q ε_τ ε_wp = [(1, post_twisted E')]
```

for some `post_twisted E'`.

**Proof sketch** (unfolding `AC.step`):

1. `twisted := if γ ∈ {C, M} ∧ ε_wp = 1 then source.twistBD (-1) (-1) else source`.

   `twistBD` on `ACResult = List (ℤ × ILS)` maps each `(c, E) ↦ (c, twistBD c E)` —
   it preserves list length and multiplicities. So `twisted = [(1, E*)]`
   for some `E*`.

2. `lifted := twisted.thetaLift γ p q`.

   `ACResult.thetaLift = flatMap (fun (c, E) => (ILS.thetaLift E γ p q).map ((c, ·)))`.

   - If `twisted = [(1, E*)]` and `ILS.thetaLift E* γ p q = [E']` (singleton),
     then `lifted = [(1, E')]`.
   - If the thetaLift returns `[]`, the result is `[]` (failure — not our
     case by hypothesis).
   - If the thetaLift returns 2+ elements (doesn't happen for ILS.thetaLift_*
     per the definitions, which all produce at most one element).

3. `post_twist := if γ ∈ {B⁺, B⁻, D} ∧ ε_τ = 1 then lifted.twistBD 1 (-1) else lifted`.

   Same argument as (1): twistBD on `[(1, E')]` gives `[(1, twistBD 1 (-1) E')]`.

Output: `[(1, final_E)]` for a unique final_E.

### Inductive case (full chain)

Induction on `chain : List ACStepData`:

- `chain = []`: `AC.fold γ [] = AC.base γ = [(1, E_γ)]`. Done.
- `chain = d :: rest`: wait — `AC.fold` uses `foldl`, so the recursion is
  `fold γ (d :: rest) = fold' (step (base γ) d) rest`.

  Actually `foldl` accumulates from left, but the chain order is
  "inner-first". The user's note is: **induction on length of dp** (dual
  partition), where the descent chain length equals the number of distinct
  column-lengths in dp.

  In Lean, induction on `chain.length` works just as well. Equivalently,
  induct on the list structure via `List.rec`.

  Step: assume `AC.fold γ chain = [(1, E)]` for some E (via IH). Then
  `AC.fold γ (chain ++ [d]) = AC.step [(1, E)] d.γ d.p d.q d.ε_τ d.ε_wp`.
  By the single-step inductive claim above, this is `[(1, E')]` for E'.

### Validity hypothesis

The single-step claim has a sign-bound hypothesis that must propagate
along the chain. The chain from `descentChain τ` is known (from Section
10's counting proofs) to satisfy these bounds at every step. Rather
than prove the propagation from scratch, we can:

**Option A**: state `AC_fold_singleton` with a hypothesis
`∀ step ∈ chain, thetaLift_singleton_at step`, then separately prove
this hypothesis holds for descent-chain instances.

**Option B**: express `AC_fold_singleton` purely at the chain level and
accept `noncomputable` / existence claims; then instantiate for descent
chains where the validity is established via existing sign-bound theorems.

## Lean skeleton

```lean
namespace BMSZ

/-- A chain of AC step data is "valid" for base type γ if each step's
    ILS.thetaLift input produces a non-empty output (singleton). -/
def AC.ChainValid (baseType : RootType) : List ACStepData → Prop
  | [] => True
  | d :: rest => ... -- complex, needs intermediate accumulator

/-- **M1.2 main lemma**: valid chains produce single-term AC.fold output. -/
theorem AC.fold_singleton (baseType : RootType) (chain : List ACStepData)
    (h_valid : AC.ChainValid baseType chain) :
    ∃ E : ILS, AC.fold baseType chain = [(1, E)]
```

## Implementation plan

1. Prove `AC_base_singleton` (trivial, by `cases γ`).
2. Prove `AC_step_preserves_singleton` (single-step): if input is `[(1, E)]`
   and `ILS.thetaLift produces a singleton`, output is `[(1, E')]`.
3. Define `AC.ChainValid` recursively, threading the current ILS through.
4. Prove `AC_fold_singleton` by induction on `chain`.
5. (Separately, later): prove descent-chain `τ ↦ descentChain τ` yields
   a `ChainValid` chain — this uses the existing sign-bound theorems
   from MYD.lean around line 860–940.

Start with steps 1 and 2; they don't depend on the chain validity
definition and can be coded incrementally.
