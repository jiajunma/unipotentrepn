# M1.3: Concrete map $\Phi_D : \PBP_D(\check{\mathcal{O}}) \times \mathrm{Fin}\ 2 \to \mathrm{ILS}$

**Milestone**: M1.3 of the MYD formalization plan
(`MYD_type_and_bijection.md`).

**Status**: natural-language draft (2026-04-19), ready for self-review.

**Context**: M1.2 established that `AC.fold γ chain` produces
`[(1, E_final)]` for any chain satisfying `ChainSingleton (baseILS γ)`.
M1.3 turns this into a concrete $\tau \mapsto L_\tau$ map at the PBP
level, parametrised by $\varepsilon \in \mathrm{Fin}\ 2$.

This file does NOT prove:
- that `descentChain τ` is always ChainSingleton-valid (defer to M1.4),
- that the result lands in $\MYD_D(O)$ (defer to M1.4),
- any bijection statement (defer to M1.6).

It only defines the plumbing: `extractILS` and `Phi_D_raw`.

## Scope

### In scope (M1.3)

1. **Singleton projection** `extractILS : ACResult → Option ILS`:
   returns the unique ILS when the AC result has exactly one term with
   multiplicity 1; returns `none` otherwise.

2. **Raw map** `Phi_D_raw : PBP → Fin 2 → Option ILS`:
   applies `extractILS` to the AC chain output, then applies the
   $(\varepsilon, \varepsilon)$-twist when $\varepsilon = 1$.
   Returns `none` iff the chain is not singleton-valid.

3. **Relation to `AC_fold_singleton`**: a compatibility lemma saying
   that when `ChainSingleton` holds, `Phi_D_raw` returns `some`.

### Out of scope (deferred)

- `descentChain_singleton`: a concrete proof that every
  `τ ∈ PBPSet .D μP μQ` yields a `ChainSingleton`-valid chain.
- `Phi_D : PBP_D(Ǒ) × Fin 2 → MYD_D(O)` (the typed version) — requires
  M1.4.
- Bijectivity — requires M1.5 + M1.6.

## Definitions

### 1. `extractILS`

**Intent**: collapse an `ACResult` to its unique `ILS` payload when
possible.

**Definition**:
$$
\mathrm{extractILS} : \mathrm{ACResult} \to \mathrm{Option}\ \mathrm{ILS}
$$
$$
\mathrm{extractILS}(\ell) =
\begin{cases}
\mathrm{some}\ E, & \text{if } \ell = [(1, E)] \text{ for some } E; \\
\mathrm{none}, & \text{otherwise.}
\end{cases}
$$

Note: we require the multiplicity to be exactly `1`, not any value.
This matches the `ChainSingleton` invariant from M1.2 and avoids
conflating signed AC results (where the multiplicity could be $\neq 1$
in principle, though in the intended application it never is).

**Key property** (M1.2 corollary):
$$
\mathrm{extractILS}([(1, E)]) = \mathrm{some}\ E.
$$

Follows by definitional unfolding plus the case split on the input list.

### 2. The chain parameter

Existing code has **per-step** `toACStepData_D/Bplus/.../C/M`
(`MYD.lean:4111+`), which converts a single PBP to a single
`ACStepData`. The **iterated** chain
`PBP → List ACStepData` (full descent until base) is **not** yet
defined in the codebase and is **M1.4's responsibility**, not M1.3's.

For M1.3 we therefore take `chain : List ACStepData` as a **direct
parameter**, avoiding the need to define `descentChain` here.

### 3. `Phi_D_raw`

**Intent**: given a chain of AC step data and $\varepsilon$, produce
either $L \otimes (\varepsilon, \varepsilon)$ as an ILS, or `none` if
the chain doesn't close to a singleton.

**Definition** (at the chain level, base type $\gamma$ fixed):
$$
\Phi_\gamma^{\mathrm{chain}}(c, \varepsilon) :=
  \mathrm{extractILS}(\mathrm{AC.fold}\ \gamma\ c)
  \ \mathrm{map}_\mathrm{Option}\
  (\text{apply } \otimes (\varepsilon, \varepsilon)\text{ if } \varepsilon = 1).
$$

In Lean syntax:
```lean
def Phi_chain (baseType : RootType) (chain : List ACStepData)
    (ε : Fin 2) : Option ILS :=
  (extractILS (AC.fold baseType chain)).map (fun E =>
    if ε = 1 then ILS.twistBD E (-1) (-1) else E)
```

When `M1.4` supplies a function `descentChain_D : PBP → List ACStepData`,
we can compose:
```lean
def Phi_D_raw (τ : PBP) (ε : Fin 2) : Option ILS :=
  Phi_chain .D (descentChain_D τ) ε
```
This PBP-level definition is a *one-liner* wrapper and lives in M1.4,
not M1.3.

### 4. Compatibility with `ChainSingleton`

**Lemma (Phi_chain_some_of_chain_singleton)**:
If `ChainSingleton (baseILS γ) chain E_final`, then
$$
\Phi_\gamma^{\mathrm{chain}}(c, \varepsilon) =
\mathrm{some}\left(
  \begin{cases}
    \mathrm{twistBD}\ E_\text{final}\ (-1)\ (-1), & \varepsilon = 1 \\
    E_\text{final}, & \varepsilon = 0
  \end{cases}
\right).
$$

**Proof**: by M1.2 (`AC_fold_singleton`), under the hypothesis we have
$\mathrm{AC.fold}\ \gamma\ c = [(1, E_\text{final})]$.
Then `extractILS [(1, E_final)] = some E_final` by definitional
unfolding. Apply `Option.map` and the case split on $\varepsilon$.
$\square$

## Why `Option` and not a total map?

Two cleaner designs were considered and rejected:

**Alternative A (Classical)**: define
`Phi_D (τ : PBP) (ε : Fin 2) : ILS` via
`Classical.choose (some_chain_singleton_hypothesis)`. This gives a
total map but (i) is non-computable even in principle, (ii) needs the
chain-singleton hypothesis baked into the caller's context which is
awkward before M1.4 is done.

**Alternative B (subtype)**: define
`Phi_D : {τ : PBP // IsValidDescent τ} × Fin 2 → ILS`. This forces
the caller to pre-check validity at the type level. Cleaner for the
final bijection but requires `IsValidDescent` as a primitive predicate,
which we haven't defined yet.

**Chosen (Option)**: `Phi_D_raw : PBP → Fin 2 → Option ILS` is
computable, and the transition to a total map on `PBPSet .D μP μQ`
happens in M1.4 once we know every such PBP has a valid descent chain.

## Why `ε ∈ Fin 2` and the twist direction

Paper Prop 11.15:
$$
(\tau, \varepsilon) \mapsto L_\tau \otimes (\varepsilon, \varepsilon).
$$

Here $\otimes (\varepsilon, \varepsilon)$ means "tensor with the sign
twist $(-1)^\varepsilon$ in both components". On ILS / ACResult this is
realised by `ILS.twistBD (-1) (-1)` applied once when $\varepsilon = 1$,
and the identity when $\varepsilon = 0$.

Note: `twistBD (-1) (-1)` is involutive, so the choice of "direction"
is consistent whichever way one reads it.

## Self-review plan

Three self-review passes (per user directive):

1. **Type correctness**: every definition has a well-typed Lean
   signature, inputs and outputs match, the Option threading is
   coherent.

2. **Semantic match to paper**: `extractILS` matches "extract the unique
   MYD from $\mathcal{L}_\tau$"; `Phi_D_raw` matches paper's map
   $(\tau, \varepsilon) \mapsto \mathcal{L}_\tau \otimes
   (\varepsilon, \varepsilon)$.

3. **Downstream compatibility**: the definitions cleanly feed into
   M1.4's statement "$\Phi_D(\tau, \varepsilon) \in \MYD_D(O)$" without
   rework.

(Review notes appended at the end of this document after each pass.)

## Lean skeleton (after review passes)

```lean
namespace BMSZ

/-- Extract the unique ILS payload from an ACResult of the form
    `[(1, E)]`. Returns `none` otherwise. -/
def extractILS : ACResult → Option ILS
  | [(1, E)] => some E
  | _ => none

theorem extractILS_singleton (E : ILS) :
    extractILS [(1, E)] = some E := rfl

/-- Chain-level raw map: `AC.fold baseType chain` projected via
    extractILS, then ε-twisted. Total; returns `none` iff the chain
    fails to produce a singleton ACResult. -/
def Phi_chain (baseType : RootType) (chain : List ACStepData)
    (ε : Fin 2) : Option ILS :=
  (extractILS (AC.fold baseType chain)).map (fun E =>
    if ε = 1 then ILS.twistBD E (-1) (-1) else E)

theorem Phi_chain_some_of_chain_singleton
    (baseType : RootType) (chain : List ACStepData) (ε : Fin 2)
    (E_final : ILS)
    (h : ChainSingleton (baseILS baseType) chain E_final) :
    Phi_chain baseType chain ε =
      some (if ε = 1 then ILS.twistBD E_final (-1) (-1) else E_final) := by
  unfold Phi_chain
  rw [AC_fold_singleton baseType chain E_final h]
  rfl

end BMSZ
```

## Review log

### Pass 1: Type correctness (2026-04-19)

**Findings**:
- `descentChain : PBP → List ACStepData` does not exist in the
  codebase. Only per-step `toACStepData_D/...` at `MYD.lean:4111+`.
- **Fix applied**: switched M1.3 signature to take `chain` directly as
  a parameter (`Phi_chain (baseType) (chain) (ε)`). The PBP-level
  `Phi_D_raw τ ε = Phi_chain .D (descentChain_D τ) ε` is deferred to
  M1.4, where `descentChain_D` will be defined.
- `extractILS` pattern `[(1, E)]`: `1 : ℤ` in `List (ℤ × ILS) = ACResult`
  is the right literal. Pattern-match works in Lean 4.
- `ILS.twistBD : ILS → ℤ → ℤ → ILS` exists (MYD.lean, checked via
  earlier work). Signature matches.
- `AC.fold baseType chain : ACResult` matches. `baseType` is `RootType`.
- Lemma proof: `rw [AC_fold_singleton …]` then `rfl`. The `rfl` relies
  on `(extractILS [(1, E_final)]).map (·) = some (f E_final)`
  reducing definitionally. Pattern-match on `[(1, E)]` is `rfl`-good
  (not `by rfl`), so this should work.

**Status**: type-correctness OK after the chain-parameter fix.

### Pass 2: Semantic match to paper (2026-04-19)

**ε-twist convention check** (paper Prop 11.15):
- Paper: $(\tau, \varepsilon) \mapsto L_\tau \otimes (\varepsilon, \varepsilon)$.
- Paper Def 9.15: $\otimes (\varepsilon^+, \varepsilon^-)$ twists with
  signs $(-1)^{\varepsilon^+}, (-1)^{\varepsilon^-}$. So
  $\otimes (0, 0) = \mathrm{id}$, $\otimes (1, 1) = $ twist with
  $(-1, -1)$ on both components.
- Existing code (e.g. `prop_11_15_complete` at MYD.lean:3912):
  `if ε = 1 then L.twistBD (-1) (-1) else L`. ✓ matches my NL proof.

**`L_τ` meaning**:
- Paper: $L_\tau := \mathrm{AC.fold}\ \gamma\ (\mathrm{descent\ chain}\ \tau)$,
  the unique MYD of the orbit for τ.
- Lean: `AC.fold γ chain : ACResult`, which under `ChainSingleton`
  equals `[(1, L_τ)]` (per M1.2).

**`extractILS` semantics**:
- Paper: "take the unique MYD from $L_\tau$" (Multiplicity-free claim
  of paper §11.7).
- Lean: `extractILS [(1, E)] = some E`. Matches the "unique MYD" notion.

**`Phi_chain` semantics**: concatenation of paper's constructions:
1. Compute $L = \mathrm{AC.fold}$
2. Extract the unique ILS
3. Apply the outer $\varepsilon$-twist

All three steps align with paper text.

**Status**: semantic match confirmed.

### Pass 3: Downstream compatibility with M1.4 (2026-04-19)

**M1.4 requirements** (inferred from the milestone plan):
1. Define `descentChain_D : PBPSet .D μP μQ → List ACStepData`.
2. Prove `∀ σ : PBPSet .D μP μQ, ChainSingleton (baseILS .D) (descentChain_D σ) _`.
3. Prove the extracted `E` satisfies `MYDRowValid .D` at each row +
   `absValues E = (dpToSYD .D dp).rows`.
4. Package into
   `Phi_D : PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)`.

**How M1.3 supports this**:
- (1) is independent of M1.3.
- (2) feeds into `Phi_chain_some_of_chain_singleton` directly: from
  ChainSingleton + M1.2 we get `Phi_chain .D (descentChain_D σ) ε = some E`
  for the specific E.
- (3) operates on the `E` obtained via `Option.get` on (2). M1.3
  provides the `some E` without structure on E; M1.4 must prove the
  structure separately.
- (4) composes: `Phi_D (σ, ε) = ⟨(Phi_chain .D (descentChain_D σ) ε).get …, proof⟩`.

**Potential concern**: `Option.get` needs a proof of `≠ none`. My
`Phi_chain_some_of_chain_singleton` gives `= some …`, from which
`≠ none` is trivial. OK.

**Signature of M1.4's Phi_D**: `PBPSet .D μP μQ × Fin 2 → MYD .D (dpToSYD .D dp)`.
The `MYD .D (dpToSYD .D dp)` target depends on dp being recoverable
from (μP, μQ). In the existing codebase, dp is related to μP, μQ via
`dpartColLensP_D / dpartColLensQ_D` (see PBP.lean). M1.4 will need to
expose the dp parameter or derive it.

**Status**: downstream compatibility confirmed. M1.4 can be written
on top of M1.3 without rework.

---

**Verdict after 3 passes**: NL proof is sound. Proceed to Lean
formalization.

