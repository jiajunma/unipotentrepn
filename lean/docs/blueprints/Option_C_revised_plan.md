# Option C revised plan: orbit-descent via paper Lemma 9.2

**Date**: 2026-04-19 (late)
**Status**: NL plan (per workflow: NL proof first, blueprint, then Lean)

## Findings from paper

**Paper Lemma 9.2** (extracted from [BMSZ] arXiv:1712.05552):

Let O ∈ Nil(p_s). Define
$$
(p_0, q_0) := (p', q') - \Sign(\nabla_{\text{naive}}(O))
$$
where:
- $\nabla_{\text{naive}}(O)(i) := O(i+1)$ (index shift)
- $(p', q')$ is the group signature at descended level $s'$
- $\Sign$ is paper's Eq. 9.10

Then O is in the image of the moment map iff $p_0, q_0 \geq 0$.
When this holds, the descent $O' := \nabla^s_{s'}(O)$ is:
$$
O'(i) = \begin{cases}
O(2) + (p_0, q_0) & \text{if } i = 1 \\
O(i+1) & \text{if } i \geq 2
\end{cases}
$$

## Key implication

The orbit descent $\nabla^s_{s'}$ is NOT just "drop first row".
It's:
- Index-shift (O' takes rows from O starting at position 2)
- Plus adjustment on row 1: $O'(1) = O(2) + (p_0, q_0)$

For the AC chain's augment structure to match, we need:
$$
O(1) = ? \text{(some relation to } p_0, q_0, \text{ augmented by } \nabla^s_{s'}(O))
$$

## Why my previous framework (`dp.drop 2`) is wrong

My `dpToSYD .D (dp.drop 2)` computes the SYD of a DIFFERENT dp
(removing two rows from dp), not the SYD of the descended orbit
$\nabla^s_{s'}(O)$.

In particular:
- `dpToSYD .D dp` gives O with rows indexed by ROW LENGTH (transposed partition)
- `dpToSYD .D (dp.drop 2)` gives SYD of a SMALLER partition, NOT the paper-descended orbit

These are fundamentally different operations.

## Correct approach (NL plan)

**Step 1**: Define `SYD.naiveDescent : SYD γ → SYD γ`
implementing $\nabla_{\text{naive}}(O)(i) = O(i+1)$. This is just
`{rows := O.rows.tail}` with the validity proof. Trivial.

**Step 2**: Define `SYD.fullDescent : SYD γ → (p' q' : ℕ) → SYD γ`
implementing paper Lemma 9.2. This:
- Computes $(p_0, q_0) = (p', q') - \Sign(\nabla_{\text{naive}}(O))$
- Requires $p_0, q_0 \geq 0$ (else undefined / partial)
- Returns O' with $O'(1) = O(2) + (p_0, q_0)$ and $O'(i) = O(i+1)$ for $i \geq 2$

Since $p', q'$ come from group signature at level $s'$, they're
external parameters — for our AC chain, they come from the
descended PBP's signature.

**Step 3**: State the correct invariant for `descentChain_D_in_MYD`:
```
absValues E = O.rows where O is built level-by-level via fullDescent
```
NOT `O = dpToSYD .D dp`.

**Step 4**: Update `descentChain_D_in_MYD` to pass the orbit O
explicitly as a parameter, and prove the invariant inductively:
- Base case: empty chain, E = [], O = ⊥ (empty SYD). Trivial.
- Step case: E = (addp, addn) :: charTwistCM E_mid _, where by IH
  absValues E_mid = O_inner.rows. The outer orbit relates to inner
  via `O_outer = reverse_descent(O_inner, new_row)`.

## Alternative simpler route: drop shape, keep sign only

Given the structural complexity above, an alternative is:
- Define `MYD_sig γ sig` with only parity + sign (no shape)
- Prove `Phi_D: PBPSet γ × Fin 2 → MYD_sig γ sig` WITHOUT shape claim
- Show `Phi_D` is injective via existing `prop_11_15_PBP_D_injective_full`
- Show `Phi_D` is surjective via existing surjectivity toolchain
- Get bijection via `Equiv.ofBijective`

This gives the BIJECTION without needing the orbit-descent machinery.
The "shape" would be proved separately (and not needed for the card
equality, the main deliverable).

## Recommendation

**Option C'** (simpler alternative): drop orbit-indexed shape
constraint from MYD; use only parity + sign. Bijection via
injective + surjective composition. This avoids paper Lemma 9.2
implementation entirely.

**Cost**: the paper's MYD_γ(O) definition is STRICTLY stronger
than our MYD_sig (it pins down the exact shape). So Phi_D lands in
a superset, but the surjectivity condition becomes "every MYD with
matching sign + parity is in the image" — which requires more than
just counting.

Hmm, actually this doesn't quite work because |MYD_sig γ sig| ≥ 2 × |PBPSet|
generically (multiple sign configurations per shape).

**Option C''**: parameterise MYD by PBP's shape (μP, μQ) directly,
not by an abstract orbit:
```
MYD_by_shape γ μP μQ := { E : ILS | parity + absValues E corresponds to
                                    some orbit extractable from μP, μQ }
```

Then the shape constraint is on E's absValues, matching paper, without
defining orbit descent explicitly. Induction uses `dp.drop 2` +
partition transpose relations directly.

This circles back to my original attempt. The structural mismatch
issue remains.

## Decision point

This needs user input on:
1. Go with Option C (implement paper Lemma 9.2 in Lean — substantial)
2. Accept a WEAKER bijection (sign-only, not shape) — may not match paper
3. Take a different approach entirely (e.g., directly via
   `Equiv.ofBijective` on a wholesale PBP→MYD map, bypassing chain
   structure)
