# Structural mismatch: `dpToSYD` vs theta-lift chain

**Finding (2026-04-19)**: during step-case assembly of
`descentChain_D_in_MYD`, the invariant
`absValues E = (dpToSYD .D dp).rows` doesn't decompose cleanly
under the inductive step.

## The issue

For the inductive step with `dp' := dp.drop 2`, the paper's
theta-lift grows `E` by **prepending one row**:
```
E = augment (addp, addn) (charTwistCM E_mid _)
```

But `(dpToSYD .D dp).rows` is NOT
`(addp.natAbs, addn.natAbs) :: (dpToSYD .D dp').rows` in general.

Why: `dpToSYD` uses `partTranspose` (partition transpose), which is
a GLOBAL operation on the whole partition. Dropping two rows from
`dp` changes the transposed partition's entire structure — not just
removes a prefix entry.

**Concrete example**: dp = [5, 3, 3, 1]
- partTranspose = [4, 3, 2, 1, 1] (column lengths for λ = [5,3,3,1])
- rowMultiplicities → SYD.rows per γ split

dp.drop 2 = [3, 1]
- partTranspose = [2, 1, 1]
- Completely different structure.

`SYD.rows` for dp vs dp.drop 2 are **unrelated** by a simple cons.

## Root cause

`dpToSYD` as currently formulated represents the **orbit O** (paper's
BV-dual of Ǒ). At each descent step, the orbit **changes** (paper's
Lemma 9.2: O' = ∇^s_{s'}(O)). The descent on the orbit is NOT `.drop 2`
on the partition.

My `dpToSYD .D (dp.drop 2)` gives the SYD of a DIFFERENT orbit —
not the "inner orbit" of paper's chain.

## Fixes

### Option A: redefine `dpToSYD` step-by-step

Change `dpToSYD` to match paper's descent structure: at each level,
the orbit shrinks by `∇^s_{s'}`, not by partition transpose of dp's
tail. This is a substantial redefinition.

### Option B: use a different invariant

Instead of `absValues E = (dpToSYD .D dp).rows`, use **signature
matching**: `Sign_MYD(E) = Sign_SYD(dpToSYD .D dp)` (paper Eq. 9.10).
This is INVARIANT-level: the signatures (ℕ × ℕ pair) match, but the
row-structure doesn't need to decompose.

However, this weakens the MYD definition (drop the shape constraint).

### Option C: orbit-as-parameter, not shape-as-equality

Redefine `MYD γ O` as the set of ILS `E` satisfying parity + signature
equality + size bound, without requiring `absValues E = O.rows`
element-wise. Paper's definition (Def 9.8) uses the signature
equality + parity, not a shape-structural match.

This is the **most faithful** to paper Def 9.3 + 9.8, and would
make the step case induction work.

## Recommendation

**Option C is correct.** The current `MYD γ O` definition (subtype
with `shape` = absValues) is too strong: paper Def 9.3 uses only
parity + signature. My error was over-constraining by adding shape
equality.

Refactoring `MYD γ O` to paper Def 9.3/9.8 form:
```lean
structure MYD (γ : RootType) (O : SYD γ) where
  E : ILS
  parity : ∀ j (h : j < E.length), MYDRowValid γ (j + 1) E[j]
  size_bound : E.length ≤ O.rows.length  -- or similar bound
  sign : Sign_MYD E = O.Sign  -- paper signature match
```

(Exact formulation depends on paper Def 9.8 which I haven't fully
checked.)

With this refactor, `descentChain_D_in_MYD` would track `Sign` rather
than `absValues`, and the step case induction would work via
`thetaLift_CD_sign` (MYD.lean:564) preserving sign correctly.

## Status

This is a **modeling-level** issue, not a technique issue. The
sub-lemmas 1–4 proved so far are still valuable but serve a slightly
different purpose in Option C.

**Next session task**: refactor `MYD γ O` per Option C, then retry
step case induction. Estimated ~1 full session.
