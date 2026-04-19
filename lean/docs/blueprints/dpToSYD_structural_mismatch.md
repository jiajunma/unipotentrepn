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

## Deeper analysis (2026-04-19, second round)

Looking at paper §9.2 + §10 more carefully, there are TWO distinct
descent operations:

1. **PBP-side descent** (paper §10): τ → doubleDescent_D_PBP τ;
   corresponds to dp → dp.drop 2. This is the CURRENT formulation.
2. **Orbit-side descent** (paper Lemma 9.2): O → ∇^s_{s'}(O);
   shifts O(i+1) to O(i), adjusts O(1).

These are DIFFERENT. `dpToSYD .D (dp.drop 2)` corresponds to NEITHER
— it's `partTranspose (dp.drop 2)`, which reshuffles the partition
structure globally.

**Key insight**: for the descentChain to correctly match orbit
descents, we need to track the orbit's ∇^s_{s'} descents separately,
NOT just dp.drop 2.

### Even simpler invariant: signature only

`ILS.sign` (MYD.lean:69) exists and gives `ℤ × ℤ`. For MYD at orbit
O, paper Def 9.10 says `Sign(E) = Sign(O)`. This is a single
`ℤ × ℤ` equality, NOT a row-structural match.

**Revised Option C**:
```lean
structure MYD (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  parity : ∀ j h, MYDRowValid γ (j+1) E[j]
  sign_match : ILS.sign E = signature
```

Indexed by signature (ℤ × ℤ), not by SYD O. For τ ∈ PBPSet .D μP μQ
(QD orbit), the target signature is τ.signature = (p_τ, q_τ). With
this formulation:

- `descentChain_D_in_MYD` concludes `ILS.sign E = τ.signature`
- Step case uses `ACResult.thetaLift_sign` (MYD.lean:821) directly:
  each theta-lift step preserves signature
- The induction is straightforward: inner chain has inner sign =
  inner τ's sign; outer step adds ε_τ twist which changes sign
  by a known formula.

**This formulation** matches paper's signature-based framework and
uses existing MYD.lean:821+ sign-preservation lemmas directly.

### Subtlety: signature depends on τ, not just (μP, μQ)

For general γ PBPs, different τ's with same shape can have different
signatures. But under **quasi-distinguished** Ǒ (paper's assumption
for Prop 11.15), `τ.signature = some_fixed_value` for all τ in
PBPSet .D μP μQ. This is paper Prop 11.4 or similar.

**For our formalization**, we should either:
- Restrict to QD (add hypothesis)
- Parameterize MYD by the τ-dependent signature

The former is cleaner; matches paper's scope. QD already has an
Is_QD predicate in `DPToSYD.lean` from previous session work.
