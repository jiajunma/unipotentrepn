# MYD_sig Finiteness Issue

**Status**: Structural design flaw in `MYD_sig` type.

## The issue

```lean
structure MYD_sig (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  sign_match : ILS.sign E = signature
```

`MYD_sig γ s` is **NOT finite**. Appending `(0, 0)` rows to any valid `E` preserves `ILS.sign E` (because `signRow i (0, 0) = (0, 0)`).

Therefore: `∀ E : ILS, ILS.sign E = s → ILS.sign (E ++ [(0, 0)]) = s`, yielding infinitely many ILSs with the same sign.

## Implications

1. **`Phi_γ_sig_equiv` hypothesis `h_surj` is unsatisfiable**: Phi_γ_sig has finite domain (PBPSet × Fin 2), so its image is finite. Surjectivity onto infinite MYD_sig is impossible.

2. **The equiv theorem is a valid Lean statement but vacuously conditional**: callers cannot supply `h_surj` in principle.

3. **`Fintype (MYD_sig γ s)` can only be derived from the equiv itself (circular)**.

## Root cause

Paper `MYD⋆(O)` is a stricter subtype — marked Young diagrams with specific paint structure bounded by the partition shape. Our `MYD_sig` only captures the sign constraint, not the structural bound.

## Fix options

### Option 1: Canonicalize via trimming trailing zeros

```lean
def ILS.trim (E : ILS) : ILS := E.reverse.dropWhile (· = (0, 0)) |>.reverse

structure MYD_sig (γ : RootType) (signature : ℤ × ℤ) where
  E : ILS
  sign_match : ILS.sign E = signature
  no_trailing_zeros : E = E.trim
```

This makes MYD_sig finite for each s (by bounding the non-zero row count).

### Option 2: Bound row count structurally

```lean
structure MYD_sig (γ : RootType) (shape_bound : ℕ) (signature : ℤ × ℤ) where
  E : ILS
  bounded : E.length ≤ shape_bound
  sign_match : ILS.sign E = signature
```

Provide `shape_bound` parameterized by μP, μQ size.

### Option 3: Full paper-accurate MYD

Use the MYD type from `MYD/TypeMYD.lean` (if available). More invasive but mathematically correct.

## Recommendation

**Option 1** (trim invariant) is minimally invasive. The trim condition composes with existing structure:
- `ILS.sign E = ILS.sign E.trim` (proven by checking trailing zeros don't contribute)
- Trim is idempotent
- Chain-extracted ILSs are naturally trimmed (no spurious trailing zeros — each chain step adds specific non-zero rows)

Implementing Option 1: ~150 LOC.

## Impact on current session's work

- `Phi_γ_sig_surj_of_inj_card` reductions still valid but require discharging Fintype independently (via the refined MYD_sig).
- Injectivity hypothesis h_inj is unaffected (still meaningful between finite source and any target).
- Without finiteness fix, `Phi_γ_sig_equiv` cannot be instantiated.
