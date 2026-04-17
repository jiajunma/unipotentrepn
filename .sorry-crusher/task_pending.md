# Pending sorries

## descent_image_balanced (line 1371)

### Status: UNPROVABLE AS STATED — needs restatement

### Attempt 1 (Apr 17): Try direct Equiv approach

**Plan**: Build Equiv PBPSet .M μP μQ ≃ {σ : B+ // non-SS} ⊕ {σ : B- // non-SS}.
- Backward direction: `liftBM_from_nonSS` (works, added as helper).
- Forward direction: descent τ must be non-SS.

**Dead end**: Forward direction FAILS for μP = μQ = [1]:
- τ = all-dot M PBP → descent has descent.Q(0, 0) = s (Zone 2 fires).
- s has layerOrd 1, not > 1 (fails non-SS filter).
- Verified by explicit construction in Lean (see session notes).

### Root cause

The filter `Q.lo > 1` does not account for the B+/B- correction:
- In paper's tail class, B+ with Q(bottom) = s gets correction to c (RC, non-SS).
- B- with Q(bottom) = s stays as s (SS).
- So non-SS for B+ and B- should use DIFFERENT predicates.

See `docs/blueprints/B_tail_symbol_correction.md` for full correction details.

### Paths forward (require >100 LOC or restatement)

1. **Change the filter**: use `Q ≠ dot` for B+ and `Q.lo > 1` for B-.
   (Actually may still not match, since it's about tail with Q at row c₁(ι), not row μQ.colLen 0 - 1.)

2. **Use an entirely different proof**: card M computed via recursion on dp, not direct bijection.

3. **Relax to inequality**: `card M ≥ ...` and then match via descent injectivity.

All of these require restating the theorem. This is beyond "filling a sorry"
and needs user guidance.

### Recommendation

Escalate to user for guidance on how to restate or resolve this.
