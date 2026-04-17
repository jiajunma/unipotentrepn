# Pending sorries

(none — all sorries closed)

## History

### descent_image_balanced — CLOSED session 2

Previously marked as "unprovable as stated". Discovery: the statement remained
incorrect even after commit 8b3e618 which tried to fix it with asymmetric filter.

Counterexample for μP = μQ = [2] (row of length 2):
- |M| = 9 (verified by manual enumeration and partial Lean construction)
- Old filter sum ((B⁺, σ.Q ≠ •) + (B⁻, σ.Q.lo > 1)) = 6.

The issue: for this shape, the all-dot M PBP (and two similar ones) descend
to B⁺ σ with σ.Q(bottom, 0) = •. The filter excluded them, breaking the
injective correspondence.

**Fix**: Changed statement to |M| = |B⁺| + |{B⁻ // σ.Q.lo > 1}|. See task_done.md.
