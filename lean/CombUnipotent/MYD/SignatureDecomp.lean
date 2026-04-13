/-
# Signature Decomposition for D-type PBP

Reference: [BMSZ] Equation (11.7), [BMSZb] Proposition 10.9.

For D-type PBP τ with orbit Ǒ = (r₁, r₂, ...):
  Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²(τ)) + Sign(τ_t)

where c₂(O) = μQ.colLen 0 = (r₂-1)/2 is the second column length of the BV dual.

This decomposes the PBP signature into:
1. A constant from the Q shape: (μQ.colLen 0, μQ.colLen 0)
2. The signature contribution from columns ≥ 1 (= double descent)
3. The tail signature from column 0 above Q
-/
import CombUnipotent.Tail

namespace PBP

open PBP

/-! ## Signature of D-type PBP decomposes into col0 + colGe1

For D type:
  p = nDot + 2·nR + nC + nD
    = (dotCol0 + dotColGe1) + 2·(rCol0 + rColGe1) + (cCol0 + cColGe1) + (dCol0 + dColGe1)

where:
  dotCol0 = Q.colLen 0 (cells below Q in P col 0 are dots)
  {s,r,c,d}Col0 in [Q.colLen 0, P.colLen 0) = tail cells
  dotColGe1 = dots in columns ≥ 1
  {s,r,c,d}ColGe1 = non-dot in columns ≥ 1

The colGe1 contributions equal those of the double descent ∇²(τ)
(since descent preserves columns ≥ 1).

The tail contribution is:
  tailP = 2·rCol0_tail + cCol0_tail + dCol0_tail
  tailQ = 2·sCol0_tail + cCol0_tail + dCol0_tail
which matches our tailSignature_D. -/

-- TODO: State and prove the signature decomposition formula.
-- This requires connecting:
-- 1. PBP.signature τ (from Signature.lean)
-- 2. countSym_split (from Tail.lean): P.countSym σ = countSymCol0 + countSymColGe1
-- 3. countCol0 decomposition into [0, Q.colLen) + [Q.colLen, P.colLen)
-- 4. The fact that col0 below Q is all dots (col0_dot_below_Q_D)
-- 5. The fact that Q has only dots for D type (Q_countSym_eq_zero_of_D)
-- 6. tailSignature_D sums the tail cell contributions

end PBP
