/-
# Counting Proof: Umbrella file

Re-exports the split sub-files:
- `CountingProof.Basic`: YoungDiagram column lengths, shiftLeft, dpart → shape
- `CountingProof.Descent`: empty PBP, double descent ∇² as PBP map
- `CountingProof.Lift`: reverse construction (liftPBP_D + LiftCondition)
- `CountingProof.TSeq`: HSeq/GSeq/TSeq monotone sequence counting + ValidCol0
- `CountingProof.Fiber`: fiber counting and primitive/balanced step theorems
- `CountingProof.Swap`: Phase 1 bijection |R_sub| = |C_sub| via swap_b0_cell

Reference: [BMSZb] Propositions 10.11–10.12.
-/
import CombUnipotent.CountingProof.Basic
import CombUnipotent.CountingProof.Descent
import CombUnipotent.CountingProof.Lift
import CombUnipotent.CountingProof.TSeq
import CombUnipotent.CountingProof.Fiber
import CombUnipotent.CountingProof.Swap
import CombUnipotent.CountingProof.Section10
