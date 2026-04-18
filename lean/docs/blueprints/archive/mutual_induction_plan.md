# Mutual Induction Plan for A1/A3/Total

## Problem

A1 balanced (line 3105), A3 balanced (line 3297), and Total (line 7981) have mutual
dependencies through `card_PBPSet_B_balanced_step` (line 7814):

- `balanced_step dp` uses `A1(rest)` + `A3(rest)` (lines 7867, 7869)
- `Total dp balanced` uses `balanced_step dp`
- `A1 dp balanced` needs `A1(rest)`, `A3(rest)`, `Total(rest)`
- `A3 dp balanced` needs `A1(rest)`, `A3(rest)`, `Total(rest)`

## Solution

Replace the top-level `A1`, `A3`, `Total`, `balanced_step` with a `mutual ... end` block
at the END of the file. Original theorems become thin wrappers that call the mutual block.

## Plan

1. **Keep existing**: A1 stub (line 3105), A3 stub (line 3297), Total (line 7981),
   balanced_step (line 7814). Delete their proof bodies, replace with:
   ```lean
   exact (A1_A3_Total_mutual dp hP hQ hsort heven hpos hQ_pos).1
   ```
   where `A1_A3_Total_mutual` is defined at end of file.

2. **Add mutual block at end**:
   ```lean
   mutual
     theorem A1_A3_Total_mutual (dp : DualPart) ... :
         (A1 dp ∧ A3 dp ∧ Total dp) := by
       ... induction on dp.length ...
       -- primitive: existing primitive helpers
       -- balanced: use card_PBPSet_B_balanced_step_raw + fiber-α lemmas + IH
   end
   ```

   Or (simpler, no actual mutual): use a single theorem with well-founded recursion:
   ```lean
   theorem A1_A3_Total_combined (dp : DualPart) ... :
       A1_pred dp ∧ A3_pred dp ∧ Total_pred dp := by
     match dp, ... with
     | [], ... => ⟨..., ..., ...⟩
     | [r₁], ... => ⟨..., ..., ...⟩
     | r₁ :: r₂ :: rest, ... =>
       have ih := A1_A3_Total_combined rest ... -- recursive call
       -- use ih.1 (A1_rest), ih.2.1 (A3_rest), ih.2.2 (Total_rest)
       ...
     termination_by dp.length
   ```

3. **Balanced case in combined**: use the extracted `card_PBPSet_B_balanced_step_raw`
   (which takes h_A1_rest, h_A3_rest, h_total_rest as explicit parameters, not calls A1/A3
   internally) plus the fiber-α lemmas built in commits 9e8d69b, 54bc0d7, c4819fa.

4. **Update call sites** (A2 at line 8078, etc.): replace `have h_A1 := card_B_DD_alpha_eq_countB_dd ...`
   with `have h_A1 := (A1_A3_Total_combined ...).1`.

## Prerequisites (all DONE)

- validCol0_B_{Qr,Qlow}_card_top_{d,lo_le_one}
- fiber_alpha_topSym_{d,lo_le_one}_count_bal_{Qd,Qr,Qlow}
- card_B_bal_grouped_fiber (line 7489)

## Estimated size

- 400-700 lines for combined theorem body
- 20-50 lines for wrapper edits
- Total: ~500-800 lines

## Expected build time

Combined theorem may need `set_option maxHeartbeats 800000`.
