# Balanced Double Descent — Precise Closing Path

## Key insight

When σ.Q_bot = d in balanced case, mono_Q on σ propagates:
  σ.Q(μP.colLen 0 - 1, 0) = d (= σ.Q_bot, top of σ col 0)
  σ.Q(μP.colLen 0 - 1, j) ≥ σ.Q(μP.colLen 0 - 1, 0) = d for all j ≥ 0
  But layerOrd max = 4 = d. So σ.Q(μP.colLen 0 - 1, j) = d for all j where cell exists.

## Concrete modification of liftPBP_B for balanced Qd

hprimQ used in 5 places (lines 1530, 1535, 1586, 1595, 1638, 1647). Each discharges:

### Line 1530, 1535 (mono_Q cross-column, Case 1 and 2)

```
by_cases hc : μP.colLen 0 ≤ i₁ ∧ i₁ < μQ.colLen 0
· exfalso; have := hprimQ (j₂ + 1) ...; omega
```

**Replacement for balanced**: 
```
· exfalso
  -- i₂ < μQ.colLen (j₂+1). In balanced: μQ.colLen (j₂+1) ≤ μP.colLen 0.
  -- With i₁ ≥ μP.colLen 0 and i₁ ≤ i₂: contradiction since i₂ ≥ μP.colLen 0 but i₂ < μP.colLen 0.
  have h_bal_weak : μQ.colLen (j₂ + 1) ≤ μP.colLen 0 := ...
  omega
```

For Case 2 (inr, i₁ could be μP.colLen 0 - 1):
```
· -- i₁ ≥ μP.colLen 0 - 1 (from Case 2 hc).
  -- If i₁ = μP.colLen 0 - 1: need σ.Q(i₁, j₂) ≠ s  (for row_s) or ≥ liftCol0Q(i₁) (for mono_Q).
  -- When σ.Q_bot = d: σ.Q(μP.colLen 0 - 1, j) = d by mono_Q propagation.
  -- τ.Q(i₁, j₂+1) = σ.Q(i₁, j₂) = d (shifted). But hypothesis says = s. d ≠ s. Contradiction.
  ...
```

### Line 1586, 1595, 1638, 1647 (row_s, row_r)

Similar pattern. When i = μP.colLen 0 - 1, σ.Q at that row in col j ≥ 0 is d (via mono_Q from σ.Q_bot). So τ.Q(i, j+1) = d, contradicting s/r hypothesis.

## Implementation

Define `liftPBP_B_bal_Qd σ v hle hP_pos h_Qbot_d : PBPSet .Bplus μP μQ` by COPYING `liftPBP_B` body and modifying the 5 hprimQ-using branches.

Required auxiliary:
- `sigma_Q_top_row_eq_d`: σ.Q(μP.colLen 0 - 1, j) = d for all j with (μP.colLen 0 - 1, j) ∈ σ.Q.shape, when σ.Q_bot = d.
  - Proof: mono_Q gives σ.Q(i, 0).lo ≤ σ.Q(i, j).lo ≤ 4. And σ.Q(i, 0) = d.lo = 4. So = 4 = d.

Estimated: ~500 lines (~400 liftPBP_B_bal_Qd + 100 auxiliary).

## Subsequent closures

Once liftPBP_B_bal_Qd exists:
- `liftPBP_B_bal_Qd_round_trip` (~80 lines, parallel to liftPBP_B_round_trip)
- `liftPBP_B_bal_Qd_injective` (~80 lines)
- `validCol0_B_le_fiber_bal_Qd` (~30 lines)
- `fiber_card_B_bal_Qd` closure: `le_antisymm fiber_le_validCol0_B validCol0_B_le_fiber_bal_Qd` (~5 lines)

Similar structure for Qr and Qlow, but with non-trivial admissibility (not all v ∈ ValidCol0_B give valid lift).

