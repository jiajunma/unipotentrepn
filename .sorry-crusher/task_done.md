# Closed sorries

## descentMB_liftBM_naive_Q_paint (session 1, commit 88f7ee4)

**Strategy**: Case analysis on σ.Q(i, j) ∈ {dot, s, r, d} (B-type symbols).

- **dot**: Use σ.dot_match to get σ.P = dot. Then τ.P(i, j+1) ∈ {dot, s}, lo ≤ 1, Zone 1 (i < dotScolLen τ.P (j+1)) gives descent = dot.
- **s**: σ.P = c (by dot_match, or outside σ.P.shape) → τ.P(i, j+1) = c or outside → ¬Zone 1. Then τ.Q(i, j) = dot since σ.Q.lo ≤ 1 → i < dotScolLen τ.Q j → Zone 2 → s.
- **r/d**: σ.P = c (or outside) → ¬Zone 1. τ.Q(i, j) = r/d (preserved by liftPaintQ_naive). Then τ.Q.lo > 1 → i ≥ dotScolLen τ.Q j → Zone 3 → τ.Q = σ.Q.
- **outside σ.Q.shape**: σ.Q = dot (paint_outside). descent split_ifs: Zone 1 gives dot; Zone 2 contradicts (i, j) ∉ τ.Q.shape; Zone 3 gives dot.

**Helpers extracted**:
- `τP_succ_outside_not_dotScolLen`: (i, j) ∉ σ.P.shape → ¬(i < dotScolLen τ.P (j+1))
- `τP_succ_c_not_dotScolLen`: σ.P(i, j) = c → ¬(i < dotScolLen τ.P (j+1))
- `σP_c_of_Q_ne_dot`: (i, j) ∈ σ.P.shape ∧ σ.Q(i, j) ≠ dot → σ.P(i, j) = c

**Lines added**: ~200.

## descent_image_balanced (session 2, this work)

**Key discovery**: The theorem statement was incorrect after the commit 8b3e618
"fix". The old `σ.Q(bottom, 0) ≠ •` filter for B⁺ was too restrictive.

**Counterexample found**: μP = μQ = single row of length 2 (`ofRowLens [2]`):
- |M| = 9 (enumerated manually + `tau1` existence verified in Lean)
- Old filter sum = 6. Mismatch.

**Correct statement**:
```
Fintype.card (PBPSet .M μP μQ) =
  Fintype.card (PBPSet .Bplus μP.shiftLeft μQ) +
  (Finset.univ.filter fun σ : PBPSet .Bminus μP.shiftLeft μQ =>
    (σ.val.Q.paint (μQ.colLen 0 - 1) 0).layerOrd > 1).card
```

**Strategy**: Equiv M ≃ B⁺ ⊕ {B⁻ // lo > 1} via:
- Forward: `descentMB_sum_balanced` routes by descentType_M.
- Backward: `liftBM_from_nonSS` (total for B⁺, filtered for B⁻).
- Round-trip: uses `descentMB_liftBM_naive` + `descentMB_injective`.

**Key helpers added**:
- `h_bal_exc_of_Bplus`: Vacuous h_bal_exc for σ ∈ B⁺ (σ.γ = Bminus false).
- `M_descent_Bminus_Q_lo_gt_one`: Forward asymmetric theorem.
  For balanced τ ∈ M with descentType_M = .Bminus: σ.Q(bottom, 0).lo > 1.
  Via Zone analysis: ¬Zone 1 (τ.P(bot, 1) = c, mono_P), ¬Zone 2 (τ.Q lo > 1),
  Zone 3 preserves τ.Q(bot, 0) ∈ {r, d}.
- `descentMB_sum_balanced`, `descent_equiv_balanced`.

**Refactor**: Changed `h_bal_exc` from  `balanced → pos → lo > 1` to
`balanced → pos → σ.γ = .Bminus → lo > 1` across 10+ lemmas. This allows
B⁺ σ to satisfy h_bal_exc vacuously (via absurd(σ.γ = Bminus)).

**Lines added**: ~200.
