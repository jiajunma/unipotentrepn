# Closed sorries

## descentMB_liftBM_naive_Q_paint (Apr 17)

**Strategy**: Case analysis on σ.Q(i, j) ∈ {dot, s, r, d} (B-type symbols).

- **dot**: Use σ.dot_match to get σ.P = dot. Then τ.P(i, j+1) ∈ {dot, s}, lo ≤ 1, Zone 1 (i < dotScolLen τ.P (j+1)) gives descent = dot.
- **s**: σ.P = c (by dot_match, or outside σ.P.shape) → τ.P(i, j+1) = c or outside → ¬Zone 1. Then τ.Q(i, j) = dot since σ.Q.lo ≤ 1 → i < dotScolLen τ.Q j → Zone 2 → s.
- **r/d**: σ.P = c (or outside) → ¬Zone 1. τ.Q(i, j) = r/d (preserved by liftPaintQ_naive). Then τ.Q.lo > 1 → i ≥ dotScolLen τ.Q j → Zone 3 → τ.Q = σ.Q.
- **outside σ.Q.shape**: σ.Q = dot (paint_outside). descent split_ifs: Zone 1 gives dot; Zone 2 contradicts (i, j) ∉ τ.Q.shape; Zone 3 gives dot.

**Helpers extracted**:
- `τP_succ_outside_not_dotScolLen`: (i, j) ∉ σ.P.shape → ¬(i < dotScolLen τ.P (j+1))
- `τP_succ_c_not_dotScolLen`: σ.P(i, j) = c → ¬(i < dotScolLen τ.P (j+1))
- `σP_c_of_Q_ne_dot`: (i, j) ∈ σ.P.shape ∧ σ.Q(i, j) ≠ dot → σ.P(i, j) = c

**Lines added**: ~200. Commit: `88f7ee4`.
