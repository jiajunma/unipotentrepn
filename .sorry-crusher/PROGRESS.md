# Progress — CorrespondenceB.lean (session 3)

## Summary

Current 5 sub-sorries in CorrespondenceB.lean for α-class count identities
and Phase 3 fiber identity. All identities numerically verified for 82 dp cases.

## Current sorries

| Line | Lemma | Case | Difficulty |
|---|---|---|---|
| 2137 | `card_B_DD_alpha_eq_countB_dd` | singleton + inductive | Medium |
| 2166 | `card_B_RC_alpha_eq_countB_rc` | singleton + inductive | Medium-Hard |
| 2201 | `card_B_SS_alpha_eq_countB_ss` | singleton | Medium |
| 2205 | `card_B_SS_alpha_eq_countB_ss` | inductive | Hard |
| 2280 | `card_B_bal_grouped_fiber` | all | Very Hard |

## Objectives (ordered by strategy)

### 1. A3 singleton (line 2201) — SIMPLEST

For dp = [r₁]: μP = ⊥, μQ has 1 col of c₁ = r₁/2 cells.
`countPBP_B([r₁]).2.2 = 1`.

For B⁻ PBPs on (⊥, μQ), use existing `PBPSet_Bminus_bot_equiv_DSeq`:
bijection with DSeq(c₁) = sequences Fin c₁ → {s,r,d} sorted with ≤1 d.

Q_bot.lo ≤ 1 ⟺ v(c₁-1).lo ≤ 1 ⟺ v(c₁-1) = s (since {s,r,d}.lo = {1,2,4}).
Sorted + v(c₁-1) = s ⟹ all v = s (unique seq).

Count = 1. ✓

### 2. A1 singleton (after A3 done)

For dp = [r₁]: |d combined| = ?
countPBP_B([r₁]).1 = 2·nu(c₁-1) = 2·c₁ (c₁ ≥ 1).

Via DSeq for B⁻ (and mirror for B⁺ via γ-swap symmetry on this filter too):
Q_bot = d ⟺ v(c₁-1) = d. Sorted + at most 1 d + last = d means d at last,
rest in {s, r}. Count of sorted (s,r) sequences of length c₁-1 = c₁.
Both γ = 2·c₁. ✓

### 3. A2 singleton (after A1, A3)

For dp = [r₁]: |B⁺ Q_bot≠d| + |B⁻ Q_bot=r|.
countPBP_B([r₁]).2.1 = nu(c₁) + nu(c₁-1) = (c₁+1) + c₁ = 2c₁+1.

|B⁺ non-d| = |B⁺| - |B⁺ d| = (2c₁+1) - c₁ = c₁+1.
|B⁻ r| = ? via DSeq: v(c₁-1)=r, sorted, all v ≤ r. v ∈ {s, r}. Count = c₁.

Total = (c₁+1) + c₁ = 2c₁+1. ✓

### 4. Inductive cases (A1/A2/A3)

Primitive (r₂ > r₃):
- Each sub σ gives 4k tail configs (uniform), tDD giving new d, tRC giving new r, tSS giving new low.
- A1 new.dd = (|sub d| + |sub r| + |sub low|)·tDD = card_rest · tDD = dd_new ✓ (primitive formula)
- Similarly A2, A3.

Balanced (r₂ ≤ r₃): use Phase 3 fiber identity + IH.

### 5. Phase 3 fiber identity

Most complex. Needs explicit fiber construction for balanced case
with non-uniform sizes 4k/4k-2/2k-1 based on sub's Q_bot.

## Proof strategies to try

- **A3 singleton**: Fintype.card_congr with DSeq bijection, restrict to filter.
- **A1, A2 singleton**: similar, adapting DSeq argument.
- **Inductive**: structural induction mirroring `card_PBPSet_B_eq_tripleSum_countPBP_B`.
- **Phase 3**: new infrastructure, defer if too complex.

## Known infrastructure

- `PBPSet_Bminus_bot_equiv_DSeq` — B⁻ PBPs on (⊥, μQ) ≃ DSeq(c₁)
- `DSeq_card`, `DSeq_equiv_GSeq`
- `card_PBPSet_Bminus_bot_singleCol` for total count
- `swapBplusBminus` for γ-swap bijection
- `card_PBPSet_B_primitive_step` for primitive recursion (uniform fiber)
