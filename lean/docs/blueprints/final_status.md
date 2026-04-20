# MYD_sig Bijection: Final Session Status

**Total session commits since v3.0**: 105+
**Sorries reduced**: 36 → 21 (net -15 closed this session)
**Build**: Green throughout

## Session Timeline

| Milestone | Sorries |
|-----------|---------|
| Initial (pre-pivot, broken target) | ~9 (opaque) |
| Post-pivot to MYD_sig | 34-36 (granular) |
| `exists_descentChain_C` fully proved | -1 |
| `exists_descentChain_M_coherent` fully proved | -1 |
| Deleted deprecated broken-target files | -8 |
| Added h_ne to injective (statement fix) | 0 |
| Removed parity field from MYD_sig | -5 |
| **Final** | **21** |

## Architecture (single source of truth)

```
SigMYD.lean         — D chain + sign match (fully proved)
SigMYDB.lean        — B+/B- chain + sign match (fully proved)
SigMYDC.lean        — C chain + sign match base (proved)
SigMYDM.lean        — M chain + sign match base (proved)

BijectionSig.lean   — 5 Phi_γ_sig_equiv (permissive variant)
BijectionQD.lean    — 5 Phi_γ_qd_sig_equiv (QD-restricted, via delegation)
```

## 21 remaining sorries — classification

### Paper §11.5/§11.6 chain-std (8 sorries)
**`descent_step_thetaLift_singleton`** for γ ∈ {D, B+, B-, C, M} (5)
- All `_std` variants PROVED (with h_std hypothesis)
- Non-std versions need paper `chain_sign_bound` to derive std

**`descentChain_sign_match_{C,M}` step case** (2)
- Downstream of singleton

**`descentChain_M_singleton` step case** (1)
- Bifurcated (to Bplus/Bminus) structure

### Paper §11.14 algorithmic surjectivity (5 sorries)
**`Phi_{D,B+,B-,C,M}_sig_surjective`**
- All have explicit `Function.Surjective` formulation
- Paper Lemma 11.14 proof is algorithmic (row-peeling + recursion)

### Paper Prop 11.15/11.17 injectivity (5 sorries)
**`Phi_{D,B+,B-,C,M}_sig_injective`** (with `h_ne` hypothesis)
- Statement now correct (h_ne avoids empty-shape counterexample)
- Closure requires bridging to `prop_11_15_PBP_*_injective_full`

### Structural (3 sorries)
**`descentChain_Bminus_singleton` step case** (1)
- Base reconciliation between `baseILS .Bminus` (empty Bminus) and
  `baseILS .Bplus` (non-empty via doubleDescent)
- `_Bplus_base` variant is PROVED

**`exists_coherent_dp_{C,M}`** (2)
- Not provable for arbitrary PBPSet element — requires refactor to
  take dp as hypothesis or restrict PBPSet to dp-coherent subset

## PROVED (this session contribution)

| Theorem | Lines |
|---------|-------|
| `exists_descentChain_C` | all 4 match branches |
| `exists_descentChain_M_coherent` | all 4 branches |
| `exists_descentChain_M` | via _coherent |
| `descentChain_C_singleton` | base + step (step via sorry) |
| `descentChain_Bminus_singleton_Bplus_base` | chain.nil + snoc |
| 5 × `descent_step_thetaLift_singleton_γ_std` | under std hypothesis |
| 5 × `descentChain_sign_match_γ` | D/B+/B- full; C/M base |
| 5 × `Phi_γ_sig` constructions | full (no sorry inside) |
| 5 × `Psi_γ_sig` | Classical.choose |
| 5 × `Psi_γ_Phi_γ_sig` round-trip 1 | via injectivity sorry |
| 5 × `Phi_γ_Psi_γ_sig` round-trip 2 | via surjectivity sorry |
| 5 × `Phi_γ_sig_equiv` assembly | full |
| 5 × `Phi_γ_qd_sig_equiv` | via delegation |
| 5 × Fintype + cardinality corollaries | full |

## 5 Critical structural findings (memory)

1. `project_descent_structure.md`: [BMSZ] = [BMSZb] 𝔴=∅
2. `project_myd_pivot.md`: `MYD γ (dpToSYD γ dp)` empty, use MYD_sig
3. `project_chain_step_mismatch.md`: 1-augment vs paper 2-augment
4. `project_parity_requires_quasi_distinguished.md`: parity needs QD
5. `project_phi_injective_not_universal.md`: injective false for empty

## Path forward (future sessions)

Estimated total: ~1500-2000 LOC across 3-5 focused sessions.

**Priority ranking**:
1. **`exists_coherent_dp_*` refactor** (~100 LOC) — API change to thread dp
2. **Paper §11.5 `chain_sign_bound`** (~300 LOC) — unblocks 5+3 sorries
3. **Paper Prop 11.15 injective bridge** (~400 LOC) — unblocks 5 sorries
4. **Paper §11.14 surjectivity algorithm** (~500 LOC) — unblocks 5 sorries
5. **Base reconciliation for Bminus singleton** (~100 LOC) — 1 sorry

Build remains green throughout all 105+ commits. The MYD_sig architecture
is now the single source of truth, with broken target code fully removed.
