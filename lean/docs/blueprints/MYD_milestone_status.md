# MYD formalization status (branch `myd-type-and-bijection`)

**Date**: 2026-04-19
**Base**: main @ v3.0 (`90aa1d6`)
**Branch head**: `736db20` (M1.5 Phase A complete)
**Commits**: 18 on branch
**Build**: Lean 931/931 green, blueprint rebuilds clean.

## Roadmap

| Milestone | Content | Status |
|---|---|---|
| M1.0 | `SYD γ` structure + `Sign(O)` (paper Def 9.1, Eq 9.10) | ✓ complete |
| M1.1 | `MYD γ O` subtype of ILS (paper Def 9.3, 9.8) | ✓ complete |
| M1.2 | `AC_fold_singleton` (chain induction) | ✓ complete |
| M1.3 | `Phi_chain` + `extractILS` (plumbing) | ✓ complete |
| M1.4 Phase A | Typed `Phi_D : PBPSet × Fin 2 → MYD` + 5 axioms | ✓ complete |
| M1.5 Phase A | `Phi_D_equiv : PBPSet × Fin 2 ≃ MYD` + 3 axioms | ✓ complete |
| pair/PP alignment | Paper Def 3.5 + 4.8 (primitive/balanced/tailed/vacant + QD) + PP_★(Ǒ) universe + counting inline check match | ✓ complete |

### Deferred (Phase B)

These axioms correspond to paper §9.19–9.20 + §11.5–11.14 theorems
and are the substantial remaining paper content.

| Axiom | Paper source | Milestone |
|---|---|---|
| `exists_descentChain_D` | strong induction on \|τ\| | M1.4.2 |
| `descentChain_D_singleton` | paper Lem 11.5/11.6 (sign bounds) | M1.4.2 |
| `descentChain_D_in_MYD` | paper §9.4 (theta-lift structural preservation) | M1.4.3 |
| `twistBD_preserves_absValues` | small self-contained lemma | quick |
| `twistBD_preserves_MYDRowValid` | small self-contained lemma | quick |
| `Psi_D` | paper §11.14 (reverse theta-lift algorithm) | M1.5.1 |
| `Psi_D_Phi_D` (left_inv) | chain induction | M1.5.1 |
| `Phi_D_Psi_D` (right_inv) | paper surjectivity §11.14 | M1.5.1 |

Total: 8 axioms pending proof.

### Out of scope for this milestone family

- M1.6: extend the bijection to γ ∈ {B⁺, B⁻, C, M}. Expected to
  mirror the D-type construction with ~4× code duplication (or
  factored through a generic γ-parametric formulation — a refactor
  best done after D Phase B).
- `Fintype (MYD γ O)` instance (needed for card equality as an
  explicit theorem).
- counting-side rewrite: change `countPBP_*` to use `PP_★(Ǒ)` as an
  explicit universe rather than inline checks (task 6 from earlier
  plan — task 5 completed via `counting_check_matches_prim_or_tailed`).

## Key outcomes

1. **Concrete bijection exists as a Lean `Equiv`**: `Phi_D_equiv dp h_coh`
   at `lean/CombUnipotent/MYD/Bijection.lean:62`. This is the object
   the user originally asked for (paper Prop 11.15 as a first-class
   theorem, not an abstract wrapper over `Injective + card match`).

2. **Paper alignment completed for Section 3-4 content**:
   Definitions 3.5, 4.8 (pair classification + quasi-distinguished) +
   explicit `PP_★(Ǒ)` + connection to existing counting inline check.

3. **Workflow established**: natural-language proof doc → 3-pass
   self-review → Lean + blueprint written simultaneously → build
   green → commit. Applied to M1.3, M1.4, M1.5.

4. **Phase A / Phase B split**: paper theorems explicitly labeled
   as axioms with proof plans, keeping the build green while work
   proceeds. No `sorry` in the source.

## Files

### New files (this branch)

- `lean/docs/blueprints/MYD_type_and_bijection.md` — overall plan
- `lean/docs/blueprints/AC_fold_singleton.md` — M1.2 NL proof
- `lean/docs/blueprints/M1_3_Phi_D.md` — M1.3 NL proof + reviews
- `lean/docs/blueprints/M1_4_PhiD_typed.md` — M1.4 NL proof + reviews
- `lean/docs/blueprints/M1_5_bijection.md` — M1.5 NL proof + reviews
- `lean/docs/blueprints/MYD_milestone_status.md` — this file
- `lean/CombUnipotent/MYD/SYD.lean` — M1.0
- `lean/CombUnipotent/MYD/TypeMYD.lean` — M1.1
- `lean/CombUnipotent/MYD/FoldSingleton.lean` — M1.2
- `lean/CombUnipotent/MYD/PhiD.lean` — M1.3
- `lean/CombUnipotent/MYD/PhiDTyped.lean` — M1.4 Phase A
- `lean/CombUnipotent/MYD/Bijection.lean` — M1.5 Phase A
- `lean/CombUnipotent/MYD/DPToSYD.lean` — orbit SYD + QD
- `lean/CombUnipotent/MYD/PairClassify.lean` — pair categories + PP
  universe + counting alignment

### Modified files

- `lean/blueprint/src/chapters/pbp.tex` — added 14 new entries
- `lean/blueprint/src/macros/common.tex` — added `\PP` macro
- `lean/CombUnipotent.lean` — 8 new imports

## Next decision point

Three natural continuations; user to pick:

1. **Breadth**: extend Phase A to γ ∈ {B⁺, B⁻, C, M} (~4 more
   axiom/theorem blocks, mostly mechanical).
2. **Depth**: start Phase B proofs for D type (prove the 8 axioms).
   This is paper §11 formalization — substantial.
3. **Infrastructure**: Fintype instance for MYD γ O + card
   equality theorem. Unlocks downstream counting-based reasoning.
