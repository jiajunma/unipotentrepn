# MYD formalization status (branch `myd-type-and-bijection`)

**Date**: 2026-04-19
**Base**: main @ v3.0 (`90aa1d6`)
**Branch head**: `736db20` (M1.5 Phase A complete)
**Commits**: 18 on branch
**Build**: Lean 1010/1010 green (post-M1.7), blueprint rebuilds clean.

## Roadmap

| Milestone | Content | Status |
|---|---|---|
| M1.0 | `SYD γ` structure + `Sign(O)` (paper Def 9.1, Eq 9.10) | ✓ complete |
| M1.1 | `MYD γ O` subtype of ILS (paper Def 9.3, 9.8) | ✓ complete |
| M1.2 | `AC_fold_singleton` (chain induction) | ✓ complete |
| M1.3 | `Phi_chain` + `extractILS` (plumbing) | ✓ complete |
| M1.4 Phase A | Typed `Phi_D : PBPSet × Fin 2 → MYD` + 5 axioms | ✓ complete |
| M1.5 Phase A | `Phi_D_equiv : PBPSet × Fin 2 ≃ MYD` + 3 axioms | ✓ complete |
| pair/PP alignment | Paper Def 3.5 + 4.8 + PP_★(Ǒ) + counting match | ✓ complete |
| M1.6 Phase A | Extend Phase A to B⁺, B⁻, C, M: `Phi_γ_equiv` axioms | ✓ complete |
| M1.7 | `Fintype (MYD γ O)` via bijection + card equalities (Nat.card) | ✓ complete |

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

User directed sequence: 1 → 3 → 2.

- ✓ **(1) Breadth**: M1.6 Phase A done (B/C/M).
- ✓ **(3) Infrastructure**: M1.7 Fintype + card equality done.
- **(2) Depth (Phase B proofs for D type)**: currently the NL plan for
  the two small `twistBD_preserves_*` lemmas is at
  `lean/docs/blueprints/M1_4_twistBD_preservation.md`. The big 6
  axioms (exists_descentChain_D, singleton, in_MYD, Psi_D + 2
  round-trips) remain as paper §11 content — each is a substantial
  milestone on its own.

Total axioms across types (Phase B obligations):
- D: 8 (M1.4 + M1.5 Phase A)
- B⁺, B⁻: 1 each (just the Equiv axiom) — expands to 8 each if
  decomposed to the D pattern.
- C, M: 1 each — expands to different structure (single descent)
  when decomposed.

**Recommended next step if continuing (2)**: prove
`twistBD_preserves_absValues` first (small, no paper content).
Then `twistBD_preserves_MYDRowValid_BD` (narrow to B/D parity case,
direct calculation). These get 2 of the 8 D-axioms out of the way.

The remaining 6 D-axioms are genuine paper §11 content and are best
tackled one at a time, each as its own session.

### Phase B progress (2026-04-19 later)

✓ `twistBD_preserves_absValues` — proved (commit `e5ff481`).
Used `List.ext_getElem` + per-index case analysis + the helpers
`pow_signed` and `natAbs_signed_mul`.

✓ `twistBD_preserves_MYDRowValid` (B/D narrowed) — proved (commit `e5ff481`).
Key insight: at B/D parity-forced positions (ℓ even), `twistBDRow`
returns the row unchanged — so MYDRowValid is trivially preserved.

✓ `ChainSingleton.snoc` — proved (commit `48f54c4`).
Chain concatenation with end-step singleton, via induction on
the ChainSingleton structure. Reconciles append-ordering
(`IsDescentChain_D.step`) with cons-ordering (`ChainSingleton.cons`).

✓ `descentChain_D_singleton` — **promoted from axiom to theorem**
(commit `48f54c4`). Induction on `IsDescentChain_D` + `ChainSingleton.snoc`.
Reduced to the narrower single-step axiom
`descent_step_thetaLift_singleton` (paper §11.5/11.6 content).

Current axiom count (10 total):
- D (PhiDTyped): exists_descentChain_D, descent_step_thetaLift_singleton,
  descentChain_D_in_MYD (paper §11)
- D (Bijection): Psi_D, Psi_D_Phi_D, Phi_D_Psi_D (paper §11.14)
- B⁺, B⁻, C, M (BijectionBCM): Phi_γ_equiv (one each)

Next tractable sub-steps:
- `exists_descentChain_D` via well-founded recursion on
  `shape.card` (needs `shiftLeft` card-decrease lemma — small).
- `descentChain_D_in_MYD` split: absValues preservation via
  shape induction + parity preservation per step.
