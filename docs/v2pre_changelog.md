# v2-pre Branch Changelog

Summary of all changes on `v2-pre` relative to `origin/main` (115 commits).

## Scope

Almost all work is on **standalone.py** — a self-contained, descent-based DRC computation
independent of the original combunipotent package. The original lift algorithms are untouched.

## New Files

| File | Description |
|------|-------------|
| `standalone.py` | Descent-based DRC, AC/LS, theta lift, PBP bijection, counting (62 commits) |
| `docs/algorithm_spec.md` | Precise paper-to-code correspondence (42 commits) |
| `tests/test_standalone.py` | Cross-check standalone.py against combunipotent |
| `tests/test_standalone_exhaustive.py` | Extended exhaustive tests |
| `tests/test_compare_ls.py` | LS comparison between standalone and drclift |
| `tests/test_descent.py` | Lift-descent inverse verification |
| `tools/lift_graph.py` | CLI for generating theta lifting diagrams |
| `requirements.txt` | Python dependencies |

## Bug Fixes in combunipotent/ (~7 commits, 610 lines net)

All lift functions (`lift_extdrc_B_M`, `lift_drc_M_B`, `lift_drc_D_C`, `lift_drc_C_D`, etc.)
have **zero logic changes**. Only comments/docstrings and descent-verification asserts were added.

### verify_drc type B (95e2166)

- Did not handle extended DRC (with `a`/`b` tag on `drcR[0]`); now auto-strips when `rtype='B'`.
- **Variable name typo**: `srddrcR = remove_tail_letter(srddrcR, 's')` used undefined variable;
  fixed to `remove_tail_letter(rddrcR, 's')`.
- **Wrong arguments to `test_bullets_drc`**: was `(scdrcL, rddrcR)`, fixed to `(cdrcL, srddrcR)`.
- Missing `None` checks on `remove_tail_letter` return values.

### descent_drc type M→B (95e2166, a38fb53)

- Called `_fill_ds_M` instead of `_fill_ds_B` (wrong fill function).
- Non-special shape condition `len(fL) > len(fR)` was **inverted** (should be `<`).
- Added B+/B- sub-type determination and `make_extdrc_B` wrapping.

### descent_drc type B→M (a38fb53, 89c80f8, 3ab0ced, e89f463)

Implemented progressively over 4 commits:

1. **Basic B→M descent**: strip `a`/`b` tag, call `_fill_ds_M(drcL, drcR[1:])`.
2. **Case (a) correction** [BMSZb Section 10.4]: when γ=B+ and Q(c₁(ι),1) ∈ {r,d},
   set P'(c₁(ι'),1) = s.
3. **Second column tail correction**: reverse `gen_drc_B_two_new`'s `tR='r' → nsR='d'`
   conversion when `tL` is empty and γ=B+.

Final result: 6229 lift-descent inverse pairs all pass (C:1016, D:797, M→B:3256, B→M:1160).

### Other minor changes

- `drclift.py` import line: added `part2drc, fill_rdot, fill_r, fill_c` (for type M drcgraph).
- `test_dpart2drcLS`: condition `rtype in ('D','C')` narrowed to `rtype == 'D'` for dpart padding.
- New helpers: `split_extdrc_B(edrc)` and `make_extdrc_B(drc, sub_rtype)`.
