# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**unipotentrepn** is a Python package for the combinatorics of unipotent representations of classical groups (Sp, SO, Mp). It implements algorithms for nilpotent orbits, Springer correspondence, DRC diagrams, local systems, and theta lifting.

## Running Tests

All tests are plain Python scripts (no pytest). Run from the project root:

```bash
python3 tests/test_verify_drc.py              # DRC diagram structural verification (B/B+/B-/C/D/M)
python3 tests/test_verify_drc.py --max-size 24 # Extended coverage
python3 tests/test_dpart2drcLS.py             # DRC-LS matching (purely even dual partitions)
python3 tests/test_purelyeven.py              # Purely even induction test
python3 tests/test_LSDRC.py                   # General partition DRC-LS matching
```

## Command-Line Tools

```bash
python3 tools/lift_graph.py 5,5,2,2 -t C              # Generate lifting graph (PDF)
python3 tools/lift_graph.py 5,5,2,2 -t C -f svg        # SVG output
python3 tools/lift_graph.py 5,5,2,2 -t C --print-drc   # Also print DRC diagrams
```

## Architecture

### Module Dependency Graph

```
tool.py          (core: partitions, symbols, Springer, BV duality)
  ↓
drc.py           (DRC diagram construction, verification, display)
LS.py            (local systems, theta lifting)
  ↓
drclift.py       (DRC-LS matching framework, theta lifting of DRCs)
  ↓
lsdrcgraph.py    (Graphviz visualization with DRC packet annotations)
recursive.py     (independent: counting via signature polynomials in Z[p,q])
combunip.py      (legacy DRC construction, kept for backward compatibility)
```

### Core Algorithm: Inductive Theta Lifting

The central algorithm works inductively on partitions:
1. Start from trivial group (empty DRC, trivial LS)
2. At each step, lift both DRC and LS via theta correspondence
3. Type alternates at each step: C ↔ D, M ↔ B
4. Verify lifted sets match independently computed sets

### Root System Types and Dual Pairs

| Type | Group | Dual type | Dual partition parity |
|------|-------|-----------|-----------------------|
| C | Sp(2n) | D | all parts odd, total odd |
| D | SO(2n) | C | all parts odd, total even |
| B | SO(2n+1) | M | all parts even, total even |
| M | Mp(2n) | B | all parts even, total even |
| B+ / B- | SO(p,q) real forms | — | (extended DRC with a/b tag) |

### Key Data Structures

- **Partition**: `(5, 3, 3, 1)` — decreasing tuple of positive integers
- **W-representation (bipartition)**: `((3, 1), (2,))` — pair `(tauL, tauR)`
- **DRC diagram**: `(('**rc', '*r'), ('**s', '*'))` — pair `(drcL, drcR)` of column-string tuples
  - Symbols: `*`=dot, `r`/`s`=real, `c`=compact, `d`=discrete
- **Local system (LS)**: `FrozenMultiset` of irreducible LS tuples `((p1,n1), (p2,n2), ...)`
- **Symbol**: `((0, 2, 4), (1, 3))` — pair of sorted integer sequences

### DRC Diagram Symbol Rules (Definition 2.25)

| γ | P (drcL) symbols | Q (drcR) symbols |
|---|---|---|
| B+ / B- | {•, c} | {•, s, r, d} |
| C | {•, r, c, d} | {•, s} |
| D | {•, s, r, c, d} | {•} |
| M (= C̃) | {•, s, c} | {•, r, d} |

### Type B Extended DRC

Type B DRC diagrams have an extended format: `drcR[0]` ends with `'a'` (B+) or `'b'` (B-).
- `split_extdrc_B(edrc)` → `(drc, 'B+'/'B-')`: strip the tag
- `make_extdrc_B(drc, 'B+'/'B-')` → `edrc`: add the tag (with verify)
- `verify_drc(edrc, 'B')`: automatically strips `a`/`b` before verification
- `verify_drc(drc, 'B+')` or `verify_drc(drc, 'B-')`: verify already-stripped DRC

### Key Entry Points

```python
from combunipotent import *

# DRC diagrams from dual partition
dpart2drc((5, 3, 1, 1), rtype='D')

# DRC diagrams from special partition
part2drc((4, 2, 2), rtype='C')

# Local systems
part2LS((4, 2, 2), rtype='C')

# Counting
countunip((3, 1), rtype='D')

# BV duality
dualBVW((5, 3, 1), rtype='C', partrc='c')

# Lifting graph
gen_lift_graph((5, 5, 2, 2), rtype='M', format='pdf')
```

## Conventions

- Every function must have a docstring or comment.
- Commit to git after completing each set of related changes.
- `dpart2drc` takes **dual partitions** (orbit side); `part2drc` takes **special partitions** (group side).
- `test_dpart2drcLS` uses `test=False` for type B (det-disjointness not yet fully verified).
- The `rich` library overrides `print` in `drc.py` and `drclift.py` for styled Jupyter output.
- `FrozenMultiset` from the `multiset` package shadows the builtin `frozenset` in several modules.
