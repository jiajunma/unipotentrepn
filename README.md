# unipotentrepn

A Python package for the **combinatorics of unipotent representations of classical groups**.

This package implements algorithms for computing and studying unipotent representations
attached to nilpotent orbits of classical Lie groups, including symplectic groups Sp(2n),
orthogonal groups O(p,q) / SO(p,q), and the metaplectic group Mp(2n).

## Mathematical Background

The theory of unipotent representations connects several areas of representation theory:

- **Nilpotent orbits** are parametrized by partitions satisfying parity conditions depending on the root system type (B, C, D, M).
- **Weyl group representations** of type B_n / C_n / D_n are parametrized by bipartitions (tauL, tauR).
- **Springer correspondence** maps nilpotent orbits to Weyl group representations.
- **DRC diagrams** (dot-r-c diagrams) are combinatorial objects that parametrize unipotent representations; each diagram encodes information about the real form and dual form of the group.
- **Local systems** on nilpotent orbits carry sign data (p, n) recording signatures of the associated real forms.
- **Theta lifting** (Howe duality) relates representations across dual pairs (Sp-O, Mp-O), realized here as inductive algorithms on DRC diagrams and local systems.
- **Barbasch-Vogan duality** is a duality operation on nilpotent orbits implemented via symbols and sign twists.

### Root System Types

| Type | Group | Partition Parity |
|------|-------|-----------------|
| `C` | Sp(2n) - Symplectic group | Even-sized partition, good parity rows are even |
| `D` | SO(2n) - Even orthogonal group | Even-sized partition, good parity rows are odd |
| `B` | SO(2n+1) - Odd orthogonal group | Odd-sized partition, good parity rows are even |
| `M` | Mp(2n) - Metaplectic group | Even-sized partition, good parity rows are even |
| `CS` | Sp - compact/split variant | Odd-sized partition |
| `DS` | O* - quaternionic variant | Even-sized partition |

## Package Structure

```
combunipotent/
  __init__.py      # Package exports
  tool.py          # Core utilities: partitions, symbols, Springer correspondence, BV duality
  drc.py           # DRC diagram construction, verification, and display for all types
  LS.py            # Local systems: construction, lifting (theta correspondence), display
  drclift.py       # DRC-LS matching via theta lifting; main testing/verification framework
  lsdrcgraph.py    # Graphviz visualization of LS lifting graphs with DRC packet info
  liftgraph.py     # (Legacy) simpler LS lifting graph visualization
  recursive.py     # Recursive counting of unipotent representations via signature polynomials
```

### Module Descriptions

#### `tool.py` - Core Combinatorial Utilities
Fundamental operations on partitions and Weyl group representations:
- Partition operations: `reg_part`, `part_trans` (transpose), `part_size`, `BDcollapse`, `Ccollapse`
- Springer correspondence: `springer_part2repn`, `springer_repn2part`, `springer_part2family`
- Symbol calculus: `repn2symbol`, `symbol2repn`, `symbol2specialsymbol`, `symbol2family`
- Barbasch-Vogan duality: `dualBVW`, `tdualBV`, `tdualLS`, `tdSP`
- W-representation operations: `reg_W_repn`, `W_repn_sgn`, `repn2specialrepn`

#### `drc.py` - DRC Diagram Engine
Construction and manipulation of dot-r-c diagrams:
- Construction: `drc_dgms_C`, `drc_dgms_B`, `drc_dgms_D` (old API); `part2drc`, `dpart2drc` (unified API)
- Display: `str_dgms`, `str_dgms_C`, `str_dgms_B`
- Verification: `verify_drc`, `test_young_drc`, `test_bullets_drc`
- Form computation: `gp_form_C`, `gp_form_D`, `gp_form_B`, `gp_form_M`, `dual_form_C`, `dual_form_D`
- Filling algorithms: `fill_r`, `fill_c`, `fill_rdot` (generic pipeline for all types)
- Springer data: `S_Wrepn_B/C/D/M`, `S_Wrepns_B/C/D/M` (special orbit to coherent family)

#### `LS.py` - Local Systems and Theta Lifting
Local systems on nilpotent orbits and their theta lifts:
- Construction: `LS_C`, `LS_D`, `LS_B`, `LS_M`
- Theta lifting: `lift_D_C`, `lift_C_D`, `lift_B_M`, `lift_M_B` (and irreducible versions)
- Character twists: `char_twist_D`, `char_twist_B`, `_char_twist_C`, `_char_twist_M`
- Display: `str_LS`, `str_row_irr_LR`, `sign_LS`
- Unified API: `part2LS`

#### `drclift.py` - DRC-LS Matching and Theta Lifting Framework
The main verification and computation framework, matching DRC diagrams with local systems via theta lifting:
- DRC lifting: `lift_drc_D_C`, `lift_drc_C_D`, `lift_drc_M_B`, `lift_extdrc_B_M`
- Shape twisting: `twist_sp2nsp`, `twist_nsp2sp`, `twist_C_nonspecial`, `twist_M_nonspecial`
- Descent: `descent_drc`
- Testing: `test_LSDRC`, `test_dpart2drcLS`, `test_purelyeven`
- Packet display: `strLSpacket`, `getLSpacket`

#### `recursive.py` - Signature Polynomial Counting
Counting unipotent representations using recursive formulas with signature polynomials in p, q:
- `countB`, `countC`, `countD`, `countM`, `countCS`, `countDS`
- Returns (DD, RC, SS) triples tracking signature patterns
- Unified API: `countunip(partition, rtype)`

#### `lsdrcgraph.py` - Visualization
Generates Graphviz digraphs showing the theta lifting tree with DRC packet annotations.

## Data Structures

### Partitions
Partitions are represented as tuples of positive integers in decreasing order:
```python
part = (5, 3, 3, 1)  # partition of 12
```

### Weyl Group Representations (Bipartitions)
A W_n representation is a pair of partitions `(tauL, tauR)`:
```python
tau = ((3, 1), (2,))  # bipartition representing a W_n-representation
```

### DRC Diagrams
A DRC diagram is a pair `(drcL, drcR)` of tuples of strings. Each string represents a column:
- `*` (dot) - complex parameter
- `r` - real parameter (type 1)
- `s` - real parameter (type 2, dual to r)
- `c` - compact parameter
- `d` - discrete parameter (dual to c)

```python
drc = (('**rc', '*r', '*'), ('**s', '*', '*'))
# Display:
# . . . | . . .
# . r   | .
# r     | .
# c     |
```

### Local Systems
An irreducible local system is a tuple of (p, n) pairs:
```python
irr_s = ((2, 1), (0, 0), (1, 0))  # rows of lengths 1, 2, 3
```
A local system is a `FrozenMultiset` of irreducible local systems.

### Symbols
Symbols are pairs of sorted integer sequences used in the Springer correspondence:
```python
sym = ((0, 2, 4), (1, 3))  # symbol for type C
```

## Tutorials

See the Jupyter notebooks for interactive examples:
- [`tutor.ipynb`](tutor.ipynb) - Basic tutorial on DRC diagrams and local systems
- [`tutorial-twists.ipynb`](tutorial-twists.ipynb) - Character twists and non-special shapes
- [`test_unip_BM.ipynb`](test_unip_BM.ipynb) - Testing for types B and M
- [`Recursive.ipynb`](Recursive.ipynb) - Recursive counting formulas
- [`Package_document.ipynb`](Package_document.ipynb) - Package documentation examples

## Installation

```bash
pip install multiset graphviz sympy rich
```

The package requires:
- `multiset` - for FrozenMultiset (used as the local system container)
- `graphviz` - for visualization of lifting graphs
- `sympy` - for polynomial ring operations in recursive counting
- `rich` - for formatted console output

## Usage

```python
from combunipotent import *

# Compute DRC diagrams for a type C partition
drcs = dpart2drc((5, 3, 3, 1), rtype='C')

# Compute local systems
LSs = part2LS((4, 2, 2), rtype='C')

# Count unipotent representations
count = countunip((4, 2), rtype='D')

# Barbasch-Vogan duality
dual = dualBVW((5, 3, 1), rtype='C', partrc='c')

# Generate lifting graph visualization
svg = gen_lift_graph((5, 3, 3, 1), rtype='C')
```

## References

The mathematical foundations are based on the theory of:
- Arthur-Barbasch-Vogan parametrization of unipotent representations
- Springer correspondence for classical groups
- Howe's theta correspondence (dual pair lifting)
- Lusztig's symbols and special representations

## License

Research software by Jiajun Ma.

See the [GitHub repository](https://github.com/jiajunma/unipotentrepn) for updates.
