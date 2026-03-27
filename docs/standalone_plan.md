# Plan: standalone.py — Descent-Based DRC and Local System Computation

## Goal

Rewrite the DRC diagram and local system computation as a single self-contained
Python file `standalone.py`, using **only the descent algorithm** from
[BMSZ, arXiv:1712.05552v6] Section 3.3 (Definition 3.14) and
[BMSZb, arXiv:2205.05266v4] Section 10.3–10.4.

No lifting (theta correspondence) is used. The descent map
∇: PBP_★(Ǒ) → PBP_{★'}(Ǒ') is the sole inductive mechanism.

## Mathematical Summary

### Data Structures

1. **Young diagram** ι: tuple of row lengths in decreasing order, e.g. `(5,3,3,1)`.
   - `r_i(ι)`: i-th row length. `c_j(ι)`: j-th column length.
   - `|ι|` = total number of boxes.

2. **Painting** P on ι: assignment `P: Box(ι) → {•, s, r, c, d}` satisfying:
   - (1) Removing {d}, {c,d}, {r,c,d}, or {s,r,c,d} boxes leaves a valid Young diagram.
   - (2) Each row has at most one `s` and at most one `r`.
   - (3) Each column has at most one `c` and at most one `d`.

3. **Painted bipartition** τ = (ι, P) × (j, Q) × γ where:
   - (ι, P) and (j, Q) are painted Young diagrams
   - P and Q have the same set of •-boxes
   - γ ∈ {B+, B−, C, D, C̃, C*, D*}
   - Symbol constraints on P and Q depend on γ (Definition 3.3)

4. **Extended painted bipartition** τ = (τ, ℘) where ℘ ⊆ PP_★(Ǒ).

### Internal Representation

We use the **column-string representation** matching the existing codebase:
- `drc = (drcL, drcR)` where `drcL` and `drcR` are tuples of strings
- Each string represents a column; characters are `*`, `s`, `r`, `c`, `d`
- `drcL` = P (left painted diagram), `drcR` = Q (right painted diagram)
- γ stored separately as `rtype`

Position mapping: `P(i, j)` = `drcL[j-1][i-1]` (0-indexed: column j-1, row i-1).

### Root System Types

| Code | Paper ★ | Group G | Dual ★' | P symbols | Q symbols |
|------|---------|---------|---------|-----------|-----------|
| `B+` | B+ | O(p,q), p+q odd | C̃ | {•, c} | {•, s, r, d} |
| `B-` | B− | O(p,q), p+q odd | C̃ | {•, c} | {•, s, r, d} |
| `C` | C | Sp(2n) | D | {•, r, c, d} | {•, s} |
| `D` | D | O(p,q), p+q even | C | {•, s, r, c, d} | {•} |
| `M` | C̃ | Mp(2n) | B | {•, s, c} | {•, r, d} |

### The Descent Algorithm

The descent ∇: PBP_★(Ǒ) → PBP_{★'}(Ǒ') is defined in 3 steps:

#### Step 1: Compute the naive descent τ'_naive = ∇_naive(τ)

Two cases depending on ★:

**Case ★ ∈ {B, C, C*}** (Lemma 10.4 / Lemma 3.7a):
- Young diagrams: (ι', j') = (ι, ∇_naive(j)) — keep ι, remove first column from j
- For (i,j) ∈ Box(ι'):
  P'_naive(i,j) = • or s  if P(i,j) ∈ {•, s};  else P(i,j)
- For (i,j) ∈ Box(j'):
  Q'_naive(i,j) = • or s  if Q(i, j+1) ∈ {•, s};  else Q(i, j+1)
- γ' determined by (3.11):
  - If ★ = C̃ and c does NOT occur in first column of (ι,P): γ' = B+
  - If ★ = C̃ and c occurs in first column of (ι,P): γ' = B−
  - Otherwise: γ' = ★' (Howe dual)

**Case ★ ∈ {C̃, D, D*}** (Lemma 10.5 / Lemma 3.7b):
- Young diagrams: (ι', j') = (∇_naive(ι), j) — remove first column from ι, keep j
- For (i,j) ∈ Box(ι'):
  P'_naive(i,j) = • or s  if P(i, j+1) ∈ {•, s};  else P(i, j+1)
- For (i,j) ∈ Box(j'):
  Q'_naive(i,j) = • or s  if Q(i,j) ∈ {•, s};  else Q(i,j)
- γ' = ★' (Howe dual)

The "• or s" ambiguity is resolved by the interlacing condition: the •-boxes of
P' and Q' must coincide, and column lengths must interleave.

#### Step 2: Check for special corrections (Definition 3.14)

**Lemma 3.10** (★ = B+, special shape):
Conditions: γ = B+, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}.
Action: P'(c₁(ι'), 1) := s (override the naive descent at one position).

**Lemma 3.12** (★ = D, special shape):
Conditions: γ = D, r₂(Ǒ) = r₃(Ǒ) > 0, (P(c₂(ι),1), P(c₂(ι),2)) = (r, c),
P(c₁(ι), 1) ∈ {r, d}.
Action: P'(c₁(ι'), 1) := r (override the naive descent at one position).

#### Step 3: Non-special shapes

NOT implemented. This file only handles the special shape case (℘ = ∅),
following [BMSZ, arXiv:1712.05552v6] which does not discuss non-special shapes.

### Orbit and Bipartition Setup

Given a dual partition Ǒ with good parity and type ★:

1. Compute (ι_Ǒ, j_Ǒ) from Ǒ using the formulas in Section 3.1 (page 12).
2. Compute PP_★(Ǒ) — the set of primitive ★-pairs.
3. For each ℘ ⊆ PP_★(Ǒ), compute PBP_★(Ǒ, ℘) — the set of painted bipartitions.

### Inductive Construction

Starting from the trivial orbit |Ǒ| = 0:
- The unique PBP is the empty painted bipartition.
- Apply ∇ repeatedly to build up all PBPs for the target orbit.

Alternatively (and what we implement): for a given orbit Ǒ, directly enumerate
all painted bipartitions by:
1. Computing (ι_Ǒ, j_Ǒ) and PP_★(Ǒ).
2. For ℘ = ∅: enumerate PBP_★(Ǒ, ∅) using the filling algorithm (Definition 3.1).
3. For each ℘ ≠ ∅: use the shape-shifting bijection T_{℘,℘↑} from Section 10.2.

Then verify the descent map is well-defined by checking ∇(τ) ∈ PBP_{★'}(Ǒ').

## Implementation Plan

### Phase 1: Core Data Structures

```python
# Young diagram operations
def reg_part(part)           # Regularize partition
def part_trans(part)         # Transpose partition
def part_size(part)          # Sum of parts
def row_lengths(part)        # r_1 >= r_2 >= ...
def col_lengths(part)        # c_1 >= c_2 >= ...

# DRC diagram (painted bipartition) representation
# drc = (drcL, drcR) where drcL/drcR are tuples of column strings
# Each string: characters from {*, s, r, c, d}
def reg_drc(drc)             # Remove empty trailing columns
def str_dgms(drc)            # Display as ASCII art
def verify_drc(drc, rtype)   # Check all structural constraints
```

### Phase 2: Orbit to Bipartition

```python
def orbit_to_bipartition(dpart, rtype)
    # Compute (ι_Ǒ, j_Ǒ) from dual partition and type
    # Returns (tauL, tauR) column-length bipartition

def primitive_pairs(dpart, rtype)
    # Compute PP_★(Ǒ)

def dual_partition_to_Wrepns(dpart, rtype)
    # Enumerate all W-representations in the coherent family
```

### Phase 3: PBP Enumeration (Filling Algorithm)

```python
def fill_drc(tau, rtype)
    # Enumerate all painted bipartitions for the bipartition tau
    # Using the layered filling: d -> c -> r/s -> dots
    # This is Definition 3.1's constructive version
```

### Phase 4: Naive Descent

```python
def naive_descent(drc, rtype)
    # Implement Lemma 10.4 (★ ∈ {B, C, C*}) and
    # Lemma 10.5 (★ ∈ {C̃, D, D*})
    # Returns (drc', rtype')
```

### Phase 5: Full Descent

```python
def descent(drc, rtype, dpart)
    # Full descent = naive descent + corrections
    # Lemma 3.10 (B+ special), Lemma 3.12 (D special)
    # Section 10.4 cases (a), (b), (c) for each ★
    # Returns (drc', rtype', dpart')
```

### Phase 6: Shape Shifting (Non-special shapes)

```python
def twist_sp2nsp(drc, rtype)    # Special → non-special shape
def twist_nsp2sp(drc, rtype)    # Non-special → special shape
```

### Phase 7: Signature and Group Form

```python
def signature(drc, rtype)       # Compute (p_τ, q_τ)
def group_form(drc, rtype)      # Compute G_τ
def epsilon(drc, rtype)         # Compute ε_τ ∈ Z/2Z
```

### Phase 8: Main API

```python
def compute_all_pbp(dpart, rtype)
    # Main entry point: compute all PBP^ext_★(Ǒ)
    # Returns list of (drc, rtype, signature, epsilon)

def verify_descent_inverse(dpart, rtype)
    # Verify that descent is the inverse of lifting
    # for all PBPs attached to (dpart, rtype)
```

### Phase 9: Tests

```python
def test_against_existing()
    # Compare standalone results against combunipotent package
    # for a set of test partitions across all types
```

## File Structure

Single file `standalone.py` with:
1. Module docstring explaining the mathematical background
2. Core utilities (partitions, display)
3. DRC verification
4. Orbit → bipartition conversion
5. PBP enumeration
6. Naive descent
7. Full descent with corrections
8. Shape shifting
9. Signature computation
10. Main API and CLI interface
11. Test functions

## Verification Strategy

For each test partition and type:
1. Generate all PBPs using the filling algorithm
2. Apply descent to each PBP
3. Verify the descent result is a valid PBP of the dual type
4. Compare counts against `countunip` from the recursive module
5. Cross-check against `dpart2drc` from the existing codebase
