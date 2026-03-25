# Recursive Counting of Painted Bipartitions

This document summarizes the recursive counting formulas from [BMSZb] Section 10.6
(Propositions 10.11-10.14) and their implementation in `recursive.py`.

## Setup

For ★ ∈ {B, D, C*}, the generating function counts PBPs by signature:

```
f_{★,Ǒ,℘}(p,q) := Σ_{τ ∈ PBP_★(Ǒ,℘)} p^{p_τ} q^{q_τ}
```

For ★ ∈ {B, D}, each PBP has a "tail symbol" x_τ ∈ {c, d, r, s}. Define:

```
PBP^S_★(Ǒ,℘) := { τ ∈ PBP_★(Ǒ,℘) | x_τ ∈ S }
f^S_{★,Ǒ,℘}(p,q) := Σ_{τ ∈ PBP^S_★(Ǒ,℘)} p^{p_τ} q^{q_τ}
```

Total: `f = f^{d} + f^{c,r} + f^{s}`.

## Tail and Tail Symbol

Reference: [BMSZb] Section 10.5.

### Definition of the tail τ_t

Given a PBP τ = (P, Q) for ★ ∈ {B, D}:

- **★ = B**: c₁(ι) ≤ c₁(j). The tail τ_t consists of cells in Q's first column
  from row c₁(ι)+1 to row c₁(j). That is, the cells in Q beyond the length of P's
  first column.

- **★ = D**: c₁(ι) ≥ c₁(j). The tail τ_t consists of cells in P's first column
  from row c₁(j)+1 to row c₁(ι). That is, the cells in P beyond the length of Q's
  first column.

Here c₁(ι) = len(P[0]) and c₁(j) = len(Q[0]) are the lengths of the first columns.

### Tail signature (p_{τ_t}, q_{τ_t})

The tail signature sums per-cell contributions over all cells in τ_t:

```
Cell symbol → (Δp, Δq):
  •  → (1, 1)
  r  → (2, 0)
  s  → (0, 2)
  c  → (1, 1)
  d  → (1, 1)
```

Reference: [BMSZ] Lemma 11.3, equation (11.10).

In code: `compute_tail_signature(drc, rtype)` in `standalone.py`.

### Tail symbol x_τ

The tail symbol x_τ := P_{τ_t}(k, 1) is the symbol in the **last box** of the tail τ_t.
x_τ ∈ {c, d, r, s}.

#### ★ = B (types B, B+, B-)

Let q_{c₁(ι)} = Q(c₁(ι), 1) be the symbol at position c₁(ι) in Q's first column.

- If c₁(ι) = 0 or q_{c₁(ι)} ∈ {•, s}:
  - B+ → x_τ = c
  - B- → x_τ = s
- Otherwise: x_τ = q_{c₁(ι)}

#### ★ = D

- If c₁(ι) = c₁(j) = 0 (empty orbit): x_τ = d
- Otherwise let p_{c₁(j)+1} = P(c₁(j)+1, 1) be the symbol at position c₁(j)+1 in P's first column.
- **Special case** (scattered tail, r₂ = r₃ > 0):
  If the last symbol in P's first column is r or d, and (P(c₁(j)+1, 1), P(c₁(j)+1, 2)) = (r, c),
  then x_τ = c.
- **General case**: x_τ = p_{c₁(j)+1}

In code: `compute_tail_symbol(drc, rtype, dpart)` in `standalone.py`.

## Lusztig left cells and the bipartitions (ι_℘, j_℘)

Reference: [BMSZb] Section 8.3, Proposition 8.3.

### Overview

For each orbit Ǒ with good parity and each ℘ ∈ A(Ǒ) (a subset of primitive pairs
PP_★(Ǒ)), formula (8.9) defines a pair of Young diagrams (ι_℘, j_℘).

Proposition 8.3 establishes a bijection:

```
Ā(Ǒ) → ᴸC_Ǒ,    ℘̄ ↦ τ_b ⊗ τ_℘̄
```

where ᴸC_Ǒ is the Lusztig left cell, τ_b is the irreducible representation of W_b
attached to Ǒ_b, and τ_{℘̄} = (ι_℘, j_℘) ∈ Irr(W'_g).
The special representation corresponds to ℘ = ∅.

### Primitive pairs PP_★(Ǒ)

Primitive pairs are pairs of consecutive row indices (1-based) of Ǒ:

```
★ = B:   PP_B(Ǒ) = { (2i, 2i+1) | r_{2i}(Ǒ) > r_{2i+1}(Ǒ), i ≥ 1 }
★ = D:   PP_D(Ǒ) = { (2i, 2i+1) | r_{2i}(Ǒ) > r_{2i+1}(Ǒ), i ≥ 1 }
★ = C:   PP_C(Ǒ) = { (2i-1, 2i) | r_{2i-1}(Ǒ) > r_{2i}(Ǒ), i ≥ 1 }
★ = M:   PP_M(Ǒ) = { (2i-1, 2i) | r_{2i-1}(Ǒ) > r_{2i}(Ǒ), i ≥ 1 }
```

### Formula (8.9): bipartition (ι_℘, j_℘) by type

Below, r_i denotes the i-th row length of Ǒ (1-based), and column lengths
c_i(ι), c_i(j) define the Young diagrams ι_℘, j_℘.

#### ★ = B

The first row is treated separately:

```
c₁(j_℘) = r₁/2
```

For each subsequent pair (2i, 2i+1), i ≥ 1:

```
(c_i(ι_℘), c_{i+1}(j_℘)) = {
    (r_{2i+1}/2, r_{2i}/2),   if (2i, 2i+1) ∈ ℘;
    (r_{2i}/2,   r_{2i+1}/2), otherwise.
}
```

#### ★ = D

The first row is treated separately:

```
c₁(ι_℘) = (r₁+1)/2
```

For each subsequent pair (2i, 2i+1), i ≥ 1:

```
(c_i(j_℘), c_{i+1}(ι_℘)) = {
    ((r_{2i+1}-1)/2, (r_{2i}+1)/2),   if (2i, 2i+1) ∈ ℘;
    ((r_{2i}-1)/2,   (r_{2i+1}+1)/2), otherwise.
}
```

#### ★ = C

No special first row. For each pair (2i-1, 2i), i ≥ 1:

```
(c_i(j_℘), c_i(ι_℘)) = {
    ((r_{2i}-1)/2,   (r_{2i-1}+1)/2), if (2i-1, 2i) ∈ ℘;
    (0, 0),                            if (2i-1, 2i) is vacant (r_{2i-1} = 0);
    ((r_{2i-1}-1)/2, 0),               if (2i-1, 2i) is tailed (r_{2i-1} > 0, r_{2i} = 0);
    ((r_{2i-1}-1)/2, (r_{2i}+1)/2),   otherwise.
}
```

#### ★ = M (C̃)

No special first row. For each pair (2i-1, 2i), i ≥ 1:

```
(c_i(ι_℘), c_i(j_℘)) = {
    (r_{2i}/2,   r_{2i-1}/2), if (2i-1, 2i) ∈ ℘;
    (r_{2i-1}/2, r_{2i}/2),   otherwise.
}
```

### Implementation: `dualpart2LC` in `drc.py`

The function `dualpart2LC(part, rtype)` takes a dual partition (row lengths of Ǒ)
and returns a dictionary `{ frozenset(℘) → bipartition(ι_℘, j_℘) }`.

**Padding conventions** (to make pairing uniform):

| Type | Condition | Padding | Purpose |
|------|-----------|---------|---------|
| B | even # parts | append 0 | ensure odd length (first row special) |
| D | even # parts | append -1 | ensure odd length; -1 trick: (−1+1)/2 = 0 |
| C | odd # parts | append -1 | ensure even length; vacant pair gives (0,0) |
| M | odd # parts | append 0 | ensure even length; 0/2 = 0 |

**Indexing**: Code PPidx `i` corresponds to:
- Types B, D: paper pair (2i+2, 2i+3) — i.e., starting from (2,3) after removing first row
- Types C, M: paper pair (2i+1, 2i+2) — i.e., starting from (1,2)

**Column length formulas in code**:

For B, M (integer division by 2):

```
Not in ℘:  tauL[i] = part[2i]   // 2,  tauR[i] = part[2i+1] // 2
In ℘:      tauL[i] = part[2i+1] // 2,  tauR[i] = part[2i]   // 2
```

For C, D (half-integer shift, then integer division):

```
Not in ℘:  tauL[i] = (part[2i+1]+1) // 2,  tauR[i] = (part[2i]-1) // 2
In ℘:      tauL[i] = (part[2i]+1)   // 2,  tauR[i] = (part[2i+1]-1) // 2
```

Note: `tauL` = column lengths of ι_℘, `tauR` = column lengths of j_℘.

**Verification**: `dualpart2LC` values match `dualpart2Wrepn` output (set equality)
for all types and all tested dual partitions.

## Shape shifting for types C and C̃

Reference: [BMSZb] Section 10.2, Lemma 10.3.

### Setup

Let ★ ∈ {C, C̃} and Ǒ an orbit with good parity such that (1,2) ∈ PP_★(Ǒ).
Let ℘ ⊆ PP_★(Ǒ) with (1,2) ∉ ℘. Put ℘↑ := ℘ ∪ {(1,2)}.

The shape shifting map T_{℘,℘↑} : PBP_G(Ǒ,℘) → PBP_G(Ǒ,℘↑) is a bijection.
Given τ = (ι_℘, P_τ) × (j_℘, Q_τ) × α ∈ PBP_G(Ǒ,℘), we define
τ↑ = (ι_{℘↑}, P_{τ↑}) × (j_{℘↑}, Q_{τ↑}) × ℘↑.

Note the column length changes:

```
★ = C:   (c₁(ι_{℘↑}), c₁(j_{℘↑})) = (c₁(j_℘) + 1, c₁(ι_℘) - 1)
★ = C̃:  (c₁(ι_{℘↑}), c₁(j_{℘↑})) = (c₁(j_℘), c₁(ι_℘))
```

### The case ★ = C (forward: sp → nsp, i.e. `twist_C_nonspecial`)

Special shape: 0 < c₁(P) ≤ c₁(Q).
Non-special shape: c₁(P) ≥ c₁(Q) + 2.

Let l = c₁(Q) - c₁(P) ≥ 0. The twist extends P's first column by (l+1) rows and
shortens Q's first column by (l+1) rows.

Let x₃ = Q(c₁(P), 1) be the symbol in Q's first column at position c₁(P)
(i.e. `fR[-(l+1)]`). Then:

**(a) P(c₁(P), 1) ≠ • (equivalently x₃ = s):**

- If c₁(P) = 1 or P(c₁(P)-1, 1) ≠ c:
  - P' first column = P[: c₁(P)-1] + r^{l+1} + P[c₁(P)-1]
- If P(c₁(P)-1, 1) = c (i.e. fL ends with 'cd'):
  - P' first column = P[: c₁(P)-2] + r^{l+1} + P[c₁(P)-2 :]   (preserves the 'cd' ending)
- Q' first column = Q[: c₁(P)-1]   (remove last l+1 symbols)
- Other columns unchanged.

**(b) P(c₁(P), 1) = • (equivalently x₃ = •):**

- If P's second column has length > c₁(P)-1 and P(c₁(P), 2) = r:
  - P' first column = P[: c₁(P)-1] + r^l + r + d
  - P' second column = sL[: -1] + c
- Otherwise:
  - P' first column = P[: c₁(P)-1] + r^l + c + d
  - P' second column unchanged
- Q' first column = Q[: c₁(P)-1]
- Other columns unchanged.

In code: `twist_C_nonspecial(drc)` in both `standalone.py` and `drclift.py`.

### The case ★ = C (inverse: nsp → sp, i.e. `twist_nsp2sp`)

Non-special shape: c₁(P) ≥ c₁(Q) + 2.
Let l = c₁(P) - c₁(Q) - 2 ≥ 0. The inverse shortens P's first column and extends Q's.

**(a) P(c₁(P)-1, 1) = c (i.e. fL[-2] = 'c'):**

- Sub-case: c₁(Q) > 0 and P(c₁(Q), 1) = r (look at `fL[len(fR)-1]`):
  - P' first column = P[: c₁(Q)-1] + c + d
  - Q' first column = Q + s^{l+1}
- Sub-case otherwise:
  - P' first column = P[: c₁(Q)] + •
  - Q' first column = Q + • + s^l

**(b) P(c₁(P)-1, 1) = r (i.e. fL[-2] = 'r'):**

- Sub-case: c₁(Q)+1 = len(sL) and (sL[-1], fL[-1]) = (c, d):
  - P' first column = P[: c₁(Q)] + •
  - P' second column = sL[: c₁(Q)] + r
  - Q' first column = Q + • + s^l
- Sub-case otherwise:
  - P' first column = P[: c₁(Q)] + fL[-1]
  - Q' first column = Q + s^{l+1}

In code: `twist_nsp2sp(drc, 'C')` in `drclift.py`.

### The case ★ = C̃ (M type)

The shape shifting for C̃ is much simpler: it swaps the first columns of P and Q
with the symbol translation c ↔ d, r ↔ s.

For τ = (P, Q), define τ↑ = (P', Q') where:

```
P'(i, 1) = translate(Q(i, 1)):   s → r,  c → d,  r → s,  d → c
Q'(i, 1) = translate(P(i, 1)):   s → r,  c → d,  r → s,  d → c
P'(i, j) = P(i, j)  for j ≥ 2
Q'(i, j) = Q(i, j)  for j ≥ 2
```

This corresponds to the paper's formulas (10.3) and (10.4):

```
P_{τ↑}(i, j) = { s   if j=1 and Q_τ(i,1) = r;
                  c   if j=1 and Q_τ(i,1) = d;
                  P_τ(i,j)  otherwise.

Q_{τ↑}(i, j) = { r   if j=1 and P_τ(i,1) = s;
                  d   if j=1 and P_τ(i,1) = c;
                  Q_τ(i,j)  otherwise.
```

The map is an involution (applying it twice gives the identity) since the translation
c ↔ d, r ↔ s is self-inverse.

In code: `twist_M_nonspecial(drc)` in both `standalone.py` and `drclift.py`.
Translation implemented via `str.maketrans('cdrs', 'dcsr')`.

### Verification summary

| Paper | Code function | Direction |
|-------|--------------|-----------|
| T_{℘,℘↑} for C | `twist_C_nonspecial` | special → non-special |
| T_{℘↑,℘}⁻¹ for C | `twist_nsp2sp(drc,'C')` | non-special → special |
| T_{℘,℘↑} for C̃ | `twist_M_nonspecial` | self-inverse (special ↔ non-special) |

## Descent of a painted bipartition (Section 10.4)

Reference: [BMSZb] Section 10.4.

### Dual descent of ℘

```
℘' := ∇̃(℘) = { (i, i+1) | i ∈ N⁺, (i+1, i+2) ∈ ℘ } ⊆ PP_{★'}(Ǒ')
```

### Young diagram pair (ι_{℘'}, j_{℘'})

The descent target bipartition depends on ★ and whether (1,2) ∈ ℘:

```
(ι_{℘'}, j_{℘'}) =
  (ι_℘, ∇_naive(j_℘)),           if ★ = B, or ★ ∈ {C, C*} and (1,2) ∉ ℘;
  (ι_{℘↓}, ∇_naive(j_{℘↓})),     if ★ ∈ {C, C*} and (1,2) ∈ ℘;
  (∇_naive(ι_℘), j_℘),           if ★ ∈ {D, D*}, or ★ = C̃ and (1,2) ∉ ℘;
  (∇_naive(ι_{℘↓}), j_{℘↓}),     if ★ = C̃ and (1,2) ∈ ℘.
```

where ℘↓ = ℘ \ {(1,2)}.

### The γ' tag

```
γ' = B+    if α = C̃ and c does not occur in first column of (ι, P);
     B-    if α = C̃ and c occurs in first column of (ι, P);
     ★'    if α ≠ C̃.
```

### Naive descent (Lemma 10.4 / 10.5)

**Lemma 10.4** (★ ∈ {B, C, C*}): remove first column of Q.
- (ι', j') = (ι, ∇_naive(j))
- P'_naive(i,j) = • or s if P(i,j) ∈ {•, s}; else P(i,j)
- Q'_naive(i,j) = • or s if Q(i, j+1) ∈ {•, s}; else Q(i, j+1)

**Lemma 10.5** (★ ∈ {C̃, D, D*}): remove first column of P.
- (ι', j') = (∇_naive(ι), j)
- P'_naive(i,j) = • or s if P(i, j+1) ∈ {•, s}; else P(i, j+1)
- Q'_naive(i,j) = • or s if Q(i,j) ∈ {•, s}; else Q(i,j)

### Descent corrections by type

#### ★ = B (general algorithm, [BMSZb] Section 10.4)

**(a)** If γ = B+, (2,3) ∉ ℘, r₂(Ǒ) > 0, Q(c₁(ι_℘), 1) ∈ {r, d}:
- P'(c₁(ι_{℘'}), 1) := s. Other entries from P'_naive.
- Q' := Q'_naive.

**(b)** If γ = B+, (2,3) ∈ ℘, Q(c₂(j_℘), 1) ∈ {r, d}:
- P' := P'_naive.
- Q'(c₁(j_{℘'}), 1) := r. Other entries from Q'_naive.

**(c)** Otherwise: P' := P'_naive, Q' := Q'_naive.

#### ★ = B, special shape ([BMSZ] Lemma 3.10)

When ℘ = ∅, Lemma 3.10 from the construction paper gives:

If γ = B+, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}:
- P'(c₁(ι'), 1) := s. Other entries from P'_naive.
- Q' := Q'_naive.

At ℘ = ∅, (2,3) ∉ ℘ is automatic, so Lemma 3.10 matches general (a) exactly.
r₂(Ǒ) > 0 ⟺ DRC has ≥ 2 non-empty columns.

#### ★ = D (general algorithm, [BMSZb] Section 10.4)

**(a)** If r₂(Ǒ) = r₃(Ǒ) > 0, P(c₂(ι_℘), 2) = c,
    P(i, 1) ∈ {r, d} for all c₂(ι_℘) ≤ i ≤ c₁(ι_℘):
- P'(c₁(ι_{℘'}), 1) := r. Other entries from P'_naive.
- Q' := Q'_naive.

**(b)** If (2,3) ∈ ℘, P(c₂(ι_℘) - 1, 1) ∈ {r, c}:
- P'(c₁(ι_{℘'}) - 1, 1) := r.
- P'(c₁(ι_{℘'}), 1) := P(c₂(ι_℘) - 1, 1).
- Other entries from P'_naive.
- Q' := Q'_naive.

**(c)** Otherwise: P' := P'_naive, Q' := Q'_naive.

#### ★ = D, special shape ([BMSZ] Lemma 3.12)

When ℘ = ∅ (special shape), Lemma 3.12 from the construction paper gives:

If γ = D, r₂(Ǒ) = r₃(Ǒ) > 0, (P(c₂(ι), 1), P(c₂(ι), 2)) = (r, c),
P(c₁(ι), 1) ∈ {r, d}:
- P'(c₁(ι'), 1) := r. Other entries from P'_naive.
- Q' := Q'_naive.

Definition 3.14 ([BMSZ]): ∇(τ) := τ' (corrected) if Lemma 3.10 or 3.12
conditions hold; τ'_naive otherwise.

#### Analysis: Lemma 3.12 vs general (a) at ℘ = ∅

| Condition | Lemma 3.12 ([BMSZ]) | General (a) ([BMSZb]) |
|-----------|---------------------|----------------------|
| r₂ = r₃ > 0 | ✓ | ✓ |
| P(c₂, 2) | = c (via pair (r,c)) | = c |
| P(c₂, 1) | = r | ∈ {r, d} (from range check) |
| Intermediate P(i,1), c₂ < i < c₁ | NOT checked | ALL must be ∈ {r, d} |
| P(c₁, 1) | ∈ {r, d} | ∈ {r, d} (from range check) |

Lemma 3.12 is WEAKER on intermediates (doesn't check them) but STRONGER
at c₂ (requires P(c₂,1)=r, not just ∈{r,d}).

Counterexample: Ǒ = (5,1,1,1), DRC = (('rcd','c'), ()):
- c₂ = 1, c₁ = 3, P entries at rows 1..3 = [r, c, d].
- Lemma 3.12: (P(1,1), P(1,2)) = (r, c) ✓, P(3,1) = d ∈ {r,d} ✓ → applies.
- General (a): P(2,1) = c ∉ {r,d} → does NOT apply.

There are 45 such discrepancy DRCs across all D partitions up to size 16.
In all discrepancy cases, Lemma 3.12 applies but general (a) does not.

**Resolution**: `descent()` implements Lemma 3.12 (from [BMSZ]) for the special
shape case. `descent_general()` implements the full [BMSZb] Section 10.4 algorithm
for arbitrary ℘. When operating on special-shape DRCs (as in the lift tree),
Lemma 3.12 is the authoritative reference.

#### ★ ∈ {C, C̃, C*, D*}

**(a)** If (1,2) ∉ ℘: τ' := ∇_naive(τ).

**(b)** If (1,2) ∈ ℘, then ★ ∈ {C, C̃} (by Prop 10.1):
  - τ' := ∇_naive(τ_{℘↓}), where τ_{℘↓} := T⁻¹_{℘↓,℘}(τ) (inverse shape shift).

### Implementation status

Two functions:
- `descent(drc, rtype)` — special shape (℘=∅), follows [BMSZ] Lemma 3.10/3.12
- `descent_general(drc, rtype)` — general ℘, follows [BMSZb] Section 10.4

| Case | `descent` (special) | `descent_general` (general) |
|------|--------------------|-----------------------------|
| B (a): B+, (2,3)∉℘ | ✓ Lemma 3.10 | ✓ Section 10.4 |
| B (b): B+, (2,3)∈℘ | N/A (℘=∅) | ✓ Section 10.4 |
| B (c): otherwise | ✓ fallthrough | ✓ fallthrough |
| D (a): r₂=r₃, correction | ✓ Lemma 3.12 | ✓ Section 10.4 (full range check) |
| D (b): (2,3)∈℘ | ✓ (shape-based) | ✓ Section 10.4 |
| D (c): otherwise | ✓ fallthrough | ✓ fallthrough |
| C/M (a): (1,2)∉℘ | ✓ naive | ✓ naive |
| C/M (b): (1,2)∈℘ | N/A (℘=∅) | ✓ via shape shift |

4. **D case (b)**: Handled implicitly via `len(sL) >= len(fR)+2` (non-special
   shape detection). Needs verification against paper for correctness.

5. **`compute_tail_symbol` for D type**: Returns P(c₁(j)+1, 1) (the FIRST
   tail symbol), but x_τ = P_{τ_t}(k, 1) should be the LAST box of the tail.
   Bug: for D type with k > 1, the function returns x₁ instead of x_k.
   This affects Cor 10.10 ε computation.

## Lifting graph design (WIP)

### Input

- Dual partition `dpart`, root type `rtype` ∈ {B, C, D, M}
- Compute PP = PP_★(Ǒ) from `dpart`
- Compute DRCs = `dpart2drc(dpart, rtype)` — special shape (℘=∅)

### Extended PBP enumeration

An extended PBP is a triple (drc, ℘, ★) where:
- drc ∈ DRCs (always special shape)
- ℘ ⊆ PP (any subset of primitive pairs)
- ★ = rtype (for B, expand to B+ and B-)

Total count: |DRCs| × 2^|PP| × (2 if B, 1 otherwise)

### Step 1: Build the extended PBP descent tree

For each extended PBP (drc, ℘, ★), recursively descent:
- drc' = descent(drc, ★)
- ℘' = ∇̃(℘) = {(j-1, j) : (j, j+1) ∈ ℘, j ≥ 2}
- ★' = Howe dual of ★
- DRC is always special shape; ℘ descent is independent of DRC descent

The descent tree, read bottom-up, is the **lifting tree**.
Root = empty DRC (base case).

### Step 2: Build lifting tree as a data structure

The lifting tree is the descent tree read bottom-up. Each tree node stores:

```
TreeNode:
    extended_pbp: (drc, ℘, ★)       # the extended PBP at this node
    parent: TreeNode or None         # descent target (= lift source)
    children: list of TreeNode       # all extended PBPs that descent to this node
    ls: FrozenMultiset of ILS        # the local system L_τ = AC(τ̂)
```

**Construction**: for each extended PBP (drc, ℘, ★):
- Compute descent: (drc', ℘', ★') where drc' = descent(drc, ★), ℘' = ∇̃(℘)
- Find the tree node for (drc', ℘', ★') → that is the **parent**
- The current node is a **child** of the parent
- Root nodes: extended PBPs with empty DRC (base case)

**Relationship**: (drc, ℘, ★) is a **lift** of (drc', ℘', ★') iff
descent(drc, ℘, ★) = (drc', ℘', ★').

### Step 3: Compute LS at each node (bottom-up)

Walk the tree from root (leaves of descent = base case) upward:

**Base case** (root, empty DRC):
- α_τ = B+: L_τ = FrozenMultiset([((1, 0),)])
- α_τ = B-: L_τ = FrozenMultiset([((0, -1),)])
- Otherwise: L_τ = FrozenMultiset([()])

**Lifting step** — parent (drc', ℘', ★') → child (drc, ℘, ★):
1. source_LS = parent.ls
2. If ★ ∈ {C, M} and (1,2) ∈ ℘: pre-twist source_LS by ⊗(1,1)
3. target_LS = theta_lift_ls(source_LS, ★, p_τ, q_τ)
4. If ★ ∈ {B, D} and ε_τ ≠ 0: post-twist target_LS by ⊗(0, ε_τ)
5. child.ls = target_LS

### Step 3: Draw the graph

**Nodes**: each node = one LS (FrozenMultiset of ILS).
- Multiple extended PBPs mapping to the same LS → same node.
- Node label: signature (p,q), ILS visual, list of (drc, ℘) in this LS.

**Lift edges** (blue arrows):
- If LS₁ = theta_lift_ls(LS₂, ...), draw arrow LS₂ → LS₁.

**Character twist nodes/edges** (B/D only):
- For each B/D LS, compute:
  - det twist (-1,-1): red
  - (1,-1) twist: green
  - (-1,1) twist: purple
- If twist = self: skip (or note invariance)
- If twist = another existing LS: connect with colored edge
- If twist = new LS: ghost node (no DRC, dashed border)

**Layout**:
- rankdir = BT (small groups top, large groups bottom)
- Group labels (Sp(2n), O(p+q), SO(p+q), Mp(2n)) on the left
- B+ and B- on the same row

### Visual representation of extended PBP

An extended PBP (drc, ℘, ★) needs a clear visual encoding of ℘.

**Type C/M**: PP_★(Ǒ) ⊆ {(1,2), (3,4), (5,6), ...}.
- (1,2) ∈ ℘: color column 1 of drcL and drcR **red**
- (3,4) ∈ ℘: color column 2 of drcL and drcR **red**
- (2k-1, 2k) ∈ ℘: color column k of drcL and drcR **red**

The red columns indicate which column pairs would be swapped under
shape shifting (special ↔ non-special). The DRC itself stays in
special shape; red marking shows which ℘ elements are "active".

**Type D**: PP_★(Ǒ) ⊆ {(2,3), (4,5), (6,7), ...}.
- (2i, 2i+1) ∈ ℘: color column (i+1) of drcL and column i of drcR **red**
- E.g., (2,3) ∈ ℘: drcL col 2 + drcR col 1

**Type B**: PP_★(Ǒ) ⊆ {(2,3), (4,5), (6,7), ...}.
- (2i, 2i+1) ∈ ℘: color column i of drcL and column (i+1) of drcR **red**
- E.g., (2,3) ∈ ℘: drcL col 1 + drcR col 2

These conventions match [BMSZb] equation (8.9): the red columns are exactly
the column pairs that would swap under the ℘-dependent bipartition change
(ι_℘, j_℘) vs (ι_∅, j_∅).

### Comparison plan: standalone vs lsdrcgraph.py

**Context**: `lsdrcgraph.py` builds a lifting graph using DRCs from
⊔_℘ PBP(Ǒ, ℘) (all shapes), while `standalone.py` uses
PBP(Ǒ, ∅) × powerset(PP(Ǒ)) (special shape + ℘ label).

These are related by the bijection BIJ established in `build_pbp_bijection`:

```
BIJ: ⊔_℘ PBP(Ǒ, ℘) ↔ PBP(Ǒ, ∅) × powerset(PP(Ǒ))
     drc_℘            ↦ (drc_∅, ℘)
```

**What to verify**:

1. **Lift edges match**: If `lsdrcgraph.py` draws an arrow from LS node A
   to LS node B, then `standalone.py` draws the same arrow (between the
   corresponding LS nodes under BIJ).

2. **LS grouping matches**: DRCs drc₁, ..., drc_k are in the same node in
   `lsdrcgraph.py` iff BIJ(drc₁), ..., BIJ(drc_k) are in the same node
   in `standalone.py`.

**Verification steps**:

Step 1: For a given (dpart, rtype), generate both graphs:
  - `lsdrcgraph.py`: produces nodes = {LS → [drc₁, ..., drc_k]}
  - `standalone.py`: produces nodes = {LS → [(drc_∅, ℘)₁, ..., (drc_∅, ℘)_k]}

Step 2: Compute BIJ via `build_pbp_bijection(dpart, rtype)`:
  - For each drc_℘ in lsdrcgraph's node, compute BIJ(drc_℘) = (drc_∅, ℘)
  - Check that all BIJ images land in the same standalone node

Step 3: Compare LS values:
  - For each drc_℘ in lsdrcgraph, compute its LS (via lsdrcgraph's method)
  - For the corresponding (drc_∅, ℘) in standalone, compute its LS
    (via compute_AC(drc_∅, ℘, rtype))
  - Verify they are equal

Step 4: Compare edges:
  - Collect all (src_LS, dst_LS) lift edges from both graphs
  - Verify the edge sets are equal

**Key files**:
- `standalone.py`: `gen_lift_tree`, `build_pbp_bijection`, `compute_AC`
- `combunipotent/lsdrcgraph.py`: the reference lifting graph implementation
- `combunipotent/drclift.py`: DRC lifting (generates ⊔_℘ PBP)

### TODO / Open questions

- [ ] `compute_AC` should return FrozenMultiset, not list of (coeff, ILS)
- [ ] `theta_lift_ls` should take and return FrozenMultiset
- [ ] Sign twist ⊗(1,1) for C/M: is this `twist_ls(ls, (-1,-1))`?
- [ ] Sign twist ⊗(0,ε) for B/D: is this `twist_ls(ls, (1,-1))`?
- [ ] Verify: does the lifting tree give the same LS as `compute_AC`?
- [ ] Implement the comparison test (Steps 1-4 above)

## Notation

In `recursive.py`:
- `r = p², s = q²` (correspond to signature contributions of r and s symbols)
- `c = d = pq` (correspond to signature contributions of c and d symbols)
- `ν_k = Σ_{i=0}^k p^{2i} q^{2(k-i)}` if k ≥ 0, else 0

In the code: `rs_n(r, s, n) = ν_n` (when called with `r=p², s=q²`).

## Base cases

### Type D, empty orbit [0]_row

```
f^{d}_{D,[0],∅} = 1,  f^{c,r}_{D,[0],∅} = 0,  f^{s}_{D,[0],∅} = 0
```

In code: `countD(()) = (R(1), R(0), R(0))`.

### Type B, single even row [2k]_row

```
f^S_{B,[2k],∅} = { (p²q + pq²)ν_{k-1},     if S = {d};
                    pν_k + p²qν_{k-1},       if S = {c,r};
                    q^{2k+1},                  if S = {s} }
```

In code: `countB((2k,))` base case.

## Tail polynomials for ★ ∈ {B, D}

For a ★-pair (1,2) with rows (R₁, R₂), let k = (R₁-R₂)/2 + 1.

### Tail ending with d, rc, s

```
TDD = ν_{k-1}·d + ν_{k-2}·cd     (= rs_n(r,s,n-1)*d + rs_n(r,s,n-2)*c*d)
TRC = ν_{k-1}·c + r·ν_{k-1}       (= rs_n(r,s,n-1)*c + r*rs_n(r,s,n-1))
TSS = s^k                          (= q^{2k})
```

### Scattered tail (when (2,3) is balanced)

```
scDD = ν_{k-2}·cd + s·ν_{k-2}·d
scRC = ν_{k-1}·c + s·ν_{k-2}·r
scSS = s^k
```

## Proposition 10.11: ★ ∈ {B, D}, r₂(Ǒ) > 0

Let k := (r₁(Ǒ) - r₂(Ǒ))/2 + 1, S = {d}, {c,r}, or {s}.

### (a) If (2,3) ∈ PP_★(Ǒ) [primitive pair]

```
f^S_{★,Ǒ,℘} = (pq)^{c₁(Ǒ)} · f^S_{D,[2k-1,1]_row,∅} · f_{★,∇̃²(Ǒ),∇̃²(℘)}
```

In code: this is the `R2 > R3` branch with `resp = (p^C2 * q^C2) * (DDp+RCp+SSp)`.

### (b) If (2,3) ∉ PP_★(Ǒ) [balanced pair]

```
f^S_{★,Ǒ,℘} = (pq)^{c₁(Ǒ)-1} · (f^S_{D,[2k-1,1]_row,∅} · f^{d}_{★,∇̃²(Ǒ),∇̃²(℘)}
                                  + h^S_k · f^{c,r}_{★,∇̃²(Ǒ),∇̃²(℘)})
```

In code: this is the `R2 <= R3` branch.

## Proposition 10.12: ★ ∈ {C, C̃}, r₁(Ǒ) > 0

### (a) If (1,2) ∈ PP_★(Ǒ)

```
#PBP_★(Ǒ,℘) = f_{★',∇̃(Ǒ),∇̃(℘)}(1,1)
```

### (b) If (1,2) ∉ PP_★(Ǒ)

```
#PBP_★(Ǒ,℘) = f^{c,r}_{★',∇̃(Ǒ),∇̃(℘)}(1,1) + f^{d}_{★',∇̃(Ǒ),∇̃(℘)}(1,1)
```

In code: `countC` and `countM` use these formulas.

## Key consequence

For ★ ∈ {B, C, C̃, D}: the generating function `f_{★,Ǒ,℘}` is INDEPENDENT of ℘.
Therefore:

```
#PBP_★(Ǒ,℘) = #PBP_★(Ǒ,∅)   for all ℘ ⊆ PP_★(Ǒ)
```

## Correspondence with `recursive.py`

| Paper | Code | Description |
|-------|------|-------------|
| ν_k | `rs_n(r,s,k)` | p²ⁱq²⁽ᵏ⁻ⁱ⁾ sum |
| f^{d}, f^{c,r}, f^{s} | `DD, RC, SS` | triple returned by `countD`, `countB` |
| f (total) | `evalsignature(DD,RC,SS)` | DD+RC+SS |
| #PBP | `f(1,1)` | evaluate at p=q=1 |
| Prop 10.12 | `countC`, `countM` | C/M counting |

## Multiplicity note

For ★ ∈ {B, D}: the generating function counts PBP_★(Ǒ,℘).
The total number of special unipotent representations is:
- `2 · #PBP^ext_G(Ǒ)` when (★,|Ǒ|) ≠ (D,0)  (Theorem 3.16)
- `#PBP^ext_G(Ǒ)` otherwise

Since `#PBP^ext = #PBP × 2^{|PP|}` for B/D, and the det twist doubles,
the DRC count from `dpart2drc` should satisfy:

```
For C, M:  #DRC = f(1,1)
For B:     #DRC × 2 = f(1,1) × 2^{|PP|}    (DRC has no ℘, but includes B+/B-)
For D:     #DRC × 2 = f(1,1) × 2^{|PP|}    (det twist doubles)
```

Verified relationship:

```
For C, M:  #DRC = f(1,1)
For D:     #DRC = f(1,1) × 2^{|PP|}
For B:     #DRC = f(1,1) × 2^{max(|PP|-1, 0)}
```

For D type: `dpart2Wrepns` generates `2^{|PP|}` bipartitions, each with the same
number of DRC diagrams. Since `f(1,1)` counts PBP for one ℘ and `#PBP(℘)` is
independent of ℘ (Proposition 10.2), `#DRC = f(1,1) × 2^{|PP|}`.

For B type: the first PP pair (2,3) is absorbed into the B+/B- split (which is
already part of the W-representation enumeration via the distinguished first row),
so one factor of 2 is consumed: `#DRC = f(1,1) × 2^{|PP|-1}` when |PP| ≥ 1.
