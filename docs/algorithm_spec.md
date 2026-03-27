# Algorithm Specification: standalone.py

Precise correspondence between `standalone.py` and the papers:

- **[BMSZ]** Barbasch–Ma–Sun–Zhu, *Special unipotent representations: construction and unitarity*, arXiv:1712.05552v6
- **[BMSZb]** Barbasch–Ma–Sun–Zhu, *Special unipotent representations: counting and reduction*, arXiv:2205.05266v4

---

## 1. Data Structures

### 1.1 Painted bipartition (PBP)

**Reference**: [BMSZb] Definition 2.24–2.25.

A PBP is τ = (ι, P) × (j, Q) × γ where:
- (ι, P) and (j, Q) are painted Young diagrams
- γ ∈ {B⁺, B⁻, C, D, M} is the type label (M = C̃)

**Code representation** (`drc`):
```
drc = (drcL, drcR)
```
where `drcL` and `drcR` are tuples of column strings. Each column string
is a sequence of symbols from {`*`, `s`, `r`, `c`, `d`}:
- `*` = dot (•)
- `s` = real type s
- `r` = real type r
- `c` = compact
- `d` = discrete

Example: `(('*rc', '*c'), ('**s', '*'))` means P has 2 columns (lengths 3, 2)
and Q has 2 columns (lengths 3, 1).

**Allowed symbols** ([BMSZb] Definition 2.25):

| γ | P (drcL) symbols | Q (drcR) symbols |
|---|---|---|
| B⁺ / B⁻ | {•, c} | {•, s, r, d} |
| C | {•, r, c, d} | {•, s} |
| D | {•, s, r, c, d} | {•} |
| M (= C̃) | {•, s, c} | {•, r, d} |

### 1.2 Extended PBP

**Reference**: [BMSZ] below Equation (3.15).

An extended PBP is τ̂ = (τ, ℘) where ℘ ⊆ PP_★(Ǒ) is a subset of
primitive pairs.

**Code representation**: `(drc, wp, rtype)` where:
- `drc`: painted bipartition as above
- `wp`: `frozenset` of PPidx integers (or `None` for ℘ = ∅)
- `rtype`: string `'B+'`, `'B-'`, `'C'`, `'D'`, or `'M'`

### 1.3 Marked Young Diagram (MYD)

**Reference**: [BMSZ] Definition 9.3, Equation (9.14).

A **marked Young diagram** (MYD) is a map N⁺ → Z × Z, i ↦ (pᵢ, qᵢ)
with finite support ([BMSZ] Definition 9.3). Each MYD parametrizes an
irreducible component of an admissible orbit datum via Equation (9.14).

An MYD is encoded as a tuple:

```
MYD = ((p₁, n₁), (p₂, n₂), ..., (pₖ, nₖ))
```

where `(pᵢ, nᵢ)` records the rows of length i. Before any twist,
pᵢ ≥ 0 is the count of +-marked rows and nᵢ ≥ 0 is the count of
−-marked rows. After character twist operations (Section 5 below),
pᵢ and nᵢ can become **negative**, encoding the twist as a sign change.
The absolute values |pᵢ|, |nᵢ| still give the row counts, and the
signs record the accumulated twist.

**Code naming**: In standalone.py, MYD tuples are called "ILS" (irreducible
local system) in function names: `_ils_sign`, `theta_lift_ils`, etc.
This reflects that each MYD parametrizes an irreducible LS component.

### 1.4 Local System (LS)

**Reference**: [BMSZ] Equation (9.28), Corollary 8.24.

A **local system** (LS) is a `FrozenMultiset` of MYD tuples, representing
an element of Z[MYD_★(O)] ([BMSZ] Equation (11.3)). Each element of the
multiset corresponds to one irreducible component of the associated cycle.

The LS attached to an extended PBP τ̂ is computed by `compute_AC` (Section 7).

---

## 2. Orbit and Good Parity

### 2.0 Good parity dual partition

**Reference**: [BMSZb] Section 2.4, Theorem 2.27.

A nilpotent orbit Ǒ in the Langlands dual Lie algebra is represented
by its **dual partition** `dpart = (r₁, r₂, ..., rₘ)` with r₁ ≥ r₂ ≥ ⋯ > 0.

Ǒ has **good parity** with respect to ★ if all its nonzero row lengths
have the same parity determined by ★:

| ★ | Good parity condition | Row lengths |
|---|----------------------|-------------|
| B, M (= C̃) | all rᵢ even | |
| C, D | all rᵢ odd | |

Additionally, the total size must satisfy:

| ★ | Total |
|---|-------|
| B | even (SO(2n+1), Ǒ in sp(2n)) |
| M | even (Mp(2n), Ǒ in so(2n+1)) |
| C | odd (Sp(2n), Ǒ in so(2n+1)) |
| D | even (SO(2n), Ǒ in sp(2n)) |

The main theorem ([BMSZb] Theorem 2.27) states:
```
#Unip_Ǒ(G) = 2^(#PP_★(Ǒ)) · #PBP_G(Ǒ)    if ★ ∈ {B, C, D, C̃}
```

Our implementation handles only good parity orbits. The reduction from
general orbits to good parity is described in [BMSZb] Section 9.

### 2.1 Primitive pairs: `compute_PPidx(dpart, rtype)` — Line 1158

**Reference**: [BMSZb] Definition 2.21.

Given dual partition Ǒ with row lengths r₁ ≥ r₂ ≥ ⋯, the **primitive
pairs** PP_★(Ǒ) are the pairs of adjacent rows where the row lengths
are strictly decreasing. Each primitive pair is indexed by an integer
(PPidx).

**For ★ ∈ {B, D}**: rows are paired starting from the second row:
```
PPidx i  ⟺  pair (r_{2i+1}, r_{2i+2})  with  r_{2i+1} > r_{2i+2} ≥ 0
```

**For ★ ∈ {C, M}**: rows are paired from the first row:
```
PPidx i  ⟺  pair (r_{2i}, r_{2i+1})  with  r_{2i} > r_{2i+1} ≥ 0
```

(Here rows use 0-based indexing after appropriate padding.)

A subset ℘ ⊆ PP_★(Ǒ) is represented as a `frozenset` of PPidx integers.

### 2.2 Bipartition: `dpart_to_bipartition(dpart, rtype)` — Line 76

**Reference**: [BMSZb] Equation (2.16), (8.9) with ℘ = ∅.

Given dual partition Ǒ and type ★, compute the special-shape bipartition
(ι_Ǒ, j_Ǒ). Returns `(tauL, tauR)`: column lengths of the two Young diagrams.

**For ★ = B**: first row r₁ contributes c₁(j) = r₁/2. Remaining rows are paired:
```
(c_i(ι), c_{i+1}(j)) = (r_{2i}/2, r_{2i+1}/2)    if PPidx i not in ℘
                      = (r_{2i+1}/2, r_{2i}/2)      if PPidx i ∈ ℘
```

**For ★ = D**: first row r₁ contributes c₁(ι) = (r₁+1)/2. Remaining rows:
```
(c_{i+1}(ι), c_i(j)) = ((r_{2i}+1)/2, (r_{2i+1}−1)/2)    if PPidx i not in ℘
```

**For ★ = C, M**: rows are paired directly (no first-row offset):
```
(c_i(ι), c_i(j)) = (r_{2i−1}/2, r_{2i}/2)              for M, PPidx i ∉ ℘
                  = ((r_{2i−1}+1)/2, (r_{2i}−1)/2)      for C, PPidx i ∉ ℘
```

### 2.3 All W-representations: `dpart2Wrepns_with_wp(dpart, rtype)` — Line 1204

**Reference**: [BMSZb] Equation (8.9), Section 8.3.

Computes all bipartitions labelled by ℘ ⊆ PP_★(Ǒ). For each ℘, the
bipartition is obtained by swapping the row pairs at positions in ℘.

Returns dict:
```
{ frozenset(PPidx subset) → bipartition (tauL, tauR) }
```

---

## 3. Signature and Epsilon

### `signature(drc, rtype)` — Line 688

**Reference**: [BMSZ] Equation (3.3); [BMSZb] Equation (2.17).

Computes (p_τ, q_τ) from symbol counts in the entire DRC:

**For ★ ∈ {B⁺, B⁻, D}**:
```
p = n_• + 2·n_r + n_c + n_d + [1 if γ = B⁺]
q = n_• + 2·n_s + n_c + n_d + [1 if γ = B⁻]
```

**For ★ ∈ {C, M}**:
```
p = q = n_• + n_r + n_s + n_c + n_d
```

### `epsilon(drc, rtype)` — Line 712

**Reference**: [BMSZ] Equation (3.6).

```
ε_τ = 0  ⟺  'd' occurs in the first column of P or Q
ε_τ = 1  otherwise
```

---

## 4. Descent Algorithm

### 4.1 Naive descent: `naive_descent(drc, rtype)` — Line 784

**Reference**: [BMSZ] Section 3.3, Lemma 3.7.

Computes τ'_naive by removing one column and redistributing •/s symbols.

| ★ | Column removed | Target type ★' | Redistribution |
|---|---------------|----------------|---------------|
| C | first col of Q (drcR) | D | `_fill_ds_D` |
| B⁺/B⁻ | first col of Q (drcR) | M | `_fill_ds_M` |
| D | first col of P (drcL) | C | `_fill_ds_C` |
| M | first col of P (drcL) | B⁺ or B⁻ | `_fill_ds_B` |

**★' for M → B** ([BMSZ] Equation (3.11)):
```
★' = B⁺  if 'c' does NOT occur in first column of P
   = B⁻  if 'c' occurs in first column of P
```

**Redistribution rule** ([BMSZ] Lemma 3.7):
The bipartition (ι', j') of τ'_naive is determined by removing one column.
Symbols r, c, d are preserved from the source (shifted by one position).
Positions with • or s are redistributed to satisfy the painting constraints
([BMSZb] Definition 2.25).

### 4.2 Descent for ℘ = ∅: `descent(drc, rtype)` — Line 833

**Reference**: [BMSZ] Section 3.3, Definition 3.14.

The descent ∇(τ) equals the naive descent τ'_naive unless the conditions
of Lemma 3.10 or Lemma 3.12 hold, in which case a correction is applied.

#### ★ = B⁺ correction (Lemma 3.10)

If γ = B⁺, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}:
```
P'(c₁(ι'), 1) := s
```
All other entries from P'_naive. Q' := Q'_naive.

Condition r₂(Ǒ) > 0 is checked as: DRC has ≥ 2 non-empty columns.

B⁻ has no corrections.

**B⁺ additional correction** (lines 891–904):

Reverses the lift algorithm's `tR='r' → nsR='d'` conversion when
P is "shorter" than Q's second column. Ported from
`combunipotent/drclift.py` lines 256–268.

#### ★ = D correction (Lemma 3.12 → generalized)

If γ = D, r₂(Ǒ) = r₃(Ǒ) > 0, P(c₂(ι), 2) = c,
P(i, 1) ∈ {r, d} for ALL c₂(ι) ≤ i ≤ c₁(ι):
```
P'(c₁(ι'), 1) := r
```
All other entries from P'_naive. Q' := Q'_naive.

Condition r₂ = r₃ > 0 is equivalent to c₂(ι) = c₁(j) + 1.

**Note**: [BMSZ] Lemma 3.12 checks only endpoints (P(c₂,1)=r and
P(c₁,1)∈{r,d}). The implementation uses the stronger condition from
[BMSZb] Section 10.4 which checks ALL intermediate entries. The two
formulations agree when ℘ = ∅ and no intermediate entry violates {r,d},
but the general condition is necessary for correctness with non-special
shapes.

#### ★ ∈ {C, M}: no correction

∇(τ) = τ'_naive.

### 4.3 Descent for general ℘ (relevant only for counting)

> *This section describes the general descent algorithm from [BMSZb]
> Section 10.4. It extends Section 4.2 to handle non-special shapes
> (℘ ≠ ∅). Readers interested only in the construction of
> representations ([BMSZ]) may skip this section.*

**Reference**: [BMSZb] Section 10.4.

The `descent` function accepts an optional `wp` parameter to handle
general ℘. When `wp` is provided, it determines (2,3) ∈ ℘ directly.
When `wp` is None, the DRC shape is used to infer (2,3) ∈ ℘:
- B type: `(2,3) ∈ ℘  ⟺  c₂(j) ≥ c₁(ι) + 2`
- D type: `(2,3) ∈ ℘  ⟺  c₂(ι) ≥ c₁(j) + 2`

#### ★ = B⁺

**(a)** γ = B⁺, (2,3) not in ℘, r₂(Ǒ) > 0, Q(c₁(ι_℘), 1) ∈ {r, d}
(same as the ℘ = ∅ case in Section 4.2):
```
P'(c₁(ι_{℘'}), 1) := s
```
All other entries from P'_naive. Q' := Q'_naive.

**(b)** γ = B⁺, (2,3) ∈ ℘, Q(c₂(j_℘), 1) ∈ {r, d}:
```
Q'(c₁(j_{℘'}), 1) := r
```
P' := P'_naive. Other Q' entries from Q'_naive.

**(c)** Otherwise: naive.

#### ★ = D

**(a)** (2,3) not in ℘, r₂ = r₃ > 0, P(c₂(ι_℘), 2) = c,
P(i, 1) ∈ {r, d} for ALL c₂(ι_℘) ≤ i ≤ c₁(ι_℘)
(same as the ℘ = ∅ case in Section 4.2):
```
P'(c₁(ι_{℘'}), 1) := r
```

**(b)** (2,3) ∈ ℘, P(c₂(ι_℘) − 1, 1) ∈ {r, c}:
```
P'(c₁(ι_{℘'}) − 1, 1) := r
P'(c₁(ι_{℘'}), 1) := P(c₂(ι_℘) − 1, 1)
```

**(c)** Otherwise: naive.

#### ★ ∈ {C, M}

**(a)** (1,2) not in ℘: naive.
**(b)** (1,2) ∈ ℘: shape shift first (Section 8), then naive.

---

## 5. MYD Operations

### `_ils_sign(myd)` — Line 1773

**Reference**: [BMSZ] Equation (9.10).

Signature (p, n) of MYD = ((p₁,n₁), ..., (pₖ,nₖ)):
```
For each row i (0-based), let (hrl, rrl) = divmod(i+1, 2):
  p += |pᵢ|·(hrl + rrl) + |nᵢ|·hrl
  n += |nᵢ|·(hrl + rrl) + |pᵢ|·hrl
```

### `_ils_firstcol_sign(myd)` — Line 1783

**Reference**: [BMSZ] Equation (9.12), first column of Lemma 9.2.

First-column signature:
```
For i even (0-based):  p += |pᵢ|, n += |nᵢ|
For i odd:             p += |nᵢ|, n += |pᵢ|
```

### `_ils_twist_BD(myd, twist)` — Line 1796

**Reference**: [BMSZ] Equation (9.15), sign twist operation.

Determinant twist with `twist = (tp, tn)` where tp, tn ∈ {1, −1}.

Acts on odd-length rows (0-based i where (i+1) is odd):
```
tpp = tp^(hrl+1) · tn^hrl
tnn = tn^(hrl+1) · tp^hrl
(pᵢ, nᵢ) → (tpp·pᵢ, tnn·nᵢ)
```
Even-length rows are unchanged.

Common cases:
- `(1, −1)`: ⊗ 1⁺'⁻ twist (B/D post-twist when ε_τ = 1)
- `(−1, −1)`: ⊗ det twist (C/M pre-twist when ε_℘ = 1)
- `(1, 1)`: identity

### `_ils_char_twist_CM(myd, j)` — Line 1821

**Reference**: [BMSZ] Equation (9.16)–(9.17), involution T.

Character twist T^j: negate entries at positions i where (i+1) ≡ 2 (mod 4),
but only when j is odd. T² = identity.

Equivalence with LS.py:
```
_char_twist_C(myd, ps, ns) = _ils_char_twist_CM(myd, (ps−ns)//2)
```

---

## 6. Theta Lifting of MYD

### `theta_lift_ils(myd, rtype, p, q)` — Line 1837

**Reference**: [BMSZ] Equations (9.29)–(9.30), Section 9.5.

Theta lift of a single MYD to target type ★ with target signature (p, q).
Implements ϑ̌ from Equation (9.29) for ★ ∈ {B, D} and (9.30) for ★ ∈ {C, C̃}.

In all cases, first compute:
```
(ps, ns) = _ils_sign(irr_s)       # source signature
(fps, fns) = _ils_firstcol_sign(irr_s)  # first-column signature
```

#### D → C (target Sp(2n), n = p = q)

```
addp = n − ps − fns
addn = n − ns − fps
```

**Descent case** (addp ≥ 0 and addn ≥ 0):
```
irr_ss = ((addp, addn),) + irr_s           # prepend new row
return [_ils_char_twist_CM(irr_ss, (ps−ns)//2)]   # then twist
```

**Generalized descent** ((addp,addn) ∈ {(−1,−1), (−2,0), (0,−2)}):
Split first row into two branches:
```
if pp₀ > 0: ((0,0), (pp₀−1, nn₀)) + irr_s[1:]  then twist
if nn₀ > 0: ((0,0), (pp₀, nn₀−1)) + irr_s[1:]  then twist
```

#### C → D (target O(p,q), p+q even)

```
addp = p − ps − fns
addn = q − ns − fps
```

**Descent case** (addp ≥ 0 and addn ≥ 0):
```
irr_s_tw = _ils_char_twist_CM(irr_s, (p−q)//2)  # twist first
return [((addp, addn),) + irr_s_tw]               # then prepend
```

Note: order is **twist then prepend** (opposite of D→C).

#### B → M (target Mp(2n), n = p = q)

Same structure as D→C but twist parameter is `(ps−ns−1)//2` instead of `(ps−ns)//2`.

#### M → B (target O(p,q), p+q odd)

Same structure as C→D but twist parameter is `(p−q+1)//2` instead of `(p−q)//2`.

### `theta_lift_ls(ls, rtype, p, q)` — Line 1920

Lifts each MYD in the `FrozenMultiset` independently:
```
result = []
for irr_s in ls:
    result.extend(theta_lift_ils(irr_s, rtype, p, q))
return FrozenMultiset(result)
```

### `twist_ls(ls, twist)` — Line 1941

Apply `_ils_twist_BD` to every MYD in the multiset.

---

## 7. Associated Cycle (LS Computation)

### `compute_AC(drc, wp, rtype, cache=None)` — Line 1978

**Reference**: [BMSZ] Equation (3.16), (11.2).

Computes AC(τ̂) for extended PBP τ̂ = (τ, ℘, ★) via recursive descent.

#### Base case (|Ǒ| = 0)

The return value is a list of `(multiplicity, MYD)` pairs.

| rtype | Base LS | Meaning |
|-------|---------|---------|
| B⁺ | `[(1, ((1, 0),))]` | 1 × MYD with one row of length 1 marked + |
| B⁻ | `[(1, ((0, −1),))]` | 1 × MYD with one row of length 1 marked − |
| C, D, M | `[(1, ())]` | 1 × empty MYD (trivial representation) |

#### Recursive step

1. Compute ε_℘ ([BMSZ] below Equation (3.16)):
   ε_℘ = 1  ⟺  (1,2) ∈ ℘.
   In code: `e_wp = 1 if (wp is not None and 0 in wp) else 0`,
   since PPidx 0 corresponds to the pair (1,2).
2. Descend ℘: `℘' = ∇̃(℘)` via `_descend_wp`.
3. Compute (p_τ, q_τ) = `signature(drc, rtype)`.
4. Compute ε_τ = `epsilon(drc, rtype)`.
5. Descent DRC: `(drc', ★') = descent(drc, rtype)`.
6. Recursively compute `source_AC = compute_AC(drc', ℘', ★')`.

Then for each `(mult, myd)` in source_AC:

**★ ∈ {C, M}** ([BMSZ] Eq. 3.16 case 2):
```
if ε_℘ = 1:
    myd = _ils_twist_BD(myd, (−1, −1))     # pre-twist by det
lifted = theta_lift_ils(myd, rtype, p_τ, q_τ)
# No post-twist for C/M
```

**★ ∈ {B⁺, B⁻, D}** ([BMSZ] Eq. 3.16 case 1):
```
# No pre-twist for B/D
lifted = theta_lift_ils(myd, rtype, p_τ, q_τ)
if ε_τ ≠ 0:
    lifted = _ils_twist_BD(lifted, (1, −1))  # post-twist by 1⁺⁻
```

### `_descend_wp(wp, rtype)` — Line 1271

**Reference**: [BMSZ] Equation (3.15); [BMSZb] Section 10.4.

The paper's definition is type-independent:
```
∇̃(℘) := { (i, i+1) : (i+1, i+2) ∈ ℘ }
```
i.e., each pair shifts down by 1 in the row numbering.

In the code, PPidx encoding differs between C/M and B/D (see Section 2.1),
so the index shift depends on the source type:
```
C/M → D/B:  PPidx i maps to PPidx (i−1), discard i=0
B/D → C/M:  PPidx i maps to PPidx i (no shift)
```

---

## 8. Lifting Tree Visualization

### `gen_lift_tree(dpart, rtype, format, filename)` — Line 2628

Generates two Graphviz graphs:
1. **LS lift graph** (`{filename}.svg`): nodes grouped by LS value
2. **Extended PBP descent tree** (`{filename}_ext.svg`): one node per extended PBP

#### 8.1 Tree construction (lines 2669–2703)

Recursively build the extended PBP tree from top-level DRCs down to the
trivial group:
- Start from all DRCs × all ℘ subsets × {B⁺, B⁻} (for B type)
- At each node: `descent(drc, rtype)` gives the parent
- Base case: empty DRC with type ∈ {C, M, D}

For B/M type: B⁺ and B⁻ both descent to Mp(0) = (empty, M), forming
a single connected tree.

#### 8.2 LS computation (lines 2705–2750)

BFS from root upward. At each child node:

```
source_ls = parent_ls
if child is C/M and ε_℘ = 1:
    source_ls = twist_ls(parent_ls, (−1, −1))  # det pre-twist
target_ls = theta_lift_ls(source_ls, child_rtype, p, q)
if child is B/D and ε_τ ≠ 0:
    target_ls = twist_ls(target_ls, (1, −1))    # 1⁺⁻ post-twist
```

This is equivalent to `compute_AC` but computed bottom-up instead of
top-down.

#### 8.3 LS lift graph node labels

Each node in the LS lift graph represents one LS value (FrozenMultiset).
Multiple extended PBPs with the same LS are grouped into one node.

**Node contents**:
1. **MYD visual**: the marked Young diagram pattern (+/−/*/=)
2. **Per-DRC entries**: for each extended PBP with this LS:
   - `(p,q)`: signature from `signature(drc, rtype)`
   - DRC diagram with red-colored columns for ℘
   - B⁺/B⁻ label (for B type)
   - ε value: `epsilon(drc, rtype)` for B/D, ε_℘ for C/M

**℘ column coloring** ([BMSZb] Equation (8.9)):

| Type | PPidx i → red columns |
|------|----------------------|
| C/M | column i of both L and R |
| D | column (i+1) of L, column i of R |
| B | column i of L, column (i+1) of R |

#### 8.4 Edges

**Lift edges** (blue, solid): represent `theta_lift_ls(source, ★, p, q)`.

For ★ ∈ {B, D}: L_τ = θ(L_{∇τ}) ⊗ (0, ε_τ).
- ε_τ = 0: draw blue edge `L_{∇τ} → θ(L_{∇τ}) = L_τ`.
- ε_τ ≠ 0: draw blue edge `L_{∇τ} → θ(L_{∇τ})`.
  The target `θ(L_{∇τ})` may be a ghost node. L_τ is then reached
  via `θ(L_{∇τ}) →[1⁺⁻ twist]→ L_τ`.

For ★ ∈ {C, M}: L_τ = θ(L_{∇τ} ⊗ (ε_℘, ε_℘)).
- ε_℘ = 0: draw blue edge `L_{∇τ} → θ(L_{∇τ}) = L_τ`.
- ε_℘ = 1: draw blue edge `(L_{∇τ} ⊗ det) → L_τ`.
  The source `L_{∇τ} ⊗ det` may be a ghost node.

**Character twist edges** (same level, bidirectional):
- Red: det twist `(−1, −1)`
- Green: 1⁺⁻ twist `(1, −1)`
- Purple: 1⁻⁺ twist `(−1, 1)`

**Ghost nodes**: LS values that appear as det-twisted variants of real
LS nodes but are not realized by any extended PBP. Shown with gray
background. Grouped in dotted boxes with their twist-related nodes.

#### 8.5 Layout

- `rankdir=TB`: small groups at top, large groups at bottom
- Group labels (Sp(2n), O(2n+1), etc.) on the left
- Nodes colored by type: blue=C, green=M, orange=D, red=B

---

The following sections describe algorithms from [BMSZb] that are relevant
only for counting and the PBP bijection. They are not needed to understand
the construction of representations in [BMSZ].

## 9. PBP Bijection

### `build_pbp_bijection(dpart, rtype)` — Line 1288

**Reference**: [BMSZb] Propositions 10.2, 10.8, 10.9; Corollary 10.10.

Builds bijection ⊔_℘ PBP(Ǒ, ℘) ↔ PBP(Ǒ, ∅) × 2^PP.

Returns `(bijection, table)` where:
- `bijection[drc] = (special_shape_drc, frozenset(℘))`
- `table[frozenset(℘)] = [list of DRCs in PBP(Ǒ, ℘)]`

#### C/M types (shape shift + descent)

**Reference**: [BMSZb] Proposition 10.8; Section 10.2 (shape shifting).

For τ ∈ PBP(Ǒ, ℘):

1. If (1,2) ∈ ℘:
   shape shift τ → τ₁ ∈ PBP(Ǒ, ℘ \ {(1,2)}) via `twist_nsp2sp` (C) or
   `twist_M_nonspecial` (M).

2. If ℘ = ∅ after step 1: bijection[τ] = (τ₁, original ℘). Done.

3. Otherwise: descent τ₁ → τ' ∈ PBP(Ǒ', ℘').
   Recursively biject τ' → τ'' ∈ PBP(Ǒ', ∅).
   Find τ₀ ∈ PBP(Ǒ, ∅) with `(∇(τ₀), γ') = (τ'', γ'_of_τ₁)`.

**Key**: The descent lookup key includes γ' (B⁺/B⁻ tag) to avoid
collisions when two different DRCs descent to the same DRC with
different γ' values.

#### B/D types (Corollary 10.10)

**Reference**: [BMSZb] Corollary 10.10.

The map τ ↦ (∇τ, p_τ, q_τ, ε_τ) is injective on PBP_★(Ǒ).

For τ ∈ PBP(Ǒ, ℘):
1. Compute (∇τ, sig, ε) where ε = 0 if tail symbol is 'd', else 1.
2. Recursively biject ∇τ → τ'' ∈ PBP(Ǒ', ∅).
3. Find τ₀ ∈ PBP(Ǒ, ∅) with `(∇τ₀ mapped to ∅, sig(τ₀), ε(τ₀)) = (τ'', sig, ε)`.

---

## 10. Tail Symbol

### `compute_tail_symbol(drc, rtype, dpart)` — Line 2211

**Reference**: [BMSZ] Section 11.2, Equation (11.5); [BMSZb] Section 10.5.

Computes x_τ ∈ {c, d, r, s} for ★ ∈ {B, D}.

The tail τ_t consists of cells in the first column of P (for D) or Q (for B)
that extend beyond the other diagram's columns.

**For ★ = D**: x_τ is the last entry in fL (P's first column) when the tail
has length > 1. For length ≤ 1, special handling for r₂ = r₃ case.

**For ★ = B**: x_τ is the last entry in fR (Q's first column) when the tail
has length > 1. For length ≤ 1, correction based on B⁺/B⁻.

---

## 11. Recursive Counting

### `countPBP(dpart, rtype)` — Line 2299

**Reference**: [BMSZb] Propositions 10.11–10.12.

Counts #PBP_★(Ǒ, ∅) recursively. Since #PBP is independent of ℘
(Proposition 10.2), this also gives #PBP for any ℘.

**For D/B types**: returns decomposition (DD, RC, SS) counting PBPs by
tail symbol: DD = #{x_τ = d}, RC = #{x_τ ∈ {c,r}}, SS = #{x_τ = s}.

Recursive formula based on whether (2,3) is a primitive pair.

**For C/M types**: reduces to D/B counting via descent:
```
#PBP_C(Ǒ) = DD_D(Ǒ[1:]) + RC_D(Ǒ[1:]) + [SS_D(Ǒ[1:]) if (1,2) primitive]
```

---

## 12. Descent Chain

### `descent_chain(drc, rtype, dpart)` — Line 2092

Computes the full descent chain from τ down to the trivial group.
Returns list of `(drc, rtype, signature, epsilon, dpart)` tuples.

**Base case**: `total == 0 and rtype in ('C', 'M', 'D')`.
For B/M chains, B⁺/B⁻ at O(1) descends one more step to Mp(0),
ensuring a single connected tree.

### `orbit_descent(dpart, rtype)` — Line 2065

**Reference**: [BMSZ] Equation (3.10).

```
Ǒ' = ∇̂_★(Ǒ) = Ǒ with first row removed
Special case: if ★ = D and |Ǒ| = 0, then Ǒ' = (1,)
```

