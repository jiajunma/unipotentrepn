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

Given dual partition Ǒ and type ★, compute the bipartition (ι_Ǒ, j_Ǒ) with ℘ = ∅.
This corresponds to the **special representation** of the Weyl group. [BMSZ] works
exclusively with special representations; the general ℘ ≠ ∅ case (Section 2.3)
extends to all W-representations. Returns `(tauL, tauR)`: column lengths of the
two Young diagrams.

All row indices below are 1-based: r₁ ≥ r₂ ≥ ⋯.

**For ★ = B**: first row r₁ contributes c₁(j) = r₁/2. Remaining rows are paired
(i = 1, 2, ...):
```
(c_i(ι), c_{i+1}(j)) = (r_{2i}/2, r_{2i+1}/2)
```

**For ★ = D**: first row r₁ contributes c₁(ι) = (r₁+1)/2. Remaining rows
(i = 1, 2, ...):
```
vacant  (r_{2i} = r_{2i+1} = 0):  skip
tailed  (r_{2i} > 0, r_{2i+1} = 0):  c_i(j) = (r_{2i}−1)/2
normal:  (c_i(j), c_{i+1}(ι)) = ((r_{2i}−1)/2, (r_{2i+1}+1)/2)
```

**For ★ = M**: rows are paired directly (i = 1, 2, ...):
```
(c_i(ι), c_i(j)) = (r_{2i−1}/2, r_{2i}/2)
```

**For ★ = C**: rows are paired directly (i = 1, 2, ...):
```
vacant  (r_{2i−1} = r_{2i} = 0):  skip
tailed  (r_{2i−1} > 0, r_{2i} = 0):  c_i(j) = (r_{2i−1}−1)/2
normal:  (c_i(j), c_i(ι)) = ((r_{2i−1}−1)/2, (r_{2i}+1)/2)
```
Note: for C, tauR corresponds to j (using `(r_{odd}−1)/2`) and tauL to ι
(using `(r_{even}+1)/2`).

### 2.3 All W-representations: `dpart2Wrepns_with_wp(dpart, rtype)` — Line 1204

**Reference**: [BMSZb] Equation (8.9), Section 8.3.

Computes all bipartitions (ι_℘, j_℘) labelled by ℘ ⊆ PP_★(Ǒ). For each ℘,
the bipartition is obtained from the ℘ = ∅ formulas (Section 2.2) by swapping
the row pair at each PPidx i ∈ ℘.

Returns dict:
```
{ frozenset(PPidx subset) → bipartition (tauL, tauR) }
```

**Padding**: rows are padded to make pairing uniform:

| Type | Condition | Pad | Purpose |
|------|-----------|-----|---------|
| B | even # rows | append 0 | first row is special |
| D | even # rows | append −1 | (−1+1)/2 = 0 trick |
| M | odd # rows | append 0 | ensure even count |
| C | odd # rows | append −1 | ensure even count |

After padding, for B/D the first row is split off; remaining rows form pairs.
For C/M all rows form pairs directly.

**PPidx enumeration** (0-based):

For ★ ∈ {B, D}: after removing the first row, pair rows at (2i+1, 2i+2).
PPidx i is primitive iff rows[2i+1] > rows[2i+2] ≥ 0.

For ★ ∈ {C, M}: pair rows at (2i, 2i+1).
PPidx i is primitive iff rows[2i] > rows[2i+1] ≥ 0.

**Bipartition formulas**: for each pair at PPidx i, when i ∉ ℘ the formula
is identical to Section 2.2. When i ∈ ℘, the two row values swap:

**★ ∈ {B, M}** (integer division by 2):
```
i ∉ ℘:  (c(ι), c(j)) = (rows[2i]   // 2,  rows[2i+1] // 2)
i ∈ ℘:  (c(ι), c(j)) = (rows[2i+1] // 2,  rows[2i]   // 2)
```

**★ ∈ {D, C}** (half-integer shift):
```
i ∉ ℘:  (c(ι), c(j)) = ((rows[2i+1]+1)//2,  (rows[2i]−1)//2)
i ∈ ℘:  (c(ι), c(j)) = ((rows[2i]+1)//2,    (rows[2i+1]−1)//2)
```

Here `rows` refers to the post-padding, post-first-row-removal array (for B/D)
or the post-padding array (for C/M). Column lengths are sorted decreasingly
and zeros are stripped to produce the final bipartition.

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

#### 8.3 Three output graphs

`gen_lift_tree` produces three SVG files:

| File | Description |
|------|-------------|
| `{name}.svg` | LS lift graph: one node per LS value, ext PBPs merged inside |
| `{name}_ext.svg` | Extended PBP descent tree: one node per ext PBP |
| `{name}_comb.svg` | Combined: LS headers with ext PBPs hanging below, plus descent edges |

#### 8.4 Nodes

**LS lift graph** (`{name}.svg`):
Each node = one LS value (FrozenMultiset). Contains:
1. MYD visual (the marked Young diagram pattern)
2. All extended PBPs with this LS, each showing:
   - `(p,q)` signature, B⁺/B⁻ label, ε value
   - DRC diagram with red columns for ℘

**Combined graph** (`{name}_comb.svg`):
Two kinds of nodes:
1. **LS header** (colored box): shows signature(s) `(p,q)` and MYD visual
2. **Ext PBP** (white box): shows B⁺/B⁻, ε, DRC diagram with red ℘ columns

LS headers connect to their ext PBPs via gray arrows (parent→child).

**Det twist nodes** (gray box): LS values obtained by det twist of real
LS nodes, not realized by any ext PBP. Placed beside (same rank as)
real LS headers.

**℘ column coloring** ([BMSZb] Equation (8.9)):

| Type | PPidx i → red columns |
|------|----------------------|
| C/M | column i of both L and R |
| D | column (i+1) of L, column i of R |
| B | column i of L, column (i+1) of R |

#### 8.5 Edges

**Blue edges (theta lift)**: represent `theta_lift_ls(source, ★, p, q)`.

For ★ ∈ {B, D}: L_τ = θ(L_{∇τ}) ⊗ (0, ε_τ).
- ε_τ = 0: blue edge `L_{∇τ} → θ(L_{∇τ}) = L_τ`.
- ε_τ ≠ 0: blue edge `L_{∇τ} → θ(L_{∇τ})`.
  Target θ(L_{∇τ}) may be a det twist node. L_τ is reached via
  θ(L_{∇τ}) →[1⁺⁻ twist edge]→ L_τ.

For ★ ∈ {C, M}: L_τ = θ(L_{∇τ} ⊗ (ε_℘, ε_℘)).
- ε_℘ = 0: blue edge `L_{∇τ} → θ(L_{∇τ}) = L_τ`.
- ε_℘ = 1: blue edge `(L_{∇τ} ⊗ det) → L_τ`.
  Source L_{∇τ} ⊗ det may be a det twist node.

**Character twist edges** (same level, bidirectional):
- Red: det twist (−1, −1)
- Green: 1⁺⁻ twist (1, −1)
- Purple: 1⁻⁺ twist (−1, 1)

Only drawn at B/D levels between real LS headers and det twist nodes.

**Gray dashed edges** (combined graph only): DRC descent edges connecting
individual ext PBP nodes across levels. One edge per parent→child pair
in the extended PBP descent tree.

**Gray solid arrows** (combined graph only): LS header → ext PBP,
showing which ext PBPs belong to each LS.

**Twist orbit clusters** (combined graph only): dashed box grouping
twist-related LS headers, det twist nodes, and their ext PBPs.

#### 8.6 Layout

- `rankdir=TB`: small groups at top, large groups at bottom
- Within same DRC total: C/M levels above B/D levels
  (parent above child in descent direction)
- Combined graph sub-levels per B/D group:
  - B/D_mid: LS headers + det twist nodes (same rank, side by side)
  - B/D_bot: ext PBP nodes
- Group labels (Sp(2n), O(2n+1), etc.) on the left
- Node colors: blue=#e6f3ff (C), green=#e6ffe6 (M),
  orange=#fff3e6 (D), red=#ffe6e6 (B), gray=#f0f0f0 (det twist)

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


---

> *The following sections describe the reference implementation in
> `combunipotent/drclift.py` and `combunipotent/lsdrcgraph.py`.
> These are independent of [BMSZ] — they implement the inductive
> theta lifting algorithm used to verify standalone.py.*

## 13. DRC Lifting (drclift.py)

The module `combunipotent/drclift.py` implements inductive theta lifting
of DRC diagrams. Given a DRC at a smaller group, it constructs all
possible DRCs at the next larger group by attaching a new column.

### 13.1 Lifting functions

Each lift direction has a dedicated function:

| Function | Direction | Input | Output |
|----------|-----------|-------|--------|
| `lift_drc_D_C(drc, cR)` | D → C | D-type DRC, column length | one C-type DRC |
| `lift_drc_D_C_gd(drc)` | D → C | D-type DRC (generalized descent) | one C-type DRC or None |
| `lift_drc_C_D(drc, a)` | C → D | C-type DRC, column length | list of (D-type DRC, twist) |
| `lift_extdrc_B_M(drc, a)` | B → M | B-type extended DRC, col length | one M-type DRC or None |
| `lift_drc_M_B(drc, a)` | M → B | M-type DRC, column length | list of (B-type extended DRC, twist) |

The C→D and M→B lifts return **(DRC, twist)** pairs where `twist ∈ {(1,1), (1,−1), (−1,1), (−1,−1)}`
indicates the character twist applied to the LS.

### 13.2 lift_DRCLS: simultaneous DRC + LS lifting

`lift_DRCLS(DRCLS, LSDRC, dpart, rtype)` lifts all DRC-LS pairs from
one level to the next. For each source `(drc, LS)`:

**C target** (D → C):
1. Compute target Sp(2n) rank from dual partition
2. Lift DRC: `ndrc = lift_drc_D_C(drc, crow)` (standard) or `lift_drc_D_C_gd(drc)` (generalized)
3. Lift LS: `nLS = lift_D_C(LS, n)`
4. If (1,2) is a primitive pair: also lift det twist `dLS = char_twist_D(LS, (−1,−1))`,
   `ndLS = lift_D_C(dLS, n)`, and the DRC becomes non-special via `twist_sp2nsp`

**D target** (C → D):
1. Lift DRC: `NDRCS = lift_drc_C_D(drc, crow)` → list of (ndrc, twist) pairs
2. For each (ndrc, twist): compute signature `(pO, nO) = gp_form_D(ndrc)`,
   lift LS `nLS = lift_C_D(LS, pO, nO)`, apply twist `nLS = char_twist_D(nLS, twist)`

**M and B targets**: similar structure with `lift_extdrc_B_M` / `lift_drc_M_B`.

### 13.3 test_dpart2drcLS: full induction from dual partition

`test_dpart2drcLS(dpart, rtype)` iterates over the dual partition rows
from bottom to top, alternating between Howe dual types (D↔C or B↔M).
At each step it calls `lift_DRCLS` and verifies the result against
independently computed DRCs (`dpart2drc`) and LS values (`part2LS`).

Returns `(lDRCLS, lLSDRC)` where `lDRCLS[0]` is the final level's
`{drc → LS}` mapping.

## 14. Lifting Graph: lsdrcgraph.py

The original implementation in `combunipotent/lsdrcgraph.py` generates the
lifting graph using a **bottom-up theta lifting** approach, in contrast to
standalone.py's **top-down descent** approach.

### 14.1 Architecture

`gen_lift_graph(part, rtype)` takes a **special partition** (group side,
not dual partition) and orchestrates three steps:

1. **`test_purelyeven(part, rtype)`** (in `drclift.py`):
   Iteratively lifts DRC and LS from small groups to the target group.
   At each step, `lift_pedrcs` lifts both the DRC (via `lift_drc_*`)
   and the LS (via `lift_*_*` from `LS.py`). Returns `(lDRCLS, lLSDRC)`:
   - `lDRCLS`: list of `{drc → frozenset(LS)}` dicts at each level
   - `lLSDRC`: list of `{LS → (signature, packet)}` dicts

2. **`LS_graph(tdict, part, rtype)`** (in `lsdrcgraph.py`):
   Recursively builds the LS lifting tree. For C/M types, removes one
   row and lifts from the Howe dual type. For B/D types, iterates over
   all possible signatures (p,q) at the target level.
   Records edges in `tdict`: `{(rtype, partsize, LS) → set of sources}`.

3. **`tdict_LSDRC_tograph(g, tdict, dLSDRC)`**:
   Converts `tdict` + DRC matching data into a Graphviz graph.

### 14.2 Node labels

Each node in the lsdrcgraph output represents one LS value and shows:
1. LS visual (MYD pattern)
2. DRC packet: all DRCs matching this LS, each with its ε indicator (0 or 1)
3. Signature (p,q)

### 14.3 Edge types

| Symbol | Color | Meaning |
|--------|-------|---------|
| `l` | Blue | Standard descent theta lifting |
| `L` | Navy | Generalized descent theta lifting |
| `d` | Red | Det twist (−1,−1) |
| `q` | Green | 1⁺⁻ twist (1,−1) |
| `p` | Purple | 1⁻⁺ twist (−1,1) |

### 14.4 Key differences from standalone.py

| Aspect | standalone.py | lsdrcgraph.py |
|--------|---------------|---------------|
| Input | Dual partition (orbit side) | Special partition (group side) |
| Direction | Top-down descent | Bottom-up theta lifting |
| DRC generation | `dpart2drc` (from dual partition) | `lift_drc_*` (inductive lifting) |
| LS computation | `compute_AC` (recursive descent) | `LS_graph` / `lift_*_*` (inductive lifting) |
| ℘ handling | Explicit via `build_pbp_bijection` | Implicit via shape (special vs non-special) |
| Graph structure | Extended PBP tree + LS grouping | LS tree + DRC packet annotation |

---

## 15. Verification: standalone vs lsdrcgraph

### 15.1 What is verified

The test `tests/test_compare_ls.py` verifies that both implementations
produce the **same LS value** for each DRC in the orbit.

### 15.2 How the correspondence works

The two systems use different partition conventions:
- **standalone**: dual partition Ǒ → `dpart2drc` → DRCs with bipartition (ι_Ǒ, j_Ǒ)
- **lsdrcgraph**: special partition → `test_purelyeven` → DRCs via inductive lifting

For D and B types, `test_dpart2drcLS(dpart, rtype)` in `drclift.py` takes a
dual partition and produces DRCs in the **same convention** as standalone.
This makes per-DRC comparison possible.

### 15.3 The PBP bijection bridge

Each DRC in the reference may be a non-special shape (℘ ≠ ∅).
`build_pbp_bijection(dpart, rtype)` maps every DRC to a pair
`(special_shape_drc, ℘)`. Then `compute_AC(special_drc, ℘, rtype)`
computes the LS. The test verifies:

```
For each DRC in test_dpart2drcLS output:
  (special_drc, ℘) = build_pbp_bijection[DRC]
  standalone_LS = compute_AC(special_drc, ℘, rtype)
  reference_LS = test_dpart2drcLS[DRC]
  assert normalize(standalone_LS) == normalize(reference_LS)
```

Normalization strips trailing (0,0) entries from MYD tuples.

### 15.4 Coverage

For D and B types with dual partition size ≤ 30:
- D: 584,224 DRCs verified
- B: 369,736 DRCs verified
- Total: 953,960 per-DRC LS matches

C and M types are verified indirectly: every D descent chain passes
through C levels, every B chain through M levels.

### 15.5 Running the test

```bash
python3 tests/test_compare_ls.py 30    # size ≤ 30, takes ~8 minutes
```
