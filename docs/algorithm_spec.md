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

### 1.3 Irreducible Local System (ILS)

**Reference**: [BMSZ] Section 9.3.

An ILS is a tuple `((p₁,n₁), (p₂,n₂), ..., (pₖ,nₖ))` where
`(pᵢ,nᵢ)` encodes the number of rows of length i in the marked Young
diagram: pᵢ rows marked with + and nᵢ rows marked with −.

### 1.4 Local System (LS)

A LS is a `FrozenMultiset` of ILS tuples, representing a direct sum
of irreducible local systems.

---

## 2. Orbit → Bipartition

### `dpart_to_bipartition(dpart, rtype)` — Line 76

**Reference**: [BMSZb] Equation (2.16), (8.9) with ℘ = ∅.

Given dual partition Ǒ = `dpart` (row lengths in decreasing order) and
type ★ = `rtype`, compute the special-shape bipartition (ι_Ǒ, j_Ǒ).

Returns `(tauL, tauR)`: column lengths of the two Young diagrams.

**For ★ = B**: first row r₁ contributes c₁(j) = r₁/2. Remaining rows are paired:
```
(c_i(ι), c_{i+1}(j)) = (r_{2i}/2, r_{2i+1}/2)    if (2i, 2i+1) ∉ ℘
                      = (r_{2i+1}/2, r_{2i}/2)      if (2i, 2i+1) ∈ ℘
```

**For ★ = D**: first row r₁ contributes c₁(ι) = (r₁+1)/2. Remaining rows are paired:
```
(c_{i+1}(ι), c_i(j)) = ((r_{2i}+1)/2, (r_{2i+1}-1)/2)    if (2i, 2i+1) ∉ ℘
```

**For ★ = C, M**: rows are paired directly (no first-row offset):
```
(c_i(ι), c_i(j)) = (r_{2i-1}/2, r_{2i}/2)    for M
                  = ((r_{2i-1}+1)/2, (r_{2i}-1)/2)    for C
```

### `dpart2Wrepns_with_wp(dpart, rtype)` — Line 1204

**Reference**: [BMSZb] Equation (8.9), Section 8.3.

Computes all W-representations labelled by ℘. Returns dict:
```
{ frozenset(PPidx subset) → bipartition (tauL, tauR) }
```

### `compute_PPidx(dpart, rtype)` — Line 1158

**Reference**: [BMSZb] Definition 2.21.

Computes the list of primitive pair indices for the dual partition Ǒ.

**For B/D**: `PPidx = [i : rows[2i+1] > rows[2i+2] ≥ 0]`
**For C/M**: `PPidx = [i : rows[2i] > rows[2i+1] ≥ 0]`

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

### `naive_descent(drc, rtype)` — Line 784

**Reference**: [BMSZb] Lemma 10.4 (★ ∈ {B, C}), Lemma 10.5 (★ ∈ {M, D}).

Computes τ'_naive by removing one column and redistributing •/s symbols.

| rtype | Column removed | Target type γ' | Redistribution |
|-------|---------------|----------------|---------------|
| C | first col of Q (drcR) | D | `_fill_ds_D` |
| B⁺/B⁻ | first col of Q (drcR) | M | `_fill_ds_M` |
| D | first col of P (drcL) | C | `_fill_ds_C` |
| M | first col of P (drcL) | B⁺ or B⁻ | `_fill_ds_B` |

**γ' for M → B** ([BMSZ] Equation (3.11)):
```
γ' = B⁺  if 'c' does NOT occur in first column of P
   = B⁻  if 'c' occurs in first column of P
```

**Redistribution rule** ([BMSZb] Lemma 10.4–10.5):
Symbols r, c, d are preserved from the source column (shifted by one position).
Positions with • or s in the source become • or s in the target, filled
to satisfy the painting constraints ([BMSZb] Definition 2.25).

### `descent(drc, rtype, dpart=None, wp=None)` — Line 833

**Reference**: [BMSZb] Section 10.4 (general ℘ algorithm).

Full descent ∇(τ) = naive descent + corrections.

**Determining (2,3) ∈ ℘**:
- If `wp` is provided: `has_23 = (1 in wp)` (PPidx 1 ⟺ pair (2,3))
- If `wp` is None: infer from DRC shape
  - B type: `has_23 = (c₂(j) ≥ c₁(ι) + 2)`
  - D type: `has_23 = (c₂(ι) ≥ c₁(j) + 2)`

#### ★ = B⁺ corrections

**(a)** If (2,3) ∉ ℘, r₂(Ǒ) > 0, Q(c₁(ι_℘), 1) ∈ {r, d}:

**Reference**: [BMSZ] Lemma 3.10; [BMSZb] Section 10.4 case B(a).

```
P'(c₁(ι_{℘'}), 1) := s
```
All other entries from P'_naive. Q' := Q'_naive.

Condition r₂(Ǒ) > 0 is checked as: DRC has ≥ 2 non-empty columns.

**(b)** If (2,3) ∈ ℘, Q(c₂(j_℘), 1) ∈ {r, d}:

**Reference**: [BMSZb] Section 10.4 case B(b).

```
Q'(c₁(j_{℘'}), 1) := r
```
P' := P'_naive. Other Q' entries from Q'_naive.

**(c)** Otherwise: P' := P'_naive, Q' := Q'_naive.

**B⁺ additional correction** (lines 891–904):

Reverses the lift algorithm's `tR='r' → nsR='d'` conversion when
P is "shorter" than Q's second column. Ported from
`combunipotent/drclift.py` lines 256–268.

**Note**: B⁻ has no corrections (only B⁺ does).

#### ★ = D corrections

**(a)** If (2,3) ∉ ℘, r₂(Ǒ) = r₃(Ǒ) > 0, P(c₂(ι_℘), 2) = c,
P(i, 1) ∈ {r, d} for ALL c₂(ι_℘) ≤ i ≤ c₁(ι_℘):

**Reference**: [BMSZb] Section 10.4 case D(a).

```
P'(c₁(ι_{℘'}), 1) := r
```
All other entries from P'_naive. Q' := Q'_naive.

Condition r₂ = r₃ > 0 is equivalent to c₂(ι) = c₁(j) + 1.

**Important**: This uses the **general algorithm** from [BMSZb] which checks
ALL intermediate entries P(i,1) ∈ {r,d}, not just endpoints. [BMSZ] Lemma 3.12
checks only endpoints (P(c₂,1)=r and P(c₁,1)∈{r,d}) which is weaker and
produces incorrect LS for 197 DRCs (size ≤ 30). Verified against reference.

**(b)** If (2,3) ∈ ℘, P(c₂(ι_℘) − 1, 1) ∈ {r, c}:

**Reference**: [BMSZb] Section 10.4 case D(b).

```
P'(c₁(ι_{℘'}) − 1, 1) := r
P'(c₁(ι_{℘'}), 1) := P(c₂(ι_℘) − 1, 1)
```
Other entries from P'_naive. Q' := Q'_naive.

**(c)** Otherwise: P' := P'_naive, Q' := Q'_naive.

---

## 5. ILS Operations

### `_ils_sign(irr_s)` — Line 1773

**Reference**: [BMSZ] Section 9.3 (LS.py: `_sign_ILS`).

Signature (p, n) of an ILS tuple irr_s = ((p₁,n₁), ..., (pₖ,nₖ)):
```
For each row i (0-based), let (hrl, rrl) = divmod(i+1, 2):
  p += |pᵢ|·(hrl + rrl) + |nᵢ|·hrl
  n += |nᵢ|·(hrl + rrl) + |pᵢ|·hrl
```

### `_ils_firstcol_sign(irr_s)` — Line 1783

**Reference**: [BMSZ] Section 9.3 (LS.py: `_sign_ILS_firstcol`).

First-column signature:
```
For i even (0-based):  p += |pᵢ|, n += |nᵢ|
For i odd:             p += |nᵢ|, n += |pᵢ|
```

### `_ils_twist_BD(irr_s, twist)` — Line 1796

**Reference**: [BMSZ] Section 9.4 (LS.py: `_char_twist_D`, `_char_twist_B`).

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

### `_ils_char_twist_CM(irr_s, j)` — Line 1821

**Reference**: [BMSZ] Section 9.4 (LS.py: `_char_twist_C`, `_char_twist_CM`).

Character twist T^j: negate entries at positions i where (i+1) ≡ 2 (mod 4),
but only when j is odd. T² = identity.

Equivalence with LS.py:
```
_char_twist_C(irr_s, ps, ns) = _ils_char_twist_CM(irr_s, (ps−ns)//2)
```

---

## 6. Theta Lifting of ILS

### `theta_lift_ils(irr_s, rtype, p, q)` — Line 1837

**Reference**: [BMSZ] Section 11.1–11.3 (LS.py: `lift_irr_D_C`, `lift_irr_C_D`,
`lift_irr_B_M`, `lift_irr_M_B`).

Theta lift a single ILS to target type ★ with target signature (p, q).

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

Lifts each ILS in the `FrozenMultiset` independently:
```
result = []
for irr_s in ls:
    result.extend(theta_lift_ils(irr_s, rtype, p, q))
return FrozenMultiset(result)
```

### `twist_ls(ls, twist)` — Line 1941

Apply `_ils_twist_BD` to every ILS in the multiset.

---

## 7. Associated Cycle (LS Computation)

### `compute_AC(drc, wp, rtype, cache=None)` — Line 1978

**Reference**: [BMSZ] Equation (3.16), Section 11.2.

Computes AC(τ̂) for extended PBP τ̂ = (τ, ℘, ★) via recursive descent.

#### Base case (|τ| = 0)

| rtype | Base LS |
|-------|---------|
| B⁺ | `[(1, ((1, 0),))]` — trivial character of O(1,0) |
| B⁻ | `[(1, ((0, −1),))]` — det character of O(0,1) |
| C, D, M | `[(1, ())]` — trivial (empty ILS) |

#### Recursive step

1. Compute ε_℘ = 1 if PPidx 0 ∈ ℘, else 0.
2. Descend ℘: `℘' = ∇̃(℘)` via `_descend_wp`.
3. Compute (p_τ, q_τ) = `signature(drc, rtype)`.
4. Compute ε_τ = `epsilon(drc, rtype)`.
5. Descent DRC: `(drc', ★') = descent(drc, rtype)`.
6. Recursively compute `source_AC = compute_AC(drc', ℘', ★')`.

Then for each `(coeff, ils)` in source_AC:

**★ ∈ {C, M}** ([BMSZ] Eq. 3.16 case 2):
```
if ε_℘ = 1:
    source_ils = _ils_twist_BD(ils, (−1, −1))   # pre-twist by det
lifted = theta_lift_ils(source_ils, rtype, p_τ, q_τ)
# No post-twist for C/M
```

**★ ∈ {B⁺, B⁻, D}** ([BMSZ] Eq. 3.16 case 1):
```
# No pre-twist for B/D
lifted = theta_lift_ils(ils, rtype, p_τ, q_τ)
if ε_τ ≠ 0:
    lifted_ils = _ils_twist_BD(lifted_ils, (1, −1))   # post-twist by 1⁺⁻
```

### `_descend_wp(wp, rtype)` — Line 1271

**Reference**: [BMSZ] Equation (3.15); [BMSZb] Section 10.4.

```
℘' = ∇̃(℘):
  For C/M → D/B:  PPidx i maps to PPidx (i−1), discard i=0
  For B/D → C/M:  PPidx i maps to PPidx i (no shift)
```

---

## 8. PBP Bijection

### `build_pbp_bijection(dpart, rtype)` — Line 1288

**Reference**: [BMSZb] Propositions 10.2, 10.8, 10.9; Corollary 10.10.

Builds bijection ⊔_℘ PBP(Ǒ, ℘) ↔ PBP(Ǒ, ∅) × 2^PP.

Returns `(bijection, table)` where:
- `bijection[drc] = (special_shape_drc, frozenset(℘))`
- `table[frozenset(℘)] = [list of DRCs in PBP(Ǒ, ℘)]`

#### C/M types (shape shift + descent)

**Reference**: [BMSZb] Proposition 10.8; Section 10.2 (shape shifting).

For τ ∈ PBP(Ǒ, ℘):

1. If PPidx 0 ∈ ℘ (i.e., (1,2) ∈ ℘ for C, or first pair for M):
   shape shift τ → τ₁ ∈ PBP(Ǒ, ℘ \ {0}) via `twist_nsp2sp` (C) or
   `twist_M_nonspecial` (M).

2. If ℘ = ∅ after step 1: bijection[τ] = (τ₁, original ℘). Done.

3. Otherwise: descent τ₁ → τ' ∈ PBP(Ǒ', ℘').
   Recursively biject τ' → τ'' ∈ PBP(Ǒ', ∅).
   Find τ₀ ∈ PBP(Ǒ, ∅) with `(∇(τ₀), γ') = (τ'', γ'_of_τ₁)`.

**Key**: The descent lookup key includes γ' (B⁺/B⁻ tag) to avoid
collisions when two different DRCs descent to the same DRC with
different γ' values. This was a bug that caused 700 B-type LS failures.

#### B/D types (Corollary 10.10)

**Reference**: [BMSZb] Corollary 10.10.

The map τ ↦ (∇τ, p_τ, q_τ, ε_τ) is injective on PBP_★(Ǒ).

For τ ∈ PBP(Ǒ, ℘):
1. Compute (∇τ, sig, ε) where ε = 0 if tail symbol is 'd', else 1.
2. Recursively biject ∇τ → τ'' ∈ PBP(Ǒ', ∅).
3. Find τ₀ ∈ PBP(Ǒ, ∅) with `(∇τ₀ mapped to ∅, sig(τ₀), ε(τ₀)) = (τ'', sig, ε)`.

---

## 9. Tail Symbol

### `compute_tail_symbol(drc, rtype, dpart)` — Line 2211

**Reference**: [BMSZb] Section 10.5, Equation (10.7).

Computes x_τ ∈ {c, d, r, s} for ★ ∈ {B, D}.

The tail τ_t consists of cells in the first column of P (for D) or Q (for B)
that extend beyond the other diagram's columns.

**For ★ = D**: x_τ is the last entry in fL (P's first column) when the tail
has length > 1. For length ≤ 1, special handling for r₂ = r₃ case.

**For ★ = B**: x_τ is the last entry in fR (Q's first column) when the tail
has length > 1. For length ≤ 1, correction based on B⁺/B⁻.

---

## 10. Recursive Counting

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

## 11. Lifting Tree Visualization

### `gen_lift_tree(dpart, rtype, format, filename)` — Line 2628

Generates two Graphviz graphs:
1. **LS lift graph** (`{filename}.svg`): nodes grouped by LS value
2. **Extended PBP descent tree** (`{filename}_ext.svg`): one node per extended PBP

#### 11.1 Tree construction (lines 2669–2703)

Recursively build the extended PBP tree from top-level DRCs down to the
trivial group:
- Start from all DRCs × all ℘ subsets × {B⁺, B⁻} (for B type)
- At each node: `descent(drc, rtype)` gives the parent
- Base case: empty DRC with type ∈ {C, M, D}

For B/M type: B⁺ and B⁻ both descent to Mp(0) = (empty, M), forming
a single connected tree.

#### 11.2 LS computation (lines 2705–2750)

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

#### 11.3 LS lift graph node labels

Each node in the LS lift graph represents one LS value (FrozenMultiset).
Multiple extended PBPs with the same LS are grouped into one node.

**Node contents**:
1. **ILS visual**: the marked Young diagram pattern (+/−/*/=)
2. **Per-DRC entries**: for each extended PBP with this LS:
   - `(p,q)`: signature from `signature(drc, rtype)`
   - DRC diagram with red-colored columns for ℘
   - B⁺/B⁻ label (for B type)
   - ε value: `epsilon(drc, rtype)` for B/D, `1 if 0∈℘` for C/M

**℘ column coloring** ([BMSZb] Equation (8.9)):

| Type | PPidx i → red columns |
|------|----------------------|
| C/M | column i of both L and R |
| D | column (i+1) of L, column i of R |
| B | column i of L, column (i+1) of R |

#### 11.4 Edges

**Lift edges** (blue, solid): from parent LS node to child LS node.
For C/M children with ε_℘ = 1, the lift source is the **det-twisted**
parent LS (which may be a ghost node).

**Character twist edges** (same level, bidirectional):
- Red: det twist `(−1, −1)`
- Green: 1⁺⁻ twist `(1, −1)`
- Purple: 1⁻⁺ twist `(−1, 1)`

**Ghost nodes**: LS values that appear as det-twisted variants of real
LS nodes but are not realized by any extended PBP. Shown with gray
background. Grouped in dotted boxes with their twist-related nodes.

#### 11.5 Layout

- `rankdir=TB`: small groups at top, large groups at bottom
- Group labels (Sp(2n), O(2n+1), etc.) on the left
- Nodes colored by type: blue=C, green=M, orange=D, red=B

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

