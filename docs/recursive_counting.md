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
