# Full Descent (Naive + Corrections)

Reference: [BMSZb] Section 10.4; [BMSZ] Section 3.3, Definition 3.14.

## Overview

The full descent ∇(τ) = naive_descent(τ) + corrections.

Corrections only exist for **B⁺ and D types**. C and M use naive descent only.

## Shape-Based Formulation of Corrections

All conditions from [BMSZb] can be expressed using PBP column lengths:
- c₁(ι) = P.shape.colLen(0) (first column length of P)
- c₂(ι) = P.shape.colLen(1) (second column length of P)
- c₁(j) = Q.shape.colLen(0)
- c₂(j) = Q.shape.colLen(1)

### Determining (2,3) ∈ ℘ from shape

When ℘ is not explicitly given, (2,3) ∈ ℘ is inferred from the PBP shape:

| Type | (2,3) ∈ ℘ condition |
|------|---------------------|
| B    | c₂(j) ≥ c₁(ι) + 2, i.e., Q.colLen(1) ≥ P.colLen(0) + 2 |
| D    | c₂(ι) ≥ c₁(j) + 2, i.e., P.colLen(1) ≥ Q.colLen(0) + 2 |

### B⁺ Corrections

**Condition for r₂(Ǒ) > 0**: "at least 2 non-empty columns" in the combined DRC.
In terms of shapes: P.colLen(1) > 0 ∨ Q.colLen(1) > 0.

#### Case (a): (2,3) ∉ ℘, r₂ > 0, Q.paint(c₁(ι)-1, 0) ∈ {r, d}

Action: Set the last cell of P' column 0 to `s`.
```
P'_full(P.colLen(0)-1, 0) := s    (overriding naive descent)
```
All other cells: P'_naive and Q'_naive.

In PBP column-length terms:
- c₁(ι) = P.colLen(0)
- c₁(ι') = P'.colLen(0) = c₁(ι) (P shape preserved by B→M naive descent? 
  Actually B→M removes Q col 0, P keeps shape. But wait, B⁺ descends to M.
  B⁺→M: remove Q col 0. P'_naive has redistributed dots/s but same shape.
  So P'.colLen(0) = P.colLen(0). The correction changes P'(P.colLen(0)-1, 0).)

Wait, this is about B⁺ type, which descends to M. The naive descent for B→M
is: remove Q col 0, redistribute via _fill_ds_M. The P side keeps its shape.
The correction modifies the P' at position (c₁(ι')-1, 0) = (c₁(ι)-1, 0).

Actually re-reading the code more carefully:
```python
# B case (a): (2,3) ∉ ℘, r₂(Ǒ) > 0, Q(c₁(ι), 1) ∈ {r, d}
# Action: P'(c₁(ι'), 1) = s
# Note: c₁(ι') = len(resL[0]) = number of rows in P' col 0
elif not has_23:
    ncols = sum(1 for c in drcL if c) + sum(1 for c in drcR if c)
    r2_pos = (ncols >= 2)
    q_c1_1 = fR[c1 - 1] if 0 < c1 <= len(fR) else ''
    if r2_pos and q_c1_1 in ('r', 'd'):
        col0 = resL[0]
        resL = (col0[:-1] + 's', *resL[1:])
```

So: the correction changes the LAST cell of P' column 0 from whatever
the naive descent produced to `s`. The condition checks Q's first column
at row c₁(ι)-1 (0-indexed).

In our paint function terms:
- Condition: Q.paint(P.colLen(0) - 1, 0) ∈ {r, d}
  (the Q symbol at the boundary between P and Q in column 0)
- Action: P'(P'.colLen(0) - 1, 0) := s

#### Case (b): (2,3) ∈ ℘, Q.paint(c₂(j)-1, 0) ∈ {r, d}

Action: Set the last cell of Q' column 0 to `r`.
```
Q'_full(Q'.colLen(0)-1, 0) := r
```

### D Corrections

#### Case (a): (2,3) ∉ ℘, c₂(ι) = c₁(j) + 1, P.paint(c₂(ι)-1, 1) = c,
              P.paint(i, 0) ∈ {r, d} for ALL c₂(ι)-1 ≤ i ≤ c₁(ι)-1

Action: Set P'(P'.colLen(0)-1, 0) := r.

In shape terms: P.colLen(1) = Q.colLen(0) + 1.

#### Case (b): (2,3) ∈ ℘, P.paint(c₂(ι)-2, 0) ∈ {r, c}

Action: Modify last two cells of P' column 0.

### C and M types

No corrections. Full descent = naive descent.

## Lean Formalization Plan

Define `fullDescentPaintL/R` that extends the naive descent with corrections:

```lean
noncomputable def fullDescentPaintL_DC (τ : PBP) : ℕ → ℕ → DRCSymbol :=
  fun i j =>
    let naive := descentPaintL_DC τ i j
    if j = 0 then
      -- Apply D correction to column 0 of P'
      let c₂ι := τ.P.shape.colLen 1
      let c₁j := τ.Q.shape.colLen 0
      let has23 := c₂ι ≥ c₁j + 2  -- (2,3) ∈ ℘ from shape
      if ¬has23 ∧ c₂ι = c₁j + 1 ∧ ... then
        -- correction (a): last cell of P' col 0 := r
        if i = P'.colLen(0) - 1 then .r else naive
      else if has23 ∧ ... then
        -- correction (b): modify last two cells
        ...
      else naive
    else naive
```

The key insight: corrections only affect **column 0** of the result,
and only change **one or two cells** at the bottom.
