# Blueprint: Tail PBP definition from [BMSZb] Section 10.5

## Source
[BMSZb] Section 10.5, pages 70-71.

## The tail multiset {x_1, ..., x_k}

For ★ ∈ {B, D, C*}, k := (r₁(Ǒ) - r₂(Ǒ))/2 + 1.

### Case ★ = B

c₁(ι) ≤ c₁(j). Multiset {x_1, ..., x_k} = union of:

Main: { Q(j, 1) | c₁(ι) + 1 ≤ j ≤ c₁(j) }

Correction:
- {c} if α = B⁺, and either c₁(ι) = 0 or Q(c₁(ι), 1) ∈ {•, s}
- {s} if α = B⁻, and either c₁(ι) = 0 or Q(c₁(ι), 1) ∈ {•, s}
- {Q(c₁(ι), 1)} otherwise

### Case ★ = D (|Ǒ| ≠ 0)

c₁(j) < c₁(ι). Multiset {x_1, ..., x_k} = union of:

Main: { P(j, 1) | c₁(j) + 2 ≤ j ≤ c₁(ι) }

Correction:
- {d} if |Ǒ| = 0 (vacuous since we assume |Ǒ| ≠ 0)
- {c} if r₂(Ǒ) = r₃(Ǒ) > 0, P(c₁(ι), 1) ∈ {r, d}, and
      (P(c₂(ι)+1, 1), P(c₂(ι)+1, 2)) = (r, c)
- {P(c₁(j)+1, 1)} otherwise

### Case ★ = C*

c₁(ι) ≤ c₁(j). Multiset = { Q(j, 1) | c₁(ι) + 1 ≤ j ≤ c₁(j) }

## Key observation

The correction in the D case can CHANGE the first symbol of the tail.
In the "otherwise" case, the first tail symbol is P(c₁(j)+1, 1), which
is just the cell right above Q's top in P's column 0.

In the balanced case (r₂ = r₃), the correction replaces that first symbol
with 'c'. This changes the tail's symbol content and hence Sign(τ_t).

## Relationship to our tailSignature_D

Our current `tailSignature_D` sums tailContrib over P's column 0 from
Q.colLen to P.colLen-1. This matches the "main set" plus the "otherwise
correction" (which is just the first cell). But it does NOT account for
the special correction in the balanced case (r₂ = r₃).

So: `tailSignature_D` = Sign(τ_t) when r₂ > r₃ or the correction is trivial.
But for the balanced case with the special correction, they differ.

## Impact on Lemma 11.3

Lemma 11.3 uses Sign(τ_t) which includes the correction.
With the correction, the tail multiset is "cleaned up" so that:
- When x_τ = s: all tail symbols are s (p_{τ_t} = 0)
- When x_τ = r: the correction ensures no non-r symbols affect q (q_{τ_t} = 0)
- When x_τ = d: ε_τ = 0

For the "otherwise" case (no special correction): the tail is exactly
P's column 0 from Q.colLen to P.colLen-1, and our tailSignature_D is correct.

## Action items

1. Define the full tail PBP τ_t with corrections in Lean
2. Verify that Sign(τ_t) satisfies Lemma 11.3
3. Connect to our existing tailSignature_D for the non-balanced case
