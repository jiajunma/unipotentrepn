# Rigorous Proof Blueprint: Lemma 11.5

## Setup and Notation

Throughout, ★ ∈ {B, D}, (★, |Ǒ|) ≠ (D, 0).

- τ = (τ, ℘) ∈ PBP★^ext(Ǒ), with descent τ' = (τ', ℘') ∈ PBP★'^ext(Ǒ'), double descent τ'' = (τ'', ℘'') ∈ PBP★^ext(Ǒ'').
- ★' is the Howe dual of ★: B↔M, D↔C.
- O = d★_BV(Ǒ) is the BV dual orbit, O' = d★'_BV(Ǒ').
- s = (★, p, q) is the classical signature of τ, s' = (★', p', q') of τ'.
- (p_{τ_t}, q_{τ_t}) = Sign(τ_t) is the signature of the tail PBP.
- ε_τ ∈ {0, 1} from (3.6), x_τ = tail symbol.
- k = (r₁(Ǒ) - r₂(Ǒ))/2 + 1 is the tail length.
- γ_τ = (p_{τ_t} - q_{τ_t})/2 + [1 if ★=B] from (11.10).
- n₀ = (c₁(O') - c₂(O'))/2 where O' is the BV dual of Ǒ'.
- δ = c₁(O') - c₂(O') = 2n₀.

## Statement

**Lemma 11.5.** Suppose ★ ∈ {B, D} and (★, |Ǒ|) ≠ (D, 0). Put γ_τ as in (11.10).

(a) If r₂(Ǒ) > r₃(Ǒ), then

  𝓛_τ = T^{γ_τ}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'})) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)    ...(11.11)

(b) If r₂(Ǒ) = r₃(Ǒ), then

  𝓛_τ = 𝓛_{τ,+} + 𝓛_{τ,-}    ...(11.12)

where

  𝓛_{τ,+} := (T^{γ_τ}(𝓛_{τ''}^+ ⊕ (0,0))) ⊕ (p_{τ_t}, q_{τ_t} - 1) ⊗ (0, ε_τ)    ...(11.13)
  𝓛_{τ,-} := (T^{γ_τ}(𝓛_{τ''}^- ⊕ (0,0))) ⊕ (p_{τ_t} - 1, q_{τ_t}) ⊗ (0, ε_τ)    ...(11.14)

## Proof

### Step 1: Apply (11.2) to express 𝓛_τ in terms of 𝓛_{τ'}

Since ★ ∈ {B, D}, formula (11.2) gives:

  𝓛_τ = θ̂^{s_τ, O}_{s_{τ'}, O'}(𝓛_{τ'}) ⊗ (0, ε_τ)

where θ̂ is defined by (9.29) for ★ ∈ {B, D}.

### Step 2: Apply (11.2) to express 𝓛_{τ'} in terms of 𝓛_{τ''}

Since ★' ∈ {C, C̃}, formula (11.2) gives:

  𝓛_{τ'} = θ̂^{s_{τ'}, O'}_{s_{τ''}, O''}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}))

where θ̂ is defined by (9.30) for ★' ∈ {C, C̃}.

### Step 3: Compute θ̂ for ★' ∈ {C, C̃} — formula (9.30)

From (9.30), for ★' = C (the case ★ = D):

  θ̂^{s_{τ'}, O'}_{s_{τ''}, O''}(𝓐') = T^{(p'-q')/2}( Σ_{j=0}^{δ'} Λ_{(j, δ'-j)}(𝓐') ⊕ (n'₀, n'₀) )

where:
- δ' = c₁(O'') - c₂(O''), n'₀ = δ'/2
- O'' is the BV dual of Ǒ''

For ★' = C̃ (the case ★ = B), the formula uses (p'-q'-1)/2 instead.

### Step 4: Substitute into Step 1

Substituting 𝓛_{τ'} from Step 2 into the θ̂ of Step 1 (formula (9.29) for ★ ∈ {B, D}):

  θ̂^{s_τ, O}_{s_{τ'}, O'}(𝓛_{τ'}) = (T^{γ}(Λ_{(δ/2, δ/2)}(𝓛_{τ'}))) ⊕ (p₀, q₀)

where:
- δ = c₁(O) - c₂(O)
- (p₀, q₀) = (p, q) - (p', q') - ˡSign(O') + (δ/2, δ/2)
- γ depends on ★ (see (9.29))

### Step 5: Use the signature formulas from Prop 11.4

From Prop 11.4 (= [BMSZb] Prop 10.9):

**(a) When r₂(Ǒ) > r₃(Ǒ):**

  Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²(τ)) + Sign(τ_t)    ...(11.7)

i.e., (p, q) = (c₂(O), c₂(O)) + (p'', q'') + (p_{τ_t}, q_{τ_t}).

**(b) When r₂(Ǒ) = r₃(Ǒ):**

  Sign(τ) = (c₂(O)-1, c₂(O)-1) + Sign(∇²(τ)) + Sign(τ_t)    ...(11.9)

### Step 6: Simplify the augmentation parameters

For case (a) (r₂ > r₃):

Using (11.7) to compute (p₀, q₀):
  (p₀, q₀) = (p, q) - (p', q') - ˡSign(O') + (δ/2, δ/2)

By Lemma 9.2 and the orbit structure, the ˡSign and δ terms combine with the
signature decomposition to give:
  (p₀, q₀) = (p_{τ_t}, q_{τ_t})

And the truncation Λ_{(δ/2, δ/2)} applied to 𝓛_{τ'} (which was computed from
𝓛_{τ''} via (9.30)) simplifies because:
- δ = c₁(O) - c₂(O) relates to the orbit structure
- The truncation + augmentation from (9.30) compose with the truncation in (9.29)
- The net effect is: Λ_{(δ/2, δ/2)} ∘ (Σ_j Λ_{(j,δ'-j)} ⊕ (n'₀, n'₀)) = ⊕ (n₀, n₀)
  when δ = 2n₀ and the truncation sum has exactly one surviving term.

The character twist γ from (9.29) composes with the one from (9.30) to give γ_τ
from (11.10):
  γ_τ = (p_{τ_t} - q_{τ_t})/2 + [1 if ★=B]

### Step 7: Assemble the formula

Combining all the simplifications:

  𝓛_τ = (T^{γ_τ}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀))) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)

This is exactly (11.11), completing case (a).

### Step 8: Case (b) — r₂(Ǒ) = r₃(Ǒ)

When r₂ = r₃, the orbit structure changes:
- δ = c₁(O) - c₂(O) = 1 (the balanced case)
- The truncation sum in (9.30) now has TWO surviving terms (j = 0 and j = 1)
- These give the + and - components:
  - j = 0: Λ_{(0, 1)}(𝓐') = 𝓐'^-  (the minus truncation)
  - j = 1: Λ_{(1, 0)}(𝓐') = 𝓐'^+  (the plus truncation)

The augmentation parameters adjust by ±1:
  (p₀, q₀) = (p_{τ_t}, q_{τ_t}) in case (a)
  becomes (p_{τ_t}, q_{τ_t} - 1) for the + branch and (p_{τ_t} - 1, q_{τ_t}) for the - branch

This gives (11.13) and (11.14). □

## Verification Checklist

- [x] Step 1: (11.2) for ★ ∈ {B, D} correctly stated
- [x] Step 2: (11.2) for ★' ∈ {C, C̃} correctly stated
- [x] Step 3: (9.30) correctly instantiated
- [x] Step 4: (9.29) correctly instantiated
- [ ] Step 5: Need to verify the exact relationship between c₁, c₂, n₀, δ across the orbit levels
- [ ] Step 6: The simplification of composed truncations needs careful arithmetic
- [ ] Step 7: The γ_τ formula needs verification from the composed character twists

## ISSUES FOUND ON REVIEW

**Issue 1 (Step 6):** The claim that "the truncation sum has exactly one surviving term"
when r₂ > r₃ needs to be justified. This depends on the specific orbit structure:
δ = c₁(O) - c₂(O) = 0 when r₂ > r₃ (the primitive case). When δ = 0, the
truncation Λ_{(0,0)} is the identity, so the sum has exactly one term. ✓

Actually wait: δ here is for the OUTER lift (9.29), not the inner lift (9.30).
The inner lift uses δ' = c₁(O'') - c₂(O'') for the double descent orbit.
Need to track δ vs δ' carefully.

**Issue 2 (Step 5):** The signature formula (11.7) is stated in the paper as a
consequence of Prop 11.4 = [BMSZb] Prop 10.9. But (11.7) is:
  Sign(τ) = (c₂(O), c₂(O)) + Sign(∇(∇(τ))) + Sign(τ_t)

This decomposes the PBP signature into three parts:
1. A constant (c₂(O), c₂(O)) depending on the BV dual orbit
2. The signature of the double descent ∇²(τ)
3. The tail signature

This is proved in [BMSZb] Prop 10.9, which we have formalized as
`doubleDescent_D_injective_on_PBPSet` (injectivity), but the SIGNATURE
DECOMPOSITION formula itself may not be explicitly stated in our Lean code.

**Action needed:** Check if the Lean codebase has a theorem stating
  PBP.signature τ = (c₂, c₂) + PBP.signature(∇²τ) + PBP.tailSignature τ
or if we need to add it.

**Issue 3:** The proof sketch for Step 6 is too hand-wavy. The composed
truncations and augmentations need explicit computation. This is the hardest
part of the formalization.

## Dependencies on existing Lean code

- `descentCD_raw`, `descentCD_PBP`: C→D descent ✓
- `liftCD_PBP`, `descentCD_liftCD_round_trip`: D→C lift ✓
- `ddescent_inj_D`: double descent injectivity (Prop 10.9) ✓
- `PBP.signature`: signature computation ✓
- `PBP.epsilon`: epsilon computation ✓
- `ILS.thetaLift_DC`, `ILS.thetaLift_CD`: theta lift formulas ✓
- `ILS.charTwistCM`, `ILS.twistBD`: character/sign twists ✓
- `AC.step`, `AC.fold`: AC recursion ✓

## Missing: Signature decomposition formula

Need to prove:
```
PBP.signature τ.val = (c₂(O), c₂(O)) + PBP.signature (∇²(τ)).val + PBP.tailSignature_D τ.val
```

This connects the counting infrastructure (which has the decomposition implicitly
via `card_PBPSet_eq_sum_tc`) to the MYD signature formulas.
