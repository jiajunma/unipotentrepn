# Detailed Proof: Lemma 11.5 (REVISED — verified computationally)

## Setup

★ ∈ {B, D}, (★, |Ǒ|) ≠ (D, 0).
- τ = (τ, ℘) ∈ PBP★^ext(Ǒ), s = (★, p, q) = signature of τ.
- τ' = ∇(τ) ∈ PBP★'^ext(Ǒ'), s' = (★', p', q').
- τ'' = ∇²(τ) ∈ PBP★^ext(Ǒ''), s'' = (★, p'', q'').
- ★' = Howe dual of ★: if ★ = B then ★' = C̃; if ★ = D then ★' = C.
- O = d★_BV(Ǒ), O' = d★'_BV(Ǒ'), O'' = d★_BV(Ǒ'').
- k = (r₁(Ǒ) - r₂(Ǒ))/2 + 1 = tail length.
- τ_t = tail PBP ∈ PBP_D(Ǒ_t), x_τ = tail symbol, (p_{τ_t}, q_{τ_t}) = Sign(τ_t).
- ε_τ = parity from (3.6), ε_{℘'} = ε of descended ℘.

## Step 1: First application of (11.2)

Since ★ ∈ {B, D}, (11.2) gives:

  𝓛_τ = θ̂^{s,O}_{s',O'}(𝓛_{τ'}) ⊗ (0, ε_τ)

where θ̂ is defined by **(9.29)** for ★ ∈ {B, D}.

Explicitly, (9.29) says:

  θ̂^{s,O}_{s',O'}(E') = (T^{γ₁}(Λ_{(δ₁/2, δ₁/2)}(E'))) ⊕ (p₀¹, q₀¹)

where:
- δ₁ = c₁(O) - c₂(O)
- (p₀¹, q₀¹) = (p, q) - (p', q') - ˡSign(O') + (δ₁/2, δ₁/2)
- γ₁ = (p-q+1)/2 if ★ = B, (p-q)/2 if ★ = D

## Step 2: Second application of (11.2)

Since ★' ∈ {C, C̃}, (11.2) gives:

  𝓛_{τ'} = θ̂^{s',O'}_{s'',O''}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}))

where θ̂ is defined by **(9.30)** for ★' ∈ {C, C̃}.

Explicitly, (9.30) says (for ★' = C):

  θ̂^{s',O'}_{s'',O''}(𝒜) = T^{γ₂}(Σ_{j=0}^{δ₂} Λ_{(j, δ₂-j)}(𝒜) ⊕ (n₀, n₀))

where:
- δ₂ = c₁(O') - c₂(O')
- n₀ = δ₂/2 = (c₁(O') - c₂(O'))/2
- γ₂ = (p'-q')/2 if ★' = C, (p'-q'-1)/2 if ★' = C̃

So:
  𝓛_{τ'} = T^{γ₂}(Σ_{j=0}^{δ₂} Λ_{(j, δ₂-j)}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'})) ⊕ (n₀, n₀))

## Step 3: Substitute and simplify

Substituting into Step 1:

  𝓛_τ = (T^{γ₁}(Λ_{(δ₁/2, δ₁/2)}(T^{γ₂}(Σ_{j=0}^{δ₂} Λ_{(j,δ₂-j)}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'})) ⊕ (n₀,n₀))))) ⊕ (p₀¹, q₀¹) ⊗ (0, ε_τ)

This is the composition of two theta lifts. To simplify, we need:

### Step 3a: Determine δ₁ and δ₂

**Claim:** δ₁ = c₁(O) - c₂(O) relates to the orbit structure:
- c₁(O) = μP.colLen 0 = (r₁(Ǒ)+1)/2 (first column of BV dual)
- c₂(O) = μQ.colLen 0 = (r₂(Ǒ)-1)/2 (second column of BV dual)
- δ₁ = (r₁(Ǒ)+1)/2 - (r₂(Ǒ)-1)/2 = (r₁-r₂)/2 + 1 = k (tail length)

**Claim:** δ₂ = c₁(O') - c₂(O') relates to the descended orbit:
- For ★ = D: ★' = C, Ǒ' = ∇(Ǒ) = (r₂, r₃, ...).
  O' = d_C^BV(Ǒ') has c₁(O') and c₂(O') determined by Ǒ'.
  Specifically: c₁(O') = (r₂+1)/2 if D→C gives P' shape from r₂, etc.

Actually, the relationship between c₁(O), c₂(O) and the orbit is:
- For D-type orbit Ǒ = (r₁, r₂, ...): 
  - P.colLens = dpartColLensP_D(Ǒ) = [(r₁+1)/2, dpartColLensP_D(rest)]
  - Q.colLens = dpartColLensQ_D(Ǒ)
- After descent D→C: Ǒ' = (r₂, r₃, ...) with ★' = C.
  - P'.colLens = dpartColLensP_C(Ǒ') = dpartColLensP_D(r₃, ...)
  - Q'.colLens = dpartColLensQ_C(Ǒ') = [(r₂-1)/2, dpartColLensQ_D(r₃,...)]

The BV dual orbit O' of Ǒ' has column structure determined by P' and Q'.

For the descent chain D→C→D:
- Ǒ = (r₁, r₂, r₃, ...) with type D
- Ǒ' = (r₂, r₃, ...) with type C
- Ǒ'' = (r₃, ...) with type D

And:
- c₁(O) = μP.colLen(0) = (r₁+1)/2
- c₂(O) = μQ.colLen(0) = (r₂-1)/2
- δ₁ = c₁(O) - c₂(O) = (r₁+1)/2 - (r₂-1)/2 = (r₁-r₂+2)/2 = (r₁-r₂)/2 + 1 = k

For O' (the BV dual of Ǒ' under C type):
- dpartColLensP_C(Ǒ') = dpartColLensP_D(r₃, ...) — P' colLens
- dpartColLensQ_C(Ǒ') = if r₂ > 1 then [(r₂-1)/2, dpartColLensQ_D(r₃,...)] else dpartColLensQ_D(r₃,...)
- For C type: P' and Q' shapes are swapped compared to D type. Actually, C-type BV dual has different column structure.

Wait, I need to be more careful. The BV dual of a C-type orbit is an odd orthogonal orbit (type B or D). The column lengths c₁(O'), c₂(O') of the BV dual O' = d_C^BV(Ǒ') are NOT the same as the P'/Q' column lengths of the C-type PBP.

Let me re-read the paper more carefully about the relationship between c₁(O), c₂(O) and the PBP shapes.

### Key insight from the paper

From page 55 of [BMSZ]:
  δ = |s'| - |∇_naive(O)| = c₁(O) - c₂(O)

where s' = (★', p', q') and |s'| = p' + q', and |∇_naive(O)| is the size of the naively descended orbit.

For ★ ∈ {B, D}:
  δ is even.
  (p₀, q₀) = (p, q) - (p', q') - ˡSign(O') + (δ/2, δ/2)

### Using Prop 11.4's signature formula

From (11.7): Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²(τ)) + Sign(τ_t)

This gives us:
  (p, q) = (c₂(O), c₂(O)) + (p'', q'') + (p_{τ_t}, q_{τ_t})

So:
  p - p' = c₂(O) + p'' + p_{τ_t} - p'
  q - q' = c₂(O) + q'' + q_{τ_t} - q'

The ˡSign(O') term and (δ/2, δ/2) depend on the orbit structure. From the descent:
  p' + q' = |s'| = |∇(s)| - (something depending on ★)

This is getting very intricate. Let me try a different approach:
instead of computing all parameters explicitly, use the fact that
Lemma 11.5 is stated in the paper as following directly from applying
(11.2) twice and using (11.7)/(11.9).

### Alternative approach: Accept (11.7) and derive (11.11) algebraically

**Given:**
1. 𝓛_τ = θ̂^{BD}(𝓛_{τ'}) ⊗ (0, ε_τ)   [from (11.2) for ★ ∈ {B,D}]
2. 𝓛_{τ'} = θ̂^{CC̃}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}))   [from (11.2) for ★' ∈ {C,C̃}]
3. Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²(τ)) + Sign(τ_t)   [from (11.7)]

**Show:** 𝓛_τ = T^{γ_τ}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)

The proof amounts to showing that the composed theta lift
  θ̂^{BD} ∘ θ̂^{CC̃}
simplifies to
  T^{γ_τ}(· ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t})

This requires:
- The truncation Λ_{(δ₁/2, δ₁/2)} in (9.29) composed with the truncation sum Σ_j Λ_{(j, δ₂-j)} in (9.30) reduces to the identity (when r₂ > r₃, i.e., δ₂ = 0 in the inner lift).

Wait, I need to understand: what is δ₂ for the inner lift?

The inner lift is θ̂^{C→D} (for ★ = D, ★' = C) or θ̂^{C̃→B} (for ★ = B, ★' = C̃).

For the inner lift θ̂^{s',O'}_{s'',O''}: this lifts from ★'' = ★ (back to the original type) through ★'.
- δ₂ = c₁(O') - c₂(O')

But O' is the BV dual of the DESCENDED orbit Ǒ'. The relationship between Ǒ and O' involves the descent on orbits.

I think the paper's proof is essentially this: apply (11.2) twice, the composed theta lift is computed by tracking all the parameters through the orbit descent, and the result simplifies via (11.7)/(11.9) to give (11.11).

The paper says "Applying the induction formula (11.2) twice and using the signature formulas (11.7) and (11.9), we get the following lemma." This suggests the proof is a direct (but tedious) computation.

### Conclusion

The full rigorous proof of Lemma 11.5 requires:
1. Precise formulas for c₁(O), c₂(O) in terms of orbit row lengths — **available in Lean**
2. Precise formulas for c₁(O'), c₂(O') for the descended orbit — **need to compute**
3. The ˡSign(O') computation — **available via ILS.firstColSign**
4. The signature formula (11.7) — **derivable from existing Lean infrastructure**
5. Algebra to show the composed parameters simplify to (n₀, n₀) and (p_{τ_t}, q_{τ_t})

This is fundamentally a computation problem, not a conceptual one. Every ingredient exists in the Lean codebase; the challenge is assembling them correctly.

## VERIFIED operation order (from user clarification + computational verification)

**Key rule: ⊗ (sign twist/tensor) always acts LAST.**

Formula (11.11) operations, in order:
```
Input: 𝓛_{τ''}

Step 1:  𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'})       — sign twist (for wp=∅: identity)
Step 2:  · ⊕ (n₀, n₀)                      — augment (prepend (n₀, n₀))
Step 3:  T^{γ_τ}(·)                         — character twist T on the INNER part
Step 4:  · ⊕ (p_{τ_t}, q_{τ_t})            — augment (prepend tail signature)
Step 5:  · ⊗ (0, ε_τ)                      — sign twist (LAST operation)

Output: 𝓛_τ
```

**n₀ = (c₁(O') - c₂(O'))/2** where O' is the BV dual of Ǒ' (descended orbit).
Empirically verified:
- 2-row orbits (r₃ = 0): n₀ = (r₂-1)/2
- Multi-row orbits (r₃ > 0): n₀ = 0 (because c₁(O') = c₂(O') when r₃ > 0)

**Computationally verified on:**
(3,1), (5,3), (5,1), (7,3), (7,5), (7,1), (7,5,3,1), (5,3,1), (9,7,5,3,1)
— ALL D-type orbits match exactly (after stripping trailing (0,0)).

## Proof strategy

The proof has two parts:
1. **Show the composed two-step theta lift equals (11.11):**
   Apply (11.2) twice, substitute (9.29) and (9.30), then verify that the
   composed parameters match (n₀, n₀) and (p_{τ_t}, q_{τ_t}).

2. **Verify the parameter values using (11.7):**
   The signature decomposition Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²τ) + Sign(τ_t)
   determines p₀, q₀, δ, γ in the theta lift formulas, which combine to give
   the simplified form (11.11).

All ingredients exist in the Lean codebase (countSym_split, col0_dot_below_Q_D,
Q_countSym_eq_zero_of_D, countSymColGe1_eq, ddescent_inj_D).

## Plan for formalization

**Phase 1:** Prove signature decomposition (11.7) as standalone theorem.
**Phase 2:** Prove that two-step theta lift composition yields (11.11).
**Phase 3:** Use (11.11) to prove Lemma 11.6, Prop 11.7, Prop 11.8, etc.
