# Complete Blueprint: [BMSZ] Section 11 — Associated Cycles, Combinatorial Aspect

Reference: [BMSZ] arXiv:1712.05552v6, pages 61–72.
Companion: [BMSZb] arXiv:2205.05266v4, Section 10.

## Global Setup

Throughout Section 11, we fix:
- ★ ∈ {B, D} (Sections 11.1–11.4), ★ ∈ {C, C̃} (Section 11.5), ★ ∈ {C*, D*} (Section 11.6)
- Ǒ a nilpotent orbit with good parity, O = d★_BV(Ǒ) the BV dual
- τ = (τ, ℘) ∈ PBP★^ext(Ǒ), with:
  - descent τ' = ∇(τ) ∈ PBP★'^ext(Ǒ')
  - double descent τ'' = ∇²(τ) ∈ PBP★^ext(Ǒ'')
  - tail τ_t ∈ PBP_D(Ǒ_t) as defined in [BMSZb] Section 10.5
- (p_τ, q_τ) = Sign(τ), ε_τ from (3.6), x_τ = tail symbol
- k = (r₁(Ǒ) - r₂(Ǒ))/2 + 1 = tail length
- 𝓛_τ ∈ ℤ[MYD★(O)] = combinatorial associated cycle

### Lean status legend
- ✅ = fully formalized and proved
- 📐 = defined but not proved
- ❌ = not yet in Lean

---

## Lemma 11.1 (Base case, ★ ∈ {B, D})

### Statement
Suppose ★ ∈ {B, D}.

(a) If r₁(O) ≤ 1, then 𝓛_τ ∈ MYD★(O) and
  𝓛_τ = (p_τ, (-1)^{ε_τ} q_τ)_★.

(b) If r₁(O) = 1, the map
  PBP★^ext(Ǒ) × ℤ/2ℤ → {(a,b) ∈ ℤ×ℤ : |a|+|b| = |O|},  (τ, ε) ↦ (-1)^ε 𝓛_τ(1)
is bijective.

### Proof
When r₁(O) ≤ 1, the orbit O has at most one row. The PBP has very simple structure.

For ★ = B with |Ǒ| = 0: α ∈ {B⁺, B⁻}, and by the base case of (11.2):
- α = B⁺: 𝓛_τ = (1, 0)_★
- α = B⁻: 𝓛_τ = (0, -1)_★

Sign(τ) = (1, 0) or (0, 1) respectively. And ε_τ = 1 (no d in empty PBP).
Check: (p_τ, (-1)^{ε_τ} q_τ) = (1, (-1)^1 · 0) = (1, 0) for B⁺. ✓
Check: (p_τ, (-1)^{ε_τ} q_τ) = (0, (-1)^1 · 1) = (0, -1) for B⁻. ✓

For ★ = D with |Ǒ| = 0: 𝓛_τ = (0, 0)_★ and Sign(τ) = (0, 0), ε_τ = 1.
Check: (0, (-1)^1 · 0) = (0, 0). ✓

For r₁(O) = 1: one step of descent gives |Ǒ'| = 0, so 𝓛_{τ'} is the base case.
Apply (11.2) once: 𝓛_τ = θ̂(𝓛_{τ'}) ⊗ (0, ε_τ).
The theta lift θ̂ is (9.29) for ★ ∈ {B, D}, which augments by (p₀, q₀) and applies T^γ.
With r₁(O) = 1, the parameters simplify to give 𝓛_τ = (p_τ, (-1)^{ε_τ} q_τ)_★.

Part (b) follows because Sign determines p_τ, q_τ, and ε_τ determines the sign of the second component. The bijectivity comes from the fact that for each pair (a, b) with |a|+|b| = |O|, there is a unique (τ, ε). □

### Lean status
- ✅ Base case definition: `AC.base`
- ✅ Base case sign: `AC.base_sign`
- ❌ Full Lemma 11.1(a) for r₁(O) = 1 (one descent step)
- ❌ Lemma 11.1(b) bijectivity

### Dependencies
- `AC.base` ✅
- `AC.step` ✅
- `ILS.thetaLift_CD_sign` ✅

---

## Proposition 11.4 (Descent map, from [BMSZb] Prop 10.9)

### Statement
Suppose ★ ∈ {B, D} and (★, |Ǒ|) ≠ (D, 0). Write Ǒ'' := ∇̃(Ǒ').
Consider the map
  PBP★(Ǒ) → PBP★(Ǒ'') × PBP_D(Ǒ_t),  τ ↦ (∇(∇(τ)), τ_t).    ...(11.6)

(a) If r₂(Ǒ) > r₃(Ǒ), then (11.6) is bijective, and
  Sign(τ) = (c₂(O), c₂(O)) + Sign(∇(∇(τ))) + Sign(τ_t).    ...(11.7)

(b) If r₂(Ǒ) = r₃(Ǒ) > 0, then (11.6) is injective with specified image, and
  Sign(τ) = (c₂(O)-1, c₂(O)-1) + Sign(∇(∇(τ))) + Sign(τ_t).    ...(11.9)

### Proof sketch
The map τ ↦ (∇²(τ), τ_t) decomposes a PBP into its "inner" part (double descent, columns ≥ 1) and "outer" part (tail, column 0 above Q).

**Signature formula (11.7):** For D type, PBP.signature decomposes as:
  p_τ = nDot_total + 2·nR_total + nC_total + nD_total

Using `countSym_split` (from Tail.lean):
  P.countSym(σ) = countSymCol0(P, σ) + countSymColGe1(P, σ)

The col0 part splits into [0, Q.colLen(0)) where all cells are dots, and [Q.colLen(0), P.colLen(0)) which is the tail. So:
  nDot_col0 = Q.colLen(0)  (dots below Q)
  nR_col0 = nR in tail, nS_col0 = nS in tail, etc.

The colGe1 part equals the corresponding count in ∇²(τ) (since descent preserves columns ≥ 1, by `countSymColGe1_eq`).

For D type Q is all dots, so Q.countSym(σ) = 0 for σ ≠ dot (`Q_countSym_eq_zero_of_D`).

Assembling:
  p_τ = Q.colLen(0) + 2·(rCol0_tail + rColGe1) + (cCol0_tail + cColGe1) + (dCol0_tail + dColGe1)
      = Q.colLen(0) + (2·rColGe1 + cColGe1 + dColGe1) + (2·rCol0_tail + cCol0_tail + dCol0_tail)
      = Q.colLen(0) + p_{∇²(τ)} + p_{τ_t}

where we use:
- c₂(O) = Q.colLen(0) = (r₂-1)/2 (`colLen_0_of_dp_cons₂_Q`)
- p_{∇²(τ)} = nDot_ge1 + 2·nR_ge1 + nC_ge1 + nD_ge1 (the double descent signature)
- p_{τ_t} = 2·nR_tail + nC_tail + nD_tail (from `DRCSymbol.tailContrib`)

The same holds for q_τ. This gives (11.7).

For case (b) with r₂ = r₃: the correction in the tail definition (see [BMSZb] p71) changes c₂(O) to c₂(O)-1.

**Injectivity/bijectivity:** This is `ddescent_inj_D` (Prop 10.9 in [BMSZb]).
The map τ ↦ (∇(τ), p_τ, q_τ, ε_τ) is injective, and (∇²(τ), τ_t) determines (∇(τ), p_τ, q_τ, ε_τ). □

### Lean status
- ✅ `ddescent_inj_D`: τ ↦ (∇²τ, sig, ε) injective
- ✅ `countSym_split`: P.countSym = col0 + colGe1
- ✅ `Q_countSym_eq_zero_of_D`: D-type Q has no non-dot
- ✅ `countSymColGe1_eq`: cols ≥ 1 agree under descent
- ✅ `colLen_0_of_dp_cons₂_Q`: c₂(O) = (r₂-1)/2
- ❌ **Signature decomposition formula (11.7) as standalone theorem**

### Key missing piece
Need to state and prove:
```lean
theorem signature_decomp_D (τ : PBP) (hγ : τ.γ = .D) ... :
    PBP.signature τ = (Q.colLen 0 + (PBP.signature (∇²τ)).1 + (tailSignature_D τ).1,
                       Q.colLen 0 + (PBP.signature (∇²τ)).2 + (tailSignature_D τ).2)
```
All ingredients exist in Tail.lean; just needs assembly.

---

## Lemma 11.3 (Tail symbol ↔ tail signature, ★ ∈ {B, D})

### Statement
Suppose ★ ∈ {B, D}, (★, |Ǒ|) ≠ (D, 0), τ ∈ PBP★(Ǒ). Then:
- ε_τ = 0 if and only if x_τ = d
- p_{τ_t} = 0 if and only if x_τ = s
- q_{τ_t} = 0 if and only if x_τ = r  ← **this claim needs refinement; skip**

### Proof
**(a) ε_τ = 0 ↔ x_τ = d:**
ε_τ = 0 iff d occurs in column 0 of P or Q. For D type, Q is all dots (no d). So ε_τ = 0 iff d occurs in P's column 0. By layer monotonicity (layerOrd non-decreasing from top to bottom), d (layerOrd 4) can only appear at the bottom. The bottom of P's column 0 is x_τ (when the tail is nonempty). So d in col 0 iff x_τ = d. ✓

**(b) p_{τ_t} = 0 ↔ x_τ = s:**
(⟸) If x_τ = s: the bottom tail cell has layerOrd(s) = 1. By layer mono, all tail cells have layerOrd ≤ 1. Since tail cells are non-dot (from dot_match: col0 above Q has no dots), they must be s (the only non-dot symbol with layerOrd ≤ 1). So every tail cell is s. tailContrib(s) = (0, 2), so p_{τ_t} = Σ 0 = 0.

(⟹) If x_τ ≠ s: then x_τ ∈ {r, c, d}. tailContrib(r).1 = 2, tailContrib(c).1 = 1, tailContrib(d).1 = 1. Since x_τ contributes ≥ 1 to p, p_{τ_t} ≥ 1 > 0. ✓

**(c)** Skipped (needs refinement — see discussion with user).

### What we actually need for Prop 11.8
Instead of (c), we need:
- q_{τ_t} ≥ 0 (always true since it's a sum of nonneg)
- q_{τ_t} > 0 when x_τ = d (because x_τ = d contributes tailContrib(d).2 = 1 ≥ 1)

These are proved as `DRCSymbol.tailContrib_nonneg` and `DRCSymbol.tailContrib_snd_pos_of_ne_r`.

### Lean status
- ✅ `tailSymbol_d_iff_d_in_col0`: x_τ = d ↔ d in col 0
- ✅ `Q_no_d_in_col0_D`: D-type Q has no d
- ✅ `tail_all_s_of_tailSymbol_s`: x_τ = s ⟹ all tail cells are s
- ✅ `tailContrib_fst_pos_of_ne_s`: σ ≠ s ⟹ tailContrib.1 > 0
- ✅ `tailContrib_snd_pos_of_ne_r`: σ ≠ r ⟹ tailContrib.2 > 0
- ✅ `tail_cell_layerOrd_D`: tail cell layerOrd bounds

---

## Lemma 11.5 (Two-step AC formula, ★ ∈ {B, D})

### Statement
Suppose ★ ∈ {B, D}, (★, |Ǒ|) ≠ (D, 0). Define γ_τ as in (11.10).

(a) If r₂(Ǒ) > r₃(Ǒ), then:
  𝓛_τ = T^{γ_τ}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ)

(b) If r₂(Ǒ) = r₃(Ǒ), then 𝓛_τ = 𝓛_{τ,+} + 𝓛_{τ,-} with formulas (11.13)-(11.14).

### Proof
Apply the induction formula (11.2) twice:

**Step 1:** Since ★ ∈ {B, D}, (11.2) gives:
  𝓛_τ = θ̂^{s_τ,O}_{s_{τ'},O'}(𝓛_{τ'}) ⊗ (0, ε_τ)

**Step 2:** Since ★' ∈ {C, C̃}, (11.2) gives:
  𝓛_{τ'} = θ̂^{s_{τ'},O'}_{s_{τ''},O''}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}))

**Step 3:** Substitute Step 2 into Step 1. The composition of two theta lifts gives:
- The inner lift (9.30) for ★' ∈ {C, C̃}: involves Σ_{j=0}^{δ'} Λ_{(j,δ'-j)} augmented by (n₀', n₀')
- The outer lift (9.29) for ★ ∈ {B, D}: truncates by (δ/2, δ/2) and augments by (p₀, q₀)

**Step 4:** Use the signature formulas (11.7)/(11.9) from Prop 11.4 to compute the augmentation parameters. The key arithmetic:
- δ = c₁(O) - c₂(O) relates to r₁(Ǒ) - r₂(Ǒ)
- For case (a) r₂ > r₃: the truncation in (9.29) is Λ_{(0,0)} = identity (since δ corresponds to the orbit structure)
- The augmentation parameters compose to give (p_{τ_t}, q_{τ_t})
- The character twist parameters compose to give γ_τ

**Step 5:** For case (b) r₂ = r₃: the truncation sum in (9.30) has δ' = 1, giving two terms. These produce 𝓛_{τ,+} via 𝓛_{τ''}^+ and 𝓛_{τ,-} via 𝓛_{τ''}^-. □

### Lean status
- ✅ `AC.step`: one step of AC recursion
- ✅ `AC.fold`: chain computation
- ✅ All theta lift formulas
- ❌ **Composition of two theta lifts**
- ❌ **Signature formula (11.7) application**

### Difficulty: Hard
This is the most complex theorem. Requires connecting:
1. Two steps of AC.step
2. The signature decomposition (Prop 11.4)
3. Orbit-level arithmetic (c₁, c₂, δ)

---

## Lemma 11.6 (First entry of 𝓛_τ, ★ ∈ {B, D})

### Statement
Suppose ★ ∈ {B, D}, (★, |Ǒ|) ≠ (D, 0).

(a) If r₂ > r₃ and ℰ has nonzero coefficient in 𝓛_τ, then:
  ℰ(1) = (p_{τ_t}, (-1)^{ε_τ} q_{τ_t})

(b) If r₂ = r₃ and ℰ₊ in 𝓛_{τ,+}, then q_{τ_t} ≥ 1 and:
  ℰ₊(1) = (p_{τ_t}, (-1)^{ε_τ}(q_{τ_t} - 1))

(c) If r₂ = r₃ and ℰ₋ in 𝓛_{τ,-}, then p_{τ_t} ≥ 1 and:
  ℰ₋(1) = (p_{τ_t} - 1, (-1)^{ε_τ} q_{τ_t})

### Proof
Direct read-off from Lemma 11.5.

**(a):** From (11.11), 𝓛_τ = ... ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ).
The augment ⊕ (p_{τ_t}, q_{τ_t}) puts (p_{τ_t}, q_{τ_t}) at position 1 (index 0).
The sign twist ⊗ (0, ε_τ) acts on odd-length rows. Row 1 (index 0, length 1) is odd.
The twist formula gives: q₁ ↦ (-1)^{(0+1)/2 · 0 + (0-1)/2 · ε_τ} doesn't simplify easily.

Actually, from (9.15) with (ε⁺, ε⁻) = (0, ε_τ) at i = 1 (odd):
  (p₁, q₁) ↦ ((-1)^{1·0 + 0·ε_τ} p₁, (-1)^{0·0 + 1·ε_τ} q₁) = (p₁, (-1)^{ε_τ} q₁)

So ℰ(1) = (p_{τ_t}, (-1)^{ε_τ} q_{τ_t}). ✓

**(b):** From (11.13), 𝓛_{τ,+} = ... ⊕ (p_{τ_t}, q_{τ_t} - 1) ⊗ (0, ε_τ).
Same twist calculation: ℰ₊(1) = (p_{τ_t}, (-1)^{ε_τ}(q_{τ_t} - 1)).
For this to be valid, we need q_{τ_t} - 1 ≥ 0, i.e., q_{τ_t} ≥ 1. This holds because 𝓛_{τ,+} is nonzero, which requires 𝓛_{τ''}^+ ≠ 0. ✓

**(c):** Symmetric to (b). □

### Lean status
- ❌ Depends on Lemma 11.5

---

## Proposition 11.7 (Multiplicity free, ★ ∈ {B, D})

### Statement
𝓛_τ is multiplicity free. When (★, |Ǒ|) ≠ (D, 0) and r₂ = r₃, both 𝓛_{τ,+} and 𝓛_{τ,-} are also multiplicity free.

### Proof
By induction on the number of rows of Ǒ.

**Base case:** |Ǒ| = 0. Then 𝓛_τ is a single MYD (from AC.base), trivially multiplicity free. ✅ `AC.base_multiplicityFree`.

**Inductive step, r₂ > r₃:** By (11.11), 𝓛_τ = T^{γ_τ}(𝓛_{τ''} ⊗ (ε_{℘'}, ε_{℘'}) ⊕ (n₀, n₀)) ⊕ (p_{τ_t}, q_{τ_t}) ⊗ (0, ε_τ).

The four operations are:
1. ⊗ (ε_{℘'}, ε_{℘'}): sign twist — bijection on MYD ✅ `ACResult.twistBD_multiplicityFree`
2. ⊕ (n₀, n₀): augmentation — injective ✅ `ACResult.augment_multiplicityFree`
3. T^{γ_τ}: involution — bijection ✅ `ACResult.charTwistCM_multiplicityFree`
4. ⊕ (p_{τ_t}, q_{τ_t}): augmentation — injective ✅
5. ⊗ (0, ε_τ): sign twist — bijection ✅

By IH, 𝓛_{τ''} is multiplicity free. Each operation preserves mult-free. So 𝓛_τ is mult-free.

**Inductive step, r₂ = r₃:** 𝓛_{τ,+} uses 𝓛_{τ''}^+ (truncation of 𝓛_{τ''}), 𝓛_{τ,-} uses 𝓛_{τ''}^-. Truncation is injective (on the set where containment holds), so preserves mult-free. Then the subsequent operations (augment, twist) also preserve mult-free.

For 𝓛_τ = 𝓛_{τ,+} + 𝓛_{τ,-}: by Lemma 11.6, elements of 𝓛_{τ,+} have first entry (p_{τ_t}, (-1)^{ε_τ}(q_{τ_t}-1)) and elements of 𝓛_{τ,-} have first entry (p_{τ_t}-1, (-1)^{ε_τ} q_{τ_t}). These are different (since p_{τ_t} ≥ 1 and q_{τ_t} ≥ 1 in this case). So the supports of 𝓛_{τ,+} and 𝓛_{τ,-} are disjoint, and 𝓛_τ is mult-free. □

### Lean status
- ✅ All preservation lemmas proved
- 📐 `AC.step_multiplicityFree_BD` (1 sorry — needs Lemma 11.5)

---

## Proposition 11.8 (Nonzero and truncation, ★ ∈ {B, D})

### Statement
(a) 𝓛_τ ≠ 0.
(b) If (★, |Ǒ|) ≠ (D, 0) and x_τ = s, then 𝓛_τ^+ = 0 and 𝓛_τ^- = 0.
(c) If x_τ ∈ {r, c}, then 𝓛_τ^+ ≠ 0 and 𝓛_τ^- = 0.
(d) If x_τ = d, then 𝓛_τ^+ ≠ 0 and 𝓛_τ^- ≠ 0.

### Proof
By induction on the number of rows of Ǒ.

**Base case |Ǒ| = 0:** 𝓛_τ is a single MYD, so (a) holds. For B⁺: (1,0), so 𝓛^+ = (0,0) ≠ 0, 𝓛^- has containment check on q₁ = 0: fails. For B⁻: (0,-1), 𝓛^+ check on p₁ = 0: fails, 𝓛^- check on q₁ = -1: 0 ≤ 1 ≤ -1 fails, -1 ≤ 1 ≤ 0 fails. So 𝓛^+ = 𝓛^- = 0. This matches x_τ = s for B⁻ (convention) and x_τ = c for B⁺.

**Inductive step, r₂ > r₃:** By Lemma 11.6(a), every ℰ in 𝓛_τ has ℰ(1) = (p_{τ_t}, (-1)^{ε_τ} q_{τ_t}).

By Lemma 11.3:
- x_τ = s ⟹ p_{τ_t} = 0, ε_τ = 1, q_{τ_t} ≥ 2 ⟹ ℰ(1) = (0, -q_{τ_t}) with q_{τ_t} ≥ 2.
  𝓛^+ = Λ_{(1,0)}: needs |p₁| ≥ 1. p₁ = 0 < 1. Fails. 𝓛^+ = 0. ✓
  𝓛^- = Λ_{(0,1)}: needs |q₁| ≥ 1. q₁ = -q_{τ_t} ≤ -2. Containment (9.19): need 0 ≤ 1 ≤ q₁ (fails since q₁ < 0) or q₁ ≤ 1 ≤ 0 (fails since 1 > 0). 𝓛^- = 0. ✓

- x_τ ∈ {r, c} ⟹ p_{τ_t} > 0, ε_τ = 1 ⟹ ℰ(1) = (p_{τ_t}, -q_{τ_t}).
  𝓛^+ = Λ_{(1,0)}: p₁ = p_{τ_t} ≥ 1. 0 ≤ 1 ≤ p₁. Succeeds. 𝓛^+ ≠ 0. ✓
  𝓛^- = Λ_{(0,1)}: q₁ = -q_{τ_t} ≤ 0. Same argument as above: fails. 𝓛^- = 0. ✓

- x_τ = d ⟹ p_{τ_t} > 0, ε_τ = 0, q_{τ_t} > 0 ⟹ ℰ(1) = (p_{τ_t}, q_{τ_t}).
  𝓛^+ = Λ_{(1,0)}: p₁ = p_{τ_t} ≥ 1. Succeeds. 𝓛^+ ≠ 0. ✓
  𝓛^- = Λ_{(0,1)}: q₁ = q_{τ_t} ≥ 1. 0 ≤ 1 ≤ q₁. Succeeds. 𝓛^- ≠ 0. ✓

**Inductive step, r₂ = r₃:** The case analysis for x_τ is similar but uses 𝓛_{τ,+} and 𝓛_{τ,-}. The argument goes through because the first entries from Lemma 11.6(b)(c) still determine the truncation behavior. □

### Lean status
- ✅ All ingredient lemmas (11.3(a)(b), tailContrib properties)
- ❌ Full theorem (needs Lemma 11.6 → Lemma 11.5)

---

## Lemma 11.9 (No cross-twist)

### Statement
If r₁(Ǒ) > r₃(Ǒ), there exist no τ₁, τ₂ ∈ PBP★^ext(Ǒ) with T(𝓛_{τ₁}^- ⊕ (0,0)) = 𝓛_{τ₂}^+ ⊕ (0,0) ≠ 0.

### Proof
Contradiction. Prop 11.8 implies x_τ = d (since 𝓛^+ ≠ 0 and 𝓛^- ≠ 0), so ε_τ = 0, p_{τ_t}, q_{τ_t} ≥ 1. Then detailed case analysis using 11.5 and 11.8 for both r₂ > r₃ and r₂ = r₃ cases leads to contradiction via the orbit structure. □

### Lean status: ❌

---

## Lemma 11.10, 11.11, Proposition 11.12 (Injectivity chain)

### Lemma 11.10
If 𝓛_{τ₁}^+ = 𝓛_{τ₂}^+ and ε_{τ₁} = ε_{τ₂}, or 𝓛_{τ₁}^- = 𝓛_{τ₂}^- ≠ 0, then tail signatures agree.

### Lemma 11.11
No τ₁, τ₂ with 𝓛_{τ₁} ⊗ (1,1) = 𝓛_{τ₂}.

### Proposition 11.12
If 𝓛_{τ₁} ⊗ (ε₁, ε₁) = 𝓛_{τ₂} ⊗ (ε₂, ε₂), then ε₁ = ε₂, ε_{τ₁} = ε_{τ₂}, 𝓛_{τ₁} = 𝓛_{τ₂}.

**Proof chain:** 11.11 follows from 11.8 (det twist creates impossible truncation pattern). 11.12 follows from 11.11 (ε₁ = ε₂) + 11.8 (ε_τ determined by truncation). 11.10 follows from 11.6 (first entry determines tail sig). □

### Lean status: ❌

---

## Lemma 11.13, 11.14 (Injectivity and surjectivity for quasi-distinguished)

### Lemma 11.13
If Ǒ quasi-distinguished and 𝓛_{τ₁} = 𝓛_{τ₂}, then τ₁ = τ₂.

### Lemma 11.14
If Ǒ quasi-distinguished, then for all ℰ ∈ MYD★(O), there exist τ and ε with 𝓛_τ ⊗ (ε,ε) = ℰ.

**Proofs:** By induction using 11.12, 11.10, and the descent injectivity (Prop 11.4). □

### Lean status: ❌

---

## Proposition 11.15 (Main theorem for B/D, quasi-distinguished)

### Statement
The map (τ, ε) ↦ 𝓛_τ ⊗ (ε, ε) from PBP★^ext(Ǒ) × ℤ/2ℤ to ℤ[MYD★(O)] is injective with image MYD★(O).

### Proof
Injectivity from 11.12 + 11.13. Surjectivity from 11.14. □

### Lean status: ❌

---

## Section 11.5: C/C̃ analogs (Prop 11.16, 11.17)

Similar results for ★ ∈ {C, C̃}, using descent properties from [BMSZb] Prop 10.8.

### Lean status: ❌

---

## Formalization Plan

### Phase 1: Signature decomposition (critical path)
1. Extract `signature_decomp_D` from existing Tail.lean infrastructure
2. Connect to tailSignature_D

### Phase 2: Lemma 11.5
3. Prove composition of two theta lifts
4. Use signature decomposition to compute augmentation parameters

### Phase 3: Downstream chain
5. Lemma 11.6 (from 11.5)
6. Prop 11.7 (fill the 1 sorry)
7. Prop 11.8 (from 11.3 + 11.6)

### Phase 4: Injectivity
8. Lemmas 11.9–11.11
9. Prop 11.12
10. Lemmas 11.13–11.14
11. Prop 11.15

### Estimated difficulty
- Phase 1: Medium (assembly of existing lemmas)
- Phase 2: Hard (composition arithmetic)
- Phase 3: Medium (case analysis using Phase 2)
- Phase 4: Medium-Hard (induction with Phase 3)
