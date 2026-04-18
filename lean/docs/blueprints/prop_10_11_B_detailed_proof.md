# Prop 10.11 for B type: Detailed Natural Language Proof

Reference: [BMSZb] Propositions 10.9 and 10.11.

## Lean 形式化
- 主定理（unconditional）：`prop_10_11_B` in `CombUnipotent/CountingProof/Section10.lean`
- 证明：`card_PBPSet_B_eq_tripleSum_countPBP_B` in `CombUnipotent/CountingProof/CorrespondenceB.lean`
- Joint theorem Total+A1+A3：`card_B_combined` in `CombUnipotent/CountingProof/CorrespondenceB.lean`

## 0. Setup

★ = B. Ǒ has even row lengths r₁ ≥ r₂ ≥ ... ≥ rₘ > 0. r₂(Ǒ) > 0.

k := (r₁ - r₂)/2 + 1. S ∈ {{d}, {c,r}, {s}}.

PBP_B(Ǒ, ℘) includes painted bipartitions with α ∈ {B⁺, B⁻}.

Signature: (p_τ, q_τ) where B⁺ adds +1 to p, B⁻ adds +1 to q.

Generating function: $f^S_{B,Ǒ,℘}(\mathbf{p},\mathbf{q}) = \sum_{\tau \in PBP_B^S} \mathbf{p}^{p_\tau} \mathbf{q}^{q_\tau}$

Goal: prove recursive formula for $f^S$, then evaluate at p=q=1 to get tripleSum(countPBP_B).

## 1. Prop 10.9 (already formalized)

The map $\tau \mapsto (\nabla^2(\tau), \tau_\mathbf{t})$ from PBP_★(Ǒ, ℘) to PBP_★(Ǒ'', ℘'') × PBP_D(Ǒ_t):

**(a) Primitive** (r₂ > r₃ or ★ = C*): The map is **bijective**, and

$$\text{Sign}(\tau) = (\mathbf{c}_2(O), \mathbf{c}_2(O)) + \text{Sign}(\nabla^2(\tau)) + \text{Sign}(\tau_\mathbf{t})$$

**(b) Balanced** (★ ∈ {B, D} and r₂ = r₃ > 0): The map is **injective** with image

$$\left\{ (\tau'', \tau_0) \in PBP_★(Ǒ'', ℘'') × PBP_D(Ǒ_t) \;\middle|\; \text{either } x_{\tau''} = d, \text{ or } x_{\tau''} \in \{r, c\} \text{ and } P_{\tau_0}^{-1}(\{s,c\}) \neq \emptyset \right\}$$

and Sign(τ) = (c₂(O) - 1, c₂(O) - 1) + Sign(∇²(τ)) + Sign(τ_t).

## 2. From Prop 10.9 to Prop 10.11: The "routine calculation"

### 2.1 Primitive case (a)

Since τ ↦ (∇²(τ), τ_t) is bijective:

$$f_{★,Ǒ,℘}(\mathbf{p},\mathbf{q}) = \sum_{\tau} \mathbf{p}^{p_\tau} \mathbf{q}^{q_\tau}$$

By the signature formula Sign(τ) = (c₂, c₂) + Sign(∇²τ) + Sign(τ_t):

$$p_\tau = c_2(O) + p_{\nabla^2\tau} + p_{\tau_t}, \quad q_\tau = c_2(O) + q_{\nabla^2\tau} + q_{\tau_t}$$

So:

$$f_{★,Ǒ,℘} = \sum_{(\tau'', \tau_0)} \mathbf{p}^{c_2 + p_{\tau''} + p_{\tau_0}} \mathbf{q}^{c_2 + q_{\tau''} + q_{\tau_0}}$$

$$= (\mathbf{pq})^{c_2} \cdot \left(\sum_{\tau''} \mathbf{p}^{p_{\tau''}} \mathbf{q}^{q_{\tau''}}\right) \cdot \left(\sum_{\tau_0} \mathbf{p}^{p_{\tau_0}} \mathbf{q}^{q_{\tau_0}}\right)$$

But wait — we sum over **all** τ, not filtered by S. To get $f^S$:

$$f^S_{★,Ǒ,℘} = \sum_{\substack{\tau : x_\tau \in S}} \mathbf{p}^{p_\tau} \mathbf{q}^{q_\tau}$$

Since τ ↦ (τ'', τ_t) is a bijection, and x_τ is determined by τ_t (from Section 10.5: x_τ = P_{τ_t}(k, 1), the last symbol of the tail PBP):

$$f^S_{★,Ǒ,℘} = (\mathbf{pq})^{c_2} \cdot f_{★,Ǒ'',℘''} \cdot \sum_{\substack{\tau_0 \in PBP_D(Ǒ_t) \\ x_{\tau_0} \in S}} \mathbf{p}^{p_{\tau_0}} \mathbf{q}^{q_{\tau_0}}$$

Wait — this doesn't quite work. x_τ is determined by the tail multiset {x₁,...,xₖ}, not directly by τ_t alone. But from Section 10.5: x_τ = xₖ = P_{τ_t}(k, 1), the bottom symbol of τ_t's P column 0.

But for ★ = B, the tail multiset includes a correction that depends on α (B⁺ vs B⁻). So x_τ is NOT just a function of τ_t — it also depends on τ'' and α.

Hmm, actually let me re-read. From p.71:

> x_τ := P_{τ_t}(k, 1)

This is the symbol in the **last box** of the tail τ_t. Since τ_t ∈ PBP_D(Ǒ_t), and ★_t = D, the tail is in P's col 0, and x_τ is the bottom symbol of τ_t's P.

But from Section 10.5, the tail multiset for ★ = B includes a **correction element** that depends on α. The correction changes x₁ (the first element), NOT xₖ (the last). So x_τ = xₖ is still the bottom of τ_t's P (for k > 1).

For k = 1: Set A is empty, so {x₁} = {correction}. x_τ = x₁ = correction. This depends on α.

**Key question**: does f^S factor as $f_{sub} \times f^S_{tail}$?

For k > 1: x_τ = P_{τ_t}(k, 1) depends only on τ_t, not on α or τ''. So:

$$f^S = (\mathbf{pq})^{c_2} \cdot f_{★,sub} \cdot f^S_{D,[2k-1,1],∅}$$

where $f^S_{D,[2k-1,1],∅} = \sum_{\tau_0 : x_{\tau_0} \in S} \mathbf{p}^{p_{\tau_0}} \mathbf{q}^{q_{\tau_0}}$.

This is exactly Prop 10.11(a). ✓

For k = 1: x_τ = correction. x₁ depends on α and Q(c₁(ι), 1).

But Prop 10.11(a) (primitive case) requires r₂ > r₃. For the primitive case, the formula is:

$$f^S = (\mathbf{pq})^{c_1(O)} \cdot f^S_{D,[2k-1,1],∅} \cdot f_{★,\nabla^2(Ǒ),\nabla^2(℘)}$$

Note: c₁(O) = c₂(O) in the primitive case (since c₁(O) = (r₁+1)/2 for D... 

Actually, wait. The formula uses c₁(O), not c₂. Let me re-read.

Prop 10.11(a): $f^S = (\mathbf{pq})^{\mathbf{c}_1(O)} \cdot f^S_{D,[2k-1,1]_{row},∅} \cdot f_{★,\nabla^2(Ǒ),\nabla^2(℘)}$

And Prop 10.9(a): Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²τ) + Sign(τ_t).

So $p_\tau + q_\tau = 2c_2(O) + (p_{\tau''} + q_{\tau''}) + (p_{\tau_t} + q_{\tau_t})$.

Hmm, but the formula uses c₁(O), not c₂(O). Let me check: what is c₁(O) vs c₂(O)?

O = d_BV(Ǒ). For ★ = B: O has odd rows. c₁(O) = first column length = (number of rows of O + 1)/2 or similar.

Actually, the notation c_i refers to column lengths of the **shapes** (ι, j), not the orbit. From Section 8.3: 

For ★ = B: c₁(j_℘) = r₁(Ǒ_g)/2 (p.56). And c₂(O) relates to the BV dual.

This is getting very deep into the paper's notation. Let me instead take a more direct approach.

## 3. Direct proof of the recursion (without full generating function)

### 3.1 What we actually need to prove

For Lean, we need:

$$\text{card}(PBP_{B^+}(\mu_P, \mu_Q)) + \text{card}(PBP_{B^-}(\mu_P, \mu_Q)) = \text{tripleSum}(\text{countPBP\_B}(dp))$$

The recursion in countPBP_B:

**Primitive** (r₂ > r₃):
$$\text{tripleSum}(\text{countPBP\_B}(r_1::r_2::\text{rest})) = \text{tripleSum}(\text{countPBP\_B}(\text{rest})) \times 4k$$

**Balanced** (r₂ ≤ r₃):
$$\text{tripleSum}(\text{countPBP\_B}(r_1::r_2::\text{rest})) = dd' \times 4k + rc' \times (4k-2)$$

where dd' = countPBP_B(rest).1, rc' = countPBP_B(rest).2.1.

### 3.2 Primitive case proof (already formalized)

τ ↦ (∇²τ, col0_data) is a bijection with uniform fiber size 4k.

card(dp) = card(sub) × 4k = tripleSum(rest) × 4k = tripleSum(dp). ✓

### 3.3 Balanced case proof (needs work)

From Prop 10.9(b): τ ↦ (∇²τ, τ_t) is injective with restricted image.

Image restriction: (τ'', τ₀) is in the image iff:
- either x_{τ''} = d, OR
- x_{τ''} ∈ {r, c} and P_{τ₀}⁻¹({s, c}) ≠ ∅

This means:
- If x_{τ''} = d (DD class): ALL τ₀ ∈ PBP_D(Ǒ_t) pair with τ''. Fiber = #PBP_D(Ǒ_t).
- If x_{τ''} ∈ {r, c} (RC class): only τ₀ with P_{τ₀}⁻¹({s,c}) ≠ ∅. Fiber = #{τ₀ : P has s or c}.
- If x_{τ''} = s (SS class): NO τ₀ pairs with τ''. Fiber = 0.

Here x_{τ''} is the tail symbol of the **sub-PBP** ∇²τ (using the paper's x_τ definition).

**But x_{τ''} uses the paper's definition, which for B type includes the α correction!**

So x_{τ''} depends on whether τ'' is B⁺ or B⁻. The classes DD, RC, SS for the sub-problem use countPBP_B(rest)'s three components.

Now:
- #PBP_D(Ǒ_t) = tripleSum(countPBP_D(Ǒ_t)) = tDD + tRC + tSS = 4k
- #{τ₀ ∈ PBP_D(Ǒ_t) : P_{τ₀}⁻¹({s,c}) ≠ ∅} = ?

What does P_{τ₀}⁻¹({s,c}) ≠ ∅ mean? τ₀ is a D-type tail PBP. P_{τ₀} is a single column of k cells (from PBP_D([2k-1, 1])). P_{τ₀}⁻¹({s,c}) ≠ ∅ means at least one cell is s or c.

Since τ₀'s P has symbols from {s, r, c, d} (non-dot, from tail definition):
- The only τ₀ with NO s or c is: P all r and d (at most 1 d). So P is all r, or (k-1 r's and 1 d).
- #{P all r} = 1
- #{P with all r except 1 d at position i} = 1 for each valid position... but mono constraint means d must be at bottom. So 1 choice.
- Total: #{P with no s or c} = 2 (all-r, or all-r-except-d-at-bottom).

Wait, but P has symbols {s, r, c, d} with mono (layerOrd non-decreasing top to bottom), col_c ≤ 1, col_d ≤ 1.

With no s or c: P ∈ {r, d}^k, mono, ≤ 1 d. 
Possible: rr...r (k r's) or rr...rd (k-1 r's then d at bottom). Since layerOrd(r)=2 < layerOrd(d)=4: both are mono. And ≤ 1 d. ✓

So #{no s or c} = 2.
#{has s or c} = #PBP_D(Ǒ_t) - 2 = 4k - 2.

**This is sc_total = scDD + scRC + scSS = 4k - 2!** ✓

### 3.4 Balanced case: assembling the formula

card(dp) = Σ_{(τ'', τ₀) ∈ Image} 1

= #{τ'' : x_{τ''} = d} × #{all τ₀} + #{τ'' : x_{τ''} ∈ {r,c}} × #{τ₀ with s or c} + #{τ'' : x_{τ''} = s} × 0

But we also need to account for the signature shift. In the generating function:
$$f_{★,Ǒ,℘} = (\mathbf{pq})^{c_2-1} \sum_{(\tau'',\tau_0) \in \text{Image}} \mathbf{p}^{p_{\tau''} + p_{\tau_0}} \mathbf{q}^{q_{\tau''} + q_{\tau_0}}$$

At p=q=1:

$$f(1,1) = 1 \times \sum_{(\tau'',\tau_0) \in \text{Image}} 1 = \text{card(Image)}$$

So:
$$\text{card}(dp) = \text{card(Image)} = DD_{sub} \times 4k + RC_{sub} \times (4k-2)$$

where:
- DD_sub = #{τ'' ∈ PBP_★(Ǒ'', ℘'') : x_{τ''} = d} = $f^{\{d\}}_{★,sub}(1,1)$ = countPBP_B(rest).1 = dd'
- RC_sub = #{τ'' ∈ PBP_★(Ǒ'', ℘'') : x_{τ''} ∈ {c,r}} = $f^{\{c,r\}}_{★,sub}(1,1)$ = countPBP_B(rest).2.1 = rc'
- SS_sub contributes 0

$$\text{card}(dp) = dd' \times 4k + rc' \times (4k-2) = \text{tripleSum}(\text{countPBP\_B}(dp))$$

The last equality is verified by expanding countPBP_B:
$$\text{tripleSum} = dd' \times tDD + rc' \times scDD + dd' \times tRC + rc' \times scRC + dd' \times tSS + rc' \times scSS$$
$$= dd' \times (tDD+tRC+tSS) + rc' \times (scDD+scRC+scSS) = dd' \times 4k + rc' \times (4k-2)$$. ✓

### 3.5 But what IS dd' and rc'?

dd' = countPBP_B(rest).1 = $f^{\{d\}}_{B,Ǒ'',℘''}(1,1)$ = #{τ'' ∈ PBP_B(Ǒ'') : x_{τ''} = d}

This is the number of B-type PBPs in the sub-problem with tail symbol d.

**x_{τ''} uses the paper's definition (Section 10.5), which for B type includes the α-dependent correction!**

So dd' is NOT our simple tailClass_B count. It's the paper's x_τ count.

For the **inductive step**, we need the IH:
- dd' = countPBP_B(rest).1 = #{τ'' with paper-x = d}
- rc' = countPBP_B(rest).2.1 = #{τ'' with paper-x ∈ {c,r}}

This requires proving countPBP_B = paper's per-class count **by induction**.

## 4. Complete induction

### Statement

For all dp, countPBP_B(dp) = ($f^{\{d\}}_B(1,1)$, $f^{\{c,r\}}_B(1,1)$, $f^{\{s\}}_B(1,1)$).

Equivalently: the triple (dd, rc, ss) = (#{paper-DD}, #{paper-RC}, #{paper-SS}).

### Base cases

**dp = []**: PBP_B(∅) = {(⊥, ⊥, B⁺), (⊥, ⊥, B⁻)}. x_τ is defined with |Ǒ| = 0.
From p.70-71: for B with |Ǒ| = 0, Ǒ_t = [] (no tail). k = 0.
PBP_{★_t}(Ǒ_t) = PBP_D(∅) = {empty PBP}. x_τ = x₀ from (10.7).

When k = 0: the element in PBP_{★_t}(Ǒ_t) is ∅ × ∅ × C*. From the paragraph after (10.7):
"When k = 0 (and thus ★ = C*), the element in PBP_{★_t}(Ǒ_t) is understood to be ∅ × ∅ × C*."

Hmm, but ★_t = D for ★ = B. And k = (r₁-r₂)/2 + 1 with r₁ = r₂ = 0 gives k = 1?

Actually for dp = []: there are no rows. The base case f_{B,∅,∅} should be defined separately.
From p.72: $f^{\{d\}}_{D,[0]_{row},∅} := 1$, $f^{\{c,r\}}_{D,[0]_{row},∅} := 0$, $f^{\{s\}}_{D,[0]_{row},∅} := 0$.

For B type [0]_row (empty): $f^{\{d\}}_{B,[0]_{row},∅} := ?$

The paper only defines base cases for $f^S_{B,[2k]_{row},∅}$ on p.72 and $f^S_{D,[2k-1,1]_{row},∅}$. For the empty orbit, we use dp = [].

countPBP_B [] = (0, 1, 1). tripleSum = 2 = card(B⁺) + card(B⁻). ✓

Paper x_τ for the two PBPs:
- (⊥, ⊥, B⁺): tail multiset is empty (k=0 for empty orbit). x_τ = ... not well-defined?
  Actually for B with empty orbit, c₁(ι) = 0, c₁(j) = 0. No tail.
  But α = B⁺ gives correction c, α = B⁻ gives correction s.

So DD = 0, RC = 1 (B⁺ with x=c from correction), SS = 1 (B⁻ with x=s). ✓

**dp = [r₁]**: Single row. Ǒ_t has row lengths [2k-1, 1] where k = r₁/2 + 1.

Wait — for single row dp = [r₁] with r₂ = 0:
k = (r₁ - 0)/2 + 1 = r₁/2 + 1.

But Ǒ_t has rows [2k-1, 1] = [r₁+1, 1]. That's a D-type tail PBP.

The recursion: since there's only 1 row, rest = []. It's primitive (r₂ = 0 > r₃ doesn't exist).

Actually countPBP_B handles [r₁] as a special base case. Let me check if the recursion formula works:

Primitive: dd' = 0, rc' = 1, ss' = 1 (from countPBP_B [] = (0,1,1)). total = 2.
result = (2 × tDD, 2 × tRC, 2 × tSS).

k = r₁/2 + 1. For r₁ = 2: k = 2. tDD = nu(1)+nu(0) = 3. tRC = 2×nu(1) = 4. tSS = 1.
result = (6, 8, 2). tripleSum = 16.

But countPBP_B [2] = (2, 3, 1). tripleSum = 6.

**Mismatch!** The recursion with rest=[] gives (6,8,2) but the base case gives (2,3,1).

This is because the recursion `r₁ :: r₂ :: rest` doesn't apply to single-element lists!
dp = [r₁] = [2] is handled by the `| [r₁] =>` case, NOT by `| r₁ :: r₂ :: rest =>`.

So the "recursion" from Prop 10.9 (double descent) doesn't apply to single-row orbits — double descent needs at least 2 rows to strip. The single-row case is a direct base case.

### Inductive step: dp = r₁ :: r₂ :: rest

**IH**: countPBP_B(rest) = (#{paper-DD in rest}, #{paper-RC in rest}, #{paper-SS in rest}).

**Primitive (r₂ > r₃)**: 
By Prop 10.9(a), τ ↦ (∇²τ, τ_t) is bijective.

x_τ is determined by τ_t (since k > 1 when r₂ > r₃... actually k = (r₁-r₂)/2+1 which could be 1).

Hmm, k depends on r₁-r₂, not on r₂-r₃. The primitive condition is about the (2,3) pair being primitive (r₂ > r₃), not about k.

When k = 1: x_τ = correction (depends on α). But τ ↦ (τ'', τ_t) is still bijective.

In this case, x_τ depends on (τ'', α), not just τ_t. So f^S doesn't factor as f_sub × f^S_tail.

Wait, actually from the formula in Prop 10.11(a):
$$f^S = (\mathbf{pq})^{c_1(O)} \cdot f^S_{D,[2k-1,1]_{row},∅} \cdot f_{★,sub}$$

The **S filter** is on the tail factor $f^S_{D,[2k-1,1]}$, not on f_sub. So f_sub is **unfiltered** (total count).

This works because: x_τ depends only on τ_t (via the tail multiset), so filtering by x_τ ∈ S is the same as filtering by the tail's contribution.

But for k = 1 with B type, x_τ depends on correction (α-dependent). How does the formula handle this?

The formula uses $f^S_{D,[2k-1,1]_{row},∅}$. This is a D-type tail generating function. For k = 1: Ǒ_t = [1, 1] (D-type). PBP_D([1,1]): P = 2 cells, Q = ⊥.

Hmm wait, [2k-1, 1] for k=1 gives [1, 1]. D-type with dp = [1, 1]: all odd ✓.

$f^S_{D,[1,1]_{row},∅}$ = the generating function of D-type PBPs with orbit [1,1], filtered by tail symbol ∈ S.

For D-type [1,1]: P has shapes from dpartColLensP_D [1,1] = [(1+1)/2] = [1], Q from dpartColLensQ_D [1,1] = [] (since r₂=1, (1-1)/2 = 0, skip).

So P has 1 cell, Q = ⊥. 4 PBPs: P(0,0) ∈ {s,r,c,d}.
x_τ for D type: P(0,0) directly (no correction for D). 
DD: d(1), RC: r,c(2), SS: s(1). $f^{\{d\}}_{D,[1,1]}(1,1) = 1$, etc.

Now back to B type. The **total** generating function factors:
$$f_B = (\mathbf{pq})^{c_1} \cdot f_{D,[2k-1,1]} \cdot f_{B,sub}$$

Per-S:
$$f^S_B = (\mathbf{pq})^{c_1} \cdot f^S_{D,[2k-1,1]} \cdot f_{B,sub}$$

At p=q=1:
$$f^S_B(1,1) = 1 \cdot f^S_{D,tail}(1,1) \cdot f_{B,sub}(1,1) = \text{tS} \times \text{total\_sub}$$

So countPBP_B(dp)_S = tS × total_sub. And tripleSum = total_sub × (tDD+tRC+tSS) = total_sub × 4k. ✓

**But this uses the D-type tail for the S-filter, not B-type!** The formula says $f^S_{D,[2k-1,1]}$ — the tail is always D-type. So the S-filtering uses D-type x_τ (no B correction).

Then why does countPBP_B have different per-class values from the D-type per-class? Because the **base case** is different: countPBP_B [] = (0,1,1) while countPBP_D [] = (1,0,0). And the singleton case countPBP_B [r₁] is computed directly from $f^S_{B,[2k]_{row},∅}$ which has different formulas from the D-type.

**The recursion multiplies D-type tail coefficients by B-type total, so the per-class split propagates from base case through the D-type tail.**

This is clean and simple! The primitive step:
- dd(dp) = total(rest) × tDD_D
- rc(dp) = total(rest) × tRC_D
- ss(dp) = total(rest) × tSS_D

The balanced step:
- dd(dp) = dd(rest) × tDD_D + rc(rest) × scDD_D
- rc(dp) = dd(rest) × tRC_D + rc(rest) × scRC_D
- ss(dp) = dd(rest) × tSS_D + rc(rest) × scSS_D

Where tDD_D, etc. are the D-type tail coefficients — same for B and D types.

And the IH: dd(rest), rc(rest), ss(rest) = countPBP_B(rest)'s three components.

**To verify**: dd(rest) should equal the number of PBPs in the rest sub-problem with paper-x ∈ {d}, and this should follow from the IH.

The only subtlety: for the **balanced** step, the image restriction uses x_{τ''} from Prop 10.9(b). This x_{τ''} is the paper's x for the sub-PBP. By IH, dd(rest) = #{paper-x_{τ''} = d}.

So the proof works by induction:
1. Base case: countPBP_B base = paper's base per-class count. ✓
2. Primitive step: card(dp) = total(rest) × 4k, and per-class follows from D-type tail split. ✓
3. Balanced step: card(dp) = dd(rest) × 4k + rc(rest) × (4k-2), from Prop 10.9(b) image characterization + IH. ✓

## 5. Summary: What needs to be proved in Lean

### 5.1 Already proved
- `doubleDescent_B_PBP`: ∇² construction ✓
- `ddescent_inj_B`: injectivity ✓
- `card_PBPSet_B_primitive_step`: primitive fiber = 4k ✓
- `card_PBPSet_B_singleton`: singleton base case ✓
- `card_PBPSet_B_empty`: empty base case ✓

### 5.2 Needs proof
- **Prop 10.9(b) image characterization for B**: In balanced case, image of τ ↦ (∇²τ, τ_t) is exactly {(τ'', τ₀) : x_{τ''} = d OR (x_{τ''} ∈ {r,c} AND τ₀ has s or c in P)}.
- **#PBP_D(Ǒ_t) with P having s or c = 4k - 2**: The restricted count.
- **Per-class induction**: countPBP_B(rest) = paper's per-class count.
- **Assembly**: card(dp) = dd' × 4k + rc' × (4k-2).

### 5.3 Key insight for B balanced

The balanced step's image restriction says:
- SS sub-PBPs (x_{τ''} = s using paper definition) have fiber = 0
- RC sub-PBPs have fiber = #{τ₀ with s or c} = 4k - 2
- DD sub-PBPs have fiber = #{all τ₀} = 4k

Using per-class IH: dd' = #{DD subs}, rc' = #{RC subs}.
card = dd' × 4k + rc' × (4k-2) + 0.

And tripleSum(countPBP_B dp) = dd' × 4k + rc' × (4k-2) (algebraic identity from the recursion definition). ✓

## 6. M-type proof (Prop 10.12)

Prop 10.12: ★ ∈ {C, C̃}. 

(a) Primitive (r₁ > r₂): #PBP_★ = f_{★', ∇Ǒ, ∇℘}(1,1) = total of the descent target.
(b) Balanced (r₁ = r₂): #PBP_★ = $f^{\{c,r\}}_{★',sub}(1,1) + f^{\{d\}}_{★',sub}(1,1)$ = DD_sub + RC_sub.

For M (= C̃): ★' = B (the descent target is B-type).

(a) Primitive: card(M) = tripleSum(countPBP_B(rest)) = countPBP_M(dp). ✓
(b) Balanced: card(M) = dd(rest) + rc(rest) = countPBP_B(rest).1 + countPBP_B(rest).2.1. 

The balanced case excludes SS because: from Prop 10.8(b), when r₁ = r₂, the descent image is {τ' : x_{τ'} ≠ s}. So PBPs with x_{τ'} = s (SS class) have no M preimage.

card(M) = #{B sub-PBPs with x ≠ s} = DD + RC = dd' + rc'. ✓
