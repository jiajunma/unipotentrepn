# B Balanced Step Fiber Structure — Complete Analysis

## Goal

Close `CorrespondenceB.lean:2170` — the B-type balanced recursive step:
```
card(B⁺ ∪ B⁻ on r₁::r₂::rest) = dd' · 4k + rc' · (4k-2)
```
where `(dd', rc', _) = countPBP_B(rest)` and `k = (r₁-r₂)/2 + 1`.

## 1. Tail Symbol x_τ with α-Correction

### Paper definition ([BMSZb] §10.5)

For τ ∈ B⁺/B⁻ with shape (P, Q):
- `c₁(ι) = P.colLen(0)`, `c₁(j) = Q.colLen(0)`
- `setA_size = c₁(j) - c₁(ι)`
- `k = setA_size + 1`

Tail multiset `{x₁, ..., x_k}`:
- **Set A** = `{Q(i, 0) | c₁(ι) ≤ i < c₁(j)}` has `setA_size` elements
- **Correction element** x₁ added:
  - If `c₁(ι) = 0` OR `Q(c₁(ι)-1, 0) ∈ {•, s}`:
    - γ = B⁺: x₁ = **c**
    - γ = B⁻: x₁ = **s**
  - Else: x₁ = `Q(c₁(ι)-1, 0)` (∈ {r, d})

`x_τ := x_k` (last element):
- If `setA_size > 0`: x_τ = Q(c₁(j)-1, 0) (γ-independent, ∈ {•,s,r,d})
- If `setA_size = 0` (k=1): x_τ = x₁ (correction, γ-dependent)

### Key consequence

When `setA_size = 0` and boundary triggers correction:
- B⁺ PBP gets x_τ = **c** (not in natural Q symbols for B!)
- B⁻ PBP gets x_τ = **s**

So `x_τ = c ⟹ γ = B⁺`, `x_τ = s via correction ⟹ γ = B⁻`.

## 2. countPBP_B Components — Combinatorial Interpretation

**Theorem (empirically verified for 22+ dp)**:
```
countPBP_B(dp) = (dd_α, rc_α, ss_α)
```
where:
```
dd_α = |{σ ∈ B⁺ ∪ B⁻ : x_τ = d}|                                    (DD_α count)
rc_α = |{σ ∈ B⁺ : x_τ ≠ d}| + |{σ ∈ B⁻ : x_τ ∈ {r, c}}|           (RC_α count)
ss_α = |{σ ∈ B⁻ : x_τ ∈ {•, s}}|                                    (SS_α count)
```

Equivalently, partition B-PBPs into α-classes (γ-dependent):
- **B⁺**: DD_α (x=d), RC_α (x ∈ {r, c, s, •}). **No SS_α for B⁺**.
- **B⁻**: DD_α (x=d), RC_α (x ∈ {r, c}), SS_α (x ∈ {s, •}).

Note: B⁻ never has x_τ = c (correction gives s for B⁻).

### Verification data

| dp | count | B⁺ nat | B⁻ nat | α-check |
|---|---|---|---|---|
| (2,) | (2,3,1) | (1,1,1) | (1,1,1) | dd=1+1 ✓, rc=(1+1)+1 ✓, ss=1 ✓ |
| (4,2) | (6,8,2) | (3,3,2) | (3,3,2) | dd=6 ✓, rc=(3+2)+3=8 ✓, ss=2 ✓ |
| (4,4) | (2,4,2) | (1,3,0) | (1,1,2) | dd=2 ✓, rc=(1+3+0)+1=5≠4 ❌|

Wait, (4,4) check: B⁺ α (correction active): x_τ = d(1), c(2), r(1), s(0) — so B⁺ non-d = 3 (not 2+0=2). And B⁻ α: x=r,c means (1), so rc = 3 + 1 = 4 ✓. OK my tabulation was off; let me redo:

| dp | count | B⁺ (d,r,c,s,•) | B⁻ (d,r,c,s,•) | α-check |
|---|---|---|---|---|
| (4,4) | (2,4,2) | (1,1,2,0,0) | (1,1,0,2,0) | dd=2, rc=(1+2)+1=4 ✓, ss=2 ✓ |
| (6,4,4) | (22,31,9) | (11,11,0,9,0) | (11,11,0,9,0) | dd=22, rc=(11+9)+11=31 ✓, ss=9 ✓ |

(For (4,4) k_sub=1, correction active; for (6,4,4) k_sub=2 at top of sub, no correction.)

## 3. Balanced Fiber Formula — Uniform by x_τ

**Theorem (empirically verified over many cases)**:

For the recursion on (r₁::r₂::rest) with `k = (r₁-r₂)/2+1` and **balanced** (r₂ ≤ r₃):

Each sub-PBP σ (on dp = rest) has fiber size in new level depending only on `σ.x_τ_corrected`:

```
fiber_bal(x_τ, k) = {
  4k        if x_τ = d
  4k - 2    if x_τ = r
  2k - 1    if x_τ ∈ {c, s, •}
}
```

### Verification data (k_new=2, balanced):

| x_τ | fiber | expected 4k / 4k-2 / 2k-1 |
|---|---|---|
| d | 8 | 4·2=8 ✓ |
| r | 6 | 4·2-2=6 ✓ |
| c | 3 | 2·2-1=3 ✓ |
| s | 3 | 2·2-1=3 ✓ |

### Structural reason

In balanced step (r₂ = r₃), the new Q col 0 cells at rows overlapping with sub's Q col 0
are constrained: layerOrd ≤ sub's Q col 0 at same row (by `mono_Q`).

At the boundary row (sub's Q col 0 top), new Q cell layerOrd is ≤ sub's top symbol layerOrd:
- sub x_τ = d (layerOrd 4): no real constraint → 4k configs
- sub x_τ = r (layerOrd 2): can't be d (4) or c (3) → 4k-2 configs
- sub x_τ ∈ {c (3), s (1), • (0)}: heavily constrained → 2k-1 configs

## 4. Primitive Fiber (for comparison)

For **primitive** (r₂ > r₃), fiber is uniform across ALL x_τ:
```
fiber_prim(x_τ, k) = 4k
```

## 5. Derivation of countPBP_B Balanced Formula

From fiber analysis:
```
card(new) = |d_subs|·4k + |r_subs|·(4k-2) + (|c_subs| + |s_subs| + |•_subs|)·(2k-1)
```

From countPBP_B balanced formula:
```
tripleSum(new) = dd_α · 4k + rc_α · (4k-2)
```

Where dd_α = |d_subs|, rc_α = |B⁺ non-d| + |B⁻ in {r,c}|.

**Key γ-swap identity**: The two formulas agree iff
```
|B⁺ with x_τ ∈ {c, s, •}| = |B⁻ with x_τ ∈ {s, •}|
```

This holds by γ-swap symmetry: the swap `τ ↦ τ'` (change γ tag, keep drc) gives a bijection:
- `(B⁺, natural Q ∈ {•,s})` ↔ `(B⁻, natural Q ∈ {•,s})` — same drc, different correction outcome
- `(B⁺, setA > 0, Q bot = s)` ↔ `(B⁻, setA > 0, Q bot = s)` — same natural x_τ
- `(B⁺, setA > 0, Q bot = •)` ↔ `(B⁻, setA > 0, Q bot = •)` — same natural x_τ

Under this bijection:
- LHS: B⁺ with x_τ=c (correction from {•,s}) + B⁺ with setA>0 and natural {s, •}
- RHS: B⁻ with x_τ=s (correction from {•,s}) + B⁻ with setA>0 and natural {s, •}

Both count the same thing up to γ-relabeling.

## 6. Lean Formalization Plan (Approach A)

Decompose the sorry at `CorrespondenceB.lean:2170` into focused lemmas:

### Phase 1: x_τ_corrected definition

```lean
def PBP.tailSymbol_B_corrected (τ : PBP) : DRCSymbol := ...
```

### Phase 2: α-class count identities (3 lemmas)

```lean
lemma count_Bpm_d_eq_countB_dd (dp : DualPart) ... :
  (Finset.univ.filter (fun σ : PBPSet .Bplus _ _ => σ.val.tailSymbol_corrected = .d)).card +
  (Finset.univ.filter (fun σ : PBPSet .Bminus _ _ => σ.val.tailSymbol_corrected = .d)).card = 
  (countPBP_B dp).1

lemma count_rc_alpha_eq_countB_rc (dp : DualPart) ... :
  -- B+ non-d + B- in {r,c}
  ... = (countPBP_B dp).2.1

lemma count_Bminus_ss_alpha_eq_countB_ss (dp : DualPart) ... :
  -- B- in {s, •}  (same as Task #13's card_Bminus_bottom_lo_le_one_eq_ss)
  ... = (countPBP_B dp).2.2
```

### Phase 3: Balanced fiber uniform by x_τ (5 lemmas)

```lean
lemma fiber_balanced_d {σ : sub-PBP with x_τ = .d} ... : fiber σ = 4 * k

lemma fiber_balanced_r {σ : sub-PBP with x_τ = .r} ... : fiber σ = 4 * k - 2

lemma fiber_balanced_c {σ : sub-PBP with x_τ = .c} ... : fiber σ = 2 * k - 1

lemma fiber_balanced_s {σ : sub-PBP with x_τ = .s} ... : fiber σ = 2 * k - 1

lemma fiber_balanced_dot {σ : sub-PBP with x_τ = .dot} ... : fiber σ = 2 * k - 1
```

### Phase 4: γ-swap symmetry

```lean
lemma gamma_swap_corrected_symmetry :
  |B⁺ with x_τ_corrected ∈ {c, s, dot}| = |B⁻ with x_τ_corrected ∈ {s, dot}|
```

### Phase 5: Combine

```lean
theorem card_PBPSet_B_balanced_step ... :
  card(B⁺∪B⁻ on r₁::r₂::rest) = dd' · 4k + rc' · (4k-2)
```

Proof: split subs by x_τ_corrected via Phase 3, use Phase 2 for counts, Phase 4 for equivalence.

## 7. Status

- Phase 1 (definition): TODO
- Phase 2 (α-class counts): TODO — Phase 2's ss identity is Task #13
- Phase 3 (fiber sizes): TODO — 5 lemmas
- Phase 4 (γ-swap): TODO
- Phase 5 (combination): quick once Phase 2-4 done

Each phase has clear, testable sub-lemmas. No single large unstructured sorry.
