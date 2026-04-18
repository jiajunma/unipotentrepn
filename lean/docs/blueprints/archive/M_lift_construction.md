# M→B Lift Construction: Complete Natural Language Proof

## 1. M→B Descent (已形式化)

Input: M PBP τ = (P, Q, M) with P symbols {•, s, c}, Q symbols {•, r, d}.

Steps:
1. Compute γ' = B⁻ if c ∈ P col 0, B⁺ otherwise
2. Remove P col 0: P' cols = P cols shifted left
3. Apply `_fill_ds_B` to (P', Q): redistribute dot/s zones
   - For each column j:
     - cL = #{dot/s in P'(·,j)}, cR = #{dot/s in Q(·,j)}
     - New P(·,j) = cL dots then P'[cL:] (non-dot/s part = c only)
     - New Q(·,j) = cL dots then (cR-cL) s's then Q[cR:] (non-dot/s part = r/d)
4. Output: B PBP (new P, new Q, γ')

Result: B PBP with P ∈ {•, c}, Q ∈ {•, s, r, d}.

## 2. B→M Lift (needs construction)

Input: B PBP σ = (P_B, Q_B, γ') with γ' ∈ {B⁺, B⁻}.

Steps (reverse of descent):
1. Apply `_fill_ds_M` to (P_B, Q_B): undo dot/s redistribution
   - For each column j:
     - cL = #{dot/s in P_B(·,j)} = #{• in P_B(·,j)} (B P has no s!)
     - cR = #{dot/s in Q_B(·,j)} = #{•, s in Q_B(·,j)}
     - M P(·,j+1) = cR dots then (cL-cR) s's then P_B[cL:] (= c cells)
     
     Wait: `_fill_ds_M` definition:
     ```
     ndrcL.append('*' * cR + 's' * (cL - cR) + colL[cL:])
     ndrcR.append('*' * cR + colR[cR:])
     ```
     So:
     - M P'(·,j) = cR dots, then (cL-cR) s's, then P_B(·,j) non-dot/s part (= c cells)
     - M Q'(·,j) = cR dots, then Q_B(·,j) non-dot/s part (= r/d cells)
     
2. Insert P col 0:
   - P col 0 length = μP.colLen(0) = r₁/2 (M type)
   - P col 0 paint:
     - Dots where M Q col 0 has dots (dot_match)
     - Non-dot zone: s and possibly c
     - γ' = B⁺ → **no c** in P col 0 → all non-dot cells are s
     - γ' = B⁻ → **c at bottom** of P col 0
   
   The non-dot boundary is determined by: M Q col 0 = cR dots then r/d cells.
   So dot boundary in P col 0 = cR (same as Q's dot count at col 0).
   
   P col 0 from boundary upward:
   - B⁺: P(i, 0) = s for cR ≤ i < μP.colLen(0)
   - B⁻: P(i, 0) = s for cR ≤ i < μP.colLen(0) - 1, P(μP.colLen(0)-1, 0) = c

3. Output: M PBP (full P with col 0, M Q', M)

## 3. Round-trip: descent(lift(σ)) = σ

### P side
descent removes P col 0, then applies _fill_ds_B.

lift's P at j+1 = _fill_ds_M(P_B, Q_B) at col j:
- = cR dots, (cL-cR) s's, c cells

descent of this at col j:
- Remove col 0 → same as lift's P at j+1 → same as _fill_ds_M result at col j
- Apply _fill_ds_B: 
  - cL' = #{dot/s in _fill_ds_M_P(·,j)} = cR + (cL-cR) = cL (dots + s's)
  - cR' = #{dot/s in _fill_ds_M_Q(·,j)} = cR (only dots)
  
  _fill_ds_B result P: cL' dots then non-dot/s = cL dots then c cells = original P_B(·,j) ✓
  _fill_ds_B result Q: cL' dots then (cR'-cL') s's then non-dot/s
  = cL dots then (cR-cL) s's then r/d
  = original Q_B(·,j)? 
  
  Wait: cR' = cR (dots in _fill_ds_M_Q) and cL' = cL. 
  _fill_ds_B gives: Q = cL' dots, (cR'-cL') s's, Q_nonDS.
  = cL dots, (cR-cL) s's, r/d cells = Q_B(·,j). ✓

### Q side
descent Q = _fill_ds_B Q from (P', Q') where P' = lift P without col 0 = _fill_ds_M P.
As shown above: _fill_ds_B of _fill_ds_M is identity. ✓

### γ side
descent γ' = B⁻ if c in lift P col 0, B⁺ otherwise.
- B⁺ lift: no c in col 0 → γ' = B⁺ ✓
- B⁻ lift: c at bottom of col 0 → γ' = B⁻ ✓

### Shapes
descent output has same shapes as σ (since _fill_ds_B/_fill_ds_M don't change shapes). ✓

**Round-trip holds.** ✓

## 4. Surjectivity (primitive case)

From round-trip: for every B PBP σ, lift(σ) is an M PBP with descent(lift(σ)) = σ.

So descent is surjective. Combined with injectivity → bijection.

card(M) = card(B target) = tripleSum(countPBP_B(r₂::rest)). ✓

## 5. Image characterization (balanced case)

When r₁ = r₂ (balanced), Prop 10.8(b): descent image = {τ' : x_{τ'} ≠ s}.

**Why SS B PBPs have no M preimage**:

If σ is a B PBP with tail symbol s (SS class with paper's x_τ = s):
- For B⁻ with correction giving s: Q(c₁(ι), 1) ∈ {•, s} and α = B⁻.
  The lift for B⁻ puts c in P col 0 bottom.
  
  But balanced means r₁ = r₂, so μP.colLen(0) = r₁/2 = r₂/2 = μQ.colLen(0)... 
  
  wait, M type: P_cols = (r₁/2, ...), Q_cols = (r₂/2, ...).
  Balanced: r₁ = r₂ → P.colLen(0) = Q.colLen(0).
  
  lift P col 0 for B⁻: P(P.colLen(0)-1, 0) = c.
  M Q col 0 has length Q.colLen(0) = P.colLen(0).
  M Q(P.colLen(0)-1, 0) 来自 _fill_ds_M Q 的最底部。
  
  dot_match 需要 P(i,0) = dot ↔ Q(i,0) = dot。
  P(P.colLen(0)-1, 0) = c ≠ dot。
  所以 Q(P.colLen(0)-1, 0) ≠ dot。
  
  M Q(P.colLen(0)-1, 0) = _fill_ds_M Q 在 col 0 的最后一个 cell。
  对 B 的 SS class（x = s 从 correction）：
  Q_B(c₁(ι), 0) ∈ {dot, s}。
  
  Hmm this is getting complicated. Let me just verify computationally:

## 6. Computational verification

Need to verify: for balanced dp, no SS B PBP has an M preimage.

From the Python output for dp=(4,4):
```
M → B+ .|./.|.  → B+ |s/|s   (x=c for B+, not SS)
M → B- .|./.|.  → B+ |s/|s   (wait, this goes to B+?)
```

Actually earlier output shows all M→B for dp=(4,4):
```
M: s|r / c|d → B-: |r / |d
M: .|. / c|d → B-: |s / |d  
M: s|r / s|d → B+: |r / |d
M: .|. / s|d → B+: |s / |d
M: s|r / c|r → B-: |r / |r
M: .|. / c|r → B-: |s / |r
M: s|r / s|r → B+: |r / |r
M: .|. / s|r → B+: |s / |r
M: .|. / .|. → B+: |s / |s
```

9 M PBPs → 9 distinct B PBPs (7 B⁺ + 2 B⁻... wait let me count).

B⁻ targets: |r/|d, |s/|d, |r/|r, |s/|r → 4 B⁻ targets.
B⁺ targets: |r/|d, |s/|d, |r/|r, |s/|r, |s/|s → 5 B⁺ targets.

Total B targets = 4 + 5 = 9 (injection, each maps to distinct). But total B = 4 B⁺ + 4 B⁻ = 8.

Wait, 9 M maps to 9 distinct B, but there are only 8 B PBPs (4 DRC × 2 types). 9 > 8?!

That can't be right. Let me re-check: for B type dp=(4,4), B has 4 DRCs. So card(B⁺) = card(B⁻) = 4. Total = 8.

But the descent of 9 M PBPs gives 9 B PBPs. 9 > 8 means... **the descent is NOT injective?!**

Or wait — the B target shapes are NOT B(dp) shapes. They are shiftLeft(M.P), M.Q = (tail(r₁/2,...), (r₂/2,...)) = (... depends on dp).

For dp=(4,4): M P cols = (2,), M Q cols = (2,). ShiftLeft M P = ⊥. So B target = (⊥, μQ with Q cols (2,)).

B with P=⊥ and Q 2 cells: 3 DRC × 2 types = 6 B PBPs. But we have 9 M PBPs mapping here.

So 9 > 6. This means descent is NOT injective?! But we proved it is!

Something is wrong. Let me re-check.
