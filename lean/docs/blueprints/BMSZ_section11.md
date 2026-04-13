# Blueprint: [BMSZ] Section 11 — Combinatorial Associated Cycles

Source: [BMSZ] arXiv:1712.05552v6, pages 62-68.

## Dependency Map: Paper → Lean

| Paper | Lean declaration | Status |
|-------|-----------------|--------|
| Def 9.3 (MYD) | `ILS = List (Z x Z)` | formalized |
| Eq (9.10) Sign | `ILS.sign` | formalized |
| Eq (9.12) firstColSign | `ILS.firstColSign` | formalized |
| Eq (9.15) sign twist | `ILS.twistBD` | formalized |
| Eq (9.16) involution T | `ILS.charTwistCM` | formalized |
| Eq (9.17) T^2=id | `charTwistCM_involutive` | proved |
| Eq (9.18) augment | `ILS.augment` | formalized |
| Eq (9.19) truncate | `ILS.truncate` | formalized |
| Eq (9.29)-(9.30) theta lift | `ILS.thetaLift_{DC,CD,BM,MB}` | formalized |
| Eq (11.2) AC recursion | `AC.step`, `AC.fold` | formalized |
| Eq (3.3) signature | `PBP.signature` | formalized |
| Eq (3.6) epsilon | `PBP.epsilon` | formalized |
| tailLen, tailSymbol | `PBP.tailLen_D/B`, `tailSymbol_D/B` | formalized |
| tailContrib | `DRCSymbol.tailContrib` | formalized |
| tailSignature | `PBP.tailSignature_D/B` | formalized |
| gamma_tau | `PBP.gammaTau` | formalized |
| Sign preservations | `charTwistCM_sign`, `twistBD_sign`, ... | proved |
| theta lift sign (std) | `thetaLift_{CD,DC,MB,BM}_sign{,_std}` | proved |
| theta lift sign (split) | `thetaLift_{DC,BM}_sign_split` | proved |
| AC base sign | `AC.base_sign` | proved |
| AC step sign (all 5 types) | `AC.step_sign_{D,Bplus,Bminus,C,M}` | proved |

---

## Lemma 11.3

### Statement

Suppose star in {B, D}, (star, |O-check|) != (D, 0), and tau in PBP_star(O-check). Then:
- epsilon_tau = 0 if and only if x_tau = d
- p_{tau_t} = 0 if and only if x_tau = s
- q_{tau_t} = 0 if and only if x_tau = r

### Dependencies
- `PBP.tailSymbol_D/B`: formalized
- `PBP.epsilon`: formalized
- `DRCSymbol.tailContrib`: formalized
- `PBP.tailSignature_D/B`: formalized
- Tail structure from `CombUnipotent/Tail.lean`: `col0_nonDot_tail_D`, layer monotonicity

### Proof Plan

**Difficulty**: routine (case analysis on x_tau in {s, r, c, d})

**Step 1** (trivial): epsilon_tau = 0 iff x_tau = d.
- By definition, epsilon_tau = 0 iff 'd' occurs in column 0 of P or Q.
- For D type: tail is in P's column 0, x_tau = tailSymbol_D = P.paint(P.colLen(0)-1, 0).
- The bottom cell of the tail determines epsilon since d can only appear at the bottom (by layer monotonicity: d has the highest layerOrd = 4).
- Already partially captured by `DRCSymbol.epsilon_iff_not_d`.

**Step 2** (routine): p_{tau_t} = 0 iff x_tau = s.
- tailContrib: s -> (0, 2), so s contributes 0 to p.
- All other symbols contribute >= 1 to p (dot->(1,1), r->(2,0), c->(1,1), d->(1,1)).
- By layer monotonicity, symbols in the tail are ordered: dots at top, then s, then r/c, then d.
- If x_tau = s (the bottom symbol), all cells above it in the tail have layerOrd <= 1, so they're dot or s. Dots contribute (1,1) and s contributes (0,2).
- p_{tau_t} = (number of dots in tail) * 1 + (number of s in tail) * 0 = number of dots in tail.
- But if x_tau = s, the bottom cell is s, and by layer monotonicity all cells above are dot or s.
- Crucially: by row_s constraint, there can be at most one s per row across P and Q. For D type in column 0 of P, there's at most one s in the entire column (since Q has no s in D type). So the tail has exactly one s (at the bottom) and the rest are dots.
- Wait, actually row_s constrains across the entire row, not just column 0. The s at the bottom of the tail is in row P.colLen(0)-1, column 0. There could be other s in that row in other columns.
- Actually, for the p_{tau_t} computation, we just need: if x_tau != s, then the bottom cell contributes >= 1 to p (since r->(2,0), c->(1,1), d->(1,1) all have p-component >= 1), so p_{tau_t} >= 1. And if x_tau = s, we need p_{tau_t} = 0.
- When x_tau = s: all cells in the tail have layerOrd <= layerOrd(s) = 1, so they're dot or s. tailContrib(dot) = (1,1), tailContrib(s) = (0,2). p-contributions are 1 for dot, 0 for s.
- But wait, there might be dots above the s. Those contribute p = 1 each. So p_{tau_t} = (number of dot cells in tail). This is 0 only if ALL tail cells are s. But by row_s, at most 1 s per row, so the tail can have at most 1 s (the bottom). If k = tail length >= 2, then there are k-1 dots above the s, giving p_{tau_t} = k-1 >= 1.
- Hmm, this means p_{tau_t} = 0 iff x_tau = s AND k = 1 (tail length 1). Is that right?
- Actually, re-reading the paper: the tail multiset {x_1, ..., x_k} defines the tail PBP tau_t. For D type, the tail cells are in P's column 0 from row c_1(j) to c_1(iota)-1. Each cell contributes its paint symbol. But the TAIL SIGNATURE is computed from the tail PBP tau_t, not from individual cell contributions. Lemma 11.3 says p_{tau_t} is the p-component of Sign(tau_t), which is more complex than just summing per-cell (p, q).
- Actually, from the code `compute_tail_signature`, it IS just summing per-cell contributions. So p_{tau_t} = sum of Dp for each cell in the tail, where Dp is the p-component of tailContrib.
- So: if x_tau = s (bottom cell), and all other tail cells are dot (since layerOrd monotone, cells above bottom have layerOrd <= layerOrd(s) = 1, so they're dot or s; but row_s says at most 1 s per row, so cells above are dot or they could be s in different rows... actually for column 0 of P in D type, each cell is in a different row, and the row_s constraint says at most 1 s per row across P and Q combined. Q is all dots in D type, so each row can have at most 1 s in P. Since each tail cell is in a different row, each could potentially be s).
- OK I think the correct argument is: if x_tau = s, then the bottom cell is s with tailContrib (0, 2). By layer monotonicity, cells ABOVE the bottom have layerOrd <= layerOrd(bottom) = 1, so they're dot (layerOrd 0) or s (layerOrd 1). Their p-contributions are 1 (dot) or 0 (s). So p_{tau_t} = (number of dot cells in tail).
- For p_{tau_t} = 0, we need ALL tail cells to be s. Is that possible? By row_s, each row has at most 1 s (across P and Q). In D type, Q is all dots, so each row of P has at most 1 s. The tail cells are in column 0 of P, each in a different row. So each tail cell could be s in a different row. That would mean k s-cells in k different rows, each the unique s in its row. This seems possible in principle.
- BUT: Lemma 11.3 says p_{tau_t} = 0 IFF x_tau = s. So either (a) my reasoning is wrong, or (b) there's an additional constraint I'm missing that forces all tail cells to be s when the bottom is s.
- Actually, re-reading: for D type, the tail is the cells of P's column 0 from row Q.colLen(0) to P.colLen(0)-1. Below Q.colLen(0), P is dot (by dot_match with Q). At Q.colLen(0), P is non-dot. By layer monotonicity, P.paint(Q.colLen(0), 0).layerOrd >= P.paint(Q.colLen(0)-1, 0).layerOrd = 0 (since below is dot). So the first tail cell is non-dot. By mono, subsequent tail cells have non-decreasing layerOrd.
- If the bottom cell (last tail cell, highest row index) is s (layerOrd 1), then ALL tail cells have layerOrd <= 1, so they're dot or s. But the first tail cell is non-dot (just proved), so it's s. Actually wait, I proved non-dot for row Q.colLen(0), but if that's the first tail cell, it must have layerOrd >= dot.layerOrd = 0 AND be in P.shape but not in Q.shape. By dot_match, a dot cell of P is iff it's in Q. Since this cell is not in Q, it's non-dot. So the first tail cell is s (since layerOrd <= 1 and non-dot). By mono, all subsequent cells also have layerOrd >= 1, and the last has layerOrd = 1 (it's s). So all tail cells have layerOrd = 1, meaning all are s. Therefore p_{tau_t} = 0.
- Conversely: if x_tau != s (it's r, c, or d), then the bottom cell has tailContrib p >= 1 (r->2, c->1, d->1). So p_{tau_t} >= 1.

**Step 3** (routine): q_{tau_t} = 0 iff x_tau = r. Similar analysis with q-component.

### Lean sketch

```lean
theorem tailSymbol_eq_d_iff_epsilon_zero (τ : PBP) (hγ : τ.γ = .D)
    (h_ne : τ.P.shape.colLen 0 > τ.Q.shape.colLen 0) :
    PBP.tailSymbol_D τ = .d ↔ PBP.epsilon τ = 0

theorem tailSignature_p_zero_iff_s (τ : PBP) (hγ : τ.γ = .D)
    (h_ne : τ.P.shape.colLen 0 > τ.Q.shape.colLen 0) :
    (PBP.tailSignature_D τ).1 = 0 ↔ PBP.tailSymbol_D τ = .s

theorem tailSignature_q_zero_iff_r (τ : PBP) (hγ : τ.γ = .D)
    (h_ne : τ.P.shape.colLen 0 > τ.Q.shape.colLen 0) :
    (PBP.tailSignature_D τ).2 = 0 ↔ PBP.tailSymbol_D τ = .r
```

---

## Lemma 11.5

### Statement

Suppose star in {B, D} and (star, |O-check|) != (D, 0). Put gamma_tau as in (11.10).

(a) If r_2(O-check) > r_3(O-check), then:
  L_tau = T^{gamma_tau}(L_{tau''} tensor (eps_{wp'}, eps_{wp'})) augment (n_0, n_0) augment (p_{tau_t}, q_{tau_t}) tensor (0, eps_tau)

(b) If r_2(O-check) = r_3(O-check), then L_tau = L_{tau,+} + L_{tau,-} where
  L_{tau,+} := (T^{gamma_tau}(L_{tau''}^+ augment (0,0))) augment (p_{tau_t}, q_{tau_t} - 1) tensor (0, eps_tau)
  L_{tau,-} := (T^{gamma_tau}(L_{tau''}^- augment (0,0))) augment (p_{tau_t} - 1, q_{tau_t}) tensor (0, eps_tau)

### Dependencies
- Eq (11.2): `AC.step` — formalized
- Eq (11.7)/(11.9): Signature formulas from Prop 11.4 — NOT YET formalized
- `PBP.gammaTau`: formalized
- `PBP.tailSignature_D/B`: formalized
- Theta lift formula (9.30) for C/tilde{C}: `thetaLift_DC` — formalized
- Truncation: `ILS.truncate` — formalized

### Proof Plan

**Difficulty**: nontrivial (requires connecting two steps of AC recursion and simplifying the theta lift)

**Step 1** (routine): Apply AC recursion (11.2) to get L_tau in terms of L_{tau'}.
- For star in {B, D}: L_tau = theta-hat(L_{tau'}) tensor (0, eps_tau)
- This is AC.step applied once.

**Step 2** (nontrivial): Apply AC recursion again to express L_{tau'} in terms of L_{tau''}.
- tau' has type star' in {C, tilde{C}} (dual of B/D)
- L_{tau'} = theta-hat_{star'}(L_{tau''} tensor (eps_{wp'}, eps_{wp'}))
- The theta lift is formula (9.30): involves sum over truncations.

**Step 3** (nontrivial): Compose the two lifts and simplify.
- The composition theta-hat_{star}(theta-hat_{star'}(...)) = the two-step lift.
- Use signature formulas (11.7)/(11.9) to compute (p_0, q_0) parameters.
- The key simplification: delta = c_1(O') - c_2(O') determines how many terms survive in the truncation sum of (9.30).

**Step 4** (routine for (a), nontrivial for (b)):
- (a) r_2 > r_3: delta contributes 0 to the truncation sum, so exactly one term survives. This gives the single formula (11.11).
- (b) r_2 = r_3: delta = 1, so two terms survive in the truncation sum, giving L_{tau,+} and L_{tau,-} via (11.13)/(11.14).

### Risks
- The composition of two theta lifts requires detailed arithmetic with signatures, which is the hardest part.
- May need additional infrastructure for orbit column lengths c_1, c_2.
- The Prop 11.4 signature formulas (11.7)/(11.9) are prerequisites not yet formalized.

---

## Lemma 11.6

### Statement

Suppose star in {B, D}, (star, |O-check|) != (D, 0).

(a) If r_2 > r_3 and E in MYD_star has nonzero coefficient in L_tau, then E(1) = (p_{tau_t}, (-1)^{eps_tau} q_{tau_t}).

(b) If r_2 = r_3 and E_+ in L_{tau,+} has nonzero coefficient, then q_{tau_t} >= 1 and E_+(1) = (p_{tau_t}, (-1)^{eps_tau}(q_{tau_t} - 1)).

(c) If r_2 = r_3 and E_- in L_{tau,-} has nonzero coefficient, then p_{tau_t} >= 1 and E_-(1) = (p_{tau_t} - 1, (-1)^{eps_tau} q_{tau_t}).

### Dependencies
- Lemma 11.5: provides the explicit formula for L_tau
- `ILS.augment`: the first entry of (a, b) :: E is (a, b)
- `ILS.twistBD`: sign twist only affects odd-length rows; row 1 (index 0) is odd-length
- `ILS.charTwistCM`: T twist potentially negates row 1

### Proof Plan

**Difficulty**: routine (direct read-off from Lemma 11.5's formula)

From (11.11): L_tau = T^{gamma_tau}(...) augment (p_{tau_t}, q_{tau_t}) tensor (0, eps_tau).
The augment puts (p_{tau_t}, q_{tau_t}) at position 1. The sign twist tensor (0, eps_tau) acts on position 1 (odd-length row): it multiplies q by (-1)^{eps_tau}. So E(1) = (p_{tau_t}, (-1)^{eps_tau} q_{tau_t}).

For (b) and (c): similar but with (p_{tau_t}, q_{tau_t} - 1) and (p_{tau_t} - 1, q_{tau_t}).

### Lean sketch

```lean
theorem AC_first_entry_quasi_distinguished ...
    (h_qd : r₂ > r₃) :
    ∀ E ∈ L_tau, E.head? = some (p_tail, (-1)^ε_τ * q_tail)
```

---

## Proposition 11.7 (Multiplicity free)

### Statement

Suppose star in {B, D}. Then L_tau is multiplicity free. When (star, |O-check|) != (D, 0) and r_2 = r_3, both L_{tau,+} and L_{tau,-} are multiplicity free.

### Dependencies
- Lemma 11.5: the explicit formula
- Lemma 11.6: first entry determines the MYD under augmentation
- Four operations preserve multiplicity free: proved properties of sign twist (involutive → bijective), T (involutive → bijective), augment (injective), truncate (injective under containment)

### Proof Plan

**Difficulty**: nontrivial (induction on number of rows of O-check)

**Step 1** (routine): Base case |O-check| = 0.
- L_tau is a single MYD (from AC.base), trivially multiplicity free.

**Step 2** (nontrivial): Inductive step, r_2 > r_3 case.
- By Lemma 11.5(a), L_tau = operations(L_{tau''}). 
- Each operation (T, augment, sign twist) is a bijection on MYD, so preserves multiplicity free.
- By induction hypothesis, L_{tau''} is multiplicity free.
- Therefore L_tau is multiplicity free.

**Step 3** (nontrivial): Inductive step, r_2 = r_3 case.
- L_{tau,+} uses L_{tau''}^+ (one-box truncation), L_{tau,-} uses L_{tau''}^-.
- Truncation is injective (under containment), so preserves multiplicity free.
- Need: L_{tau,+} and L_{tau,-} have disjoint supports. By Lemma 11.6, their first entries differ ((p, q-1) vs (p-1, q)), so the MYDs are distinct.

### Lean sketch

This requires defining "multiplicity free" for ACResult:

```lean
def ACResult.multiplicityFree (ac : ACResult) : Prop :=
  ∀ i j, i < ac.length → j < ac.length → i ≠ j → ac[i].2 ≠ ac[j].2
```

---

## Proposition 11.8 (Nonzero and truncation)

### Statement

Suppose star in {B, D}.
(a) L_tau != 0.
(b) If (star, |O-check|) != (D, 0) and x_tau = s, then L_tau^+ = 0 and L_tau^- = 0.
(c) If x_tau in {r, c}, then L_tau^+ != 0 and L_tau^- = 0.
(d) If x_tau = d, then L_tau^+ != 0 and L_tau^- != 0.

### Dependencies
- Lemma 11.3: connects x_tau to p_{tau_t}, q_{tau_t}
- Lemma 11.5: explicit formula
- Lemma 11.6: first entry of L_tau's MYDs

### Proof Plan

**Difficulty**: nontrivial (induction on rows of O-check)

**Step 1** (trivial): (a) follows from Lemma 11.6 — the formula always produces at least one MYD.

**Step 2** (routine): (b) x_tau = s. By Lemma 11.3, p_{tau_t} = 0. By Lemma 11.6(a), E(1) = (0, (-1)^{eps_tau} q_{tau_t}). 
- L_tau^+ = Lambda_{(1,0)}(L_tau): needs E(1).1 >= 1 (containment). But E(1).1 = 0 < 1. So truncation fails, L_tau^+ = 0.
- L_tau^- = Lambda_{(0,1)}(L_tau): needs E(1).2 in the right range. Since eps_tau = 1 (x_tau = s != d), E(1).2 = -q_{tau_t} < 0. Lambda_{(0,1)} needs 0 <= 1 <= E(1).2 or E(1).2 <= 1 <= 0. Neither holds for q_{tau_t} >= 2. For q_{tau_t} = 1, E(1).2 = -1 and 0 <= 1 fails and -1 <= 1 <= 0 fails. So L_tau^- = 0.

**Step 3** (routine): (c) x_tau in {r, c}. By Lemma 11.3, p_{tau_t} > 0 and (-1)^{eps_tau} q_{tau_t} <= 0.
- L_tau^+: E(1).1 = p_{tau_t} >= 1 so Lambda_{(1,0)} succeeds. L_tau^+ != 0.
- L_tau^-: E(1).2 = (-1)^{eps_tau} q_{tau_t} <= 0, so Lambda_{(0,1)} needs 0 <= 1 <= E(1).2 (fails since E(1).2 <= 0) or E(1).2 <= 1 <= 0 (fails since 1 > 0). So L_tau^- = 0.

**Step 4** (routine): (d) x_tau = d. By Lemma 11.3, p_{tau_t} > 0 and q_{tau_t} > 0, eps_tau = 0 so (-1)^0 q_{tau_t} = q_{tau_t} > 0. Both truncations succeed.

---

## Formalization Priority

Topological order (prove in this sequence):

1. **Lemma 11.3** — case analysis, depends only on existing tail infrastructure
2. **Lemma 11.6** — direct read-off from AC formulas (after connecting to Lean's AC.step)
3. **Proposition 11.7** — induction, depends on 11.5 + 11.6
4. **Proposition 11.8** — induction, depends on 11.3 + 11.6
5. **Lemma 11.5** — most complex, depends on Prop 11.4 (signature formulas)

Parallelizable: Lemma 11.3 and Lemma 11.6 are independent and can be proved in parallel.

## Blocking Dependencies (not yet formalized)

- **Prop 11.4** (descent map properties, signature formulas (11.7)/(11.9)) — needed for Lemma 11.5
- **Orbit column lengths** c_1(O), c_2(O) — needed for delta computation
- **BV dual** d^star_BV — needed to connect orbits
