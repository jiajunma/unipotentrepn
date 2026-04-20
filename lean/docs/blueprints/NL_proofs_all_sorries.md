# NL Proofs for All 36 Remaining Sorries

**Date**: 2026-04-20
**Purpose**: Natural-language proofs for every remaining sorry, grouped
by category. Each proof identifies exact paper content and concrete
Lean lemmas to invoke.

---

## Category A: `Phi_γ_sig_injective` (5 sorries)

### A.1 `Phi_D_sig_injective`

**Restriction needed**: `h_ne : μP.cells.card + μQ.cells.card > 0`.
Empty case fails: 2 inputs → 1 output.

**Proof** (see `Phi_D_sig_injective_NL.md` for full 7-step version):

Given `Phi_D_sig (σh₁, ε₁) = Phi_D_sig (σh₂, ε₂)`, extract `.E` equality:
`twistBD E₁ ε_int_1 ε_int_1 = twistBD E₂ ε_int_2 ε_int_2`.

Package as ACResult `Lᵢ = [(1, E_twistedᵢ)]`. Apply
`prop_11_15_PBP_D_injective_full` with:
- `hγᵢ` from `σᵢ.prop.1`
- `Lᵢ ≠ []` trivial
- `h_firstᵢ` via sub-lemma `chain_extract_first_entry_D` (paper Lemma 11.6)
- `hpᵢ_nn, hqᵢ_nn` via existing `tailSig_nonneg_D`
- `h_ntᵢ` via non-empty hypothesis (paper 11.6 + tail content)
- `h_eq` via ACResult twistBD unfolding

Conclude `ε₁ = ε₂ ∧ L₁ = L₂`. From L equality, E₁ = E₂.
From E equality + same chain + non-empty: τ₁ = τ₂ via sub-lemma
`chain_extract_injective_D` (paper Lemma 11.13 + `ddescent_inj_D`).

### A.2-5 `Phi_{B+,B-,C,M}_sig_injective`

Mirror of A.1 using respective `prop_11_15_PBP_{Bplus,Bminus}_complete` and
Prop 11.17 for C/M. B+/B- need non-empty, C/M need non-empty + ε handling
depending on whether source has `Fin 2` factor.

---

## Category B: `Phi_γ_sig_surjective` (5 sorries)

### B.1 `Phi_D_sig_surjective`

**Paper reference**: Lemma 11.14 proof (constructive algorithm).

**Proof by induction** on `s.1 + s.2` (equivalent to |Ǒ|):

**Base case** (|Ǒ| = 0, equivalent to s = (0, 0) and μP = μQ = ⊥):
MYD_sig .D (0, 0) has only E = [] (sign (0,0) forces E = []). PBPSet has
1 element (empty τ). Map it to [] via Phi. Surjective.

**Inductive step** (r₂(Ǒ) > r₃(Ǒ)):
Given `M : MYD_sig .D s`, recover `(τ, ε)` from E as follows:
1. From `M.E[0] = (e_p, e_q)`, extract `p^τ_t := e_p`,
   `q^τ_t := |e_q|`, `ε_τ := if e_q < 0 then 1 else 0` (paper Lemma 11.6).
2. Define `E'' := descendMYD M.E` (paper Eq. after 11.14: strip first row
   + index-shift formula).
3. Apply induction on `E''` (which has shorter E): get `(τ'', ε')` with
   `Phi (τ'', ε') = E''`.
4. Construct `τ := liftCD_PBP τ'' h_sub + paint from (p^τ_t, q^τ_t, ε_τ)`
   (paper eq. 11.11 inverse). Use existing `liftCD_PBP` + tail construction.
5. Verify `Phi (τ, ε) = M` by chain composition.

**Sub-lemmas**:
- `descendMYD` (new function): strips E[0] + applies inverse Tγ on rest
- `liftCD_to_PBP_with_tail` (new): constructs outer PBP from descended + tail data
- Chain singleton preservation under lift

### B.2-5 `Phi_{B+,B-,C,M}_sig_surjective`

Mirror of B.1. B+/B- use `liftBM_PBP` (paper §11.3), C/M use composition
via descentCD/MB inverses.

---

## Category C: `descentChain_γ_parity` (5 sorries, step cases)

### C.1 `descentChain_D_parity` step case

**Restriction needed**: `IsQuasiDistinguished .D dp` (paper Lemma 11.14).

**Proof by induction on chain**:

IH: E_inner satisfies MYDRowValid .D (j+1) E_inner[j] for all j.

After chain step:
E_outer[0] = (addp, addn), at ℓ = 1 (odd). Vacuous for D.

E_outer[k+1] = charTwistCM E_inner γ[k], where γ = (p-q)/2.
At ℓ = k+2 (even iff k even):
- Forced iff k even.
- charTwistCM at i=k: negates iff (k+1)%4 = 2 ∧ γ odd.
  For k even: k+1 odd. (k+1)%4 ∈ {1, 3}. So (k+1)%4 = 2 NEVER.
  Thus E_outer[k+1] = E_inner[k] directly for k even.

- IH at E_inner[k]: MYDRowValid .D (k+1) E_inner[k]. For k even: forced (k+1 odd ℓ+1 → wait).

Let me redo. SYDParityForced .D j = (j % 2 = 0). So parity-forced at even ℓ (j = ℓ).

- E_outer[k+1] at ℓ_new = k+2. Forced iff k+2 even iff k even.
- For k even: forced at E_outer[k+1] with ℓ = k+2.
- Under QD: the (addp, addn) at each chain level satisfies specific
  constraints (from paper Eq 11.11: (n_0, n_0) is symmetric → p = q).
- Paper uses this to show E_outer's position k+1 (ℓ = k+2 even)
  has p = q ∧ p ≥ 0.

**Sub-lemma needed** (paper §9.4): `thetaLift_CD_preserves_MYD_QD`:
Under QD + IH, charTwistCM + augment preserves MYDRowValid at the
shifted position.

### C.2-5 `descentChain_{B+,B-,C,M}_parity`

Mirror. B+/B- use Bplus/Bminus parity (same forced pattern as D).
C/M have odd-ℓ forced pattern — different but symmetric argument.

---

## Category D: `descent_step_thetaLift_singleton_γ` (5 sorries, non-std versions)

### D.1 `descent_step_thetaLift_singleton_D`

**Paper reference**: Lemma 11.5 + §11.5 sign-bound analysis.

**Proof**: Show the std hypothesis `addp ≥ 0 ∧ addn ≥ 0` holds for
chain-supplied (E_inner, τ). Then invoke `descent_step_thetaLift_singleton_D_std`
(already PROVED).

**Chain std bound**:
`addp = (signature τ).1 - sign(E_inner).1 - firstColSign(E_inner).2`

Claims:
(i) `sign(E_inner) = signature(τ_inner)` where τ_inner = doubleDescent(τ).
    Already proved: `descentChain_sign_match_D` on inner chain.

(ii) `(signature τ).1 - (signature τ_inner).1 = contribution from tail rows`
     of τ. Paper §11.3 proves this = (tailSignature_D τ).1 + |P col-0 dots
     between Q's height and P's height|.

(iii) `firstColSign(E_inner).2 ≤ (signature τ).1 - (signature τ_inner).1
     - (tailSignature_D τ).1`. Paper §11.6 proves.

Combining: `addp = (tailSignature_D τ).1 + nonnegative rest`. Since
`tailSig_nonneg_D` gives (tailSignature_D τ).1 ≥ 0, addp ≥ 0. ✓

### D.2-5

Mirror with different theta-lift functions:
- B+, B-: thetaLift_MB (paper §11.4)
- C: thetaLift_DC (paper §11.1)
- M: thetaLift_BM (paper §11.3)

---

## Category E: B-/M singleton base reconciliation (3 sorries)

### E.1 `descentChain_Bminus_singleton` (step case)

**Issue**: IsDescentChain_Bminus.step uses `doubleDescent_B` which
produces Bplus inner. Inner chain singleton is from `baseILS .Bplus`
(proved as `descentChain_Bminus_singleton_Bplus_base`). But outer
singleton expects `baseILS .Bminus`.

**Resolution**: Need a "base translation" at the first chain step.

**Proof**: For non-empty Bminus τ:
1. From `descentChain_Bminus_singleton_Bplus_base`: ∃ E, ChainSingleton (baseILS .Bplus) chain E (**PROVED**).
2. Apply first step thetaLift_MB on baseILS .Bminus = [(0, -1)]:
   - Sign of [(0, -1)] = (0, 1).
   - For doubleDescent_B(τ)'s Bplus inner τ_inner, signature(τ_inner) = (1, 0).
   - addp_first = 1 - 0 - firstColSign(baseILS .Bminus).2
                 = 1 - 0 - ... . Compute firstColSign([(0, -1)]) = (0, 1).
                 → addp_first = 1 - 0 - 1 = 0.
   - Similarly addn_first: hmm details.
3. Show thetaLift_MB baseILS .Bminus targets' matches thetaLift_MB baseILS .Bplus target after some shift. Specifically, Bplus's chain results should be related to Bminus's chain results via specific Equation.

**Sub-lemma**: relate `thetaLift_MB (baseILS .Bminus) p q` to
`thetaLift_MB (baseILS .Bplus) p q`. Paper has this relation implicitly
via baseILS's role in AC.fold.

### E.2-3 `descentChain_M_singleton` step_to_Bplus, step_to_Bminus

Mirror — M chain has 2 outer step variants, each needs own base reconciliation.

---

## Category F: C/M sign match step cases (2 sorries)

### F.1 `descentChain_sign_match_C` step case

**Depends on**: `descent_step_thetaLift_singleton_C` (Cat D.3) closure +
`thetaLift_DC_sign_std` under std hypothesis.

**Proof**: Given chain singleton exists (Cat D.3), apply std → sign = (n, n).
Then verify signTarget_C' τ = (n, n) for C-type τ.

### F.2 `descentChain_sign_match_M` step cases

Mirror.

---

## Category G: exists_coherent_dp_* + chain (4 sorries)

### G.1 `exists_coherent_dp_C`

**Claim**: For any C-type σ : PBPSet .C μP μQ, there exists a dp
matching (μP, μQ).

**Reality check**: NOT true for arbitrary (μP, μQ) — they must satisfy
C-shape structure.

**Correct statement**: If μP, μQ come from some valid C-PBP, then dp
exists by inverting dpartColLens_C formulas.

**Proof sketch** (assuming shape validity):
- Given μP.colLens = list l_P and μQ.colLens = list l_Q
- Construct dp recursively:
  - If l_Q empty and l_P empty: dp = []
  - If l_Q has head x > 0: r₁ = 2x + 1
  - Recurse on (l_P, l_Q.tail) to build r_2, r_3, ...
- Verify SortedGE + odd at each step

**Sub-lemma needed**: `shape_coherent_C_implies_valid_dp`
(probably requires `τ.γ = .C` + paint structure).

### G.2 `exists_descentChain_C_coherent`

**Given**: dp coherence + SortedGE + odd.
**Goal**: chain exists.

**Proof**: Strong induction on dp.length + shape size.
- Base: dp = [] → empty shapes → chain = []
- Step: dp = r₁ :: r₂ :: rest → 
  - Use `shiftLeft_Q_le_P_of_dp` to get h_sub
  - Apply `descentCD_PBP` → D-type PBP with dp' = r₂ :: rest
  - Recurse via `exists_descentChain_D` on the D-PBP
  - Snoc with outer C step

### G.3 `exists_coherent_dp_M`

Mirror of G.1 for M type.

### G.4 `exists_descentChain_M_coherent`

Mirror of G.2 — but bifurcated into step_to_Bplus and step_to_Bminus.

---

## Category H: Miscellaneous remaining sorries (other ~7)

### H.1 `descentChain_sign_match_M` split + split

Downstream of D.5 (thetaLift_BM singleton + std).

### H.2 Various helpers and compatibility lemmas

Each typically ~50 LOC bridging specific lemmas.

---

## Total LOC estimate

| Category | Sorries | LOC per | Total |
|----------|---------|---------|-------|
| A. Phi_*_injective | 5 | 570 | 2850 |
| B. Phi_*_surjective | 5 | 600 | 3000 |
| C. parity | 5 | 300 | 1500 |
| D. per-step singleton | 5 | 200 | 1000 |
| E. base reconciliation | 3 | 150 | 450 |
| F. sign match step | 2 | 100 | 200 |
| G. exists_coherent + chain | 4 | 150 | 600 |
| H. misc | 7 | 100 | 700 |
| **Total** | **36** | | **~10,300** |

## Priority order for closure

1. **G (600 LOC)** — unblocks C/M chain construction. Purely structural.
2. **D (1000 LOC, shared across 5 types)** — unblocks singleton sorries.
3. **E (450 LOC)** — structural base reconciliation.
4. **F (200 LOC)** — downstream of D.
5. **C (1500 LOC)** — parity via paper §9.4 (needs QD).
6. **A (2850 LOC)** — injectivity via paper Prop 11.15.
7. **B (3000 LOC)** — surjectivity via paper Lemma 11.14 algorithm.

## Common theme

**All Category A-F proofs reduce to paper-content sub-lemmas**:
- Paper Lemma 11.5 (chain structure)
- Paper Lemma 11.6 (first-entry formula)
- Paper Lemma 11.11 (no det twist)
- Paper Lemma 11.13 (chain invertibility)
- Paper Lemma 11.14 (algorithmic surjectivity)
- Paper Prop 11.15 (PBP-level injectivity)
- Paper §9.4 (MYD parity preservation)
- Paper §11.5-11.6 (sign bounds on chain)

Future sessions: translate these one at a time. Each is its own
sub-project.
