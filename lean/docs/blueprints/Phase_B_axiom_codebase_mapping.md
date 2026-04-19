# Phase B axioms ↔ existing codebase mapping

**Created**: 2026-04-19 (applying `feedback_search_codebase_first` rule).

Before attempting Phase B proofs, map each remaining axiom to the
nearest existing code so we reuse rather than re-derive.

## 10 axioms → code pointer table

### Per-step and chain-level (PhiDTyped.lean)

#### `descent_step_thetaLift_singleton`
**Statement**: for a D-type τ, the ILS.thetaLift at the step data of
`toACStepData_D τ hγ` is a singleton.

**Key observation**: `ILS.thetaLift_CD` (MYD.lean:180) is
definitionally `if h_std then [lifted] else []`. So "at most 1" is
automatic; "exactly 1" reduces to proving `h_std` (the sign bound).

**Existing**:
- `ILS.thetaLift_CD_nonempty` (MYD.lean:4679) — non-emptiness given `h_std`.
- `ILS.thetaLift_MB_nonempty` (MYD.lean:4688) — same for MB.

**What's missing**: proving `h_std` holds for descent-chain-supplied
(p, q, E) triples. This is paper Lemma 11.5/11.6 content.

**Path**: prove a single lemma
`toACStepData_D_satisfies_sign_bound (τ) (hγ)`, then compose.

#### `exists_descentChain_D`
**Statement**: every τ ∈ PBPSet .D μP μQ has a descent chain.

**Missing**: `YoungDiagram.shiftLeft.card < YoungDiagram.card` when
shape non-empty. Small YoungDiagram lemma.

**Path**: (a) add the `shiftLeft_card_lt` lemma; (b) well-founded
recursion on `τ.P.shape.card + τ.Q.shape.card`.

**Existing**: `doubleDescent_D_PBP` (Descent.lean:95) — the descent
primitive. `PBP.cardCells` (Prop11_5_AtomicDischarge.lean:38) —
potential measure.

#### `descentChain_D_in_MYD`
**Statement**: the extracted ILS satisfies MYD parity + shape.

**Existing machinery** (extensive):
- Sign preservation: `ACResult.thetaLift_sign` (MYD.lean:821),
  `thetaLift_{CD,MB}_sign` (564, 655), `AC.step_sign_D` (865+).
- firstColSign preservation: `thetaLift_{CD,MB,DC,BM}_firstColSign`
  (MYD.lean:2426, 2445, 2470, 2489).
- Multiplicity-free: `ACResult.thetaLift_multiplicityFree` (MYD.lean:1999).

**Path**: induction on chain, apply sign/firstColSign preservation
at each step.

### Inverse and round-trips (Bijection.lean)

#### `Psi_D`, `Psi_D_Phi_D`, `Phi_D_Psi_D`

**Approach choice**:
- **(a) Constructive**: implement paper §11.14 inverse algorithm.
- **(b) Via bijective**: use `Equiv.ofBijective` from a proof of
  `Bijective Phi_D`. Requires injective (from prop_11_15 family) +
  surjective (from ac_twist_charTwist_surjective + counting).

**Existing surjectivity**:
- `ILS.charTwistCM_surjective` (MYD.lean:4747) — char twist is invertible.
- `ILS.twistBD_surjective` (MYD.lean:4753) — sign twist invertible for
  tp, tn ∈ {1, -1}.
- `ACResult.charTwistCM_surjective`, `ACResult.twistBD_surjective`
  (MYD.lean:4763, 4771).
- `ACResult.augment_injective` (MYD.lean:3961) — augment is
  injective (surjectivity implicit via existence of preimage).
- `ac_twist_charTwist_surjective` (MYD.lean:4831) — composition is
  surjective (paper Lemma 11.14).

**Existing injectivity**:
- `prop_11_15_PBP_D_injective_full` (MYD.lean:5018) — full version
  with tail-signature hypotheses. Needs these hypotheses to be
  established, which is what `descentChain_D_in_MYD` would do.

**Gap**: the hypotheses of `prop_11_15_PBP_D_injective_full` (h_ne,
h_first, h_nt, hp_nn, hq_nn) are properties of `Phi_D`'s output that
we haven't established as theorems. They would follow from
`descentChain_D_in_MYD` + tail-sig lemmas (`tailSig_nonneg_D`).

**Path**: close `descentChain_D_in_MYD` first; then `Psi_D` follows
via `Equiv.ofBijective` once bijectivity is shown. This removes **3
axioms** with one deeper proof.

### Other types (BijectionBCM.lean)

#### `Phi_Bplus_equiv`, `Phi_Bminus_equiv`, `Phi_C_equiv`, `Phi_M_equiv`

**Structural parallel**: B⁺, B⁻ mirror D; C, M have different descent
structure (single descent alternating types).

**Existing**:
- `toACStepData_Bplus/Bminus/C/M` (MYD.lean:4119+) — per-step data.
- `doubleDescent_B_PBP` (CorrespondenceB.lean:432) — B-analogue.
- `prop_11_17_injectivity` (MYD.lean:4026) — C/M injectivity.
- `prop_11_15_PBP_Bplus_injective_full` etc. (MYD.lean) — B mirrors.

**Path per type**: follow the D template:
1. `IsDescentChain_γ` inductive
2. `exists_descentChain_γ`, `_singleton`, `_in_MYD`
3. `Phi_γ` typed
4. Bijectivity via injectivity + surjectivity
5. Wrap as `Equiv`

Each is ~D-sized effort.

## Strategy for max efficiency

**Reuse-first priorities** (approximate effort reduction from reuse):

1. **`descentChain_D_in_MYD`** — direct application of existing
   `thetaLift_*_sign` + `thetaLift_*_firstColSign` preservation.
   HIGH reuse, HIGH impact (unblocks 3 Bijection axioms).

2. **`descent_step_thetaLift_singleton`** — `h_std` proof is the
   only missing piece; the rest follows by definitional unfolding.
   MEDIUM reuse.

3. **`exists_descentChain_D`** — add one `shiftLeft_card_lt`
   YoungDiagram lemma, then termination is standard.
   LOW reuse (new lemma), MEDIUM impact.

4. **`Psi_D` / round-trips** — requires (1) as prerequisite but
   then flows from existing surjectivity + injectivity.
   Blocked by (1), but massive reuse once unblocked.

5. **B⁺/B⁻/C/M equivs** — parallel reruns of the D template.
   LOW reuse across types (structural parallelism), HIGH code
   volume. Best done as a batch after D is fully closed.

## Recommended order

1. Prove `shiftLeft_card_lt` small lemma (tractable, unblocks 3).
2. Close `exists_descentChain_D`.
3. Close `descentChain_D_in_MYD` via existing sign/firstColSign
   preservation lemmas.
4. Close `descent_step_thetaLift_singleton` (now the h_std piece
   follows from descentChain_D_in_MYD's tail-signature output).
5. Prove `Phi_D` is injective + surjective via existing machinery;
   derive `Phi_D_equiv` directly. Removes Psi_D + 2 round-trips.
6. Parallelize for B⁺/B⁻ (reuse D template).
7. Separately handle C/M (different descent structure).

## Footnote on `feedback_search_codebase_first`

This analysis itself is an application of the codebase-first rule.
Had I jumped directly into proving `descentChain_D_in_MYD` by
re-deriving sign preservation, I would have duplicated the 864–940
line block in MYD.lean. Mapping first revealed the existing
machinery.
