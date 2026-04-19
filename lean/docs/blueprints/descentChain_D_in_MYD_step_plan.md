# `descentChain_D_in_MYD` step case: detailed proof plan

**Context**: `descentChain_D_in_MYD` is the main paper §9.4
theorem for D type. Base case proved. Step case decomposed via
`ChainSingleton.snoc_inv` but proof deferred. This doc breaks the
step case into **four independent sub-lemmas** so future sessions
can attack them one at a time.

## Step case structure

```lean
| step hγ h_rest ih =>
  rename_i τ_outer chain_inner
  obtain ⟨E_mid, E', h_inner_sing, h_theta, h_E_final⟩ :=
    ChainSingleton.snoc_inv h_sing
  sorry
```

We have:
- `h_coh : PBPIsCoherent_D τ_outer dp`
- `h_inner_sing : ChainSingleton (baseILS .D) chain_inner E_mid`
- `h_theta : ILS.thetaLift (stepPreTwist E_mid outer_step) outer.γ outer.p outer.q = [E']`
- `h_E_final : E = stepPostTwist E' outer_step`
- IH generalized over E, dp for the inner PBP.

## Sub-lemma 1: coherence preservation under double descent

**Statement**:
```
theorem coherence_descend_D {τ : PBP} (hγ : τ.γ = .D) {dp : DualPart}
    (h_coh : PBPIsCoherent_D τ dp) :
    ∃ dp_inner, PBPIsCoherent_D (doubleDescent_D_PBP τ hγ) dp_inner
```

Most likely `dp_inner = dp.drop 2` (since double descent shifts
shapes left, and `dp.drop 2` matches the `dpartColLensP_D` recursion).

**Subtlety**: the Q-side `dpartColLensQ_D` has conditional
`if r₂ > 1`, so the relationship to `dp.drop 2` is not uniform.
Handle by case-splitting on the first 2 entries of dp.

**Paper citation**: none (pure combinatorial fact).

**Dependency**: none.

## Sub-lemma 2: theta-lift output shape

**Statement**: after `ILS.thetaLift` at D-type produces `[E']`,
`E' = augment (p₀, q₀) (charTwistCM E_twisted ((p - q) / 2))` for
some `(p₀, q₀)` derived from `(p, q, sign, firstColSign)`.

This is LITERALLY the `thetaLift_CD` definition (MYD.lean:180):
```lean
if addp ≥ 0 ∧ addn ≥ 0 then
  [augment (addp, addn) (charTwistCM E ((p - q) / 2))]
else []
```

**Statement**:
```lean
theorem thetaLift_CD_output_form (E : ILS) (p q : ℤ) (E' : ILS)
    (h : ILS.thetaLift_CD E p q = [E']) :
    ∃ addp addn,
      addp = p - (ILS.sign E).1 - (ILS.firstColSign E).2 ∧
      addn = q - (ILS.sign E).2 - (ILS.firstColSign E).1 ∧
      addp ≥ 0 ∧ addn ≥ 0 ∧
      E' = (addp, addn) :: (ILS.charTwistCM E ((p - q) / 2))
```

Proof: unfold `thetaLift_CD`, case on the `if`. In the `else` branch
`h` contradicts `[E'] ≠ []`. In `if` branch, `[augment ...] = [E']`
gives `E' = augment ...`, and `augment (addp, addn) E = (addp, addn) :: E`.

**Paper citation**: Def 9.18 (augment) + Eq 9.29.

## Sub-lemma 3: shape growth via augment

**Statement**: if E_twisted's absValues matches dp_inner's
transpose-partition structure, and E' = augment (addp, addn) E_twisted,
then E'.absValues matches dp's transpose at one more position.

**Statement** (schematic):
```lean
theorem absValues_augment (E : ILS) (pq : ℤ × ℤ) :
    absValues ((pq.1, pq.2) :: E) = (pq.1.natAbs, pq.2.natAbs) :: absValues E
```

Trivial by unfolding `absValues = E.map ...`.

**Then** combine with Sub-lemma 1 + IH to get:
`absValues E' = (dpToSYD .D dp).rows`.

**Paper citation**: Eq 9.18 (augment).

## Sub-lemma 4: stepPostTwist preservation

`stepPostTwist E' d` applies `twistBD E' 1 (-1)` when
`d.ε_τ = 1 ∧ d.γ ∈ {B⁺, B⁻, D}`, else identity.

For D type with ε_τ = 1, we apply `twistBD 1 (-1)`. This preserves
MYDRowValid (via `twistBD_preserves_MYDRowValid` — already proved
for B/D with t = t, but here we have tp = 1, tn = -1, different).

**New helper needed**:
```lean
theorem twistBD_1_neg1_preserves_MYDRowValid_D (E : ILS)
    (h : ∀ j (hj : j < E.length), MYDRowValid .D (j + 1) E[j]) :
    ∀ j (hj : j < (ILS.twistBD E 1 (-1)).length),
      MYDRowValid .D (j + 1) (ILS.twistBD E 1 (-1))[j]
```

At D-parity-forced positions (paper ℓ even), twistBDRow with ℓ
even is identity, same as the proved `twistBD_preserves_MYDRowValid`
(just different tp, tn values, but still identity at ℓ even).

And `absValues` preservation: `twistBD_preserves_absValues` already
proved for any (tp, tn) ∈ {1, -1}² — works directly.

**Paper citation**: Eq 9.15 (sign twist definition).

## Assembly

With all 4 sub-lemmas:

```lean
-- (A) Use Sub-lemma 1 to get dp_inner + inner coherence
obtain ⟨dp_inner, h_coh_inner⟩ := coherence_descend_D hγ h_coh

-- (B) Apply IH on E_mid, dp_inner
have ih_mid := ih h_coh_inner h_inner_sing
-- ih_mid.1: MYDRowValid for E_mid
-- ih_mid.2: absValues E_mid = (dpToSYD .D dp_inner).rows

-- (C) Use Sub-lemma 2 to get E' = augment (addp, addn) E_mid'
obtain ⟨addp, addn, h_addp_def, h_addn_def, h_addp_nn, h_addn_nn, h_E'_eq⟩ :=
  thetaLift_CD_output_form ...

-- (D) Combine: E' shape = augment result, so absValues lifts.
--     Parity: augment at row 1 adds (addp, addn); for D parity at ℓ even,
--     row 1 is ℓ = 1 odd → NOT parity-forced, so parity vacuous at new row.
--     Interior rows inherit from E_mid via IH.

-- (E) Sub-lemma 4: stepPostTwist preserves both properties.
rw [h_E_final]
-- h_E_final : E = stepPostTwist E' outer_step
-- ...
```

## Suggested order

1. **Sub-lemma 3** (absValues_augment): trivial (1–2 lines).
2. **Sub-lemma 2** (thetaLift_CD_output_form): definitional unfold.
3. **Sub-lemma 1** (coherence_descend_D): case analysis on dp.
4. **Sub-lemma 4** (twistBD 1 (-1) preservation for D): extends
   already-proved twistBD lemmas.
5. Final assembly: combine the four sub-lemmas.

Each sub-lemma is a self-contained session. After all four land,
the step case of `descentChain_D_in_MYD` closes.
