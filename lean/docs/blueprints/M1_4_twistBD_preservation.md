# M1.4 Phase B (partial): `twistBD_preserves_*` lemmas

**Milestone**: M1.4 Phase B, small self-contained lemmas.

**Status**: natural-language draft (2026-04-19).

## Goal

Prove the two small axioms remaining from M1.4 Phase A:

1. `twistBD_preserves_absValues`: for $\mathrm{tp}, \mathrm{tn} \in \{1, -1\}$,
   $\mathrm{absValues}(\mathrm{twistBD}\ E\ \mathrm{tp}\ \mathrm{tn}) = \mathrm{absValues}\ E$.

2. `twistBD_preserves_MYDRowValid`: for the specific B/D-type
   $\gamma \in \{B^+, B^-, D\}$ parity convention (paper i even), the
   twist by $(t, t)$ with $t \in \{1, -1\}$ preserves
   $\mathrm{MYDRowValid}\ \gamma$ at every row.

## Why these hold

### (1) absValues preservation

`twistBDRow i tp tn pq` is either `pq` (when $\ell = i + 1$ is even)
or `(tpp * p, tnn * q)` with $\mathrm{tpp}, \mathrm{tnn} \in \{1, -1\}$
(since $\mathrm{tp}, \mathrm{tn} \in \{1, -1\}$ and products of these
are also in $\{1, -1\}$).

In the first case, absolute values trivially match. In the second,
$|\mathrm{tpp} \cdot p| = |\mathrm{tpp}| \cdot |p| = 1 \cdot |p| = |p|$,
and similarly for $q$. So absolute values are preserved.

### (2) MYDRowValid preservation at parity-forced positions

**Key observation**: in the `twistBDRow` formula, the transform is
applied iff $\ell := i + 1$ is **odd** (Lean's 0-indexed $i$). This
corresponds to paper's 1-indexed row $\ell$ being odd.

Paper's parity constraint for B/D forces $p_\ell = q_\ell \geq 0$ at
$\ell$ **even** — i.e., at positions where `twistBDRow` is the
identity. So the twist never modifies the parity-forced rows.

Formally: for B/D, MYDRowValid is checked at positions where
`SYDParityForced γ (j+1)` holds, which is `(j+1) % 2 = 0` i.e.
$\ell$ even. At such $j$, `twistBDRow` returns `pq` unchanged.
So MYDRowValid is trivially preserved.

## Lean proofs

### twistBD_preserves_absValues

```lean
theorem twistBD_preserves_absValues (E : ILS) (tp tn : ℤ)
    (htp : tp = 1 ∨ tp = -1) (htn : tn = 1 ∨ tn = -1) :
    absValues (ILS.twistBD E tp tn) = absValues E := by
  unfold absValues ILS.twistBD
  rw [List.map_mapIdx]  -- or similar lemma
  apply List.mapIdx_eq_mapIdx_of_eq
  intro i pq
  show (twistBDRow i tp tn pq).1.natAbs = pq.1.natAbs ∧
       (twistBDRow i tp tn pq).2.natAbs = pq.2.natAbs
  unfold twistBDRow
  split_ifs with hℓ
  · exact ⟨rfl, rfl⟩
  · -- tpp * p.1 and tnn * p.2, with tpp, tnn ∈ {1, -1}
    constructor
    · rw [Int.natAbs_mul]
      -- |tpp| = 1
      ...
    · similar
```

Straightforward calculation. May need `Int.natAbs_mul`, `Int.natAbs_pow`.

### twistBD_preserves_MYDRowValid

```lean
theorem twistBD_preserves_MYDRowValid (E : ILS) (γ : RootType) (t : ℤ)
    (_ht : t = 1 ∨ t = -1)
    (h : ∀ j (hj : j < E.length), MYDRowValid γ (j + 1) E[j]) :
    ∀ j (hj : j < (ILS.twistBD E t t).length),
      MYDRowValid γ (j + 1) (ILS.twistBD E t t)[j] := by
  intro j hj
  have hlen : (ILS.twistBD E t t).length = E.length := by
    unfold ILS.twistBD; simp
  -- The twisted entry at j
  have heq : (ILS.twistBD E t t)[j] = twistBDRow j t t E[j] := by
    unfold ILS.twistBD; simp [List.getElem_mapIdx]
  rw [heq]
  intro hforced
  -- SYDParityForced γ (j+1) holds; for B/D this means (j+1) even,
  -- which means j odd, which means in twistBDRow ℓ = j+1 is even,
  -- so the row is unchanged.
  have h_orig := h j (by rwa [hlen] at hj) hforced
  -- SYDParityForced γ (j+1) for γ ∈ {Bplus, Bminus, D} is (j+1) % 2 = 0.
  -- In twistBDRow, ℓ = j + 1. If ℓ even, return pq unchanged.
  cases γ with
  | Bplus | Bminus | D =>
    -- hforced : (j + 1) % 2 = 0
    have hℓ_even : (j + 1) % 2 = 0 := hforced
    simp only [twistBDRow, hℓ_even, if_pos]
    exact h_orig
  | C | M =>
    -- hforced is (j + 1) % 2 = 1 for C/M. But we're only claiming
    -- the theorem for B/D — the t = t (same tp, tn) case is used
    -- only in the Phi_D context. For C/M the outer ε doesn't apply.
    -- We can still state the theorem for all γ: for C/M, the
    -- parity is j+1 odd, so twistBDRow applies the transform:
    -- (tpp * p, tnn * q). Need to show p = q → tpp * p = tnn * q.
    -- With tp = tn = t, tpp = tnn (same formula), so preserved.
    -- But p ≥ 0 may break.
    -- **However** — this lemma is used only for B/D in Phi_D.
    -- For a clean statement, we can specialize to B/D only, or
    -- prove the weaker statement.
    sorry  -- Not needed for D case; placeholder
```

Actually the cleanest: state the lemma for **B/D only** to avoid the
C/M case complication.

## Scope decision

Given the C/M complication, let me split:

- `twistBD_preserves_absValues`: always holds (for any γ); prove
  unconditionally.
- `twistBD_preserves_MYDRowValid_BD`: prove for B/D only (where it
  matters for Phi_D with ε).

For the existing axiom `twistBD_preserves_MYDRowValid`, the current
signature is `∀ γ`, but we only use it for D. We can either:
(a) narrow the signature to `γ ∈ {B+, B-, D}` via hypothesis
(b) keep the general signature but only prove for B/D (C/M axioms
    remain in case future code uses them).

**Decision**: go with (a) for honesty.

## Review

### Pass 1: types ✓
- `absValues_length` already proved in TypeMYD.lean.
- `List.mapIdx_eq_mapIdx_of_eq` may not exist — check alternative.
- `Int.natAbs_mul` is standard Mathlib.

### Pass 2: paper ✓
- Paper Def 9.3 + Eq 9.15: matches my understanding.
- The "twist identity on even ℓ" is explicit in twistBDRow's source.

### Pass 3: downstream ✓
- Replaces 2 axioms in PhiDTyped.lean with proved theorems.
- Phi_D construction unchanged.

**Verdict**: proceed, with scope narrowing of MYDRowValid to B/D only.
