# NL proof: `Phi_D_sig_injective` (D-type)

**Goal**: `Function.Injective (fun p : PBPSet_D_sig μP μQ s × Fin 2 => Phi_D_sig p.1 p.2)`

**Restriction needed**: `(μP, μQ) ≠ (⊥, ⊥)` (non-empty shapes),
else Phi fails to distinguish the two ε values for the unique empty τ.

## Setup

Given `σh₁, σh₂ : PBPSet_D_sig μP μQ s`, `ε₁, ε₂ : Fin 2`, and
`h_eq : Phi_D_sig σh₁ ε₁ = Phi_D_sig σh₂ ε₂`, we must show
`(σh₁, ε₁) = (σh₂, ε₂)`.

Let `σᵢ := σhᵢ.val` and `τᵢ := σᵢ.val`, so `τᵢ : PBP` with:
- `τᵢ.γ = .D`
- `τᵢ.P.shape = μP`, `τᵢ.Q.shape = μQ`
- `signTarget_D τᵢ = s`

From `Phi_D_sig` def:
- `chainᵢ := Classical.choose (exists_descentChain_D σᵢ)`
- `Eᵢ := Classical.choose (descentChain_D_singleton h_chainᵢ)`
- `ε_intᵢ := if εᵢ = 1 then -1 else 1`
- `E_twistedᵢ := ILS.twistBD Eᵢ ε_intᵢ ε_intᵢ`

`h_eq` gives `E_twisted₁ = E_twisted₂` (via `MYD_sig.ext`).

## Proof strategy

### Step 1: Package E as ACResult

`Lᵢ := [(1, E_twistedᵢ)] : ACResult`. Since `Lᵢ = [(1, twistBD Eᵢ ε_intᵢ ε_intᵢ)]`,
we have:
- `Lᵢ.twistBD (-1) (-1) = [(1, twistBD E_twistedᵢ (-1) (-1))]`
- After double twist: `twistBD (twistBD Eᵢ ε_intᵢ ε_intᵢ) (-1) (-1) = twistBD Eᵢ (ε_intᵢ · -1) (ε_intᵢ · -1) = twistBD Eᵢ (-ε_intᵢ) (-ε_intᵢ)`

### Step 2: Identify the ε_inner parameter

For `prop_11_15_PBP`, we need an `ε_inner : Fin 2` such that every `r ∈ Lᵢ`
has first entry `(tailSignature_D τᵢ .1, ± tailSignature_D τᵢ .2)` where the
sign of `.2` is determined by `ε_inner` and `PBP.epsilon τᵢ`.

Take `ε_inner := ε₁` (or ε₂; they should match).

### Step 3: Verify `h_first₁` (and `h_first₂`)

Claim: `E₁[0] = (tailSignature_D τ₁ .1, ± tailSignature_D τ₁ .2)`.

**Sub-proof**: By induction on the chain. For the outer-most augment at the
last chain step, `thetaLift_CD_first_entry` gives `E[0] = (addp, addn)` where
`addp = p - sign(E_mid).1 - firstColSign(E_mid).2` and similarly for addn.

Claim: `addp = tailSignature_D τ .1` and `addn = ± tailSignature_D τ .2`.
This is paper Lemma 11.6 content. **Sub-lemma needed**.

### Step 4: Apply `prop_11_15_PBP_D_injective_full`

Hypotheses:
- `hγᵢ : τᵢ.γ = .D` — from `σᵢ.prop.1`
- `Lᵢ ≠ []` — trivial (singleton list)
- `ε_inner` — from Step 2
- `h_firstᵢ` — from Step 3
- `hpᵢ_nn, hqᵢ_nn` — `tailSig_nonneg_D τᵢ hγᵢ` (already proved in MYD.lean:4235)
- `h_ntᵢ` — tail non-triviality. Requires `shape ≠ ⊥` assumption (**uses non-empty hypothesis**)
- `h_eq` — from Step 1's ACResult packaging + twistBD linearity

Conclusion: `ε₁ = ε₂ ∧ L₁ = L₂`.

### Step 5: From `L₁ = L₂` to `E_untwisted_1 = E_untwisted_2`

`Lᵢ = [(1, E_twistedᵢ)]`. `L₁ = L₂` gives `E_twisted_1 = E_twisted_2`. Combined
with `ε₁ = ε₂`, we get `twistBD E₁ ε_int ε_int = twistBD E₂ ε_int ε_int`.
Since twistBD is invertible (self-inverse when squared), `E₁ = E₂`.

### Step 6: From `E₁ = E₂` to `σ₁ = σ₂`

This is the HARDEST step. Paper Prop 11.15's full argument:
- Decomposes each `Eᵢ` by truncating outermost row → recovers `(p_{τᵢ,t}, q_{τᵢ,t})` pair
- Uses `Lemma 11.6` to get the first-entry pattern
- Uses `Lemma 11.13`: chain invertibility — from E agreement at inner levels, recover τ at each level
- Uses `ddescent_inj_D` at the PBP level to get τ₁ = τ₂

**Critical sub-lemma** (paper content): `chain_extract_injective_D`:
```
theorem chain_extract_injective_D (τ₁ τ₂ : PBP) (hγ₁ : τ₁.γ = .D) (hγ₂ : τ₂.γ = .D)
    (hshapeP : τ₁.P.shape = τ₂.P.shape) (hshapeQ : τ₁.Q.shape = τ₂.Q.shape)
    (chain₁ : IsDescentChain_D τ₁ c₁) (chain₂ : IsDescentChain_D τ₂ c₂)
    (E : ILS)
    (h_sing₁ : ChainSingleton (baseILS .D) c₁ E)
    (h_sing₂ : ChainSingleton (baseILS .D) c₂ E) :
    τ₁ = τ₂
```

This is paper-specific content not easily derivable without the full
argument.

### Step 7: Conclude

From Steps 5, 6: `τ₁ = τ₂`. Combined with shape/γ equality, `σ₁ = σ₂`.
From Step 4: `ε₁ = ε₂`. Hence `(σh₁, ε₁) = (σh₂, ε₂)`.

## Framework (Lean scaffold)

```lean
theorem Phi_D_sig_injective {μP μQ : YoungDiagram} {s : ℤ × ℤ}
    (h_ne : μP.cells.card + μQ.cells.card > 0) :
    Function.Injective (fun p : PBPSet_D_sig μP μQ s × Fin 2 =>
      Phi_D_sig p.1 p.2) := by
  intro ⟨σh₁, ε₁⟩ ⟨σh₂, ε₂⟩ h_eq_phi
  -- Step 1: Extract .E equality
  have h_E_eq : (Phi_D_sig σh₁ ε₁).E = (Phi_D_sig σh₂ ε₂).E :=
    congrArg MYD_sig.E h_eq_phi

  -- Chain extractions
  let σ₁ := σh₁.val
  let σ₂ := σh₂.val
  let chain₁ := Classical.choose (exists_descentChain_D σ₁)
  let h_chain₁ := Classical.choose_spec (exists_descentChain_D σ₁)
  let E₁ := Classical.choose (descentChain_D_singleton h_chain₁)
  let h_sing₁ := Classical.choose_spec (descentChain_D_singleton h_chain₁)
  let chain₂ := Classical.choose (exists_descentChain_D σ₂)
  let h_chain₂ := Classical.choose_spec (exists_descentChain_D σ₂)
  let E₂ := Classical.choose (descentChain_D_singleton h_chain₂)
  let h_sing₂ := Classical.choose_spec (descentChain_D_singleton h_chain₂)

  -- Step 2-4: use prop_11_15_PBP via ACResult packaging
  sorry  -- detailed bridge below

  -- Step 5: E₁ = E₂ from twistBD invertibility
  -- Step 6: σ₁ = σ₂ from chain_extract_injective_D (sorry)
  -- Step 7: pair equality
```

## Estimated effort

- Step 2 (ε_inner choice): ~20 LOC, trivial
- Step 3 (h_first): ~150 LOC. Sub-lemma requires `thetaLift_CD_first_entry`
  at chain scale + Lemma 11.6 translation
- Step 4 (prop_11_15 application): ~50 LOC
- Step 5 (twistBD invertibility): ~30 LOC
- Step 6 (`chain_extract_injective_D`): ~300 LOC paper content
- Step 7 (pair equality): ~20 LOC

**Total**: ~570 LOC for full closure of one `Phi_D_sig_injective` sorry.

## Critical sub-sorries introduced

1. `chain_extract_first_entry_D`: chain-extracted E[0] = (tailSignature_D τ .1, ±τ.2)
2. `chain_extract_injective_D`: chain-extracted E determines τ

Both are paper-content. Closing Phi_D_sig_injective reduces the 1 original
sorry to 2 new focused sorries (each closer to specific paper lemmas).
