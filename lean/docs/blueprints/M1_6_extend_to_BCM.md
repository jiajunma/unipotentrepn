# M1.6: extend constructive bijection to γ ∈ {B⁺, B⁻, C, M}

**Milestone**: M1.6 of the MYD formalization plan.

**Status**: natural-language draft (2026-04-19).

## Overview

M1.4/M1.5 established the Phase A interface for D type. M1.6 extends
this to the remaining root types, yielding Phase A axioms/Equiv for:

- **Paper Prop 11.15**: the D case is done. B⁺ and B⁻ are analogous.
- **Paper Prop 11.17**: C and M cases. These use `PBPSet ≃ MYD`
  **without** the `Fin 2` factor (the paper's C/M result doesn't
  need the extra ε).

## Paper statements

**Prop 11.15** (B/D): for $\gamma \in \{B^+, B^-, D\}$,
$$
(\tau, \varepsilon) \mapsto L_\tau \otimes (\varepsilon, \varepsilon)
$$
gives a bijection $\PBP_\gamma(\check{\mathcal{O}}) \times \mathrm{Fin}\,2 \simeq \MYD_\gamma(O)$.

**Prop 11.17** (C/M): for $\gamma \in \{C, \tilde{C}\}$,
$$
\tau \mapsto L_\tau
$$
gives a bijection $\PBP_\gamma(\check{\mathcal{O}}) \simeq \MYD_\gamma(O)$.

No $\varepsilon$ in the C/M case because the C/M chain doesn't have
the ε_τ degree of freedom (absorbed by the ε_℘ primitive pair choice).

## Phase A strategy

Rather than re-doing the full `IsDescentChain_γ` + 3-axiom interface +
Equiv construction for each γ (D already has this), we take a
**thinner** Phase A for B⁺, B⁻, C, M: directly axiomatize the
`Equiv` per type, with the `DPCoherent_γ` shape-vs-dp coherence.

This is acceptable because:
- Phase A's purpose is to state the bijection as a usable Lean term.
- The internal chain decomposition is an implementation detail of
  Phase B.
- For the downstream user (M1.7+ or application code), having
  `Phi_γ_equiv` as a `Equiv` is what matters.

## Interface: one Equiv per γ

```lean
namespace BMSZ

/-- Shape-dp coherence per γ. -/
def DPCoherent_Bplus (μP μQ : YoungDiagram) (dp : DualPart) : Prop :=
  μP.colLens = dpartColLensP_B dp ∧ μQ.colLens = dpartColLensQ_B dp

def DPCoherent_Bminus : ... := DPCoherent_Bplus    -- same shape structure
def DPCoherent_C : ... := ...  via dpartColLensP_C, dpartColLensQ_C
def DPCoherent_M : ... := ...  via dpartColLensP_M, dpartColLensQ_M

/-- Phi_Bplus_equiv: paper Prop 11.15 B⁺. -/
axiom Phi_Bplus_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_Bplus μP μQ dp) :
    PBPSet .Bplus μP μQ × Fin 2 ≃ MYD .Bplus (dpToSYD .Bplus dp)

/-- Phi_Bminus_equiv: paper Prop 11.15 B⁻. -/
axiom Phi_Bminus_equiv ...

/-- Phi_C_equiv: paper Prop 11.17 C. Note: no Fin 2. -/
axiom Phi_C_equiv {μP μQ : YoungDiagram} (dp : DualPart)
    (h_coh : DPCoherent_C μP μQ dp) :
    PBPSet .C μP μQ ≃ MYD .C (dpToSYD .C dp)

/-- Phi_M_equiv: paper Prop 11.17 M (= C̃). Note: no Fin 2. -/
axiom Phi_M_equiv ...

end BMSZ
```

## Self-review

### Pass 1: type correctness

- B⁺ / B⁻ signatures mirror D's `Phi_D_equiv` exactly — only γ and
  the coherence predicate differ. ✓
- C / M signatures drop `× Fin 2` on the source side — matches paper
  Prop 11.17. ✓
- `DPCoherent_γ` for each γ uses the corresponding `dpartColLensP_γ`,
  `dpartColLensQ_γ` functions, all of which exist
  (`CountingProof/Basic.lean:101+`). ✓

### Pass 2: paper semantics

- Paper Prop 11.15: applies to $\star \in \{B^+, B^-, D\}$. Not to C/M.
  My B⁺ and B⁻ axioms match. ✓
- Paper Prop 11.17: applies to $\star \in \{C, \tilde{C}\}$ (= C, M).
  My C and M axioms match the source × Fin 2 structure absent. ✓
- Paper Prop 11.16 (C/M descent bijectivity) is a separate statement;
  in our formalization it's captured by `card_PBPSet_C_eq_countPBP_C`
  et al. (the counting theorems). Not stated here as a separate axiom.

### Pass 3: downstream compatibility

- The 4 new Equivs give uniform downstream access. Anyone who wants
  paper's bijection for any γ can invoke `Phi_γ_equiv`.
- Phase B for each γ would follow the D template (descent chain,
  singleton, in-MYD, Psi, round-trips). C/M would need a separate
  descent structure (paper uses single-descent alternating types,
  different from D's double-descent).

**Verdict**: proceed to formalization.
