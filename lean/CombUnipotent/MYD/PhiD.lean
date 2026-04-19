/-
# M1.3: Chain-level MYD extraction Φ_γ^chain

Reference: NL proof at `lean/docs/blueprints/M1_3_Phi_D.md`
(3-pass self-reviewed, 2026-04-19).

This file defines the **plumbing** layer for the paper Prop 11.15 map
`(τ, ε) ↦ L_τ ⊗ (ε, ε)`. M1.3 operates at the AC-chain level: given a
`List ACStepData` and an `ε`, produce either `some (ε-twisted L)` or
`none` if the chain doesn't close to a singleton `ACResult`.

The PBP-level wrapper `Phi_D_raw τ ε := Phi_chain .D (descentChain_D τ) ε`
is deferred to M1.4, which will also define `descentChain_D`.
-/
import CombUnipotent.MYD.FoldSingleton

namespace BMSZ

/-- Extract the unique ILS payload from an `ACResult` of the form
    `[(1, E)]`. Returns `none` for any other shape (empty list, multi-term,
    coefficient ≠ 1). -/
def extractILS : ACResult → Option ILS
  | [(1, E)] => some E
  | _ => none

theorem extractILS_singleton (E : ILS) :
    extractILS [(1, E)] = some E := rfl

/-- **Chain-level raw map** (paper Prop 11.15, chain form):
    `Phi_chain γ chain ε` applies `AC.fold γ chain`, extracts the unique
    ILS payload (if present), and applies the ε-twist by `(-1, -1)` when
    `ε = 1`. Returns `none` iff the chain doesn't produce a singleton.
-/
def Phi_chain (baseType : RootType) (chain : List ACStepData)
    (ε : Fin 2) : Option ILS :=
  (extractILS (AC.fold baseType chain)).map (fun E =>
    if ε = 1 then ILS.twistBD E (-1) (-1) else E)

/-- **Compatibility lemma**: under `ChainSingleton`, `Phi_chain` returns
    `some`, matching paper's `L_τ ⊗ (ε, ε)` formula.

    Proof: `AC_fold_singleton` (M1.2) gives
    `AC.fold γ chain = [(1, E_final)]`; then `extractILS` evaluates to
    `some E_final`, and `Option.map` applies the ε-twist. -/
theorem Phi_chain_some_of_chain_singleton
    (baseType : RootType) (chain : List ACStepData) (ε : Fin 2)
    (E_final : ILS)
    (h : ChainSingleton (baseILS baseType) chain E_final) :
    Phi_chain baseType chain ε =
      some (if ε = 1 then ILS.twistBD E_final (-1) (-1) else E_final) := by
  unfold Phi_chain
  rw [AC_fold_singleton baseType chain E_final h]
  rfl

end BMSZ
