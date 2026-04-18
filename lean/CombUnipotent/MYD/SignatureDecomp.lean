/-
# Signature Decomposition for D-type PBP

Reference: [BMSZ] Equation (11.7), [BMSZb] Proposition 10.9.

For D-type PBP τ with orbit Ǒ = (r₁, r₂, ...):
  Sign(τ) = (c₂(O), c₂(O)) + Sign(∇²(τ)) + Sign(τ_t)

where c₂(O) = μQ.colLen 0 = (r₂-1)/2 is the second column length of the BV dual.

This decomposes the PBP signature into:
1. A constant from the Q shape: (μQ.colLen 0, μQ.colLen 0)
2. The signature contribution from columns ≥ 1 (= double descent)
3. The tail signature from column 0 above Q

## Status

This file is a documentation stub — the actual formal statements live in
`CombUnipotent/MYD.lean`:

- `PBP.signature_fst_decomp_D` (line ~2159): signature.1 split as
  `Q.colLen 0 + colGe1 contribution + tail col 0 contribution`.
- `PBP.signature_snd_decomp_D` (line ~2189): signature.2 analog.
- `prop_11_4_signature_decomp_D` (line ~2248): packaged both components.

The colGe1 contribution corresponds to `Sign(∇²(τ))` at the PBP level, and the
tail col 0 contribution is precisely `tailSignature_D τ`.

For the PBP-level bridge to `Sign(∇²(τ))` (connecting colGe1 to a signature of
the descended PBP), see `CombUnipotent/MYD/Prop11_5_AtomicDischarge.lean`
for the atomic 3-fact discharge form that sidesteps this bridge.
-/
import CombUnipotent.MYD

namespace PBP

/-! Re-export the key signature decomposition theorems for documentation purposes. -/

/-- **Re-export**: D-type signature decomposition (fst).
    See `PBP.signature_fst_decomp_D` in `MYD.lean` for the proof. -/
theorem signature_decomp_D_fst (τ : PBP) (hγ : τ.γ = .D) :
    (PBP.signature τ).1 =
      τ.Q.shape.colLen 0 +
      (PBP.countSymColGe1 τ.P .dot + τ.Q.countSym .dot +
       2 * PBP.countSymColGe1 τ.P .r + PBP.countSymColGe1 τ.P .c +
       PBP.countSymColGe1 τ.P .d) +
      (2 * PBP.countCol0 τ.P.paint .r (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0) +
       PBP.countCol0 τ.P.paint .c (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0) +
       PBP.countCol0 τ.P.paint .d (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0)) :=
  PBP.signature_fst_decomp_D τ hγ

/-- **Re-export**: D-type signature decomposition (snd).
    See `PBP.signature_snd_decomp_D` in `MYD.lean` for the proof. -/
theorem signature_decomp_D_snd (τ : PBP) (hγ : τ.γ = .D) :
    (PBP.signature τ).2 =
      τ.Q.shape.colLen 0 +
      (PBP.countSymColGe1 τ.P .dot + τ.Q.countSym .dot +
       2 * PBP.countSymColGe1 τ.P .s + PBP.countSymColGe1 τ.P .c +
       PBP.countSymColGe1 τ.P .d) +
      (2 * PBP.countCol0 τ.P.paint .s (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0) +
       PBP.countCol0 τ.P.paint .c (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0) +
       PBP.countCol0 τ.P.paint .d (τ.Q.shape.colLen 0)
           (τ.P.shape.colLen 0 - τ.Q.shape.colLen 0)) :=
  PBP.signature_snd_decomp_D τ hγ

end PBP
