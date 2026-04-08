/-
# Signature and Epsilon

Reference: [BMSZ] Equations (3.3), (3.6); [BMSZb] Equation (2.17).

The signature (p_τ, q_τ) encodes the real form of the group.
The epsilon ε_τ ∈ {0, 1} detects the presence of `d` in the first columns.
-/
import CombUnipotent.PBP

/-! ## Symbol counting -/

/-- Count cells with symbol σ in a painted Young diagram. -/
def PaintedYoungDiagram.countSym (D : PaintedYoungDiagram) (σ : DRCSymbol) : ℕ :=
  (D.shape.cells.filter (fun c => D.paint c.1 c.2 = σ)).card

/-! ## Signature -/

/-- Signature (p_τ, q_τ) of a PBP.
    Reference: [BMSZ] Equation (3.3); [BMSZb] Equation (2.17).

    For B⁺/B⁻/D:
      p = n_• + 2·n_r + n_c + n_d + [1 if B⁺]
      q = n_• + 2·n_s + n_c + n_d + [1 if B⁻]

    For C/M:
      p = q = n_• + n_r + n_s + n_c + n_d -/
noncomputable def PBP.signature (τ : PBP) : ℕ × ℕ :=
  let nDot := τ.P.countSym .dot + τ.Q.countSym .dot
  let nR := τ.P.countSym .r + τ.Q.countSym .r
  let nS := τ.P.countSym .s + τ.Q.countSym .s
  let nC := τ.P.countSym .c + τ.Q.countSym .c
  let nD := τ.P.countSym .d + τ.Q.countSym .d
  match τ.γ with
  | .Bplus | .Bminus | .D =>
    let p := nDot + 2 * nR + nC + nD + (if τ.γ = .Bplus then 1 else 0)
    let q := nDot + 2 * nS + nC + nD + (if τ.γ = .Bminus then 1 else 0)
    (p, q)
  | .C | .M =>
    let n := nDot + nR + nS + nC + nD
    (n, n)

/-! ## Epsilon -/

/-- Whether `d` occurs in column 0 of a painted Young diagram. -/
def PaintedYoungDiagram.hasDInCol0 (D : PaintedYoungDiagram) : Bool :=
  (D.shape.cells.filter (fun c => c.2 = 0 ∧ D.paint c.1 c.2 = .d)).Nonempty

/-- ε_τ ∈ {0, 1}: detects whether `d` occurs in column 0 of P or Q.
    Reference: [BMSZ] Equation (3.6).

    ε_τ = 0  iff  `d` occurs in column 0 of P or column 0 of Q.
    ε_τ = 1  otherwise. -/
def PBP.epsilon (τ : PBP) : Fin 2 :=
  if τ.P.hasDInCol0 || τ.Q.hasDInCol0 then 0 else 1
