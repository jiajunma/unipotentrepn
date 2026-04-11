/-
# Counting Proof: Base case and double descent map (D type)

Extracted from the monolithic `CountingProof.lean`.
-/
import CombUnipotent.CountingProof.Basic

open Classical

/-! ## Base case: empty PBP -/

/-- The empty painted Young diagram: shape ⊥, paint always dot. -/
def emptyPYD : PaintedYoungDiagram where
  shape := ⊥
  paint := fun _ _ => .dot
  paint_outside := fun _ _ _ => rfl

/-- The unique PBP with empty shapes. -/
def emptyPBP (γ : RootType) : PBP where
  γ := γ
  P := emptyPYD
  Q := emptyPYD
  sym_P := fun _ _ h => absurd h (YoungDiagram.notMem_bot _)
  sym_Q := fun _ _ h => absurd h (YoungDiagram.notMem_bot _)
  dot_match := by
    intro i j; constructor
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
    · intro ⟨h, _⟩; exact absurd h (YoungDiagram.notMem_bot _)
  mono_P := fun _ _ _ _ _ _ h => absurd h (YoungDiagram.notMem_bot _)
  mono_Q := fun _ _ _ _ _ _ h => absurd h (YoungDiagram.notMem_bot _)
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ _
    simp only [paintBySide, emptyPYD] at h₁
    cases s₁ <;> simp at h₁
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ _
    simp only [paintBySide, emptyPYD] at h₁
    cases s₁ <;> simp at h₁
  col_c_P := by intro _ _ _ h; simp [emptyPYD] at h
  col_c_Q := by intro _ _ _ h; simp [emptyPYD] at h
  col_d_P := by intro _ _ _ h; simp [emptyPYD] at h
  col_d_Q := by intro _ _ _ h; simp [emptyPYD] at h

/-- Any PBP with empty P shape has P = emptyPYD. -/
theorem PYD_eq_emptyPYD_of_shape_bot {D : PaintedYoungDiagram} (h : D.shape = ⊥) :
    D = emptyPYD := by
  apply PaintedYoungDiagram.ext'
  · exact h
  · ext i j
    have : (i, j) ∉ D.shape := by rw [h]; exact YoungDiagram.notMem_bot _
    rw [D.paint_outside i j this]
    rfl

/-- Any PBP in PBPSet γ ⊥ ⊥ equals emptyPBP γ. -/
theorem PBPSet_bot_unique (γ : RootType) (x : PBPSet γ ⊥ ⊥) :
    x.val = emptyPBP γ := by
  have hγ := x.prop.1
  have hP := x.prop.2.1
  have hQ := x.prop.2.2
  apply PBP.ext''
  · exact hγ
  · exact PYD_eq_emptyPYD_of_shape_bot hP
  · exact PYD_eq_emptyPYD_of_shape_bot hQ

/-- The empty PBP is in PBPSet. -/
def emptyPBP_mem (γ : RootType) : PBPSet γ ⊥ ⊥ :=
  ⟨emptyPBP γ, rfl, rfl, rfl⟩

/-- PBPSet γ ⊥ ⊥ has exactly one element. -/
theorem card_PBPSet_bot (γ : RootType) :
    Fintype.card (PBPSet γ ⊥ ⊥) = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨emptyPBP_mem γ, fun x => Subtype.ext (PBPSet_bot_unique γ x)⟩

/-! ## Double descent as PBP map (D type)

Construct `∇²τ` as a formal PBP for D-type τ.
Shape: P' = shiftLeft(P), Q' = shiftLeft(Q).
Paint: P' = doubleDescent_D_paintL, Q' = all dots. -/

/-- Extract: if doubleDescent_D_paintL = σ with σ ∉ {dot, s}, then P.paint = σ. -/
theorem doubleDescent_D_paintL_extract (τ : PBP) {i j : ℕ}
    (hdd : PBP.doubleDescent_D_paintL τ i j ≠ .dot)
    (hdd_s : PBP.doubleDescent_D_paintL τ i j ≠ .s) :
    τ.P.paint i (j + 1) = PBP.doubleDescent_D_paintL τ i j := by
  simp only [PBP.doubleDescent_D_paintL] at hdd hdd_s ⊢
  by_cases ha : i < τ.Q.shape.colLen (j + 1)
  · exact absurd (if_pos ha ▸ rfl) hdd
  · rw [if_neg ha] at hdd hdd_s ⊢
    by_cases hb : i < PBP.dotScolLen τ.P (j + 1)
    · exact absurd (if_pos hb ▸ rfl) hdd_s
    · rw [if_neg hb]

/-- The double descent PBP ∇²τ for D type. All 13 constraints verified. -/
noncomputable def doubleDescent_D_PBP (τ : PBP) (hγ : τ.γ = .D) : PBP where
  γ := .D
  P := {
    shape := τ.P.shape.shiftLeft
    paint := PBP.doubleDescent_D_paintL τ
    paint_outside := fun i j hmem => by
      rw [YoungDiagram.mem_shiftLeft] at hmem
      exact doubleDescent_D_paintL_dot τ hγ (by
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem; omega)
  }
  Q := {
    shape := τ.Q.shape.shiftLeft
    paint := fun _ _ => .dot
    paint_outside := fun _ _ _ => rfl
  }
  sym_P := fun _ _ _ => by simp [DRCSymbol.allowed]  -- D/L: all True
  sym_Q := fun _ _ _ => by simp [DRCSymbol.allowed]  -- D/R: dot = dot
  dot_match := by
    intro i j; constructor
    · intro ⟨hmemP, hpaint⟩
      have hmemP' := YoungDiagram.mem_shiftLeft.mp hmemP
      -- paint = dot means i < Q.colLen(j+1) (the dot region)
      have h₁ : i < τ.Q.shape.colLen (j + 1) := by
        simp only [PBP.doubleDescent_D_paintL] at hpaint
        by_contra hge; push_neg at hge
        by_cases hs : i < PBP.dotScolLen τ.P (j + 1)
        · rw [if_neg (by omega), if_pos hs] at hpaint; exact absurd hpaint (by decide)
        · rw [if_neg (by omega), if_neg hs] at hpaint
          have ⟨hmQ, _⟩ := (τ.dot_match i (j+1)).mp ⟨hmemP', hpaint⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hmQ) (by omega)
      exact ⟨YoungDiagram.mem_shiftLeft.mpr (YoungDiagram.mem_iff_lt_colLen.mpr h₁), rfl⟩
    · intro ⟨hmemQ, _⟩
      have hmemQ' := YoungDiagram.mem_shiftLeft.mp hmemQ
      have h₁ : i < τ.Q.shape.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp hmemQ'
      refine ⟨YoungDiagram.mem_shiftLeft.mpr (PBP.Q_le_P_of_D τ hγ hmemQ'), ?_⟩
      simp [PBP.doubleDescent_D_paintL, if_pos h₁]
  mono_P := by
    intro i₁ j₁ i₂ j₂ hi hj hmem
    have hmem' := YoungDiagram.mem_shiftLeft.mp hmem
    simp only [PBP.doubleDescent_D_paintL]
    by_cases h₁ : i₁ < τ.Q.shape.colLen (j₁ + 1)
    · rw [if_pos h₁]; simp [DRCSymbol.layerOrd]
    · by_cases h₂ : i₁ < PBP.dotScolLen τ.P (j₁ + 1)
      · rw [if_neg h₁, if_pos h₂]
        have hQ_anti := τ.Q.shape.colLen_anti (j₁+1) (j₂+1) (by omega)
        by_cases h₃ : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · omega
        · rw [if_neg h₃]
          by_cases h₄ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
          · rw [if_pos h₄]
          · rw [if_neg h₄]
            have hlo := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P
              (Nat.not_lt.mp h₄) hmem'
            simp only [DRCSymbol.layerOrd] at hlo ⊢; omega
      · rw [if_neg h₁, if_neg h₂]
        have hQ_anti := τ.Q.shape.colLen_anti (j₁+1) (j₂+1) (by omega)
        have hQ_le := PBP.Q_colLen_le_dotScolLen_of_D τ hγ (j₁ + 1)
        by_cases h₃ : i₂ < τ.Q.shape.colLen (j₂ + 1)
        · omega
        · rw [if_neg h₃]
          by_cases h₄ : i₂ < PBP.dotScolLen τ.P (j₂ + 1)
          · -- Impossible: dotScolLen(P, j₁+1) ≤ i₁ ≤ i₂ < dotScolLen(P, j₂+1)
            -- but dotScolLen is anti-monotone (j₁+1 ≤ j₂+1)
            exfalso
            have hds_anti := (PBP.dotSdiag τ.P τ.mono_P).colLen_anti (j₁+1) (j₂+1) (by omega)
            rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P,
                ← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P] at hds_anti
            omega
          · rw [if_neg h₄]
            exact τ.mono_P i₁ (j₁+1) i₂ (j₂+1) hi (by omega) hmem'
  mono_Q := fun _ _ _ _ _ _ h => by
    simp [DRCSymbol.layerOrd]
  row_s := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    simp only [paintBySide] at h₁ h₂
    -- Q' is all dots → s can only come from P' (side L)
    cases s₁ <;> cases s₂ <;> simp only at h₁ h₂
    · -- Both L: s in P' comes from middle region Q.colLen(j+1) ≤ i < dotScolLen(P, j+1)
      -- This means P(i, j+1) has layerOrd ≤ 1 and is not dot → P(i, j+1) = s
      -- Row uniqueness in τ gives j₁+1 = j₂+1
      simp only [PBP.doubleDescent_D_paintL] at h₁ h₂
      -- h₁: s at (i, j₁) means Q.colLen(j₁+1) ≤ i < dotScolLen(P, j₁+1)
      have hq₁ : ¬(i < τ.Q.shape.colLen (j₁ + 1)) := by
        intro hlt; rw [if_pos hlt] at h₁; exact absurd h₁ (by decide)
      have hds₁ : i < PBP.dotScolLen τ.P (j₁ + 1) := by
        by_contra hge; push_neg at hge
        rw [if_neg hq₁, if_neg (by omega)] at h₁
        -- h₁ : P.paint(i, j₁+1) = s. paint ≠ dot → in shape.
        have hmem : (i, j₁ + 1) ∈ τ.P.shape := by
          by_contra hout
          exact absurd (τ.P.paint_outside i (j₁+1) hout) (by rw [h₁]; decide)
        have := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P hge hmem
        rw [h₁, DRCSymbol.layerOrd] at this; omega
      -- P(i, j₁+1) ∈ {dot, s} and ∉ Q (not dot by dot_match) → P(i, j₁+1) = s
      have hPi₁ : τ.P.paint i (j₁ + 1) = .s := by
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hds₁)
        have hne : τ.P.paint i (j₁ + 1) ≠ .dot := by
          intro heq
          have hmem₁ : (i, j₁+1) ∈ τ.P.shape := YoungDiagram.mem_iff_lt_colLen.mpr
            (Nat.lt_of_lt_of_le hds₁ (PBP.dotScolLen_le_colLen τ.P τ.mono_P _))
          have ⟨hq, _⟩ := (τ.dot_match i (j₁+1)).mp ⟨hmem₁, heq⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hq) (by omega)
        revert hlo hne; cases τ.P.paint i (j₁ + 1) <;> simp [DRCSymbol.layerOrd]
      -- Similarly for j₂
      have hq₂ : ¬(i < τ.Q.shape.colLen (j₂ + 1)) := by
        intro hlt; rw [if_pos hlt] at h₂; exact absurd h₂ (by decide)
      have hds₂ : i < PBP.dotScolLen τ.P (j₂ + 1) := by
        by_contra hge; push_neg at hge
        rw [if_neg hq₂, if_neg (by omega)] at h₂
        have hmem : (i, j₂ + 1) ∈ τ.P.shape := by
          by_contra hout
          exact absurd (τ.P.paint_outside i (j₂+1) hout) (by rw [h₂]; decide)
        have := PBP.layerOrd_gt_one_of_ge_dotScolLen τ.P τ.mono_P hge hmem
        rw [h₂, DRCSymbol.layerOrd] at this; omega
      have hPi₂ : τ.P.paint i (j₂ + 1) = .s := by
        have hlo := PBP.layerOrd_le_one_of_lt_dotSdiag_colLen τ.P τ.mono_P
          (by rw [← PBP.dotScolLen_eq_dotSdiag_colLen _ τ.mono_P]; exact hds₂)
        have hne : τ.P.paint i (j₂ + 1) ≠ .dot := by
          intro heq
          have hmem₂ : (i, j₂+1) ∈ τ.P.shape := YoungDiagram.mem_iff_lt_colLen.mpr
            (Nat.lt_of_lt_of_le hds₂ (PBP.dotScolLen_le_colLen τ.P τ.mono_P _))
          have ⟨hq, _⟩ := (τ.dot_match i (j₂+1)).mp ⟨hmem₂, heq⟩
          exact absurd (YoungDiagram.mem_iff_lt_colLen.mp hq) (by omega)
        revert hlo hne; cases τ.P.paint i (j₂ + 1) <;> simp [DRCSymbol.layerOrd]
      -- Apply row_s of τ
      have := τ.row_s i .L .L (j₁+1) (j₂+1)
        (show paintBySide τ.P τ.Q .L i (j₁+1) = .s by simp [paintBySide]; exact hPi₁)
        (show paintBySide τ.P τ.Q .L i (j₂+1) = .s by simp [paintBySide]; exact hPi₂)
      exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  row_r := by
    intro i s₁ s₂ j₁ j₂ h₁ h₂
    -- Q' is all dots → r can only come from P' (side L)
    cases s₁ <;> cases s₂ <;> simp only [paintBySide] at h₁ h₂
    · -- Both L: r in P' only from the P.paint region (not dot/s regions)
      simp only [PBP.doubleDescent_D_paintL] at h₁ h₂
      by_cases ha₁ : i < τ.Q.shape.colLen (j₁+1)
      · rw [if_pos ha₁] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha₁] at h₁; by_cases hb₁ : i < PBP.dotScolLen τ.P (j₁+1)
        · rw [if_pos hb₁] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb₁] at h₁
          by_cases ha₂ : i < τ.Q.shape.colLen (j₂+1)
          · rw [if_pos ha₂] at h₂; exact absurd h₂ (by decide)
          · rw [if_neg ha₂] at h₂; by_cases hb₂ : i < PBP.dotScolLen τ.P (j₂+1)
            · rw [if_pos hb₂] at h₂; exact absurd h₂ (by decide)
            · rw [if_neg hb₂] at h₂
              have := τ.row_r i .L .L (j₁+1) (j₂+1)
                (show paintBySide τ.P τ.Q .L i (j₁+1) = .r by simp [paintBySide]; exact h₁)
                (show paintBySide τ.P τ.Q .L i (j₂+1) = .r by simp [paintBySide]; exact h₂)
              exact ⟨rfl, by omega⟩
    · exact absurd h₂ (by decide)
    · exact absurd h₁ (by decide)
    · exact absurd h₁ (by decide)
  col_c_P := by
    intro j i₁ i₂ h₁ h₂
    -- c only comes from the P.paint branch of doubleDescent_D_paintL
    -- c only from P.paint branch: use by_cases to extract
    have hc₁ : τ.P.paint i₁ (j+1) = .c := by
      simp only [PBP.doubleDescent_D_paintL] at h₁
      by_cases ha : i₁ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hc₂ : τ.P.paint i₂ (j+1) = .c := by
      simp only [PBP.doubleDescent_D_paintL] at h₂
      by_cases ha : i₂ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_c_P (j+1) i₁ i₂ hc₁ hc₂
  col_c_Q := by intro _ _ _ h; exact DRCSymbol.noConfusion h
  col_d_P := by
    intro j i₁ i₂ h₁ h₂
    have hd₁ : τ.P.paint i₁ (j+1) = .d := by
      simp only [PBP.doubleDescent_D_paintL] at h₁
      by_cases ha : i₁ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₁; exact absurd h₁ (by decide)
      · rw [if_neg ha] at h₁; by_cases hb : i₁ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₁; exact absurd h₁ (by decide)
        · rw [if_neg hb] at h₁; exact h₁
    have hd₂ : τ.P.paint i₂ (j+1) = .d := by
      simp only [PBP.doubleDescent_D_paintL] at h₂
      by_cases ha : i₂ < τ.Q.shape.colLen (j+1)
      · rw [if_pos ha] at h₂; exact absurd h₂ (by decide)
      · rw [if_neg ha] at h₂; by_cases hb : i₂ < PBP.dotScolLen τ.P (j+1)
        · rw [if_pos hb] at h₂; exact absurd h₂ (by decide)
        · rw [if_neg hb] at h₂; exact h₂
    exact τ.col_d_P (j+1) i₁ i₂ hd₁ hd₂
  col_d_Q := by intro _ _ _ h; exact DRCSymbol.noConfusion h

/-! ## Scaffolding for counting proof

### Already proved (Prop 10.9, in Tail.lean):
  `ddescent_inj_D`: same shapes + same ∇² paint + same (sig, eps) → same PBP paint
  This is the core uniqueness: τ ↦ (∇²τ, sig, eps) is injective.

### What's needed for counting:
  1. ∇² as map PBPSet(μP, μQ) → PBPSet(shiftLeft μP, shiftLeft μQ)  [done above]
  2. Wrap ddescent_inj_D for PBPSet  [next]
  3. Fiber decomposition: |PBPSet(dp)| = Σ_σ |fiber(σ)|
  4. |fiber(σ)| = tailCoeffs(k, tailClass(σ))
  5. Assembly: countPBP_D recurrence
-/

/-! ### ∇² as a map between PBPSets -/

/-- ∇² as a function between PBPSets. -/
noncomputable def doubleDescent_D_map {μP μQ : YoungDiagram}
    (τ : PBPSet .D μP μQ) :
    PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ) :=
  ⟨doubleDescent_D_PBP τ.val τ.prop.1, rfl,
   congrArg YoungDiagram.shiftLeft τ.prop.2.1,
   congrArg YoungDiagram.shiftLeft τ.prop.2.2⟩

/-! ### Wrap ddescent_inj_D for PBPSet -/

/-- Two PBPSet elements with same ∇², sig, eps are equal.
    Direct wrapper of ddescent_inj_D. -/
theorem doubleDescent_D_injective_on_PBPSet {μP μQ : YoungDiagram}
    (τ₁ τ₂ : PBPSet .D μP μQ)
    (hdd : ∀ i j, PBP.doubleDescent_D_paintL τ₁.val i j =
                   PBP.doubleDescent_D_paintL τ₂.val i j)
    (hsig : PBP.signature τ₁.val = PBP.signature τ₂.val)
    (heps : PBP.epsilon τ₁.val = PBP.epsilon τ₂.val) :
    τ₁ = τ₂ := by
  have ⟨hPeq, hQeq⟩ := PBP.ddescent_inj_D τ₁.val τ₂.val τ₁.prop.1 τ₂.prop.1
    (by rw [τ₁.prop.2.1, τ₂.prop.2.1])
    (by rw [τ₁.prop.2.2, τ₂.prop.2.2])
    hdd hsig heps
  exact Subtype.ext (PBP.ext''
    (by rw [τ₁.prop.1, τ₂.prop.1])
    (PaintedYoungDiagram.ext' (by rw [τ₁.prop.2.1, τ₂.prop.2.1])
      (funext fun i => funext (hPeq i)))
    (PaintedYoungDiagram.ext' (by rw [τ₁.prop.2.2, τ₂.prop.2.2])
      (funext fun i => funext (hQeq i))))

/-! ### Fiber of ∇² -/

/-- Fiber of ∇² over a given sub-PBP. -/
def doubleDescent_D_fiber {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :=
  {τ : PBPSet .D μP μQ // doubleDescent_D_map τ = σ}

instance {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :
    Finite (doubleDescent_D_fiber σ) :=
  Finite.of_injective (fun x => x.val) (fun _ _ h => Subtype.ext h)

noncomputable instance {μP μQ : YoungDiagram}
    (σ : PBPSet .D (YoungDiagram.shiftLeft μP) (YoungDiagram.shiftLeft μQ)) :
    Fintype (doubleDescent_D_fiber σ) :=
  Fintype.ofFinite _

/-! ### Counting theorem: roadmap with key lemmas

The counting theorem for D type is proved by induction on dp.

For the balanced case, ∇² is NOT surjective:
  - DD/RC class sub-PBPs have non-empty fibers
  - SS class sub-PBPs have EMPTY fibers (no valid column 0 extension)

So |PBPSet(dp)| = Σ_{σ, tc(σ)=DD} fiberDD + Σ_{σ, tc(σ)=RC} fiberRC
where fiberDD = tDD+tRC+tSS, fiberRC = scDD+scRC+scSS.

For the primitive case, all classes have the same fiber size.
-/

/-! ### Tail sequence counting

A valid tail of length k is a sequence s^a r^b c^{δc} d^{δd}
with a + b + δc + δd = k, δc ∈ {0,1}, δd ∈ {0,1}.

Count by (δc, δd):
  (0,0): a+b=k → k+1 = nu(k)
  (1,0): a+b=k-1 → k = nu(k-1) (k≥1)
  (0,1): a+b=k-1 → k = nu(k-1) (k≥1)
  (1,1): a+b=k-2 → k-1 = nu(k-2) (k≥2)

By tail class:
  DD (δd=1): nu(k-1) + nu(k-2)
  RC (δd=0, has r or c): nu(k-1) + nu(k-1) = 2·nu(k-1)
  SS (all-s): 1
-/

/-- The tail count (DD, RC, SS) for unconstrained tails equals tailCoeffs.1.
    k ≥ 1 in all uses (k = (r₁-r₂)/2 + 1). -/
theorem tailCoeffs_fst_DD (k : ℕ) :
    (tailCoeffs k).1.1 = nu (k - 1) + (if k ≥ 2 then nu (k - 2) else 0) := rfl

theorem tailCoeffs_fst_RC (k : ℕ) :
    (tailCoeffs k).1.2.1 = 2 * nu (k - 1) := rfl

theorem tailCoeffs_fst_SS (k : ℕ) :
    (tailCoeffs k).1.2.2 = 1 := rfl

/-- Primitive condition: tail rows are outside P.shape at columns ≥ 1.
    When μQ.colLen 0 ≥ (shiftLeft μP).colLen 0 = μP.colLen 1,
    any tail painting at column 0 has no s/r row conflicts. -/
theorem primitive_tail_rows_outside {μP μQ : YoungDiagram}
    (h_prim : μQ.colLen 0 ≥ (YoungDiagram.shiftLeft μP).colLen 0)
    {i : ℕ} (hi : μQ.colLen 0 ≤ i) {j : ℕ} (hj : 1 ≤ j)
    (τ : PBPSet .D μP μQ) :
    τ.val.P.paint i j = .dot := by
  apply τ.val.P.paint_outside
  rw [τ.prop.2.1, YoungDiagram.mem_iff_lt_colLen]
  rw [YoungDiagram.colLen_shiftLeft] at h_prim
  have hcol := YoungDiagram.colLen_anti μP 1 j (by omega)
  push_neg
  calc μP.colLen j ≤ μP.colLen 1 := hcol
    _ ≤ μQ.colLen 0 := h_prim
    _ ≤ i := hi

/-- Lift painting: column 0 from col0, columns ≥ 1 from σ.P shifted right.

    This is the REVERSE of doubleDescent: given sub-PBP σ and column 0
    painting col0, produce a painting for the "lifted" PBP.
    τ.P.paint(i, 0) = col0(i), τ.P.paint(i, j+1) = σ.P.paint(i, j). -/
def liftPaint_D (σ : PBP) (col0 : ℕ → DRCSymbol) : ℕ → ℕ → DRCSymbol :=
  fun i j => match j with
    | 0 => col0 i
    | j + 1 => σ.P.paint i j

