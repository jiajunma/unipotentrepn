/-
# Counting Proof: HSeq/GSeq/TSeq and ValidCol0 counting

Extracted from the monolithic `CountingProof.lean`.
-/
import CombUnipotent.CountingProof.Lift

open Classical

/-! ### Recursive counting: HSeq / GSeq / TSeq

Three nested subtypes of finite monotone sequences:
- `HSeq k`: length-k sequences in {s, r}, layerOrd-monotone.
- `GSeq k`: length-k sequences in {s, r, c}, monotone, at most one `c`.
- `TSeq k`: length-k sequences in {s, r, c, d}, monotone, ≤1 `c`, ≤1 `d`.

Each layer peels off the last element and splits 2-way, giving:
- `|HSeq k| = k + 1`
- `|GSeq k| = 2k + 1`
- `|TSeq k| = 4k` (for k ≥ 1)
-/

/-- Length-k sequences in {s, r}, monotone by layerOrd. -/
def HSeq (k : ℕ) : Type :=
  { v : Fin k → DRCSymbol //
    (∀ i, v i = .s ∨ v i = .r) ∧
    (∀ i j : Fin k, i.val ≤ j.val → (v i).layerOrd ≤ (v j).layerOrd) }

/-- Length-k sequences in {s, r, c}, monotone, at most one `c`. -/
def GSeq (k : ℕ) : Type :=
  { v : Fin k → DRCSymbol //
    (∀ i, v i = .s ∨ v i = .r ∨ v i = .c) ∧
    (∀ i j : Fin k, i.val ≤ j.val → (v i).layerOrd ≤ (v j).layerOrd) ∧
    (∀ i j : Fin k, v i = .c → v j = .c → i = j) }

/-- Length-k sequences in {s, r, c, d}, monotone, ≤1 `c`, ≤1 `d`. -/
def TSeq (k : ℕ) : Type :=
  { v : Fin k → DRCSymbol //
    (∀ i, v i = .s ∨ v i = .r ∨ v i = .c ∨ v i = .d) ∧
    (∀ i j : Fin k, i.val ≤ j.val → (v i).layerOrd ≤ (v j).layerOrd) ∧
    (∀ i j : Fin k, v i = .c → v j = .c → i = j) ∧
    (∀ i j : Fin k, v i = .d → v j = .d → i = j) }

instance (k : ℕ) : Fintype (HSeq k) := by unfold HSeq; infer_instance
instance (k : ℕ) : Fintype (GSeq k) := by unfold GSeq; infer_instance
instance (k : ℕ) : Fintype (TSeq k) := by unfold TSeq; infer_instance

/-! #### Helpers: truncation and append -/

/-- Drop the last entry of a `Fin (k+1) → X` sequence. -/
def truncLast {X : Type*} {k : ℕ} (v : Fin (k + 1) → X) : Fin k → X :=
  fun i => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- Append an element to the end of a `Fin k → X` sequence. -/
def snocLast {X : Type*} {k : ℕ} (v : Fin k → X) (x : X) : Fin (k + 1) → X :=
  fun i => if h : i.val < k then v ⟨i.val, h⟩ else x

lemma truncLast_snocLast {X : Type*} {k : ℕ} (v : Fin k → X) (x : X) :
    truncLast (snocLast v x) = v := by
  funext i
  simp [truncLast, snocLast, i.isLt]

lemma snocLast_last {X : Type*} {k : ℕ} (v : Fin k → X) (x : X) :
    snocLast v x ⟨k, Nat.lt_succ_self k⟩ = x := by
  simp [snocLast]

lemma snocLast_lt {X : Type*} {k : ℕ} (v : Fin k → X) (x : X) (i : Fin (k + 1))
    (hi : i.val < k) : snocLast v x i = v ⟨i.val, hi⟩ := by
  simp [snocLast, hi]

lemma snocLast_truncLast {X : Type*} {k : ℕ} (v : Fin (k + 1) → X)
    (hlast : v ⟨k, Nat.lt_succ_self k⟩ = v ⟨k, Nat.lt_succ_self k⟩) :
    snocLast (truncLast v) (v ⟨k, Nat.lt_succ_self k⟩) = v := by
  funext i
  by_cases h : i.val < k
  · simp [snocLast, truncLast, h]
  · simp [snocLast, h]
    have : i.val = k := by omega
    congr 1
    exact Fin.ext this.symm

/-! #### HSeq equivalence: peel last symbol -/

/-- Last-element extraction map for `HSeq (k+1)`. -/
noncomputable def HSeq_equiv_succ (k : ℕ) : HSeq (k + 1) ≃ Unit ⊕ HSeq k where
  toFun v :=
    if h : v.val ⟨k, Nat.lt_succ_self k⟩ = .s then Sum.inl ()
    else Sum.inr ⟨truncLast v.val, by
      refine ⟨fun i => v.property.1 _, fun i j hij => v.property.2 _ _ hij⟩⟩
  invFun x :=
    match x with
    | Sum.inl _ => ⟨fun _ => .s, by
        refine ⟨fun _ => Or.inl rfl, fun _ _ _ => ?_⟩
        simp [DRCSymbol.layerOrd]⟩
    | Sum.inr w => ⟨snocLast w.val .r, by
        refine ⟨?_, ?_⟩
        · intro i
          by_cases hi : i.val < k
          · rw [snocLast_lt _ _ _ hi]; exact w.property.1 _
          · right
            have : i.val = k := by omega
            simp [snocLast, this]
        · intro i j hij
          by_cases hj : j.val < k
          · have hi : i.val < k := by omega
            rw [snocLast_lt _ _ _ hi, snocLast_lt _ _ _ hj]
            exact w.property.2 _ _ hij
          · rw [show snocLast w.val .r j = .r by
              have : j.val = k := by omega
              simp [snocLast, this]]
            by_cases hi : i.val < k
            · rw [snocLast_lt _ _ _ hi]
              rcases w.property.1 ⟨i.val, hi⟩ with h | h <;>
                simp [h, DRCSymbol.layerOrd]
            · have : i.val = k := by omega
              simp [snocLast, this, DRCSymbol.layerOrd]⟩
  left_inv v := by
    by_cases hlast : v.val ⟨k, Nat.lt_succ_self k⟩ = .s
    · simp only [hlast, dite_true]
      apply Subtype.ext
      funext i
      have hile : i.val ≤ k := by have := i.isLt; omega
      have hmono := v.property.2 i ⟨k, Nat.lt_succ_self k⟩ hile
      rw [hlast] at hmono
      rcases v.property.1 i with h | h
      · rw [h]
      · exfalso
        rw [h, DRCSymbol.layerOrd] at hmono
        simp [DRCSymbol.layerOrd] at hmono
    · simp only [hlast, dite_false]
      apply Subtype.ext
      funext i
      by_cases hi : i.val < k
      · simp [snocLast, truncLast, hi]
      · have heq : i.val = k := by have := i.isLt; omega
        have hlast_r : v.val ⟨k, Nat.lt_succ_self k⟩ = .r := by
          rcases v.property.1 ⟨k, Nat.lt_succ_self k⟩ with h | h
          · exact absurd h hlast
          · exact h
        have heqi : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
        rw [heqi, hlast_r]
        simp [snocLast]
  right_inv x := by
    rcases x with u | w
    · rfl
    · dsimp only
      have hlast_ne : snocLast w.val .r ⟨k, Nat.lt_succ_self k⟩ ≠ .s := by
        simp [snocLast]
      rw [dif_neg hlast_ne]
      apply congrArg Sum.inr
      apply Subtype.ext
      funext i
      simp [truncLast, snocLast, i.isLt]

theorem HSeq_card (k : ℕ) : Fintype.card (HSeq k) = k + 1 := by
  induction k with
  | zero =>
    -- HSeq 0: unique empty function
    have : Fintype.card (HSeq 0) = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨fun i => Fin.elim0 i, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩, ?_⟩
      intro v
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    omega
  | succ k ih =>
    rw [Fintype.card_congr (HSeq_equiv_succ k)]
    simp [Fintype.card_sum, ih]
    omega

/-! #### GSeq equivalence: peel last symbol -/

/-- `GSeq (k+1)` splits as "last ∈ {s,r}" (whole seq is HSeq (k+1))
    and "last = c" (prefix is HSeq k). -/
noncomputable def GSeq_equiv_succ (k : ℕ) : GSeq (k + 1) ≃ HSeq (k + 1) ⊕ HSeq k where
  toFun v :=
    if h : v.val ⟨k, Nat.lt_succ_self k⟩ = .c then
      Sum.inr ⟨truncLast v.val, by
        refine ⟨fun i => ?_, fun i j hij => v.property.2.1 _ _ hij⟩
        rcases v.property.1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hs | hr | hc
        · left; exact hs
        · right; exact hr
        · exfalso
          have := v.property.2.2 ⟨i.val, _⟩ ⟨k, Nat.lt_succ_self k⟩ hc h
          have : i.val = k := Fin.mk.inj_iff.mp this
          omega⟩
    else
      Sum.inl ⟨v.val, by
        refine ⟨fun i => ?_, fun i j hij => v.property.2.1 _ _ hij⟩
        rcases v.property.1 i with hs | hr | hc
        · left; exact hs
        · right; exact hr
        · exfalso
          apply h
          have hile : i.val ≤ k := by have := i.isLt; omega
          have hmono := v.property.2.1 i ⟨k, Nat.lt_succ_self k⟩ hile
          rw [hc, DRCSymbol.layerOrd] at hmono
          rcases v.property.1 ⟨k, Nat.lt_succ_self k⟩ with hs' | hr' | hc'
          · rw [hs', DRCSymbol.layerOrd] at hmono; omega
          · rw [hr', DRCSymbol.layerOrd] at hmono; omega
          · exact hc'⟩
  invFun x :=
    match x with
    | Sum.inl w => ⟨w.val, by
        refine ⟨fun i => ?_, fun i j hij => w.property.2 _ _ hij, ?_⟩
        · rcases w.property.1 i with h | h
          · left; exact h
          · right; left; exact h
        · intro i j hi hj
          exfalso
          rcases w.property.1 i with h | h <;> rw [h] at hi <;>
            exact DRCSymbol.noConfusion hi⟩
    | Sum.inr w => ⟨snocLast w.val .c, by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          by_cases hi : i.val < k
          · rw [snocLast_lt _ _ _ hi]
            rcases w.property.1 ⟨i.val, hi⟩ with h | h
            · left; exact h
            · right; left; exact h
          · right; right
            have : i.val = k := by omega
            simp [snocLast, this]
        · intro i j hij
          by_cases hj : j.val < k
          · have hi : i.val < k := by omega
            rw [snocLast_lt _ _ _ hi, snocLast_lt _ _ _ hj]
            exact w.property.2 _ _ hij
          · have hj' : j.val = k := by omega
            rw [show snocLast w.val .c j = .c by simp [snocLast, hj']]
            by_cases hi : i.val < k
            · rw [snocLast_lt _ _ _ hi]
              rcases w.property.1 ⟨i.val, hi⟩ with h | h <;>
                simp [h, DRCSymbol.layerOrd]
            · have : i.val = k := by omega
              simp [snocLast, this, DRCSymbol.layerOrd]
        · intro i j hi hj
          by_cases hi' : i.val < k
          · exfalso
            rw [snocLast_lt _ _ _ hi'] at hi
            rcases w.property.1 ⟨i.val, hi'⟩ with h | h <;>
              rw [h] at hi <;> exact DRCSymbol.noConfusion hi
          · by_cases hj' : j.val < k
            · exfalso
              rw [snocLast_lt _ _ _ hj'] at hj
              rcases w.property.1 ⟨j.val, hj'⟩ with h | h <;>
                rw [h] at hj <;> exact DRCSymbol.noConfusion hj
            · have hi_eq : i.val = k := by omega
              have hj_eq : j.val = k := by omega
              exact Fin.ext (hi_eq.trans hj_eq.symm)⟩
  left_inv v := by
    by_cases hlast : v.val ⟨k, Nat.lt_succ_self k⟩ = .c
    · simp only [hlast, dite_true]
      apply Subtype.ext
      funext i
      by_cases hi : i.val < k
      · simp [snocLast, truncLast, hi]
      · have heq : i.val = k := by have := i.isLt; omega
        have hvi : v.val i = .c := by
          have heqi : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
          rw [heqi]; exact hlast
        rw [hvi]
        simp [snocLast, heq]
    · simp only [hlast, dite_false]
      rfl
  right_inv x := by
    rcases x with w | w
    · have hlast_ne : w.val ⟨k, Nat.lt_succ_self k⟩ ≠ .c := by
        rcases w.property.1 ⟨k, Nat.lt_succ_self k⟩ with h | h <;>
          rw [h] <;> decide
      simp only [hlast_ne, dite_false]
      rfl
    · have hlast_c : snocLast w.val .c ⟨k, Nat.lt_succ_self k⟩ = .c := by
        simp [snocLast]
      simp only [hlast_c, dite_true]
      apply congrArg Sum.inr
      apply Subtype.ext
      funext i
      simp [truncLast, snocLast, i.isLt]

theorem GSeq_card (k : ℕ) : Fintype.card (GSeq k) = 2 * k + 1 := by
  induction k with
  | zero =>
    have : Fintype.card (GSeq 0) = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨fun i => Fin.elim0 i,
        ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩, ?_⟩
      intro v
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    omega
  | succ k ih =>
    rw [Fintype.card_congr (GSeq_equiv_succ k)]
    simp [Fintype.card_sum, HSeq_card]
    omega

/-! #### TSeq equivalence: peel last symbol -/

/-- `TSeq (k+1)` splits as "last ∈ {s,r,c}" (whole seq is GSeq (k+1))
    and "last = d" (prefix is GSeq k). -/
noncomputable def TSeq_equiv_succ (k : ℕ) : TSeq (k + 1) ≃ GSeq (k + 1) ⊕ GSeq k where
  toFun v :=
    if h : v.val ⟨k, Nat.lt_succ_self k⟩ = .d then
      Sum.inr ⟨truncLast v.val, by
        refine ⟨fun i => ?_,
                fun i j hij => v.property.2.1 _ _ hij,
                fun i j hi hj => ?_⟩
        · rcases v.property.1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hs | hr | hc | hd
          · left; exact hs
          · right; left; exact hr
          · right; right; exact hc
          · exfalso
            have := v.property.2.2.2 ⟨i.val, _⟩ ⟨k, Nat.lt_succ_self k⟩ hd h
            have : i.val = k := Fin.mk.inj_iff.mp this
            omega
        · have := v.property.2.2.1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
                    ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hi hj
          exact Fin.ext (Fin.mk.inj_iff.mp this)⟩
    else
      Sum.inl ⟨v.val, by
        refine ⟨fun i => ?_,
                fun i j hij => v.property.2.1 _ _ hij,
                fun i j hi hj => v.property.2.2.1 _ _ hi hj⟩
        rcases v.property.1 i with hs | hr | hc | hd
        · left; exact hs
        · right; left; exact hr
        · right; right; exact hc
        · exfalso
          apply h
          have hile : i.val ≤ k := by have := i.isLt; omega
          have hmono := v.property.2.1 i ⟨k, Nat.lt_succ_self k⟩ hile
          rw [hd, DRCSymbol.layerOrd] at hmono
          rcases v.property.1 ⟨k, Nat.lt_succ_self k⟩ with hs' | hr' | hc' | hd'
          · rw [hs', DRCSymbol.layerOrd] at hmono; omega
          · rw [hr', DRCSymbol.layerOrd] at hmono; omega
          · rw [hc', DRCSymbol.layerOrd] at hmono; omega
          · exact hd'⟩
  invFun x :=
    match x with
    | Sum.inl w => ⟨w.val, by
        refine ⟨fun i => ?_,
                fun i j hij => w.property.2.1 _ _ hij,
                fun i j hi hj => w.property.2.2 _ _ hi hj, ?_⟩
        · rcases w.property.1 i with h | h | h
          · left; exact h
          · right; left; exact h
          · right; right; left; exact h
        · intro i j hi hj
          exfalso
          rcases w.property.1 i with h | h | h <;>
            rw [h] at hi <;> exact DRCSymbol.noConfusion hi⟩
    | Sum.inr w => ⟨snocLast w.val .d, by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          by_cases hi : i.val < k
          · rw [snocLast_lt _ _ _ hi]
            rcases w.property.1 ⟨i.val, hi⟩ with h | h | h
            · left; exact h
            · right; left; exact h
            · right; right; left; exact h
          · right; right; right
            have : i.val = k := by have := i.isLt; omega
            simp [snocLast, this]
        · intro i j hij
          by_cases hj : j.val < k
          · have hi : i.val < k := by omega
            rw [snocLast_lt _ _ _ hi, snocLast_lt _ _ _ hj]
            exact w.property.2.1 _ _ hij
          · have hj' : j.val = k := by have := j.isLt; omega
            rw [show snocLast w.val .d j = .d by simp [snocLast, hj']]
            by_cases hi : i.val < k
            · rw [snocLast_lt _ _ _ hi]
              rcases w.property.1 ⟨i.val, hi⟩ with h | h | h <;>
                simp [h, DRCSymbol.layerOrd]
            · have : i.val = k := by have := i.isLt; omega
              simp [snocLast, this, DRCSymbol.layerOrd]
        · intro i j hi hj
          by_cases hi' : i.val < k
          · by_cases hj' : j.val < k
            · rw [snocLast_lt _ _ _ hi'] at hi
              rw [snocLast_lt _ _ _ hj'] at hj
              have := w.property.2.2 _ _ hi hj
              exact Fin.ext (Fin.mk.inj_iff.mp this)
            · exfalso
              have hj_eq : j.val = k := by have := j.isLt; omega
              rw [show snocLast w.val .d j = .d by simp [snocLast, hj_eq]] at hj
              exact DRCSymbol.noConfusion hj
          · by_cases hj' : j.val < k
            · exfalso
              have hi_eq : i.val = k := by have := i.isLt; omega
              rw [show snocLast w.val .d i = .d by simp [snocLast, hi_eq]] at hi
              exact DRCSymbol.noConfusion hi
            · have hi_eq : i.val = k := by have := i.isLt; omega
              have hj_eq : j.val = k := by have := j.isLt; omega
              exact Fin.ext (hi_eq.trans hj_eq.symm)
        · intro i j hi hj
          by_cases hi' : i.val < k
          · exfalso
            rw [snocLast_lt _ _ _ hi'] at hi
            rcases w.property.1 ⟨i.val, hi'⟩ with h | h | h <;>
              rw [h] at hi <;> exact DRCSymbol.noConfusion hi
          · by_cases hj' : j.val < k
            · exfalso
              rw [snocLast_lt _ _ _ hj'] at hj
              rcases w.property.1 ⟨j.val, hj'⟩ with h | h | h <;>
                rw [h] at hj <;> exact DRCSymbol.noConfusion hj
            · have hi_eq : i.val = k := by have := i.isLt; omega
              have hj_eq : j.val = k := by have := j.isLt; omega
              exact Fin.ext (hi_eq.trans hj_eq.symm)⟩
  left_inv v := by
    by_cases hlast : v.val ⟨k, Nat.lt_succ_self k⟩ = .d
    · simp only [hlast, dite_true]
      apply Subtype.ext
      funext i
      by_cases hi : i.val < k
      · simp [snocLast, truncLast, hi]
      · have heq : i.val = k := by have := i.isLt; omega
        have hvi : v.val i = .d := by
          have heqi : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
          rw [heqi]; exact hlast
        rw [hvi]
        simp [snocLast, heq]
    · simp only [hlast, dite_false]
      rfl
  right_inv x := by
    rcases x with w | w
    · have hlast_ne : w.val ⟨k, Nat.lt_succ_self k⟩ ≠ .d := by
        rcases w.property.1 ⟨k, Nat.lt_succ_self k⟩ with h | h | h <;>
          rw [h] <;> decide
      simp only [hlast_ne, dite_false]
      rfl
    · have hlast_d : snocLast w.val .d ⟨k, Nat.lt_succ_self k⟩ = .d := by
        simp [snocLast]
      simp only [hlast_d, dite_true]
      apply congrArg Sum.inr
      apply Subtype.ext
      funext i
      simp [truncLast, snocLast, i.isLt]

theorem TSeq_card (k : ℕ) (hk : 1 ≤ k) : Fintype.card (TSeq k) = 4 * k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Fintype.card_congr (TSeq_equiv_succ k)]
    simp [Fintype.card_sum, GSeq_card]
    omega

/-! #### Bridge: `ValidCol0 ≃ TSeq k` -/

/-- Structure extensionality for `ValidCol0`: equal paints ⇒ equal structures. -/
lemma ValidCol0.ext {μP μQ : YoungDiagram} {v₁ v₂ : ValidCol0 μP μQ}
    (h : v₁.paint = v₂.paint) : v₁ = v₂ := by
  cases v₁; cases v₂; simp_all

/-- Forward direction: restrict `ValidCol0` paint to `Fin k` (the tail window). -/
noncomputable def ValidCol0.toTSeq {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) (v : ValidCol0 μP μQ) :
    TSeq (μP.colLen 0 - μQ.colLen 0) := by
  refine ⟨fun i => v.paint (μQ.colLen 0 + i.val), ?mem, ?mono, ?uc, ?ud⟩
  case mem =>
    intro i
    show v.paint (μQ.colLen 0 + i.val) = .s ∨ v.paint (μQ.colLen 0 + i.val) = .r
         ∨ v.paint (μQ.colLen 0 + i.val) = .c ∨ v.paint (μQ.colLen 0 + i.val) = .d
    have hlt : μQ.colLen 0 + i.val < μP.colLen 0 := by have := i.isLt; omega
    have hne := v.nondot_tail (μQ.colLen 0 + i.val) (by omega) hlt
    generalize hsym : v.paint (μQ.colLen 0 + i.val) = sym at hne ⊢
    cases sym
    · exact absurd rfl hne
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  case mono =>
    intro i j hij
    have hlt : μQ.colLen 0 + j.val < μP.colLen 0 := by have := j.isLt; omega
    exact v.mono _ _ (by omega) hlt
  case uc =>
    intro i j hi hj
    have := v.col_c_unique _ _ hi hj
    exact Fin.ext (by omega)
  case ud =>
    intro i j hi hj
    have := v.col_d_unique _ _ hi hj
    exact Fin.ext (by omega)

/-- Backward direction: extend a `TSeq k` with dots outside `[b, c)`. -/
noncomputable def ValidCol0.ofTSeq {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (w : TSeq (μP.colLen 0 - μQ.colLen 0)) : ValidCol0 μP μQ where
  paint i :=
    if hlt : μQ.colLen 0 ≤ i ∧ i < μP.colLen 0 then
      w.val ⟨i - μQ.colLen 0, by omega⟩
    else .dot
  dot_below i hi := by
    have : ¬(μQ.colLen 0 ≤ i ∧ i < μP.colLen 0) := by omega
    simp [this]
  nondot_tail i h1 h2 := by
    have hpos : μQ.colLen 0 ≤ i ∧ i < μP.colLen 0 := ⟨h1, h2⟩
    rw [dif_pos hpos]
    have hmem := w.property.1 ⟨i - μQ.colLen 0, by omega⟩
    rcases hmem with h | h | h | h <;> rw [h] <;> decide
  dot_above i hi := by
    have : ¬(μQ.colLen 0 ≤ i ∧ i < μP.colLen 0) := by omega
    simp [this]
  mono i₁ i₂ h12 h2 := by
    by_cases h1 : μQ.colLen 0 ≤ i₁
    · have h1' : μQ.colLen 0 ≤ i₁ ∧ i₁ < μP.colLen 0 := ⟨h1, by omega⟩
      have h2' : μQ.colLen 0 ≤ i₂ ∧ i₂ < μP.colLen 0 := ⟨by omega, h2⟩
      rw [dif_pos h1', dif_pos h2']
      exact w.property.2.1 _ _ (by simp; omega)
    · have h1' : ¬(μQ.colLen 0 ≤ i₁ ∧ i₁ < μP.colLen 0) := by
        push_neg; intro h; exact absurd h h1
      rw [dif_neg h1']
      simp [DRCSymbol.layerOrd]
  col_c_unique i₁ i₂ hc1 hc2 := by
    by_cases h1 : μQ.colLen 0 ≤ i₁ ∧ i₁ < μP.colLen 0
    · by_cases h2 : μQ.colLen 0 ≤ i₂ ∧ i₂ < μP.colLen 0
      · rw [dif_pos h1] at hc1
        rw [dif_pos h2] at hc2
        have := w.property.2.2.1 _ _ hc1 hc2
        have heq : i₁ - μQ.colLen 0 = i₂ - μQ.colLen 0 := Fin.mk.inj_iff.mp this
        omega
      · rw [dif_neg h2] at hc2; exact DRCSymbol.noConfusion hc2
    · rw [dif_neg h1] at hc1; exact DRCSymbol.noConfusion hc1
  col_d_unique i₁ i₂ hd1 hd2 := by
    by_cases h1 : μQ.colLen 0 ≤ i₁ ∧ i₁ < μP.colLen 0
    · by_cases h2 : μQ.colLen 0 ≤ i₂ ∧ i₂ < μP.colLen 0
      · rw [dif_pos h1] at hd1
        rw [dif_pos h2] at hd2
        have := w.property.2.2.2 _ _ hd1 hd2
        have heq : i₁ - μQ.colLen 0 = i₂ - μQ.colLen 0 := Fin.mk.inj_iff.mp this
        omega
      · rw [dif_neg h2] at hd2; exact DRCSymbol.noConfusion hd2
    · rw [dif_neg h1] at hd1; exact DRCSymbol.noConfusion hd1

/-- The Equiv between `ValidCol0 μP μQ` and `TSeq (μP.colLen 0 - μQ.colLen 0)`. -/
noncomputable def ValidCol0.equivTSeq {μP μQ : YoungDiagram}
    (hQP : μQ.colLen 0 ≤ μP.colLen 0) :
    ValidCol0 μP μQ ≃ TSeq (μP.colLen 0 - μQ.colLen 0) where
  toFun := ValidCol0.toTSeq hQP
  invFun := ValidCol0.ofTSeq hQP
  left_inv v := by
    apply ValidCol0.ext
    funext i
    by_cases h : μQ.colLen 0 ≤ i ∧ i < μP.colLen 0
    · show (ValidCol0.ofTSeq hQP _).paint i = v.paint i
      show (if _ : _ then _ else _) = v.paint i
      rw [dif_pos h]
      show v.paint (μQ.colLen 0 + (i - μQ.colLen 0)) = v.paint i
      congr 1; omega
    · show (ValidCol0.ofTSeq hQP _).paint i = v.paint i
      show (if _ : _ then _ else _) = v.paint i
      rw [dif_neg h]
      push_neg at h
      by_cases h1 : i < μQ.colLen 0
      · exact (v.dot_below i h1).symm
      · exact (v.dot_above i (h (by omega))).symm
  right_inv w := by
    apply Subtype.ext
    funext i
    have hi : μQ.colLen 0 + i.val < μP.colLen 0 := by have := i.isLt; omega
    have hpos : μQ.colLen 0 ≤ μQ.colLen 0 + i.val ∧ μQ.colLen 0 + i.val < μP.colLen 0 :=
      ⟨by omega, hi⟩
    show (ValidCol0.ofTSeq hQP w).paint (μQ.colLen 0 + i.val) = w.val i
    show (if _ : _ then _ else _) = w.val i
    rw [dif_pos hpos]
    have heq : (⟨μQ.colLen 0 + i.val - μQ.colLen 0, by omega⟩ : Fin _) = i :=
      Fin.ext (by simp)
    rw [heq]

/-- The number of valid column 0 paintings equals the tailCoeffs sum.
    Proof: `ValidCol0 ≃ TSeq k` and `|TSeq k| = 4k`. -/
theorem validCol0_card {μP μQ : YoungDiagram}
    (k : ℕ) (hk : k = μP.colLen 0 - μQ.colLen 0)
    (hQP : μQ.colLen 0 ≤ μP.colLen 0)
    (hk_pos : 1 ≤ k) :
    Fintype.card (ValidCol0 μP μQ) =
      (tailCoeffs k).1.1 + (tailCoeffs k).1.2.1 + (tailCoeffs k).1.2.2 := by
  rw [tailCoeffs_total k hk_pos]
  rw [Fintype.card_congr (ValidCol0.equivTSeq hQP)]
  subst hk
  exact TSeq_card _ hk_pos

