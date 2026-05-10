import CombUnipotent.ClassicalGroup.Lemmas

/-!
# Explicit standard models for the ClassicalGroup task

The constructions in this file are deliberately elementary.  We use finite
coordinate spaces and write the bilinear forms directly in coordinates, so the
standard-model existence proofs in `Existence.lean` can reduce to concrete
linear algebra calculations.
-/

namespace ClassicalGroup

open scoped BigOperators

noncomputable section

/-! ## Coordinate spaces and elementary Hermitian estimates -/

/-- Coordinate space `ℂ^n`. -/
abbrev Coord (n : ℕ) : Type :=
  Fin n → ℂ

/-- Paired coordinate space `ℂ^n ⊕ ℂ^n`. -/
abbrev PairVec (n : ℕ) : Type :=
  Coord n × Coord n

/-- The coordinate dot product, bilinear over `ℂ`. -/
def dot {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, x i * y i

/-- The standard Hermitian expression `∑ x_i \bar y_i`, kept as a scalar-valued
function rather than a Mathlib Hermitian form. -/
def stdHerm {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, x i * (starRingEnd ℂ) (y i)

theorem dot_zero_left {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    dot (fun _ => 0) x = 0 := by
  simp [dot]

theorem dot_zero_right {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    dot x (fun _ => 0) = 0 := by
  simp [dot]

theorem dot_zero_left' {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    dot (0 : ι → ℂ) x = 0 := by
  simp [dot]

theorem dot_zero_right' {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    dot x (0 : ι → ℂ) = 0 := by
  simp [dot]

theorem dot_comm {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_conj_conj {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    dot (fun i => (starRingEnd ℂ) (x i)) (fun i => (starRingEnd ℂ) (y i)) =
      (starRingEnd ℂ) (dot x y) := by
  unfold dot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [map_mul]

theorem dot_single_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (i : ι) :
    dot x (Pi.single i 1) = x i := by
  unfold dot
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hi
    simp at hi

theorem dot_single_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (i : ι) :
    dot (Pi.single i 1) x = x i := by
  rw [dot_comm, dot_single_right]

theorem stdHerm_symm {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    stdHerm y x = (starRingEnd ℂ) (stdHerm x y) := by
  unfold stdHerm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [map_mul, mul_comm]

theorem stdHerm_self {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    stdHerm x x = ∑ i, (Complex.normSq (x i) : ℂ) := by
  unfold stdHerm
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.mul_conj (x i)

theorem sum_normSq_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    0 ≤ ∑ i, Complex.normSq (x i) := by
  exact Finset.sum_nonneg (by intro i _; exact Complex.normSq_nonneg (x i))

theorem sum_normSq_pos {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : x ≠ 0) :
    0 < ∑ i, Complex.normSq (x i) := by
  have hne : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    exact of_not_not (by exact fun hi => h ⟨i, hi⟩)
  rcases hne with ⟨i, hi⟩
  exact Finset.sum_pos'
    (by intro j _; exact Complex.normSq_nonneg (x j))
    ⟨i, Finset.mem_univ i, (Complex.normSq_pos.mpr hi)⟩

theorem pair_normSq_pos {m n : ℕ} (x : Coord m × Coord n) (hx : x ≠ 0) :
    0 < (∑ i, Complex.normSq (x.1 i)) + ∑ j, Complex.normSq (x.2 j) := by
  have hsplit : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    ext i <;> simp [h.1, h.2]
  rcases hsplit with hfirst | hsecond
  · have hpos := sum_normSq_pos x.1 hfirst
    have hnonneg := sum_normSq_nonneg x.2
    linarith
  · have hnonneg := sum_normSq_nonneg x.1
    have hpos := sum_normSq_pos x.2 hsecond
    linarith

theorem pair_pair_normSq_pos {m n : ℕ} (x : PairVec m × PairVec n) (hx : x ≠ 0) :
    0 < ((∑ i, Complex.normSq (x.1.1 i)) + ∑ i, Complex.normSq (x.1.2 i)) +
        ((∑ j, Complex.normSq (x.2.1 j)) + ∑ j, Complex.normSq (x.2.2 j)) := by
  have hsplit : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    ext i <;> simp [h.1, h.2]
  rcases hsplit with hfirst | hsecond
  · have hpos := pair_normSq_pos x.1 hfirst
    have hnonneg₁ := sum_normSq_nonneg x.2.1
    have hnonneg₂ := sum_normSq_nonneg x.2.2
    linarith
  · have hnonneg₁ := sum_normSq_nonneg x.1.1
    have hnonneg₂ := sum_normSq_nonneg x.1.2
    have hpos := pair_normSq_pos x.2 hsecond
    linarith

/-! ## Bilinear dot-product form -/

/-- The coordinate dot product as a bilinear form. -/
def dotForm {ι : Type*} [Fintype ι] : LinearMap.BilinForm ℂ (ι → ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => dot x y)
    (by
      intro x₁ x₂ y
      simp [dot, Finset.sum_add_distrib, mul_add, mul_comm])
    (by
      intro c x y
      simp [dot, Finset.mul_sum, mul_comm, mul_left_comm])
    (by
      intro x y₁ y₂
      simp [dot, Finset.sum_add_distrib, mul_add])
    (by
      intro c x y
      simp [dot, Finset.mul_sum, mul_left_comm])

theorem dotForm_apply {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    dotForm x y = dot x y :=
  rfl

theorem dotForm_nondegenerate {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (dotForm (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    simpa [dotForm_apply, dot_single_right] using h
  · intro y hy
    ext i
    have h := hy (Pi.single i 1)
    simpa [dotForm_apply, dot_single_left] using h

/-! ## Shared linear maps -/

/-- Coordinatewise complex conjugation, as a conjugate-linear equivalence. -/
def conjPiSemilinearEquiv (ι : Type*) :
    (ι → ℂ) ≃ₛₗ[starRingEnd ℂ] (ι → ℂ) where
  toFun x i := (starRingEnd ℂ) (x i)
  invFun x i := (starRingEnd ℂ) (x i)
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext i; simp
  map_add' := by intro x y; ext i; simp
  map_smul' := by intro c x; ext i; simp [map_mul]

/-- Product conjugation. -/
def pairConjSemilinearEquiv (m n : ℕ) :
    (Coord m × Coord n) ≃ₛₗ[starRingEnd ℂ] (Coord m × Coord n) where
  toFun x := (fun i => (starRingEnd ℂ) (x.1 i), fun j => (starRingEnd ℂ) (x.2 j))
  invFun x := (fun i => (starRingEnd ℂ) (x.1 i), fun j => (starRingEnd ℂ) (x.2 j))
  left_inv := by intro x; ext i <;> simp
  right_inv := by intro x; ext i <;> simp
  map_add' := by intro x y; ext i <;> simp
  map_smul' := by intro c x; ext i <;> simp [map_mul]

/-- The sign involution `(x,y) ↦ (x,-y)` on a product. -/
def prodSignLinearEquiv (P Q : Type*) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] :
    (P × Q) ≃ₗ[ℂ] (P × Q) where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp
    abel
  map_smul' := by intro c x; ext <;> simp

theorem prodSign_plus_second_zero (P Q : Type*) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] (x : P × Q)
    (hx : x ∈ linearEigenspace (prodSignLinearEquiv P Q) 1) :
    x.2 = 0 := by
  rw [linearEigenspace, LinearMap.mem_ker] at hx
  have hL : prodSignLinearEquiv P Q x = (1 : ℂ) • x := sub_eq_zero.mp hx
  have hcomp : -x.2 = x.2 := by
    simpa using congrArg Prod.snd hL
  have htwo : (2 : ℂ) • x.2 = 0 := by
    calc
      (2 : ℂ) • x.2 = x.2 + x.2 := by simp [two_smul]
      _ = -x.2 + x.2 := by rw [hcomp]
      _ = 0 := by simp
  rcases smul_eq_zero.mp htwo with htwo_zero | hx_zero
  · norm_num at htwo_zero
  · exact hx_zero

theorem prodSign_minus_first_zero (P Q : Type*) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] (x : P × Q)
    (hx : x ∈ linearEigenspace (prodSignLinearEquiv P Q) (-1)) :
    x.1 = 0 := by
  rw [linearEigenspace, LinearMap.mem_ker] at hx
  have hL : prodSignLinearEquiv P Q x = (-1 : ℂ) • x := sub_eq_zero.mp hx
  have hcomp : x.1 = -x.1 := by
    simpa using congrArg Prod.fst hL
  have hcomp' : -x.1 = x.1 := by simpa using hcomp.symm
  have htwo : (2 : ℂ) • x.1 = 0 := by
    calc
      (2 : ℂ) • x.1 = x.1 + x.1 := by simp [two_smul]
      _ = -x.1 + x.1 := by rw [hcomp']
      _ = 0 := by simp
  rcases smul_eq_zero.mp htwo with htwo_zero | hx_zero
  · norm_num at htwo_zero
  · exact hx_zero

/-- The `+1` eigenspace of `(x,y) ↦ (x,-y)` is the first factor. -/
def prodSignPlusEigenspaceEquiv (P Q : Type*) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] :
    linearEigenspace (prodSignLinearEquiv P Q) 1 ≃ₗ[ℂ] P where
  toFun x := x.1.1
  invFun p := ⟨(p, 0), by
    rw [linearEigenspace, LinearMap.mem_ker]
    apply sub_eq_zero.mpr
    ext <;> simp [prodSignLinearEquiv]⟩
  left_inv := by
    intro x
    ext
    · rfl
    · exact (prodSign_plus_second_zero P Q x.1 x.2).symm
  right_inv := by intro p; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- The `-1` eigenspace of `(x,y) ↦ (x,-y)` is the second factor. -/
def prodSignMinusEigenspaceEquiv (P Q : Type*) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] :
    linearEigenspace (prodSignLinearEquiv P Q) (-1) ≃ₗ[ℂ] Q where
  toFun x := x.1.2
  invFun q := ⟨(0, q), by
    rw [linearEigenspace, LinearMap.mem_ker]
    apply sub_eq_zero.mpr
    ext <;> simp [prodSignLinearEquiv]⟩
  left_inv := by
    intro x
    ext
    · exact (prodSign_minus_first_zero P Q x.1 x.2).symm
    · rfl
  right_inv := by intro q; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-! ## Orthogonal `B/D` model -/

/-- The model vector space for `B` and `D`: `ℂ^p ⊕ ℂ^q`. -/
abbrev OrthVec (p q : ℕ) : Type :=
  Coord p × Coord q

/-- The symmetric form `dot(x,x') - dot(y,y')`. -/
def orthForm (p q : ℕ) : LinearMap.BilinForm ℂ (OrthVec p q) :=
  (dotForm (ι := Fin p)).comp
      (LinearMap.fst ℂ (Coord p) (Coord q)) (LinearMap.fst ℂ (Coord p) (Coord q)) -
    (dotForm (ι := Fin q)).comp
      (LinearMap.snd ℂ (Coord p) (Coord q)) (LinearMap.snd ℂ (Coord p) (Coord q))

theorem orthForm_apply (p q : ℕ) (x y : OrthVec p q) :
    orthForm p q x y = dot x.1 y.1 - dot x.2 y.2 := by
  simp [orthForm, dotForm_apply]

instance orthFormedSpace (p q : ℕ) : FormedSpace Sign.pos (OrthVec p q) where
  form := orthForm p q
  nondegenerate := by
    constructor
    · intro x hx
      ext i
      · have h := hx (Pi.single i 1, 0)
        simpa [orthForm_apply, dotForm_apply, dot_single_right, dot_zero_right,
          dot_zero_left, dot_zero_right'] using h
      · have h := hx (0, Pi.single i 1)
        have hneg : -x.2 i = 0 := by
          simpa [orthForm_apply, dotForm_apply, dot_single_right, dot_zero_right,
            dot_zero_left, dot_zero_right'] using h
        exact neg_eq_zero.mp hneg
    · intro y hy
      ext i
      · have h := hy (Pi.single i 1, 0)
        simpa [orthForm_apply, dotForm_apply, dot_single_left, dot_zero_left,
          dot_zero_right, dot_zero_left'] using h
      · have h := hy (0, Pi.single i 1)
        have hneg : -y.2 i = 0 := by
          simpa [orthForm_apply, dotForm_apply, dot_single_left, dot_zero_right,
            dot_zero_left, dot_zero_left'] using h
        exact neg_eq_zero.mp hneg
  eps_symm := by
    intro x y
    simp [orthForm_apply, Sign.toComplex_pos, dot_comm y.1 x.1, dot_comm y.2 x.2]

/-- Coordinate conjugation for the orthogonal model. -/
def orthJ (p q : ℕ) : JStructure Sign.pos (OrthVec p q) Sign.pos where
  toSemilinearEquiv := pairConjSemilinearEquiv p q
  sq := by intro v; ext i <;> simp [pairConjSemilinearEquiv, Sign.toComplex_pos]
  preserves_form := by
    intro u v
    change orthForm p q (pairConjSemilinearEquiv p q u)
        (pairConjSemilinearEquiv p q v) = (starRingEnd ℂ) (orthForm p q u v)
    simp [orthForm_apply, pairConjSemilinearEquiv, dot_conj_conj, map_sub]

/-- The Cartan involution `(x,y) ↦ (x,-y)` for the orthogonal model. -/
def orthL (p q : ℕ) : LStructure Sign.pos (OrthVec p q) Sign.pos where
  toLinearEquiv := prodSignLinearEquiv (Coord p) (Coord q)
  sq := by intro v; ext i <;> simp [prodSignLinearEquiv, Sign.toComplex_pos]
  preserves_form := by
    intro u v
    change orthForm p q (prodSignLinearEquiv (Coord p) (Coord q) u)
        (prodSignLinearEquiv (Coord p) (Coord q) v) = orthForm p q u v
    simp [orthForm_apply, prodSignLinearEquiv, dot]

theorem orth_H_apply (p q : ℕ) (u v : OrthVec p q) :
    orthForm p q (orthL p q v) (orthJ p q u) =
      stdHerm v.1 u.1 + stdHerm v.2 u.2 := by
  simp [orthForm_apply, orthL, orthJ, prodSignLinearEquiv, pairConjSemilinearEquiv,
    dot, stdHerm]

theorem orth_positive (p q : ℕ) :
    PositiveDefiniteHermitian Sign.pos (OrthVec p q) (orthJ p q) (orthL p q) := by
  constructor
  · intro u v
    change orthForm p q (orthL p q v) (orthJ p q u) =
      (starRingEnd ℂ) (orthForm p q (orthL p q u) (orthJ p q v))
    rw [orth_H_apply, orth_H_apply]
    rw [map_add, ← stdHerm_symm, ← stdHerm_symm]
  · intro v hv
    change 0 < (orthForm p q (orthL p q v) (orthJ p q v)).re
    rw [orth_H_apply, stdHerm_self, stdHerm_self]
    simp
    exact pair_normSq_pos v hv

theorem orth_compatible (p q : ℕ) : JLCompatible (orthJ p q) (orthL p q) where
  commute := by intro v; ext i <;> simp [orthJ, orthL, pairConjSemilinearEquiv,
    prodSignLinearEquiv]
  cartan_positive := orth_positive p q

theorem orth_finrank (p q : ℕ) :
    Module.finrank ℂ (OrthVec p q) = p + q := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]

theorem orth_LSignature (p q : ℕ) :
    LSignatureCondition ClassicalStar.B p q (OrthVec p q) (orthL p q) := by
  constructor
  · calc
      Module.finrank ℂ (linearEigenspace (orthL p q).toLinearEquiv 1)
          = Module.finrank ℂ (Coord p) :=
            LinearEquiv.finrank_eq (prodSignPlusEigenspaceEquiv (Coord p) (Coord q))
      _ = p := Module.finrank_fin_fun ℂ
  · calc
      Module.finrank ℂ (linearEigenspace (orthL p q).toLinearEquiv (-1))
          = Module.finrank ℂ (Coord q) :=
            LinearEquiv.finrank_eq (prodSignMinusEigenspaceEquiv (Coord p) (Coord q))
      _ = q := Module.finrank_fin_fun ℂ

/-! ## Symplectic `C/Ctilda` model -/

/-- The standard alternating form `dot(z,w') - dot(w,z')` on `ℂ^r ⊕ ℂ^r`. -/
def sympForm (r : ℕ) : LinearMap.BilinForm ℂ (PairVec r) :=
  (dotForm (ι := Fin r)).comp
      (LinearMap.fst ℂ (Coord r) (Coord r)) (LinearMap.snd ℂ (Coord r) (Coord r)) -
    (dotForm (ι := Fin r)).comp
      (LinearMap.snd ℂ (Coord r) (Coord r)) (LinearMap.fst ℂ (Coord r) (Coord r))

theorem sympForm_apply (r : ℕ) (x y : PairVec r) :
    sympForm r x y = dot x.1 y.2 - dot x.2 y.1 := by
  simp [sympForm, dotForm_apply]

instance sympFormedSpace (r : ℕ) : FormedSpace Sign.neg (PairVec r) where
  form := sympForm r
  nondegenerate := by
    constructor
    · intro x hx
      ext i
      · have h := hx (0, Pi.single i 1)
        simpa [sympForm_apply, dotForm_apply, dot_single_right, dot_zero_right,
          dot_zero_left, dot_zero_left', dot_zero_right'] using h
      · have h := hx (Pi.single i 1, 0)
        have hneg : -x.2 i = 0 := by
          simpa [sympForm_apply, dotForm_apply, dot_single_right, dot_single_left,
            dot_zero_right, dot_zero_left, dot_zero_right'] using h
        exact neg_eq_zero.mp hneg
    · intro y hy
      ext i
      · have h := hy (0, Pi.single i 1)
        have hneg : -y.1 i = 0 := by
          simpa [sympForm_apply, dotForm_apply, dot_single_right, dot_single_left,
            dot_zero_right, dot_zero_left, dot_zero_left'] using h
        exact neg_eq_zero.mp hneg
      · have h := hy (Pi.single i 1, 0)
        simpa [sympForm_apply, dotForm_apply, dot_single_left, dot_zero_right,
          dot_zero_left, dot_zero_left', dot_zero_right'] using h
  eps_symm := by
    intro x y
    simp [sympForm_apply, Sign.toComplex_neg, dot_comm y.1 x.2, dot_comm y.2 x.1]

/-- The linear map `(z,w) ↦ (w,-z)`. -/
def rotateLinearEquiv (r : ℕ) : PairVec r ≃ₗ[ℂ] PairVec r where
  toFun x := (x.2, -x.1)
  invFun x := (-x.2, x.1)
  left_inv := by intro x; ext i <;> simp
  right_inv := by intro x; ext i <;> simp
  map_add' := by
    intro x y
    ext i <;> simp
    abel
  map_smul' := by intro c x; ext i <;> simp

/-- Coordinate conjugation in the real symplectic model. -/
def sympRealJ (r : ℕ) : JStructure Sign.neg (PairVec r) Sign.pos where
  toSemilinearEquiv := pairConjSemilinearEquiv r r
  sq := by intro v; ext i <;> simp [pairConjSemilinearEquiv, Sign.toComplex_pos]
  preserves_form := by
    intro u v
    change sympForm r (pairConjSemilinearEquiv r r u)
        (pairConjSemilinearEquiv r r v) = (starRingEnd ℂ) (sympForm r u v)
    simp [sympForm_apply, pairConjSemilinearEquiv, dot_conj_conj, map_sub]

/-- The compatible `L` with square `-1` in the real symplectic model. -/
def sympL (r : ℕ) : LStructure Sign.neg (PairVec r) Sign.neg where
  toLinearEquiv := rotateLinearEquiv r
  sq := by intro v; ext i <;> simp [rotateLinearEquiv, Sign.toComplex_neg]
  preserves_form := by
    intro u v
    change sympForm r (rotateLinearEquiv r u) (rotateLinearEquiv r v) = sympForm r u v
    simp [sympForm_apply, rotateLinearEquiv, dot]
    ring

theorem symp_H_apply (r : ℕ) (u v : PairVec r) :
    sympForm r (sympL r v) (sympRealJ r u) =
      stdHerm v.2 u.2 + stdHerm v.1 u.1 := by
  simp [sympForm_apply, sympL, sympRealJ, rotateLinearEquiv, pairConjSemilinearEquiv,
    dot, stdHerm]

theorem symp_positive (r : ℕ) :
    PositiveDefiniteHermitian Sign.neg (PairVec r) (sympRealJ r) (sympL r) := by
  constructor
  · intro u v
    change sympForm r (sympL r v) (sympRealJ r u) =
      (starRingEnd ℂ) (sympForm r (sympL r u) (sympRealJ r v))
    rw [symp_H_apply, symp_H_apply]
    rw [map_add, ← stdHerm_symm, ← stdHerm_symm]
  · intro v hv
    change 0 < (sympForm r (sympL r v) (sympRealJ r v)).re
    rw [symp_H_apply, stdHerm_self, stdHerm_self]
    simp
    have hpos := pair_normSq_pos (v.2, v.1) (by
      intro hpair
      have h2 : v.2 = 0 := congrArg Prod.fst hpair
      have h1 : v.1 = 0 := congrArg Prod.snd hpair
      apply hv
      ext i
      · simp [h1]
      · simp [h2])
    simpa [add_comm] using hpos

theorem symp_compatible (r : ℕ) : JLCompatible (sympRealJ r) (sympL r) where
  commute := by intro v; ext i <;> simp [sympRealJ, sympL, pairConjSemilinearEquiv,
    rotateLinearEquiv]
  cartan_positive := symp_positive r

theorem symp_finrank (r : ℕ) :
    Module.finrank ℂ (PairVec r) = r + r := by
  simp [PairVec, Coord, Module.finrank_prod]

/-! ## Quaternionic `C*` model -/

/-- The conjugate-linear quaternionic operator `(z,w) ↦ (-\bar w,\bar z)`. -/
def quatJEquiv (r : ℕ) : PairVec r ≃ₛₗ[starRingEnd ℂ] PairVec r where
  toFun x := (fun i => - (starRingEnd ℂ) (x.2 i), fun i => (starRingEnd ℂ) (x.1 i))
  invFun x := (fun i => (starRingEnd ℂ) (x.2 i), fun i => - (starRingEnd ℂ) (x.1 i))
  left_inv := by intro x; ext i <;> simp
  right_inv := by intro x; ext i <;> simp
  map_add' := by
    intro x y
    ext i <;> simp
    abel
  map_smul' := by intro c x; ext i <;> simp [map_mul]

theorem symp_quatJ_preserves (r : ℕ) (u v : PairVec r) :
    sympForm r (quatJEquiv r u) (quatJEquiv r v) =
      (starRingEnd ℂ) (sympForm r u v) := by
  simp [sympForm_apply, quatJEquiv, map_sub, dot]
  ring

theorem symp_quat_H_apply (r : ℕ) (u v : PairVec r) :
    sympForm r v (quatJEquiv r u) = stdHerm v.1 u.1 + stdHerm v.2 u.2 := by
  simp [sympForm_apply, quatJEquiv, dot, stdHerm]

/-- The `C*` model vector space:
`(ℂ^a ⊕ ℂ^a) ⊕ (ℂ^b ⊕ ℂ^b)`. -/
abbrev CstarVec (a b : ℕ) : Type :=
  PairVec a × PairVec b

/-- The alternating form with opposite signs on the two quaternionic blocks. -/
def cstarForm (a b : ℕ) : LinearMap.BilinForm ℂ (CstarVec a b) :=
  (sympForm a).comp
      (LinearMap.fst ℂ (PairVec a) (PairVec b)) (LinearMap.fst ℂ (PairVec a) (PairVec b)) -
    (sympForm b).comp
      (LinearMap.snd ℂ (PairVec a) (PairVec b)) (LinearMap.snd ℂ (PairVec a) (PairVec b))

theorem cstarForm_apply (a b : ℕ) (x y : CstarVec a b) :
    cstarForm a b x y = sympForm a x.1 y.1 - sympForm b x.2 y.2 := by
  simp [cstarForm]

instance cstarFormedSpace (a b : ℕ) : FormedSpace Sign.neg (CstarVec a b) where
  form := cstarForm a b
  nondegenerate := by
    constructor
    · intro x hx
      have hx₁ : x.1 = 0 := by
        exact (FormedSpace.nondegenerate (eps := Sign.neg) (V := PairVec a)).1 x.1 (by
          intro y
          have h := hx (y, 0)
          simpa [cstarForm_apply] using h)
      have hx₂ : x.2 = 0 := by
        exact (FormedSpace.nondegenerate (eps := Sign.neg) (V := PairVec b)).1 x.2 (by
          intro y
          have h := hx (0, y)
          have hneg : -sympForm b x.2 y = 0 := by
            simpa [cstarForm_apply] using h
          exact neg_eq_zero.mp hneg)
      exact Prod.ext hx₁ hx₂
    · intro y hy
      have hy₁ : y.1 = 0 := by
        exact (FormedSpace.nondegenerate (eps := Sign.neg) (V := PairVec a)).2 y.1 (by
          intro x
          have h := hy (x, 0)
          simpa [cstarForm_apply] using h)
      have hy₂ : y.2 = 0 := by
        exact (FormedSpace.nondegenerate (eps := Sign.neg) (V := PairVec b)).2 y.2 (by
          intro x
          have h := hy (0, x)
          have hneg : -sympForm b x y.2 = 0 := by
            simpa [cstarForm_apply] using h
          exact neg_eq_zero.mp hneg)
      exact Prod.ext hy₁ hy₂
  eps_symm := by
    intro x y
    simp [cstarForm_apply, sympForm_apply, Sign.toComplex_neg, dot_comm y.1.1 x.1.2,
      dot_comm y.1.2 x.1.1, dot_comm y.2.1 x.2.2, dot_comm y.2.2 x.2.1]
    ring_nf

/-- Product quaternionic semilinear equivalence for the `C*` model. -/
def cstarJSemilinearEquiv (a b : ℕ) : CstarVec a b ≃ₛₗ[starRingEnd ℂ] CstarVec a b where
  toFun x := (quatJEquiv a x.1, quatJEquiv b x.2)
  invFun x := ((quatJEquiv a).symm x.1, (quatJEquiv b).symm x.2)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  map_add' := by intro x y; ext <;> simp
  map_smul' := by intro c x; ext <;> simp [map_smulₛₗ]

/-- Product quaternionic `J` for the `C*` model. -/
def cstarJ (a b : ℕ) : JStructure Sign.neg (CstarVec a b) Sign.neg where
  toSemilinearEquiv := cstarJSemilinearEquiv a b
  sq := by
    intro v
    ext i <;> simp [cstarJSemilinearEquiv, quatJEquiv, Sign.toComplex_neg]
  preserves_form := by
    intro u v
    change cstarForm a b ((quatJEquiv a u.1), (quatJEquiv b u.2))
        ((quatJEquiv a v.1), (quatJEquiv b v.2)) =
      (starRingEnd ℂ) (cstarForm a b u v)
    rw [cstarForm_apply, cstarForm_apply, symp_quatJ_preserves,
      symp_quatJ_preserves, map_sub]

/-- The involution `+1` on the first quaternionic block and `-1` on the second. -/
def cstarL (a b : ℕ) : LStructure Sign.neg (CstarVec a b) Sign.pos where
  toLinearEquiv := prodSignLinearEquiv (PairVec a) (PairVec b)
  sq := by intro v; ext <;> simp [prodSignLinearEquiv, Sign.toComplex_pos]
  preserves_form := by
    intro u v
    change cstarForm a b (prodSignLinearEquiv (PairVec a) (PairVec b) u)
        (prodSignLinearEquiv (PairVec a) (PairVec b) v) = cstarForm a b u v
    simp [cstarForm_apply, prodSignLinearEquiv, sympForm_apply, dot]
    ring

theorem cstar_H_apply (a b : ℕ) (u v : CstarVec a b) :
    cstarForm a b (cstarL a b v) (cstarJ a b u) =
      (stdHerm v.1.1 u.1.1 + stdHerm v.1.2 u.1.2) +
        (stdHerm v.2.1 u.2.1 + stdHerm v.2.2 u.2.2) := by
  simp [cstarForm_apply, cstarL, cstarJ, cstarJSemilinearEquiv, prodSignLinearEquiv,
    quatJEquiv, sympForm_apply, dot, stdHerm]
  ring

theorem cstar_positive (a b : ℕ) :
    PositiveDefiniteHermitian Sign.neg (CstarVec a b) (cstarJ a b) (cstarL a b) := by
  constructor
  · intro u v
    change cstarForm a b (cstarL a b v) (cstarJ a b u) =
      (starRingEnd ℂ) (cstarForm a b (cstarL a b u) (cstarJ a b v))
    rw [cstar_H_apply, cstar_H_apply]
    repeat rw [map_add]
    repeat rw [← stdHerm_symm]
  · intro v hv
    change 0 < (cstarForm a b (cstarL a b v) (cstarJ a b v)).re
    rw [cstar_H_apply]
    repeat rw [stdHerm_self]
    simp
    exact pair_pair_normSq_pos v hv

theorem cstar_compatible (a b : ℕ) : JLCompatible (cstarJ a b) (cstarL a b) where
  commute := by intro v; ext i <;>
    simp [cstarJ, cstarL, cstarJSemilinearEquiv, prodSignLinearEquiv, quatJEquiv]
  cartan_positive := cstar_positive a b

theorem cstar_finrank (a b : ℕ) :
    Module.finrank ℂ (CstarVec a b) = 2 * a + 2 * b := by
  rw [Module.finrank_prod, symp_finrank, symp_finrank]
  omega

theorem cstar_LSignature (a b : ℕ) :
    LSignatureCondition ClassicalStar.Cstar (2 * a) (2 * b) (CstarVec a b) (cstarL a b) := by
  constructor
  · calc
      Module.finrank ℂ (linearEigenspace (cstarL a b).toLinearEquiv 1)
          = Module.finrank ℂ (PairVec a) :=
            LinearEquiv.finrank_eq (prodSignPlusEigenspaceEquiv (PairVec a) (PairVec b))
      _ = a + a := symp_finrank a
      _ = 2 * a := by omega
  · calc
      Module.finrank ℂ (linearEigenspace (cstarL a b).toLinearEquiv (-1))
          = Module.finrank ℂ (PairVec b) :=
            LinearEquiv.finrank_eq (prodSignMinusEigenspaceEquiv (PairVec a) (PairVec b))
      _ = b + b := symp_finrank b
      _ = 2 * b := by omega

/-! ## Quaternionic `D*` model -/

/-- The symmetric form `-i (dot(z,w') + dot(w,z'))`. -/
def dstarForm (r : ℕ) : LinearMap.BilinForm ℂ (PairVec r) :=
  (-Complex.I) •
    ((dotForm (ι := Fin r)).comp
        (LinearMap.fst ℂ (Coord r) (Coord r)) (LinearMap.snd ℂ (Coord r) (Coord r)) +
      (dotForm (ι := Fin r)).comp
        (LinearMap.snd ℂ (Coord r) (Coord r)) (LinearMap.fst ℂ (Coord r) (Coord r)))

theorem dstarForm_apply (r : ℕ) (x y : PairVec r) :
    dstarForm r x y = (-Complex.I) * (dot x.1 y.2 + dot x.2 y.1) := by
  simp [dstarForm, dotForm, dot]
  ring

theorem neg_I_ne_zero : (-Complex.I : ℂ) ≠ 0 := by
  exact neg_ne_zero.mpr Complex.I_ne_zero

instance dstarFormedSpace (r : ℕ) : FormedSpace Sign.pos (PairVec r) where
  form := dstarForm r
  nondegenerate := by
    constructor
    · intro x hx
      ext i
      · have h := hx (0, Pi.single i 1)
        have hmul : (-Complex.I) * x.1 i = 0 := by
          simpa [dstarForm_apply, dotForm_apply, dot_single_right, dot_zero_right,
            dot_zero_left, dot_zero_left', dot_zero_right'] using h
        rcases mul_eq_zero.mp hmul with hI | hx0
        · exact False.elim (neg_I_ne_zero hI)
        · exact hx0
      · have h := hx (Pi.single i 1, 0)
        have hmul : (-Complex.I) * x.2 i = 0 := by
          simpa [dstarForm_apply, dotForm_apply, dot_single_right, dot_single_left,
            dot_zero_right, dot_zero_left, dot_zero_right'] using h
        rcases mul_eq_zero.mp hmul with hI | hx0
        · exact False.elim (neg_I_ne_zero hI)
        · exact hx0
    · intro y hy
      ext i
      · have h := hy (0, Pi.single i 1)
        have hmul : (-Complex.I) * y.1 i = 0 := by
          simpa [dstarForm_apply, dotForm_apply, dot_single_right, dot_single_left,
            dot_zero_right, dot_zero_left, dot_zero_left'] using h
        rcases mul_eq_zero.mp hmul with hI | hy0
        · exact False.elim (neg_I_ne_zero hI)
        · exact hy0
      · have h := hy (Pi.single i 1, 0)
        have hmul : (-Complex.I) * y.2 i = 0 := by
          simpa [dstarForm_apply, dotForm_apply, dot_single_left, dot_zero_right,
            dot_zero_left, dot_zero_left', dot_zero_right'] using h
        rcases mul_eq_zero.mp hmul with hI | hy0
        · exact False.elim (neg_I_ne_zero hI)
        · exact hy0
  eps_symm := by
    intro x y
    simp [dstarForm_apply, Sign.toComplex_pos, dot_comm y.1 x.2, dot_comm y.2 x.1]
    ring_nf

/-- The linear map `(z,w) ↦ (i z,-i w)`. -/
def iLinearEquiv (r : ℕ) : PairVec r ≃ₗ[ℂ] PairVec r where
  toFun x := (fun i => Complex.I * x.1 i, fun i => -Complex.I * x.2 i)
  invFun x := (fun i => -Complex.I * x.1 i, fun i => Complex.I * x.2 i)
  left_inv := by
    intro x
    ext i <;> simp
    all_goals
      rw [← mul_assoc, Complex.I_mul_I]
      simp
  right_inv := by
    intro x
    ext i <;> simp
    all_goals
      rw [← mul_assoc, Complex.I_mul_I]
      simp
  map_add' := by intro x y; ext i <;> simp [mul_add]
  map_smul' := by intro c x; ext i <;> simp [Pi.smul_apply] <;> ring

/-- Quaternionic `J` for the `D*` model. -/
def dstarJ (r : ℕ) : JStructure Sign.pos (PairVec r) Sign.neg where
  toSemilinearEquiv := quatJEquiv r
  sq := by intro v; ext i <;> simp [quatJEquiv, Sign.toComplex_neg]
  preserves_form := by
    intro u v
    change dstarForm r (quatJEquiv r u) (quatJEquiv r v) =
      (starRingEnd ℂ) (dstarForm r u v)
    simp [dstarForm_apply, quatJEquiv, dot, map_add, map_mul]
    ring

/-- The compatible `L` with square `-1` for the `D*` model. -/
def dstarL (r : ℕ) : LStructure Sign.pos (PairVec r) Sign.neg where
  toLinearEquiv := iLinearEquiv r
  sq := by
    intro v
    ext i <;> simp [iLinearEquiv, Sign.toComplex_neg]
    all_goals
      rw [← mul_assoc, Complex.I_mul_I]
      simp
  preserves_form := by
    intro u v
    change dstarForm r (iLinearEquiv r u) (iLinearEquiv r v) = dstarForm r u v
    simp [dstarForm_apply, iLinearEquiv, dot]
    ring_nf
    simp

theorem dstar_H_apply (r : ℕ) (u v : PairVec r) :
    dstarForm r (dstarL r v) (dstarJ r u) =
      stdHerm v.1 u.1 + stdHerm v.2 u.2 := by
  simp [dstarForm_apply, dstarL, dstarJ, iLinearEquiv, quatJEquiv, dot, stdHerm]
  simp [mul_add, Finset.mul_sum, ← mul_assoc, Complex.I_mul_I]
  ring

theorem dstar_positive (r : ℕ) :
    PositiveDefiniteHermitian Sign.pos (PairVec r) (dstarJ r) (dstarL r) := by
  constructor
  · intro u v
    change dstarForm r (dstarL r v) (dstarJ r u) =
      (starRingEnd ℂ) (dstarForm r (dstarL r u) (dstarJ r v))
    rw [dstar_H_apply, dstar_H_apply]
    rw [map_add, ← stdHerm_symm, ← stdHerm_symm]
  · intro v hv
    change 0 < (dstarForm r (dstarL r v) (dstarJ r v)).re
    rw [dstar_H_apply, stdHerm_self, stdHerm_self]
    simp
    exact pair_normSq_pos v hv

theorem dstar_compatible (r : ℕ) : JLCompatible (dstarJ r) (dstarL r) where
  commute := by intro v; ext i <;> simp [dstarJ, dstarL, iLinearEquiv, quatJEquiv,
    map_mul]
  cartan_positive := dstar_positive r

end

end ClassicalGroup
