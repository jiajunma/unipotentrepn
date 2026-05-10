import CombUnipotent.ClassicalGroup.Basic

/-!
# Lemma statements for the ClassicalGroup task

This file records the reusable theorems that the construction and uniqueness
proofs need.  Each nontrivial statement carries the blueprint argument as a
source comment when the proof is conceptually tied to the paper proof.
-/

namespace ClassicalGroup

universe u

/-! ## Basic destructors for `IsClassicalSpace` -/

/-- Extract the signature condition from a classical-space proof. -/
theorem isClassicalSpace_signature {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    IsClassicalSignature star p q :=
  h.1

/-- Extract the complex-dimension condition from a classical-space proof. -/
theorem isClassicalSpace_finrank {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    Module.finrank ℂ V = p + q :=
  h.2.1

/-- Extract the paired compatibility condition from a classical-space proof. -/
theorem isClassicalSpace_compatible {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    JLCompatible J L :=
  h.2.2.1

/-- Extract the `L`-signature/eigenspace condition from a classical-space proof. -/
theorem isClassicalSpace_LSignature {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    LSignatureCondition star p q V L :=
  h.2.2.2

/-- Extract the commutation relation `LJ = JL`. -/
theorem isClassicalSpace_commute {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    ∀ v : V, L (J v) = J (L v) :=
  (isClassicalSpace_compatible h).commute

/-- Extract positivity of the Cartan Hermitian form. -/
theorem isClassicalSpace_cartan_positive {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    PositiveDefiniteHermitian star.eps V J L :=
  (isClassicalSpace_compatible h).cartan_positive

/-! ## Real forms fixed by a conjugate-linear operator -/

/-- The real subspace fixed by a conjugate-linear operator `J`.

This is the Lean interface for the blueprint notation `V_R = V^J`.  It is an
`ℝ`-submodule, not a complex submodule: closure under real scalars uses that
complex conjugation fixes real numbers. -/
def JFixedRealSubmodule {eps : Sign}
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign} (J : JStructure eps V jSign) :
    Submodule ℝ V where
  carrier := {v : V | J v = v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change J (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change J ((r : ℂ) • x) = (r : ℂ) • x
    rw [J.toSemilinearEquiv.map_smulₛₗ, hx]
    simp

theorem mem_JFixedRealSubmodule {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign} (J : JStructure eps V jSign) (v : V) :
    v ∈ JFixedRealSubmodule V J ↔ J v = v :=
  Iff.rfl

/-- If `J` and `L` commute, then `L` preserves the real form `V^J`. -/
theorem L_mem_JFixedRealSubmodule_of_commute {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ JFixedRealSubmodule V J) :
    L v ∈ JFixedRealSubmodule V J := by
  change J (L v) = L v
  rw [← hJL.commute v, hv]

/-- On `J`-fixed vectors, the complex bilinear form is fixed by complex conjugation.

For `J^2=1` this says that the restriction of the form to `V^J` is real-valued,
which is the first step in the `B/D` and `C/Ctilda` normal-form arguments. -/
theorem form_star_eq_of_mem_JFixedRealSubmodule {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign} (J : JStructure eps V jSign)
    {u v : V} (hu : u ∈ JFixedRealSubmodule V J)
    (hv : v ∈ JFixedRealSubmodule V J) :
    (starRingEnd ℂ) (FormedSpace.B eps V u v) = FormedSpace.B eps V u v := by
  have h := J.preserves_form u v
  rw [hu, hv] at h
  exact h.symm

/-- Complex conjugation fixes `1/2`. -/
theorem star_half : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
  rw [map_div₀]
  simp only [map_one, map_ofNat]

/-- Complex conjugation sends `-i/2` to `i/2`. -/
theorem star_neg_I_div_two :
    (starRingEnd ℂ) ((-Complex.I / 2 : ℂ)) = (Complex.I / 2 : ℂ) := by
  rw [map_div₀]
  simp only [map_neg, map_ofNat]
  simp

/-- A complex number fixed by conjugation is determined by its real part. -/
theorem complex_eq_of_star_eq_of_re_eq {z : ℂ} {r : ℝ}
    (hz : (starRingEnd ℂ) z = z) (hre : z.re = r) : z = (r : ℂ) := by
  apply Complex.ext
  · simp [hre]
  · have him : z.im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      simpa using hz
    simp [him]

/-- The scalar identity `i(-i/2)=1/2`. -/
theorem I_mul_neg_I_div_two : Complex.I * (-Complex.I / 2 : ℂ) = (1 / 2 : ℂ) := by
  calc
    Complex.I * (-Complex.I / 2 : ℂ) = -(Complex.I * Complex.I) * (2⁻¹ : ℂ) := by
      ring
    _ = -(-1 : ℂ) * (2⁻¹ : ℂ) := by rw [Complex.I_mul_I]
    _ = (1 / 2 : ℂ) := by norm_num [div_eq_mul_inv]

/-- Real part of a vector with respect to a conjugation `J` with `J²=1`. -/
noncomputable def JFixedRealPart {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (v : V) : V :=
  ((1 / 2 : ℂ) : ℂ) • (v + J v)

/-- Imaginary part of a vector with respect to a conjugation `J` with `J²=1`.

With this convention, `v = JFixedRealPart J v + i • JFixedImagPart J v`. -/
noncomputable def JFixedImagPart {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (v : V) : V :=
  ((-Complex.I / 2 : ℂ) : ℂ) • (v - J v)

/-- The `J`-real part is fixed by `J`. -/
theorem JFixedRealPart_mem {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (v : V) :
    JFixedRealPart J v ∈ JFixedRealSubmodule V J := by
  change J (JFixedRealPart J v) = JFixedRealPart J v
  rw [JFixedRealPart, J.toSemilinearEquiv.map_smulₛₗ, star_half, map_add, J.sq v]
  simp only [Sign.toComplex_pos, one_smul]
  module

/-- The `J`-imaginary part is fixed by `J`. -/
theorem JFixedImagPart_mem {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (v : V) :
    JFixedImagPart J v ∈ JFixedRealSubmodule V J := by
  change J (JFixedImagPart J v) = JFixedImagPart J v
  rw [JFixedImagPart, J.toSemilinearEquiv.map_smulₛₗ, star_neg_I_div_two, map_sub, J.sq v]
  simp only [Sign.toComplex_pos, one_smul]
  module

/-- Every vector decomposes as real part plus `i` times imaginary part. -/
theorem JFixed_real_add_i_smul_imag {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (v : V) :
    JFixedRealPart J v + Complex.I • JFixedImagPart J v = v := by
  simp only [JFixedRealPart, JFixedImagPart, smul_add, smul_sub, smul_smul]
  simp only [I_mul_neg_I_div_two]
  module

/-! ### Complexification of a `J`-stable subspace

The following package is the Lean version of the blueprint fact that a
`J² = 1` conjugation identifies any `J`-stable complex subspace with the
complexification of its fixed real part.  It is used in the `B/D` and
`C/Ctilda` normal-form construction to convert complex eigenspace dimensions
into dimensions of real fixed eigenspaces. -/

/-- Fixed real part of a `J`-stable complex subspace, as a real subspace of the
subtype `S`. -/
noncomputable def JFixedSubmoduleIn {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (S : Submodule ℂ V) :
    Submodule ℝ S where
  carrier := {x : S | J x.1 = x.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change J (x.1 + y.1) = x.1 + y.1
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change J ((r : ℂ) • x.1) = (r : ℂ) • x.1
    rw [J.toSemilinearEquiv.map_smulₛₗ, hx]
    simp

theorem mem_JFixedSubmoduleIn {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (S : Submodule ℂ V) (x : S) :
    x ∈ JFixedSubmoduleIn J S ↔ J x.1 = x.1 :=
  Iff.rfl

/-- A `J`-stable complex subspace is the complexification of its fixed real
subspace.  The equivalence sends `(x,y)` to `x + i y`; its inverse is given by
the `J`-real and `J`-imaginary projections. -/
noncomputable def JFixedComplexificationEquiv {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (S : Submodule ℂ V)
    (hS : ∀ {v : V}, v ∈ S → J v ∈ S) :
    (JFixedSubmoduleIn J S × JFixedSubmoduleIn J S) ≃ₗ[ℝ] S where
  toFun xy :=
    ⟨xy.1.1.1 + Complex.I • xy.2.1.1,
      S.add_mem xy.1.1.2 (S.smul_mem Complex.I xy.2.1.2)⟩
  invFun x :=
    (⟨⟨JFixedRealPart J x.1,
        S.smul_mem (1 / 2 : ℂ) (S.add_mem x.2 (hS x.2))⟩,
        JFixedRealPart_mem J x.1⟩,
      ⟨⟨JFixedImagPart J x.1,
        S.smul_mem (-Complex.I / 2 : ℂ) (S.sub_mem x.2 (hS x.2))⟩,
        JFixedImagPart_mem J x.1⟩)
  left_inv := by
    intro xy
    rcases xy with ⟨x, y⟩
    ext
    · simp only [JFixedRealPart]
      have hxJ : J x.1.1 = x.1.1 := x.2
      have hyJ : J y.1.1 = y.1.1 := y.2
      rw [map_add, J.toSemilinearEquiv.map_smulₛₗ, hxJ, hyJ]
      simp
      module
    · simp only [JFixedImagPart]
      have hxJ : J x.1.1 = x.1.1 := x.2
      have hyJ : J y.1.1 = y.1.1 := y.2
      rw [map_add, J.toSemilinearEquiv.map_smulₛₗ, hxJ, hyJ]
      simp
      rw [← add_smul, smul_smul]
      have hcoef : ((-Complex.I / 2 + -Complex.I / 2 : ℂ) * Complex.I) = 1 := by
        calc
          ((-Complex.I / 2 + -Complex.I / 2 : ℂ) * Complex.I) =
              -Complex.I * Complex.I := by
            ring
          _ = 1 := by simp [Complex.I_mul_I]
      rw [hcoef]
      simp
  right_inv := by
    intro x
    ext
    exact JFixed_real_add_i_smul_imag J x.1
  map_add' := by
    intro xy zw
    ext
    simp [add_assoc, add_left_comm]
  map_smul' := by
    intro r xy
    ext
    simp [smul_add]
    rw [smul_comm]

/-- The fixed real subspace of a `J`-stable complex subspace has real dimension
equal to the complex dimension of the original subspace. -/
theorem finrank_JFixedSubmoduleIn_eq_complex {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (J : JStructure eps V Sign.pos) (S : Submodule ℂ V)
    (hS : ∀ {v : V}, v ∈ S → J v ∈ S) :
    Module.finrank ℝ (JFixedSubmoduleIn J S) = Module.finrank ℂ S := by
  let F := JFixedSubmoduleIn J S
  have hlin := (JFixedComplexificationEquiv J S hS).finrank_eq
  change Module.finrank ℝ (F × F) = Module.finrank ℝ S at hlin
  rw [Module.finrank_prod, finrank_real_of_complex S] at hlin
  change Module.finrank ℝ F = Module.finrank ℂ S
  omega

/-! ## The Cartan Hermitian form as an inner-product core -/

/-- The Cartan positive Hermitian form as a Mathlib inner-product core.

Mathlib's convention is conjugate-linear in the first variable and linear in the
second.  Since the paper's Hermitian form is
`H(u,v)=B(Lu,Jv)`, which is linear in `u` and conjugate-linear in `v`, we use
`inner x y = H(y,x)=B(Ly,Jx)`. -/
noncomputable def cartanInnerCore {eps : Sign}
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hH : PositiveDefiniteHermitian eps V J L) :
    InnerProductSpace.Core ℂ V where
  inner x y := FormedSpace.B eps V (L y) (J x)
  conj_inner_symm := by
    intro x y
    exact (hH.1 x y).symm
  re_inner_nonneg := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · exact le_of_lt (hH.2 x hx)
  add_left := by
    intro x y z
    simp [map_add]
  smul_left := by
    intro x y r
    change FormedSpace.B eps V (L y) (J (r • x)) =
      (starRingEnd ℂ) r * FormedSpace.B eps V (L y) (J x)
    rw [J.toSemilinearEquiv.map_smulₛₗ]
    simp
  definite := by
    intro x hxzero
    by_contra hx
    have hpos := hH.2 x hx
    rw [hxzero] at hpos
    simp at hpos

/-! ## The `±1` projections for an involutive `L` -/

/-- The `+1` projection for a linear involution `L`. -/
noncomputable def LPlusPart {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) (v : V) : V :=
  ((1 / 2 : ℂ) : ℂ) • (v + L v)

/-- The `-1` projection for a linear involution `L`. -/
noncomputable def LMinusPart {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) (v : V) : V :=
  ((1 / 2 : ℂ) : ℂ) • (v - L v)

/-- The `+1` projection lands in the `+1` eigenspace. -/
theorem LPlusPart_mem_eig_one {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) (v : V) :
    LPlusPart L v ∈ linearEigenspace L.toLinearEquiv 1 := by
  rw [linearEigenspace, LinearMap.mem_ker]
  apply sub_eq_zero.mpr
  rw [LPlusPart]
  change L (((1 / 2 : ℂ) : ℂ) • (v + L v)) = (1 : ℂ) •
    (((1 / 2 : ℂ) : ℂ) • (v + L v))
  rw [map_smul, map_add, L.sq v]
  simp only [Sign.toComplex_pos, one_smul]
  module

/-- The `-1` projection lands in the `-1` eigenspace. -/
theorem LMinusPart_mem_eig_neg_one {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) (v : V) :
    LMinusPart L v ∈ linearEigenspace L.toLinearEquiv (-1) := by
  rw [linearEigenspace, LinearMap.mem_ker]
  apply sub_eq_zero.mpr
  rw [LMinusPart]
  change L (((1 / 2 : ℂ) : ℂ) • (v - L v)) = (-1 : ℂ) •
    (((1 / 2 : ℂ) : ℂ) • (v - L v))
  rw [map_smul, map_sub, L.sq v]
  simp only [Sign.toComplex_pos, one_smul]
  module

/-- The `+1` and `-1` projections add back to the original vector. -/
theorem LPlusPart_add_LMinusPart {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) (v : V) :
    LPlusPart L v + LMinusPart L v = v := by
  simp only [LPlusPart, LMinusPart, smul_add, smul_sub]
  module

theorem mem_linearEigenspace_iff_apply_eq {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (L : LStructure eps V lSign) {a : ℂ} {v : V} :
    v ∈ linearEigenspace L.toLinearEquiv a ↔ L v = a • v := by
  rw [linearEigenspace, LinearMap.mem_ker]
  exact sub_eq_zero

theorem linearEigenspace_apply_eq {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (L : LStructure eps V lSign) {a : ℂ} {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    L v = a • v :=
  (mem_linearEigenspace_iff_apply_eq L).mp hv

theorem linearEigenspace_one_neg_one_disjoint {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) :
    Disjoint (linearEigenspace L.toLinearEquiv 1)
      (linearEigenspace L.toLinearEquiv (-1)) := by
  rw [Submodule.disjoint_def]
  intro x hx hxn
  have hxL : L x = x := by simpa using linearEigenspace_apply_eq L hx
  have hxnL : L x = -x := by simpa using linearEigenspace_apply_eq L hxn
  have htwo : (2 : ℂ) • x = 0 := by
    calc
      (2 : ℂ) • x = x + x := by simp [two_smul]
      _ = x + -x := by rw [← hxnL, hxL]
      _ = 0 := by simp
  rcases smul_eq_zero.mp htwo with htwo_zero | hx_zero
  · norm_num at htwo_zero
  · exact hx_zero

theorem linearEigenspace_one_neg_one_sup_eq_top {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) :
    linearEigenspace L.toLinearEquiv 1 ⊔ linearEigenspace L.toLinearEquiv (-1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  exact ⟨LPlusPart L v, LPlusPart_mem_eig_one L v,
    LMinusPart L v, LMinusPart_mem_eig_neg_one L v, LPlusPart_add_LMinusPart L v⟩

theorem linearEigenspace_one_neg_one_isCompl {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (L : LStructure eps V Sign.pos) :
    IsCompl (linearEigenspace L.toLinearEquiv 1)
      (linearEigenspace L.toLinearEquiv (-1)) := by
  exact IsCompl.of_eq
    (linearEigenspace_one_neg_one_disjoint L).eq_bot
    (linearEigenspace_one_neg_one_sup_eq_top L)

/-- If `v` is `J`-fixed and `J,L` commute, then the `+1` projection is `J`-fixed. -/
theorem LPlusPart_mem_JFixedRealSubmodule {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.pos)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ JFixedRealSubmodule V J) :
    LPlusPart L v ∈ JFixedRealSubmodule V J := by
  change J (LPlusPart L v) = LPlusPart L v
  rw [LPlusPart, J.toSemilinearEquiv.map_smulₛₗ, star_half, map_add, hv]
  have hLv : J (L v) = L v := by
    rw [← hJL.commute v, hv]
  rw [hLv]

/-- If `v` is `J`-fixed and `J,L` commute, then the `-1` projection is `J`-fixed. -/
theorem LMinusPart_mem_JFixedRealSubmodule {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.pos)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ JFixedRealSubmodule V J) :
    LMinusPart L v ∈ JFixedRealSubmodule V J := by
  change J (LMinusPart L v) = LMinusPart L v
  rw [LMinusPart, J.toSemilinearEquiv.map_smulₛₗ, star_half, map_sub, hv]
  have hLv : J (L v) = L v := by
    rw [← hJL.commute v, hv]
  rw [hLv]

/-! ## Eigenspace lemmas needed by the blueprint -/

/-- `J` sends an `L`-eigenvector of eigenvalue `a` to an `L`-eigenvector of
conjugate eigenvalue `star a`, assuming `LJ = JL`.

Blueprint proof: if `L v = a v`, then
`L (J v) = J (L v) = J (a v) = star a • J v`, using conjugate-linearity of
`J`. -/
theorem linearEigenspace_J_mem_conj {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ} {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    J v ∈ linearEigenspace L.toLinearEquiv ((starRingEnd ℂ) a) := by
  rw [linearEigenspace, LinearMap.mem_ker] at hv ⊢
  have hvL : L v = a • v := by
    simpa using (sub_eq_zero.mp hv)
  apply sub_eq_zero.mpr
  calc
    L (J v) = J (L v) := hJL.commute v
    _ = J (a • v) := by rw [hvL]
    _ = ((starRingEnd ℂ) a) • J v := by
      simpa using J.toSemilinearEquiv.map_smulₛₗ a v

/-- If the eigenvalue is fixed by complex conjugation, then the corresponding
`L`-eigenspace is `J`-stable. -/
theorem linearEigenspace_J_mem_of_star_eq {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ}
    (ha : (starRingEnd ℂ) a = a) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    J v ∈ linearEigenspace L.toLinearEquiv a := by
  simpa [ha] using linearEigenspace_J_mem_conj J L hJL hv

/-- For `J²=1`, a real-eigenvalue `L`-eigenspace has fixed-real dimension
equal to its complex dimension. -/
theorem finrank_JFixed_linearEigenspace_eq_complex {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (J : JStructure eps V Sign.pos) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ} (ha : (starRingEnd ℂ) a = a) :
    Module.finrank ℝ (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv a)) =
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv a) := by
  exact finrank_JFixedSubmoduleIn_eq_complex J (linearEigenspace L.toLinearEquiv a)
    (fun hv => linearEigenspace_J_mem_of_star_eq J L hJL ha hv)

/-- If `v` lies in an `L`-eigenspace with real eigenvalue, then its `J`-real part
lies in the same eigenspace. -/
theorem JFixedRealPart_mem_linearEigenspace {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (J : JStructure eps V Sign.pos) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ}
    (ha : (starRingEnd ℂ) a = a) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    JFixedRealPart J v ∈ linearEigenspace L.toLinearEquiv a := by
  exact Submodule.smul_mem _ _ <|
    Submodule.add_mem _ hv (linearEigenspace_J_mem_of_star_eq J L hJL ha hv)

/-- If `v` lies in an `L`-eigenspace with real eigenvalue, then its `J`-imaginary
part lies in the same eigenspace. -/
theorem JFixedImagPart_mem_linearEigenspace {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (J : JStructure eps V Sign.pos) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ}
    (ha : (starRingEnd ℂ) a = a) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    JFixedImagPart J v ∈ linearEigenspace L.toLinearEquiv a := by
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ hv (linearEigenspace_J_mem_of_star_eq J L hJL ha hv)

/-- In the `dotε = -1` cases, `J` maps the `i`-eigenspace of `L` into the
`-i`-eigenspace. -/
theorem linearEigenspace_J_mem_i_to_neg_i {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv Complex.I) :
    J v ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
  simpa using linearEigenspace_J_mem_conj J L hJL hv

/-- In the `dotε = -1` cases, `J` maps the `-i`-eigenspace of `L` into the
`i`-eigenspace. -/
theorem linearEigenspace_J_mem_neg_i_to_i {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv (-Complex.I)) :
    J v ∈ linearEigenspace L.toLinearEquiv Complex.I := by
  simpa using linearEigenspace_J_mem_conj J L hJL hv

/-- A conjugate-semilinear equivalence preserves complex finite dimension.

This general helper is used for the `dotε = -1` eigenspace-dimension theorem.
The proof transports a basis through the semilinear equivalence; linear
independence and spanning are preserved because complex conjugation is a
surjective ring endomorphism. -/
theorem finrank_eq_of_star_semilinearEquiv
    {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    [AddCommGroup N] [Module ℂ N] [Module.Finite ℂ N]
    (e : M ≃ₛₗ[starRingEnd ℂ] N) :
    Module.finrank ℂ M = Module.finrank ℂ N := by
  classical
  let b := Module.finBasis ℂ M
  let f : Fin (Module.finrank ℂ M) → N := fun i => e (b i)
  have hli : LinearIndependent ℂ f := by
    dsimp [f]
    exact b.linearIndependent.map_of_surjective_injectiveₛ (starRingEnd ℂ)
      e.toAddEquiv.toAddMonoidHom (RingHom.surjective (starRingEnd ℂ))
      (EquivLike.injective e) (by intro r m; simpa using e.map_smulₛₗ r m)
  have hsp_eq : Submodule.span ℂ (Set.range f) = ⊤ := by
    have hrange : Set.range f = (e : M →ₛₗ[starRingEnd ℂ] N) '' Set.range b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange]
    rw [← Submodule.map_span (e : M →ₛₗ[starRingEnd ℂ] N)]
    rw [b.span_eq]
    simp [Submodule.map_top]
  let bN : Module.Basis (Fin (Module.finrank ℂ M)) ℂ N :=
    Module.Basis.mk hli (by rw [hsp_eq])
  calc
    Module.finrank ℂ M = Fintype.card (Fin (Module.finrank ℂ M)) := by simp
    _ = Module.finrank ℂ N := (Module.finrank_eq_card_basis bN).symm


/-- When `L² = -1`, the `i` and `-i` eigenspaces have equal complex dimension,
provided `J` and `L` are compatible.

This is a theorem, not part of the definition of `LStructure`: the equality uses
conjugate-linearity of `J`, bijectivity of `J`, and `LJ = JL`.  The proof should
restrict `J` to an anti-linear equivalence between the two eigenspaces and then
convert that anti-linear equivalence into equality of complex dimensions. -/
theorem eig_i_finrank_eq_eig_neg_i_finrank {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) :
    Module.finrank ℂ (linearEigenspace L.toLinearEquiv Complex.I) =
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-Complex.I)) := by
  let Ei := linearEigenspace L.toLinearEquiv Complex.I
  let En := linearEigenspace L.toLinearEquiv (-Complex.I)
  have hmap : Ei.map (J.toSemilinearEquiv : V →ₛₗ[starRingEnd ℂ] V) = En := by
    subst Ei
    subst En
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact linearEigenspace_J_mem_i_to_neg_i J L hJL hx
    · intro hy
      let x : V := J.toSemilinearEquiv.symm y
      have hJx : J x = y := by simp [x]
      have hyL : L y = (-Complex.I) • y := by
        rw [linearEigenspace, LinearMap.mem_ker] at hy
        simpa using (sub_eq_zero.mp hy)
      have hxL : L x = Complex.I • x := by
        apply J.toSemilinearEquiv.injective
        calc
          J (L x) = L (J x) := (hJL.commute x).symm
          _ = L y := by rw [hJx]
          _ = (-Complex.I) • y := hyL
          _ = (-Complex.I) • J x := by rw [hJx]
          _ = J (Complex.I • x) := by
            symm
            simpa using J.toSemilinearEquiv.map_smulₛₗ Complex.I x
      have hx : x ∈ linearEigenspace L.toLinearEquiv Complex.I := by
        rw [linearEigenspace, LinearMap.mem_ker]
        exact sub_eq_zero.mpr hxL
      exact ⟨x, hx, hJx⟩
  exact finrank_eq_of_star_semilinearEquiv
    (J.toSemilinearEquiv.ofSubmodules Ei En hmap)

/-- Distinct `L`-eigenspaces are orthogonal for the bilinear form whenever the
product of eigenvalues is not `1`.

Blueprint proof: if `L u = a u` and `L v = b v`, then form preservation gives
`B(u,v)=B(Lu,Lv)=a*b*B(u,v)`.  If `a*b ≠ 1`, then `B(u,v)=0`. -/
theorem L_eigenspaces_form_orthogonal {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (L : LStructure eps V lSign) {a b : ℂ} (hab : a * b ≠ 1)
    {u v : V} (hu : u ∈ linearEigenspace L.toLinearEquiv a)
    (hv : v ∈ linearEigenspace L.toLinearEquiv b) :
    FormedSpace.B eps V u v = 0 := by
  rw [linearEigenspace, LinearMap.mem_ker] at hu hv
  have huL : L u = a • u := by
    simpa using (sub_eq_zero.mp hu)
  have hvL : L v = b • v := by
    simpa using (sub_eq_zero.mp hv)
  have hmul : FormedSpace.B eps V u v = (a * b) * FormedSpace.B eps V u v := by
    calc
      FormedSpace.B eps V u v = FormedSpace.B eps V (L u) (L v) :=
        (L.preserves_form u v).symm
      _ = FormedSpace.B eps V (a • u) (b • v) := by rw [huL, hvL]
      _ = (a * b) * FormedSpace.B eps V u v := by simp [mul_assoc, mul_left_comm]
  have hcoeff : (1 - a * b) ≠ 0 := by
    intro hzero
    apply hab
    exact (sub_eq_zero.mp hzero).symm
  have hzero : (1 - a * b) * FormedSpace.B eps V u v = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp hzero).resolve_left hcoeff

/-- A subspace is totally isotropic for the formed-space bilinear form. -/
def FormTotallyIsotropic (eps : Sign)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (S : Submodule ℂ V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, FormedSpace.B eps V u v = 0

/-! ## Case-specific intermediate theorem statements -/

/-- In the `B,D` cases, the `+1` and `-1` eigenspaces of `L` are orthogonal. -/
theorem BD_plus_minus_orthogonal
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.pos)
    {u v : V} (hu : u ∈ linearEigenspace L.toLinearEquiv 1)
    (hv : v ∈ linearEigenspace L.toLinearEquiv (-1)) :
    FormedSpace.B Sign.pos V u v = 0 := by
  exact L_eigenspaces_form_orthogonal L (by norm_num : (1 : ℂ) * (-1) ≠ 1) hu hv

/-- In the `B,D` cases, the bilinear form is positive on `J`-fixed `L=+1`
vectors, as a consequence of Cartan positivity. -/
theorem BD_form_re_pos_of_Jfixed_mem_plus
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hJL : JLCompatible J L)
    {v : V} (hvJ : v ∈ JFixedRealSubmodule V J)
    (hvL : v ∈ linearEigenspace L.toLinearEquiv 1)
    (hvne : v ≠ 0) :
    0 < (FormedSpace.B Sign.pos V v v).re := by
  rw [linearEigenspace, LinearMap.mem_ker] at hvL
  have hLv : L v = (1 : ℂ) • v := by
    simpa using sub_eq_zero.mp hvL
  have hJv : J v = v := hvJ
  have hpos := hJL.cartan_positive.2 v hvne
  simpa [hLv, hJv] using hpos

/-- In the `B,D` cases, the negative of the bilinear form is positive on
`J`-fixed `L=-1` vectors, as a consequence of Cartan positivity. -/
theorem BD_neg_form_re_pos_of_Jfixed_mem_minus
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hJL : JLCompatible J L)
    {v : V} (hvJ : v ∈ JFixedRealSubmodule V J)
    (hvL : v ∈ linearEigenspace L.toLinearEquiv (-1))
    (hvne : v ≠ 0) :
    0 < (-(FormedSpace.B Sign.pos V v v)).re := by
  rw [linearEigenspace, LinearMap.mem_ker] at hvL
  have hLv : L v = (-1 : ℂ) • v := by
    simpa using sub_eq_zero.mp hvL
  have hJv : J v = v := hvJ
  have hpos := hJL.cartan_positive.2 v hvne
  simpa [hLv, hJv] using hpos

/-- In the `C*` case, the `+1` eigenspace of `L` is stable under `J`. -/
theorem Cstar_J_stable_plus (a b : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (h : @IsClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) V _ _ _
      ‹FormedSpace Sign.neg V› J L)
    {v : V} (hv : v ∈ linearEigenspace L.toLinearEquiv 1) :
    J v ∈ linearEigenspace L.toLinearEquiv 1 := by
  exact linearEigenspace_J_mem_of_star_eq J L (isClassicalSpace_compatible h) (by simp) hv

/-- In the `C*` case, the `-1` eigenspace of `L` is stable under `J`. -/
theorem Cstar_J_stable_minus (a b : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (h : @IsClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) V _ _ _
      ‹FormedSpace Sign.neg V› J L)
    {v : V} (hv : v ∈ linearEigenspace L.toLinearEquiv (-1)) :
    J v ∈ linearEigenspace L.toLinearEquiv (-1) := by
  exact linearEigenspace_J_mem_of_star_eq J L (isClassicalSpace_compatible h) (by simp) hv

namespace DStarAux

/-- In the `D*` case, the auxiliary operator `A = -iL`. -/
noncomputable def A
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) : V →ₗ[ℂ] V :=
  (-Complex.I) • L.toLinearMap

/-- The `A=+1` eigenspace is the `L=i` eigenspace. -/
theorem A_eigenspace_one_eq_L_i
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    LinearMap.ker (A L - 1 • LinearMap.id) = linearEigenspace L.toLinearEquiv Complex.I := by
  ext v
  rw [linearEigenspace, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hv
    have hvA : DStarAux.A L v = (1 : ℂ) • v := by
      simpa using (sub_eq_zero.mp hv)
    apply sub_eq_zero.mpr
    calc
      L v = (Complex.I * (-Complex.I)) • L v := by simp [Complex.I_mul_I]
      _ = Complex.I • ((-Complex.I) • L v) := by rw [smul_smul]
      _ = Complex.I • DStarAux.A L v := rfl
      _ = Complex.I • ((1 : ℂ) • v) := by rw [hvA]
      _ = Complex.I • v := by simp
  · intro hv
    have hvL : L v = Complex.I • v := by
      simpa using (sub_eq_zero.mp hv)
    apply sub_eq_zero.mpr
    calc
      DStarAux.A L v = (-Complex.I) • L v := rfl
      _ = (-Complex.I) • (Complex.I • v) := by rw [hvL]
      _ = (1 : ℂ) • v := by simp [smul_smul, Complex.I_mul_I]
      _ = (1 • LinearMap.id) v := by simp

/-- The `A=-1` eigenspace is the `L=-i` eigenspace. -/
theorem A_eigenspace_neg_one_eq_L_neg_i
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    LinearMap.ker (A L - (-1) • LinearMap.id) =
      linearEigenspace L.toLinearEquiv (-Complex.I) := by
  ext v
  rw [linearEigenspace, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hv
    have hvA : DStarAux.A L v = (-1 : ℂ) • v := by
      simpa using (sub_eq_zero.mp hv)
    apply sub_eq_zero.mpr
    calc
      L v = (Complex.I * (-Complex.I)) • L v := by simp [Complex.I_mul_I]
      _ = Complex.I • ((-Complex.I) • L v) := by rw [smul_smul]
      _ = Complex.I • DStarAux.A L v := rfl
      _ = Complex.I • ((-1 : ℂ) • v) := by rw [hvA]
      _ = (-Complex.I) • v := by simp
  · intro hv
    have hvL : L v = (-Complex.I) • v := by
      simpa using (sub_eq_zero.mp hv)
    apply sub_eq_zero.mpr
    calc
      DStarAux.A L v = (-Complex.I) • L v := rfl
      _ = (-Complex.I) • ((-Complex.I) • v) := by rw [hvL]
      _ = (-1 : ℂ) • v := by simp [smul_smul, Complex.I_mul_I]
      _ = ((-1) • LinearMap.id) v := by simp

end DStarAux

/-- In the `D*` case, `J` maps the `A=+1` eigenspace to the `A=-1` eigenspace. -/
theorem Dstar_J_maps_A_plus_to_minus (r : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (h : @IsClassicalSpace ClassicalStar.Dstar r r V _ _ _
      ‹FormedSpace Sign.pos V› J L)
    {v : V} (hv : v ∈ LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) :
    J v ∈ LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id) := by
  have hSource := DStarAux.A_eigenspace_one_eq_L_i (L := L)
  have hTarget := DStarAux.A_eigenspace_neg_one_eq_L_neg_i (L := L)
  have hvL : v ∈ linearEigenspace L.toLinearEquiv Complex.I := by
    rw [← hSource]
    exact hv
  have hJ : J v ∈ linearEigenspace L.toLinearEquiv (-Complex.I) :=
    linearEigenspace_J_mem_i_to_neg_i J L (isClassicalSpace_compatible h) hvL
  rw [hTarget]
  exact hJ

/-- In the `D*` case, the two eigenspaces of `A = -iL` have equal dimension. -/
theorem Dstar_A_eigen_dims_eq (r : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (h : @IsClassicalSpace ClassicalStar.Dstar r r V _ _ _
      ‹FormedSpace Sign.pos V› J L) :
    Module.finrank ℂ (LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) =
      Module.finrank ℂ (LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id)) := by
  rw [DStarAux.A_eigenspace_one_eq_L_i (L := L),
    DStarAux.A_eigenspace_neg_one_eq_L_neg_i (L := L)]
  exact eig_i_finrank_eq_eig_neg_i_finrank J L (isClassicalSpace_compatible h)

/-- In the `D*` case, the `A=+1` eigenspace is totally isotropic. -/
theorem Dstar_A_plus_totally_isotropic
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    FormTotallyIsotropic Sign.pos V (LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) := by
  intro u hu v hv
  have hEq := DStarAux.A_eigenspace_one_eq_L_i (L := L)
  have huL : u ∈ linearEigenspace L.toLinearEquiv Complex.I := by
    rw [← hEq]
    exact hu
  have hvL : v ∈ linearEigenspace L.toLinearEquiv Complex.I := by
    rw [← hEq]
    exact hv
  exact L_eigenspaces_form_orthogonal L
    (by norm_num [Complex.I_mul_I] : Complex.I * Complex.I ≠ (1 : ℂ)) huL hvL

/-- In the `D*` case, the `A=-1` eigenspace is totally isotropic. -/
theorem Dstar_A_minus_totally_isotropic
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    FormTotallyIsotropic Sign.pos V (LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id)) := by
  intro u hu v hv
  have hEq := DStarAux.A_eigenspace_neg_one_eq_L_neg_i (L := L)
  have huL : u ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
    rw [← hEq]
    exact hu
  have hvL : v ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
    rw [← hEq]
    exact hv
  exact L_eigenspaces_form_orthogonal L
    (by norm_num [Complex.I_mul_I] : (-Complex.I) * (-Complex.I) ≠ (1 : ℂ)) huL hvL

end ClassicalGroup
