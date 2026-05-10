import CombUnipotent.ClassicalGroup.StandardModels

/-!
# Normal-form theorem interfaces for the ClassicalGroup task

This file is the proof-interface layer between the blueprint and the final
uniqueness theorem.

Each theorem states that an arbitrary classical space of the indicated type is
isomorphic to the explicit standard model from `StandardModels.lean`.  The final
uniqueness theorem in `Uniqueness.lean` then contains only the formal operation
"go from the first space to the standard model, then back to the second".

The remaining work is to prove these normal-form statements from the lower-level
real-form, symplectic, and quaternionic Gram-Schmidt lemmas.
-/

namespace ClassicalGroup

universe u

open scoped BigOperators

/-! ## Coordinate delta lemmas

The adapted-basis-to-coordinate-map proofs repeatedly evaluate the standard
coordinate forms on images of basis vectors.  Under
`LinearEquiv.sumArrowLequivProdArrow`, a basis vector indexed by `Sum.inl i`
has first coordinate the usual delta function at `i` and second coordinate zero;
the following two lemmas record the resulting dot products for the two blocks. -/

private theorem dot_sum_single_inl_inl {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    dot (((Finsupp.single (Sum.inl i : ι ⊕ κ) (1 : ℂ) : (ι ⊕ κ) →₀ ℂ) :
          (ι ⊕ κ) → ℂ) ∘ Sum.inl)
        (((Finsupp.single (Sum.inl j : ι ⊕ κ) (1 : ℂ) : (ι ⊕ κ) →₀ ℂ) :
          (ι ⊕ κ) → ℂ) ∘ Sum.inl) =
      if i = j then 1 else 0 := by
  classical
  unfold dot
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have h : (Sum.inl i : ι ⊕ κ) ≠ Sum.inl b := by
        intro h
        exact hb (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · intro hi
      simp at hi
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = i
    · subst x
      have h : (Sum.inl j : ι ⊕ κ) ≠ Sum.inl i := by
        intro h
        exact hij (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · have h : (Sum.inl i : ι ⊕ κ) ≠ Sum.inl x := by
        intro h
        exact hxi (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]

private theorem dot_sum_single_inr_inr {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    dot (((Finsupp.single (Sum.inr i : κ ⊕ ι) (1 : ℂ) : (κ ⊕ ι) →₀ ℂ) :
          (κ ⊕ ι) → ℂ) ∘ Sum.inr)
        (((Finsupp.single (Sum.inr j : κ ⊕ ι) (1 : ℂ) : (κ ⊕ ι) →₀ ℂ) :
          (κ ⊕ ι) → ℂ) ∘ Sum.inr) =
      if i = j then 1 else 0 := by
  classical
  unfold dot
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have h : (Sum.inr i : κ ⊕ ι) ≠ Sum.inr b := by
        intro h
        exact hb (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · intro hi
      simp at hi
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = i
    · subst x
      have h : (Sum.inr j : κ ⊕ ι) ≠ Sum.inr i := by
        intro h
        exact hij (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · have h : (Sum.inr i : κ ⊕ ι) ≠ Sum.inr x := by
        intro h
        exact hxi (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]

private theorem dot_sum_single_inl_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    dot (((Finsupp.single (Sum.inl i : ι ⊕ ι) (1 : ℂ) : (ι ⊕ ι) →₀ ℂ) :
          (ι ⊕ ι) → ℂ) ∘ Sum.inl)
        (((Finsupp.single (Sum.inr j : ι ⊕ ι) (1 : ℂ) : (ι ⊕ ι) →₀ ℂ) :
          (ι ⊕ ι) → ℂ) ∘ Sum.inr) =
      if i = j then 1 else 0 := by
  classical
  unfold dot
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have h : (Sum.inl i : ι ⊕ ι) ≠ Sum.inl b := by
        intro h
        exact hb (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · intro hi
      simp at hi
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = i
    · subst x
      have h : (Sum.inr j : ι ⊕ ι) ≠ Sum.inr i := by
        intro h
        exact hij (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · have h : (Sum.inl i : ι ⊕ ι) ≠ Sum.inl x := by
        intro h
        exact hxi (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]

private theorem dot_sum_single_inr_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    dot (((Finsupp.single (Sum.inr i : ι ⊕ ι) (1 : ℂ) : (ι ⊕ ι) →₀ ℂ) :
          (ι ⊕ ι) → ℂ) ∘ Sum.inr)
        (((Finsupp.single (Sum.inl j : ι ⊕ ι) (1 : ℂ) : (ι ⊕ ι) →₀ ℂ) :
          (ι ⊕ ι) → ℂ) ∘ Sum.inl) =
      if i = j then 1 else 0 := by
  classical
  unfold dot
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have h : (Sum.inr i : ι ⊕ ι) ≠ Sum.inr b := by
        intro h
        exact hb (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · intro hi
      simp at hi
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = i
    · subst x
      have h : (Sum.inl j : ι ⊕ ι) ≠ Sum.inl i := by
        intro h
        exact hij (Sum.inl.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]
    · have h : (Sum.inr i : ι ⊕ ι) ≠ Sum.inr x := by
        intro h
        exact hxi (Sum.inr.inj h).symm
      simp [Finsupp.single_eq_of_ne' h]

/-! ## Orthogonal normal forms: `B` and `D` -/

/-- Adapted orthogonal basis data for the `B,D` normal form.

The basis is indexed by `Fin p ⊕ Fin q`.  The `inl` block is the positive
`L=+1` block and the `inr` block is the negative `L=-1` block. -/
structure OrthogonalAdaptedBasis (p q : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos) (L : LStructure Sign.pos V Sign.pos) where
  /-- The adapted complex basis. -/
  basis : Module.Basis (Fin p ⊕ Fin q) ℂ V
  /-- All adapted basis vectors are fixed by `J`. -/
  J_basis : ∀ i, J (basis i) = basis i
  /-- The positive block is the `L=+1` block. -/
  L_inl : ∀ i, L (basis (Sum.inl i)) = basis (Sum.inl i)
  /-- The negative block is the `L=-1` block. -/
  L_inr : ∀ j, L (basis (Sum.inr j)) = -basis (Sum.inr j)
  /-- The positive block has identity Gram matrix. -/
  form_inl_inl :
    ∀ i j, FormedSpace.B Sign.pos V (basis (Sum.inl i)) (basis (Sum.inl j)) =
      if i = j then 1 else 0
  /-- The negative block has negative identity Gram matrix. -/
  form_inr_inr :
    ∀ i j, FormedSpace.B Sign.pos V (basis (Sum.inr i)) (basis (Sum.inr j)) =
      if i = j then -1 else 0
  /-- The positive and negative blocks are orthogonal. -/
  form_inl_inr :
    ∀ i j, FormedSpace.B Sign.pos V (basis (Sum.inl i)) (basis (Sum.inr j)) = 0
  /-- The negative and positive blocks are orthogonal. -/
  form_inr_inl :
    ∀ i j, FormedSpace.B Sign.pos V (basis (Sum.inr i)) (basis (Sum.inl j)) = 0

namespace OrthogonalAdaptedBasis

/-- Coordinate equivalence associated to an adapted orthogonal basis. -/
noncomputable def toLinearEquiv {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.pos} {L : LStructure Sign.pos V Sign.pos}
    (A : OrthogonalAdaptedBasis p q V J L) : V ≃ₗ[ℂ] OrthVec p q :=
  A.basis.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ)

/-- The coordinate map attached to an orthogonal adapted basis intertwines `L`. -/
theorem intertwines_L {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.pos} {L : LStructure Sign.pos V Sign.pos}
    (A : OrthogonalAdaptedBasis p q V J L) :
    ∀ v : V, A.toLinearEquiv (L v) = orthL p q (A.toLinearEquiv v) := by
  let f₁ : V →ₗ[ℂ] OrthVec p q :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap.comp L.toLinearMap
  let f₂ : V →ₗ[ℂ] OrthVec p q :=
    (orthL p q).toLinearMap.comp (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_inl, orthL, prodSignLinearEquiv,
          LinearEquiv.sumArrowLequivProdArrow]
    | inr j =>
        ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_inr, orthL, prodSignLinearEquiv,
          LinearEquiv.sumArrowLequivProdArrow]
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an orthogonal adapted basis intertwines `J`. -/
theorem intertwines_J {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.pos} {L : LStructure Sign.pos V Sign.pos}
    (A : OrthogonalAdaptedBasis p q V J L) :
    ∀ v : V, A.toLinearEquiv (J v) = orthJ p q (A.toLinearEquiv v) := by
  let f₁ : V →ₛₗ[starRingEnd ℂ] OrthVec p q :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap.comp J.toSemilinearMap
  let f₂ : V →ₛₗ[starRingEnd ℂ] OrthVec p q :=
    (orthJ p q).toSemilinearMap.comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k
        · by_cases hki : k = i
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inl i : Fin p ⊕ Fin q) ≠ Sum.inl k := by
              intro h
              exact hki (Sum.inl.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum]
            simp
        · simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
    | inr j =>
        ext k
        · simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
        · by_cases hkj : k = j
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inr j : Fin p ⊕ Fin q) ≠ Sum.inr k := by
              intro h
              exact hkj (Sum.inr.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_basis, orthJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum]
            simp
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an orthogonal adapted basis preserves the
bilinear forms. -/
theorem preserves_form {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.pos} {L : LStructure Sign.pos V Sign.pos}
    (A : OrthogonalAdaptedBasis p q V J L) :
    ∀ u v : V,
      FormedSpace.B Sign.pos (OrthVec p q) (A.toLinearEquiv u) (A.toLinearEquiv v) =
        FormedSpace.B Sign.pos V u v := by
  let Bpull : LinearMap.BilinForm ℂ V :=
    (FormedSpace.B Sign.pos (OrthVec p q)).comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap
      (A.toLinearEquiv : V ≃ₗ[ℂ] OrthVec p q).toLinearMap
  have hB : Bpull = FormedSpace.B Sign.pos V := by
    apply LinearMap.BilinForm.ext_basis A.basis
    intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, orthFormedSpace, orthForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inl_inl]
            rw [dot_sum_single_inl_inl (κ := Fin q) i j]
            simp [dot]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, orthFormedSpace, orthForm_apply, dot,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inl_inr]
    | inr i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, orthFormedSpace, orthForm_apply, dot,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inr_inl]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, orthFormedSpace, orthForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inr_inr]
            rw [dot_sum_single_inr_inr (κ := Fin p) i j]
            by_cases hij : i = j <;> simp [hij, dot]
  intro u v
  have h := congrArg (fun B : LinearMap.BilinForm ℂ V => B u v) hB
  simpa [Bpull] using h

/-- An adapted orthogonal basis gives the required coordinate isomorphism.

This is the purely coordinate-checking half of the `B,D` normal form: form
preservation is checked on the adapted basis and extended bilinearly; the `J`
and `L` intertwining identities are checked on the same basis and extended by
semilinearity/linearity. -/
theorem toNormalFormIso {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.pos} {L : LStructure Sign.pos V Sign.pos}
    (A : OrthogonalAdaptedBasis p q V J L) :
      Nonempty
        { e : FormedSpaceIso Sign.pos V (OrthVec p q) //
            ((∀ v : V, e.toLinearEquiv (J v) = orthJ p q (e.toLinearEquiv v)) ∧
              (∀ v : V, e.toLinearEquiv (L v) = orthL p q (e.toLinearEquiv v))) } := by
    let e : FormedSpaceIso Sign.pos V (OrthVec p q) :=
      { toLinearEquiv := A.toLinearEquiv, preserves_form := A.preserves_form }
    exact ⟨⟨e, ⟨A.intertwines_J, A.intertwines_L⟩⟩⟩

end OrthogonalAdaptedBasis

/-! ### Real fixed eigenspace dimension layer for `B,D`

The existence proof for an adapted orthogonal basis must choose real
orthonormal bases in the `J`-fixed parts of the `L=±1` eigenspaces.  The two
lemmas below discharge the dimension bookkeeping for those real spaces: the
general complexification lemma in `Lemmas.lean` identifies the fixed-real
dimension with the prescribed complex eigenspace dimension. -/

private theorem orthogonal_plus_fixed_finrank (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    Module.finrank ℝ (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv 1)) = p := by
  rw [finrank_JFixed_linearEigenspace_eq_complex J L hcompat (by simp)]
  exact hLsig.1

private theorem orthogonal_minus_fixed_finrank (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    Module.finrank ℝ (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv (-1))) = q := by
  rw [finrank_JFixed_linearEigenspace_eq_complex J L hcompat (by simp)]
  exact hLsig.2

/-- Positive real inner-product core on the `J`-fixed `L=+1` eigenspace.

Its inner product is the real part of the original bilinear form.  Positivity is
exactly the Cartan positivity statement specialized by
`BD_form_re_pos_of_Jfixed_mem_plus`. -/
private noncomputable def BDPlusFixedInnerCore
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L) :
    InnerProductSpace.Core ℝ (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv 1)) where
  inner x y := (FormedSpace.B Sign.pos V x.1.1 y.1.1).re
  conj_inner_symm := by
    intro x y
    have hsym := FormedSpace.eps_symm (eps := Sign.pos) (V := V) x.1.1 y.1.1
    simpa [FormedSpace.B, Sign.toComplex_pos] using congrArg Complex.re hsym.symm
  re_inner_nonneg := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · have hxv : x.1.1 ≠ 0 := by
        intro h
        apply hx
        ext
        exact h
      exact le_of_lt (BD_form_re_pos_of_Jfixed_mem_plus J L hcompat x.2 x.1.2 hxv)
  add_left := by
    intro x y z
    simp
  smul_left := by
    intro x y r
    change (FormedSpace.B Sign.pos V ((r : ℂ) • x.1.1) y.1.1).re =
      r * (FormedSpace.B Sign.pos V x.1.1 y.1.1).re
    simp
  definite := by
    intro x hxzero
    by_contra hx
    have hxv : x.1.1 ≠ 0 := by
      intro h
      apply hx
      ext
      exact h
    have hpos := BD_form_re_pos_of_Jfixed_mem_plus J L hcompat x.2 x.1.2 hxv
    rw [hxzero] at hpos
    exact (lt_irrefl _ hpos)

/-- Positive real inner-product core on the `J`-fixed `L=-1` eigenspace.

Here the positive form is the negative of the original bilinear form, using
`BD_neg_form_re_pos_of_Jfixed_mem_minus`. -/
private noncomputable def BDMinusFixedInnerCore
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L) :
    InnerProductSpace.Core ℝ (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv (-1))) where
  inner x y := (-(FormedSpace.B Sign.pos V x.1.1 y.1.1)).re
  conj_inner_symm := by
    intro x y
    have hsym := FormedSpace.eps_symm (eps := Sign.pos) (V := V) x.1.1 y.1.1
    simpa [FormedSpace.B, Sign.toComplex_pos] using congrArg Complex.re hsym.symm
  re_inner_nonneg := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · have hxv : x.1.1 ≠ 0 := by
        intro h
        apply hx
        ext
        exact h
      exact le_of_lt (BD_neg_form_re_pos_of_Jfixed_mem_minus J L hcompat x.2 x.1.2 hxv)
  add_left := by
    intro x y z
    simp
    ring
  smul_left := by
    intro x y r
    change (-(FormedSpace.B Sign.pos V ((r : ℂ) • x.1.1) y.1.1)).re =
      r * (-(FormedSpace.B Sign.pos V x.1.1 y.1.1)).re
    simp
  definite := by
    intro x hxzero
    by_contra hx
    have hxv : x.1.1 ≠ 0 := by
      intro h
      apply hx
      ext
      exact h
    have hpos := BD_neg_form_re_pos_of_Jfixed_mem_minus J L hcompat x.2 x.1.2 hxv
    rw [hxzero] at hpos
    exact (lt_irrefl _ hpos)

/-- A real orthonormal basis of the positive fixed eigenspace, with the Gram
identity converted back to the original complex bilinear form. -/
private theorem BDPlusFixedOrthonormalBasis_exists (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    ∃ b : Module.Basis (Fin p) ℝ
        (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv 1)),
      ∀ i j,
        FormedSpace.B Sign.pos V (b i).1.1 (b j).1.1 = if i = j then 1 else 0 := by
  let F := JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv 1)
  let core : InnerProductSpace.Core ℝ F := BDPlusFixedInnerCore J L hcompat
  letI : InnerProductSpace.Core ℝ F := core
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedSpace ℝ F := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore core.toCore
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F :=
    stdOrthonormalBasis ℝ F
  have hdim : Module.finrank ℝ F = p :=
    orthogonal_plus_fixed_finrank p q J L hcompat hLsig
  let bON : OrthonormalBasis (Fin p) ℝ F := b₀.reindex (finCongr hdim)
  refine ⟨bON.toBasis, ?_⟩
  intro i j
  change FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1 = if i = j then 1 else 0
  have hon := (orthonormal_iff_ite.mp bON.orthonormal) i j
  have hre :
      (FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1).re =
        (if i = j then 1 else 0 : ℝ) := by
    simpa [bON, b₀, F] using hon
  have hstar :
      (starRingEnd ℂ) (FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1) =
        FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1 :=
    form_star_eq_of_mem_JFixedRealSubmodule J (bON i).2 (bON j).2
  have hcomplex := complex_eq_of_star_eq_of_re_eq hstar hre
  by_cases hij : i = j <;> simpa [hij] using hcomplex

/-- A real orthonormal basis of the negative fixed eigenspace, normalized so
that the original bilinear form has Gram matrix `-I`. -/
private theorem BDMinusFixedOrthonormalBasis_exists (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    ∃ b : Module.Basis (Fin q) ℝ
        (JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv (-1))),
      ∀ i j,
        FormedSpace.B Sign.pos V (b i).1.1 (b j).1.1 = if i = j then -1 else 0 := by
  let F := JFixedSubmoduleIn J (linearEigenspace L.toLinearEquiv (-1))
  let core : InnerProductSpace.Core ℝ F := BDMinusFixedInnerCore J L hcompat
  letI : InnerProductSpace.Core ℝ F := core
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedSpace ℝ F := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore core.toCore
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F :=
    stdOrthonormalBasis ℝ F
  have hdim : Module.finrank ℝ F = q :=
    orthogonal_minus_fixed_finrank p q J L hcompat hLsig
  let bON : OrthonormalBasis (Fin q) ℝ F := b₀.reindex (finCongr hdim)
  refine ⟨bON.toBasis, ?_⟩
  intro i j
  change FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1 = if i = j then -1 else 0
  have hon := (orthonormal_iff_ite.mp bON.orthonormal) i j
  have hneg_re :
      (-(FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1)).re =
        (if i = j then 1 else 0 : ℝ) := by
    simpa [bON, b₀, F] using hon
  have hre :
      (FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1).re =
        (if i = j then -1 else 0 : ℝ) := by
    by_cases hij : i = j <;> simp [hij] at hneg_re ⊢
    · linarith
    · exact hneg_re
  have hstar :
      (starRingEnd ℂ) (FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1) =
        FormedSpace.B Sign.pos V (bON i).1.1 (bON j).1.1 :=
    form_star_eq_of_mem_JFixedRealSubmodule J (bON i).2 (bON j).2
  have hcomplex := complex_eq_of_star_eq_of_re_eq hstar hre
  by_cases hij : i = j <;> simpa [hij] using hcomplex

/-- A family whose Gram matrix is diagonal with nonzero diagonal is linearly
independent.  This is used to promote the fixed-real orthonormal bases to
complex bases of the `L = ±1` eigenspaces. -/
private theorem form_orthogonal_linearIndependent
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {S : Submodule ℂ V} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → S} {d : ℂ} (hd : d ≠ 0)
    (hgram : ∀ i j,
      FormedSpace.B Sign.pos V (v i : V) (v j : V) = if i = j then d else 0) :
    LinearIndependent ℂ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hBsum_zero :
      FormedSpace.B Sign.pos V ((∑ j, c j • v j : S) : V) (v i : V) = 0 := by
    rw [hsum]
    simp
  have hcalc :
      FormedSpace.B Sign.pos V ((∑ j, c j • v j : S) : V) (v i : V) = c i * d := by
    simp [hgram, Finset.sum_ite_eq', Finset.mem_univ]
  have hi : c i * d = 0 := by
    rw [← hcalc]
    exact hBsum_zero
  exact (mul_eq_zero.mp hi).resolve_right hd

/-- Build a basis from a diagonal nondegenerate Gram family once its cardinality
matches the finite dimension of the ambient subspace. -/
private noncomputable def basisOfFormOrthogonal
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (S : Submodule ℂ V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → S) {d : ℂ} (hd : d ≠ 0)
    (hcard : Fintype.card ι = Module.finrank ℂ S)
    (hgram : ∀ i j,
      FormedSpace.B Sign.pos V (v i : V) (v j : V) = if i = j then d else 0) :
    Module.Basis ι ℂ S := by
  classical
  have hli : LinearIndependent ℂ v := form_orthogonal_linearIndependent hd hgram
  refine Module.Basis.mk hli ?_
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  rw [hspan]

/-- Existence of an adapted orthogonal basis from the `B,D` hypotheses.

This is the real-form/Sylvester-law part of the proof. -/
theorem orthogonalAdaptedBasis_exists (p q : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hfin : Module.finrank ℂ V = p + q)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    Nonempty (OrthogonalAdaptedBasis p q V J L) := by
  classical
  have _ := hfin
  let Eplus := linearEigenspace L.toLinearEquiv 1
  let Eminus := linearEigenspace L.toLinearEquiv (-1)
  rcases BDPlusFixedOrthonormalBasis_exists p q J L hcompat hLsig with
    ⟨bPlusFixed, hPlusGram⟩
  rcases BDMinusFixedOrthonormalBasis_exists p q J L hcompat hLsig with
    ⟨bMinusFixed, hMinusGram⟩
  let vPlus : Fin p → Eplus := fun i => (bPlusFixed i).1
  let vMinus : Fin q → Eminus := fun i => (bMinusFixed i).1
  have hPlusGram' :
      ∀ i j, FormedSpace.B Sign.pos V (vPlus i : V) (vPlus j : V) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    simpa [vPlus, Eplus] using hPlusGram i j
  have hMinusGram' :
      ∀ i j, FormedSpace.B Sign.pos V (vMinus i : V) (vMinus j : V) =
        if i = j then (-1 : ℂ) else 0 := by
    intro i j
    simpa [vMinus, Eminus] using hMinusGram i j
  let bPlus : Module.Basis (Fin p) ℂ Eplus :=
    basisOfFormOrthogonal Eplus vPlus (d := 1) (by norm_num)
      (by simpa [Eplus] using hLsig.1.symm) hPlusGram'
  let bMinus : Module.Basis (Fin q) ℂ Eminus :=
    basisOfFormOrthogonal Eminus vMinus (d := -1) (by norm_num)
      (by simpa [Eminus] using hLsig.2.symm) hMinusGram'
  let hcompl : IsCompl Eplus Eminus := by
    simpa [Eplus, Eminus] using linearEigenspace_one_neg_one_isCompl (V := V) L
  let basis : Module.Basis (Fin p ⊕ Fin q) ℂ V :=
    (bPlus.prod bMinus).map (Submodule.prodEquivOfIsCompl Eplus Eminus hcompl)
  have hbasis_inl : ∀ i, basis (Sum.inl i) = (bPlusFixed i).1.1 := by
    intro i
    simp [basis, bPlus, bMinus, vPlus, vMinus, Eplus, Eminus, basisOfFormOrthogonal]
  have hbasis_inr : ∀ i, basis (Sum.inr i) = (bMinusFixed i).1.1 := by
    intro i
    simp [basis, bPlus, bMinus, vPlus, vMinus, Eplus, Eminus, basisOfFormOrthogonal]
  refine ⟨
    { basis := basis
      J_basis := ?_
      L_inl := ?_
      L_inr := ?_
      form_inl_inl := ?_
      form_inr_inr := ?_
      form_inl_inr := ?_
      form_inr_inl := ?_ }⟩
  · intro i
    cases i with
    | inl i =>
        rw [hbasis_inl]
        exact (bPlusFixed i).2
    | inr i =>
        rw [hbasis_inr]
        exact (bMinusFixed i).2
  · intro i
    rw [hbasis_inl]
    simpa using linearEigenspace_apply_eq L (a := (1 : ℂ)) (bPlusFixed i).1.2
  · intro i
    rw [hbasis_inr]
    simpa using linearEigenspace_apply_eq L (a := (-1 : ℂ)) (bMinusFixed i).1.2
  · intro i j
    rw [hbasis_inl, hbasis_inl]
    exact hPlusGram i j
  · intro i j
    rw [hbasis_inr, hbasis_inr]
    exact hMinusGram i j
  · intro i j
    rw [hbasis_inl, hbasis_inr]
    exact BD_plus_minus_orthogonal L (bPlusFixed i).1.2 (bMinusFixed j).1.2
  · intro i j
    rw [hbasis_inr, hbasis_inl]
    have hsym := FormedSpace.eps_symm (eps := Sign.pos) (V := V)
      (bMinusFixed i).1.1 (bPlusFixed j).1.1
    have horth : FormedSpace.B Sign.pos V (bPlusFixed j).1.1 (bMinusFixed i).1.1 = 0 :=
      BD_plus_minus_orthogonal L (bPlusFixed j).1.2 (bMinusFixed i).1.2
    simpa [horth] using hsym

/-- Raw orthogonal normal form, independent of whether the family is `B` or `D`.

This is the real-form/Sylvester-law core of the `B,D` uniqueness proof.  The
output is a formed-space isomorphism to the explicit `OrthVec p q` model,
together with the two intertwining identities for `J` and `L`. -/
theorem orthogonalNormalFormIso (p q : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.pos)
    (L : LStructure Sign.pos V Sign.pos)
    (hfin : Module.finrank ℂ V = p + q)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = p ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = q) :
    Nonempty
      { e : FormedSpaceIso Sign.pos V (OrthVec p q) //
          (∀ v : V, e.toLinearEquiv (J v) = orthJ p q (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = orthL p q (e.toLinearEquiv v)) } := by
  rcases orthogonalAdaptedBasis_exists p q V J L hfin hcompat hLsig with ⟨A⟩
  exact A.toNormalFormIso

/-- Normal form for the `B` family.

Blueprint content: pass to the real form `V^J`, decompose it into the real
`L=+1` and `L=-1` eigenspaces, choose orthonormal bases for the positive and
negative parts, and complexify the resulting real basis. -/
theorem normalForm_B (p q : ℕ) (_hOdd : Odd (p + q))
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.B.eps V]
    (J : JStructure ClassicalStar.B.eps V ClassicalStar.B.jSign)
    (L : LStructure ClassicalStar.B.eps V ClassicalStar.B.dotEps)
    (hV : IsClassicalSpace ClassicalStar.B p q V J L) :
    Nonempty (ClassicalSpaceIso ClassicalStar.B V (OrthVec p q) J L (orthJ p q) (orthL p q)) := by
  rcases orthogonalNormalFormIso p q V J L (isClassicalSpace_finrank hV)
      (isClassicalSpace_compatible hV)
      (by simpa [LSignatureCondition] using isClassicalSpace_LSignature hV) with ⟨e, hJ, hL⟩
  exact ⟨{ toFormedSpaceIso := e, intertwines_J := hJ, intertwines_L := hL }⟩

/-- Normal form for the `D` family.

The proof is identical to `normalForm_B`; only the signature parity hypothesis
differs. -/
theorem normalForm_D (p q : ℕ) (_hEven : Even (p + q))
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.D.eps V]
    (J : JStructure ClassicalStar.D.eps V ClassicalStar.D.jSign)
    (L : LStructure ClassicalStar.D.eps V ClassicalStar.D.dotEps)
    (hV : IsClassicalSpace ClassicalStar.D p q V J L) :
    Nonempty (ClassicalSpaceIso ClassicalStar.D V (OrthVec p q) J L (orthJ p q) (orthL p q)) := by
  rcases orthogonalNormalFormIso p q V J L (isClassicalSpace_finrank hV)
      (isClassicalSpace_compatible hV)
      (by simpa [LSignatureCondition] using isClassicalSpace_LSignature hV) with ⟨e, hJ, hL⟩
  exact ⟨{ toFormedSpaceIso := e, intertwines_J := hJ, intertwines_L := hL }⟩

/-! ## Real symplectic normal forms: `C` and `Ctilda` -/

/-- Adapted symplectic basis data for the `C`/`Ctilda` normal form.

The basis is indexed by `Fin r ⊕ Fin r`; the first block is the `e` block and
the second block is the `f` block, with `L e_i = -f_i` and `L f_i = e_i`. -/
structure SymplecticAdaptedBasis (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.pos) (L : LStructure Sign.neg V Sign.neg) where
  /-- The adapted complex basis. -/
  basis : Module.Basis (Fin r ⊕ Fin r) ℂ V
  /-- All adapted basis vectors are fixed by `J`. -/
  J_basis : ∀ i, J (basis i) = basis i
  /-- `L` sends the `e` block to minus the `f` block. -/
  L_inl : ∀ i, L (basis (Sum.inl i)) = -basis (Sum.inr i)
  /-- `L` sends the `f` block to the `e` block. -/
  L_inr : ∀ i, L (basis (Sum.inr i)) = basis (Sum.inl i)
  /-- The `e` block is isotropic. -/
  form_inl_inl :
    ∀ i j, FormedSpace.B Sign.neg V (basis (Sum.inl i)) (basis (Sum.inl j)) = 0
  /-- The `f` block is isotropic. -/
  form_inr_inr :
    ∀ i j, FormedSpace.B Sign.neg V (basis (Sum.inr i)) (basis (Sum.inr j)) = 0
  /-- Pairing from `e` to `f` is the identity matrix. -/
  form_inl_inr :
    ∀ i j, FormedSpace.B Sign.neg V (basis (Sum.inl i)) (basis (Sum.inr j)) =
      if i = j then 1 else 0
  /-- Pairing from `f` to `e` is minus the identity matrix. -/
  form_inr_inl :
    ∀ i j, FormedSpace.B Sign.neg V (basis (Sum.inr i)) (basis (Sum.inl j)) =
      if i = j then -1 else 0

namespace SymplecticAdaptedBasis

/-- Coordinate equivalence associated to an adapted symplectic basis. -/
noncomputable def toLinearEquiv {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.pos} {L : LStructure Sign.neg V Sign.neg}
    (A : SymplecticAdaptedBasis r V J L) : V ≃ₗ[ℂ] PairVec r :=
  A.basis.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) ℂ ℂ)

/-- The coordinate map attached to a symplectic adapted basis intertwines `L`. -/
theorem intertwines_L {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.pos} {L : LStructure Sign.neg V Sign.neg}
    (A : SymplecticAdaptedBasis r V J L) :
    ∀ v : V, A.toLinearEquiv (L v) = sympL r (A.toLinearEquiv v) := by
  let f₁ : V →ₗ[ℂ] PairVec r :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap.comp L.toLinearMap
  let f₂ : V →ₗ[ℂ] PairVec r :=
    (sympL r).toLinearMap.comp (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k
        · simp [f₁, f₂, toLinearEquiv, A.L_inl, sympL, rotateLinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
        · by_cases hki : k = i
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.L_inl, sympL, rotateLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum₁ : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hki (Sum.inr.inj h).symm
            have hsum₂ : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl k := by
              intro h
              exact hki (Sum.inl.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.L_inl, sympL, rotateLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum₁, Finsupp.single_eq_of_ne' hsum₂]
    | inr j =>
        ext k
        · by_cases hkj : k = j
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.L_inr, sympL, rotateLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum₁ : (Sum.inl j : Fin r ⊕ Fin r) ≠ Sum.inl k := by
              intro h
              exact hkj (Sum.inl.inj h).symm
            have hsum₂ : (Sum.inr j : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hkj (Sum.inr.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.L_inr, sympL, rotateLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum₁, Finsupp.single_eq_of_ne' hsum₂]
        · simp [f₁, f₂, toLinearEquiv, A.L_inr, sympL, rotateLinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to a symplectic adapted basis intertwines `J`. -/
theorem intertwines_J {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.pos} {L : LStructure Sign.neg V Sign.neg}
    (A : SymplecticAdaptedBasis r V J L) :
    ∀ v : V, A.toLinearEquiv (J v) = sympRealJ r (A.toLinearEquiv v) := by
  let f₁ : V →ₛₗ[starRingEnd ℂ] PairVec r :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap.comp J.toSemilinearMap
  let f₂ : V →ₛₗ[starRingEnd ℂ] PairVec r :=
    (sympRealJ r).toSemilinearMap.comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k
        · by_cases hki : k = i
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl k := by
              intro h
              exact hki (Sum.inl.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum]
            simp
        · simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
    | inr j =>
        ext k
        · simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
        · by_cases hkj : k = j
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inr j : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hkj (Sum.inr.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_basis, sympRealJ, pairConjSemilinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' hsum]
            simp
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to a symplectic adapted basis preserves the
bilinear forms. -/
theorem preserves_form {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.pos} {L : LStructure Sign.neg V Sign.neg}
    (A : SymplecticAdaptedBasis r V J L) :
    ∀ u v : V,
      FormedSpace.B Sign.neg (PairVec r) (A.toLinearEquiv u) (A.toLinearEquiv v) =
        FormedSpace.B Sign.neg V u v := by
  let Bpull : LinearMap.BilinForm ℂ V :=
    (FormedSpace.B Sign.neg (PairVec r)).comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have hB : Bpull = FormedSpace.B Sign.neg V := by
    apply LinearMap.BilinForm.ext_basis A.basis
    intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, sympFormedSpace, sympForm_apply, dot,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inl_inl]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, sympFormedSpace, sympForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inl_inr]
            rw [dot_sum_single_inl_inr i j]
            simp [dot]
    | inr i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, sympFormedSpace, sympForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inr_inl]
            rw [dot_sum_single_inr_inl i j]
            by_cases hij : i = j <;> simp [hij, dot]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, sympFormedSpace, sympForm_apply, dot,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_inr_inr]
  intro u v
  have h := congrArg (fun B : LinearMap.BilinForm ℂ V => B u v) hB
  simpa [Bpull] using h

/-- An adapted symplectic basis gives the required coordinate isomorphism. -/
theorem toNormalFormIso {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.pos} {L : LStructure Sign.neg V Sign.neg}
    (A : SymplecticAdaptedBasis r V J L) :
    Nonempty
      { e : FormedSpaceIso Sign.neg V (PairVec r) //
          ((∀ v : V, e.toLinearEquiv (J v) = sympRealJ r (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = sympL r (e.toLinearEquiv v))) } := by
  let e : FormedSpaceIso Sign.neg V (PairVec r) :=
    { toLinearEquiv := A.toLinearEquiv, preserves_form := A.preserves_form }
  exact ⟨⟨e, ⟨A.intertwines_J, A.intertwines_L⟩⟩⟩

end SymplecticAdaptedBasis

/-- A family with the standard symplectic Gram matrix is linearly independent. -/
private theorem symplectic_gram_linearIndependent
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {r : ℕ} {v : Fin r ⊕ Fin r → V}
    (h_inl_inl : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inl j)) = 0)
    (h_inr_inr : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inr j)) = 0)
    (h_inl_inr : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inr j)) =
        if i = j then 1 else 0)
    (h_inr_inl : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inl j)) =
        if i = j then -1 else 0) :
    LinearIndependent ℂ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  cases k with
  | inl i =>
      have hBsum_zero :
          FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr i)) = 0 := by
        rw [hsum]
        simp
      have hcalc :
          FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr i)) =
            c (Sum.inl i) := by
        simp [h_inl_inr, h_inr_inr, Finset.sum_ite_eq', Finset.mem_univ]
      rw [← hcalc]
      exact hBsum_zero
  | inr i =>
      have hBsum_zero :
          FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl i)) = 0 := by
        rw [hsum]
        simp
      have hcalc :
          FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl i)) =
            -c (Sum.inr i) := by
        simp [h_inl_inl, h_inr_inl, Finset.sum_ite_eq', Finset.mem_univ]
      have hneg : -c (Sum.inr i) = 0 := by
        rw [← hcalc]
        exact hBsum_zero
      simpa using neg_eq_zero.mp hneg

/-- Promote a standard symplectic Gram family to a basis when the cardinality
matches the complex dimension. -/
private noncomputable def basisOfSymplecticGram
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {r : ℕ} (v : Fin r ⊕ Fin r → V)
    (hfin : Module.finrank ℂ V = r + r)
    (h_inl_inl : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inl j)) = 0)
    (h_inr_inr : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inr j)) = 0)
    (h_inl_inr : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inr j)) =
        if i = j then 1 else 0)
    (h_inr_inl : ∀ i j,
      FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inl j)) =
        if i = j then -1 else 0) :
    Module.Basis (Fin r ⊕ Fin r) ℂ V := by
  classical
  have hli : LinearIndependent ℂ v :=
    symplectic_gram_linearIndependent h_inl_inl h_inr_inr h_inl_inr h_inr_inl
  refine Module.Basis.mk hli ?_
  have hcard : Fintype.card (Fin r ⊕ Fin r) = Module.finrank ℂ V := by
    simp [hfin]
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  rw [hspan]

/-- Positive real inner-product core on the `J`-fixed real form for the
symplectic case.  Its inner product is `g(x,y)=Re B(Lx,y)`. -/
private noncomputable def symplecticJFixedInnerCore
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.pos)
    (L : LStructure Sign.neg V Sign.neg)
    (hcompat : JLCompatible J L) :
    InnerProductSpace.Core ℝ (JFixedRealSubmodule V J) where
  inner x y := (FormedSpace.B Sign.neg V (L x.1) y.1).re
  conj_inner_symm := by
    intro x y
    have hH := hcompat.cartan_positive.1 x.1 y.1
    rw [x.2, y.2] at hH
    have h := congrArg Complex.re hH
    simpa using h
  re_inner_nonneg := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · have hxv : x.1 ≠ 0 := by
        intro h
        apply hx
        ext
        exact h
      have hpos := hcompat.cartan_positive.2 x.1 hxv
      rw [x.2] at hpos
      exact le_of_lt hpos
  add_left := by
    intro x y z
    simp [map_add]
  smul_left := by
    intro x y r
    change (FormedSpace.B Sign.neg V (L ((r : ℂ) • x.1)) y.1).re =
      r * (FormedSpace.B Sign.neg V (L x.1) y.1).re
    rw [map_smul]
    simp
  definite := by
    intro x hxzero
    by_contra hx
    have hxv : x.1 ≠ 0 := by
      intro h
      apply hx
      ext
      exact h
    have hpos := hcompat.cartan_positive.2 x.1 hxv
    rw [x.2] at hpos
    rw [hxzero] at hpos
    exact (lt_irrefl _ hpos)

/-- The real fixed subspace of a conjugation has real dimension equal to the
ambient complex dimension. -/
private theorem finrank_JFixedRealSubmodule_eq_complex {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V]
    (J : JStructure eps V Sign.pos) :
    Module.finrank ℝ (JFixedRealSubmodule V J) = Module.finrank ℂ V := by
  classical
  let S : Submodule ℂ V := ⊤
  let e :
      JFixedRealSubmodule V J ≃ₗ[ℝ] JFixedSubmoduleIn J S :=
    { toFun := fun x => ⟨⟨x.1, by simp [S]⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro r x
        ext
        rfl }
  calc
    Module.finrank ℝ (JFixedRealSubmodule V J)
        = Module.finrank ℝ (JFixedSubmoduleIn J S) := e.finrank_eq
    _ = Module.finrank ℂ S :=
        finrank_JFixedSubmoduleIn_eq_complex J S (by intro v hv; simp [S])
    _ = Module.finrank ℂ V := by simp [S]

/-- Compatible real Gram-Schmidt for an orthogonal complex structure.

The output is an orthonormal family `e_i` whose `L`-rotates are orthogonal to
all `e_j`.  In the symplectic application this is exactly the family whose
`e_i,-Le_i` pairs give the standard symplectic Gram matrix. -/
private theorem symplecticCompatibleFamily_exists :
    ∀ (n : ℕ), ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F],
      (L : F →ₗ[ℝ] F) →
      (∀ x y : F, inner ℝ (L x) y = -inner ℝ x (L y)) →
      (∀ x : F, L (L x) = -x) →
      Module.finrank ℝ F = 2 * n →
      ∃ e : Fin n → F,
        (∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) ∧
          (∀ i j, inner ℝ (L (e i)) (e j) = 0) := by
  intro n
  induction n with
  | zero =>
      intro F _ _ _ L hskew hsq hfin
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      constructor <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
      intro F _ _ _ L hskew hsq hfin
      classical
      have hpos : 0 < Module.finrank ℝ F := by
        rw [hfin]
        omega
      let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F :=
        stdOrthonormalBasis ℝ F
      let i₀ : Fin (Module.finrank ℝ F) := ⟨0, hpos⟩
      let v : F := b₀ i₀
      have hvv : inner ℝ v v = 1 := by
        simp [v, b₀]
      have hLv_v : inner ℝ (L v) v = 0 := by
        have h := hskew v v
        have hsym : inner ℝ v (L v) = inner ℝ (L v) v :=
          real_inner_comm (L v) v
        linarith
      have hv_Lv : inner ℝ v (L v) = 0 := by
        simpa [real_inner_comm] using hLv_v
      have hLvLv : inner ℝ (L v) (L v) = 1 := by
        calc
          inner ℝ (L v) (L v) = -inner ℝ v (L (L v)) := hskew v (L v)
          _ = -inner ℝ v (-v) := by rw [hsq v]
          _ = inner ℝ v v := by simp
          _ = 1 := hvv
      let pair : Fin 2 → F := ![v, L v]
      have hpair : Orthonormal ℝ pair := by
        rw [orthonormal_iff_ite]
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [pair] using hvv
        · simpa [pair] using hv_Lv
        · simpa [pair] using hLv_v
        · simpa [pair] using hLvLv
      let P : Submodule ℝ F := Submodule.span ℝ (Set.range pair)
      have hvP : v ∈ P := by
        exact Submodule.subset_span ⟨0, by simp [pair]⟩
      have hLvP : L v ∈ P := by
        exact Submodule.subset_span ⟨1, by simp [pair]⟩
      have hfinP : Module.finrank ℝ P = 2 := by
        have hli : LinearIndependent ℝ pair := hpair.linearIndependent
        simpa [P] using (finrank_span_eq_card (R := ℝ) hli)
      have hLP : ∀ u : F, u ∈ P → L u ∈ P := by
        intro u hu
        refine Submodule.span_induction (p := fun x _ => L x ∈ P) ?_ ?_ ?_ ?_ hu
        · intro x hx
          rcases hx with ⟨i, rfl⟩
          fin_cases i
          · exact hLvP
          · simpa [pair, hsq v] using P.neg_mem hvP
        · simp
        · intro x y hx hy hxL hyL
          simpa [map_add] using P.add_mem hxL hyL
        · intro a x hx hxL
          simpa using P.smul_mem a hxL
      let K : Submodule ℝ F := Pᗮ
      have hLK_mem : ∀ x : K, L x.1 ∈ K := by
        intro x
        rw [Submodule.mem_orthogonal]
        intro u hu
        have hLu : L u ∈ P := hLP u hu
        have horth : inner ℝ (L u) x.1 = 0 :=
          Submodule.inner_right_of_mem_orthogonal (K := P) hLu x.2
        have h := hskew u x.1
        linarith
      let LK : K →ₗ[ℝ] K :=
        { toFun := fun x => ⟨L x.1, hLK_mem x⟩
          map_add' := by
            intro x y
            ext
            simp [map_add]
          map_smul' := by
            intro a x
            ext
            simp }
      have hskewK :
          ∀ x y : K, inner ℝ (LK x) y = -inner ℝ x (LK y) := by
        intro x y
        simpa [LK] using hskew x.1 y.1
      have hsqK : ∀ x : K, LK (LK x) = -x := by
        intro x
        ext
        simpa [LK] using hsq x.1
      have hfinK : Module.finrank ℝ K = 2 * n := by
        have hsum : Module.finrank ℝ P + Module.finrank ℝ K = Module.finrank ℝ F := by
          simpa [K] using Submodule.finrank_add_finrank_orthogonal P
        rw [hfinP, hfin] at hsum
        omega
      rcases ih LK hskewK hsqK hfinK with ⟨tail, htailON, htailL⟩
      let e : Fin (n + 1) → F := Fin.cases v (fun i => (tail i : F))
      refine ⟨e, ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · simpa [e] using hvv
          · intro j
            have horth : inner ℝ v (tail j : F) = 0 :=
              Submodule.inner_right_of_mem_orthogonal (K := P) hvP (tail j).2
            simpa [e] using horth
        · intro i
          refine Fin.cases ?_ ?_ j
          · have horth : inner ℝ (tail i : F) v = 0 :=
              Submodule.inner_left_of_mem_orthogonal (K := P) hvP (tail i).2
            simpa [e] using horth
          · intro j
            simpa [e] using htailON i j
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · simpa [e] using hLv_v
          · intro j
            have horth : inner ℝ (L v) (tail j : F) = 0 :=
              Submodule.inner_right_of_mem_orthogonal (K := P) hLvP (tail j).2
            simpa [e] using horth
        · intro i
          refine Fin.cases ?_ ?_ j
          · have horth : inner ℝ (L (tail i : F)) v = 0 :=
              Submodule.inner_left_of_mem_orthogonal (K := P) hvP (hLK_mem (tail i))
            simpa [e] using horth
          · intro j
            simpa [e, LK] using htailL i j

/-- Build an adapted symplectic basis from a `J`-fixed isotropic family whose
`L`-translates give an orthonormal partner for the Cartan metric. -/
private theorem symplecticAdaptedBasis_of_isotropic_g_orthonormal
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {r : ℕ} (J : JStructure Sign.neg V Sign.pos)
    (L : LStructure Sign.neg V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r)
    (hcompat : JLCompatible J L)
    (e : Fin r → V)
    (hJ : ∀ i, J (e i) = e i)
    (hIso : ∀ i j, FormedSpace.B Sign.neg V (e i) (e j) = 0)
    (hG : ∀ i j,
      FormedSpace.B Sign.neg V (L (e i)) (e j) = if i = j then 1 else 0) :
    Nonempty (SymplecticAdaptedBasis r V J L) := by
  classical
  let v : Fin r ⊕ Fin r → V
    | Sum.inl i => e i
    | Sum.inr i => -L (e i)
  have h_inl_inl :
      ∀ i j, FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inl j)) = 0 := by
    intro i j
    simpa [v] using hIso i j
  have h_inr_inr :
      ∀ i j, FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inr j)) = 0 := by
    intro i j
    have hpres := L.preserves_form (e i) (e j)
    simp [v, hpres, hIso i j]
  have h_inl_inr :
      ∀ i j,
        FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inr j)) =
          if i = j then 1 else 0 := by
    intro i j
    have hsym := FormedSpace.eps_symm (eps := Sign.neg) (V := V) (e i) (L (e j))
    have hswap :
        FormedSpace.B Sign.neg V (e i) (L (e j)) =
          -FormedSpace.B Sign.neg V (L (e j)) (e i) := by
      simpa [FormedSpace.B, Sign.toComplex_neg] using hsym
    calc
      FormedSpace.B Sign.neg V (v (Sum.inl i)) (v (Sum.inr j))
          = -FormedSpace.B Sign.neg V (e i) (L (e j)) := by
            simp [v]
      _ = FormedSpace.B Sign.neg V (L (e j)) (e i) := by
            rw [hswap]
            simp
      _ = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · subst j
              simpa using hG i i
            · have hji : j ≠ i := fun h => hij h.symm
              simpa [hij, hji] using hG j i
  have h_inr_inl :
      ∀ i j,
        FormedSpace.B Sign.neg V (v (Sum.inr i)) (v (Sum.inl j)) =
          if i = j then -1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [v] using congrArg Neg.neg (hG i i)
    · simpa [v, hij] using congrArg Neg.neg (hG i j)
  let basis : Module.Basis (Fin r ⊕ Fin r) ℂ V :=
    basisOfSymplecticGram v hfin h_inl_inl h_inr_inr h_inl_inr h_inr_inl
  refine ⟨
    { basis := basis
      J_basis := ?_
      L_inl := ?_
      L_inr := ?_
      form_inl_inl := ?_
      form_inr_inr := ?_
      form_inl_inr := ?_
      form_inr_inl := ?_ }⟩
  · intro idx
    cases idx with
    | inl i =>
        simpa [basis, basisOfSymplecticGram, v] using hJ i
    | inr i =>
        have hJL_e : J (L (e i)) = L (e i) := by
          rw [← hcompat.commute (e i), hJ i]
        simp [basis, basisOfSymplecticGram, v, hJL_e]
  · intro i
    simp [basis, basisOfSymplecticGram, v]
  · intro i
    have hsq : L (L (e i)) = -e i := by
      simpa [Sign.toComplex_neg] using L.sq (e i)
    simp [basis, basisOfSymplecticGram, v, hsq]
  · intro i j
    simpa [basis, basisOfSymplecticGram] using h_inl_inl i j
  · intro i j
    simpa [basis, basisOfSymplecticGram] using h_inr_inr i j
  · intro i j
    simpa [basis, basisOfSymplecticGram] using h_inl_inr i j
  · intro i j
    simpa [basis, basisOfSymplecticGram] using h_inr_inl i j

/-- Existence of an adapted symplectic basis from the `C`/`Ctilda` hypotheses.

This is the compatible symplectic Gram-Schmidt part of the proof. -/
theorem symplecticAdaptedBasis_exists (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.pos)
    (L : LStructure Sign.neg V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r)
    (hcompat : JLCompatible J L) :
    Nonempty (SymplecticAdaptedBasis r V J L) := by
  /-
  Proof target:
  * pass to `V^J`;
  * define the real symplectic form `ω` and positive metric `g`;
  * prove the `g`-orthogonal complement induction is `L`-stable and symplectic;
  * produce `e_i,f_i=-L e_i` and complexify.
  -/
  classical
  suffices h_e :
      ∃ e : Fin r → V,
        (∀ i, J (e i) = e i) ∧
          (∀ i j, FormedSpace.B Sign.neg V (e i) (e j) = 0) ∧
            (∀ i j,
              FormedSpace.B Sign.neg V (L (e i)) (e j) =
                if i = j then 1 else 0) by
    rcases h_e with ⟨e, hJ, hIso, hG⟩
    exact symplecticAdaptedBasis_of_isotropic_g_orthonormal J L hfin hcompat e hJ hIso hG
  -- Remaining blueprint subgoal: run compatible symplectic Gram-Schmidt on the
  -- positive real inner product `symplecticJFixedInnerCore J L hcompat`.
  let F := JFixedRealSubmodule V J
  let core : InnerProductSpace.Core ℝ F := symplecticJFixedInnerCore J L hcompat
  letI : InnerProductSpace.Core ℝ F := core
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : NormedSpace ℝ F := InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)
  letI : InnerProductSpace ℝ F := InnerProductSpace.ofCore core.toCore
  let Lfixed : F →ₗ[ℝ] F :=
    { toFun := fun x => ⟨L x.1, L_mem_JFixedRealSubmodule_of_commute J L hcompat x.2⟩
      map_add' := by
        intro x y
        ext
        simp [map_add]
      map_smul' := by
        intro a x
        ext
        change L.toLinearEquiv ((a : ℂ) • x.1) = (a : ℂ) • L.toLinearEquiv x.1
        simpa using L.toLinearEquiv.map_smul (a : ℂ) x.1 }
  have hskew :
      ∀ x y : F, inner ℝ (Lfixed x) y = -inner ℝ x (Lfixed y) := by
    intro x y
    change
      (FormedSpace.B Sign.neg V (L (L x.1)) y.1).re =
        -(FormedSpace.B Sign.neg V (L x.1) (L y.1)).re
    have hsqx : L (L x.1) = -x.1 := by
      simpa [Sign.toComplex_neg] using L.sq x.1
    have hpres :
        FormedSpace.B Sign.neg V (L x.1) (L y.1) =
          FormedSpace.B Sign.neg V x.1 y.1 :=
      L.preserves_form x.1 y.1
    rw [hsqx, hpres]
    simp
  have hsq : ∀ x : F, Lfixed (Lfixed x) = -x := by
    intro x
    ext
    change L (L x.1) = -x.1
    simpa [Sign.toComplex_neg] using L.sq x.1
  have hfinF : Module.finrank ℝ F = 2 * r := by
    rw [finrank_JFixedRealSubmodule_eq_complex J, hfin]
    omega
  rcases symplecticCompatibleFamily_exists r Lfixed hskew hsq hfinF with
    ⟨eF, hON, hLorth⟩
  refine ⟨fun i => (eF i : V), ?_, ?_, ?_⟩
  · intro i
    exact (eF i).2
  · intro i j
    have hstar :
        (starRingEnd ℂ) (FormedSpace.B Sign.neg V (eF i : V) (eF j : V)) =
          FormedSpace.B Sign.neg V (eF i : V) (eF j : V) :=
      form_star_eq_of_mem_JFixedRealSubmodule J (eF i).2 (eF j).2
    have hre :
        (FormedSpace.B Sign.neg V (eF i : V) (eF j : V)).re = (0 : ℝ) := by
      have h := hLorth i j
      change
        (FormedSpace.B Sign.neg V (L (L (eF i).1)) (eF j).1).re = 0 at h
      have hsqe : L (L (eF i).1) = -(eF i).1 := by
        simpa [Sign.toComplex_neg] using L.sq (eF i).1
      rw [hsqe] at h
      simpa using h
    have hcomplex := complex_eq_of_star_eq_of_re_eq hstar hre
    simpa using hcomplex
  · intro i j
    have hstar :
        (starRingEnd ℂ) (FormedSpace.B Sign.neg V (L (eF i : V)) (eF j : V)) =
          FormedSpace.B Sign.neg V (L (eF i : V)) (eF j : V) := by
      simpa [Lfixed] using
        form_star_eq_of_mem_JFixedRealSubmodule J (Lfixed (eF i)).2 (eF j).2
    have hre :
        (FormedSpace.B Sign.neg V (L (eF i : V)) (eF j : V)).re =
          (if i = j then 1 else 0 : ℝ) := by
      have h := hON i j
      change
        (FormedSpace.B Sign.neg V (L (eF i).1) (eF j).1).re =
          (if i = j then 1 else 0 : ℝ) at h
      exact h
    have hcomplex := complex_eq_of_star_eq_of_re_eq hstar hre
    by_cases hij : i = j <;> simpa [hij] using hcomplex

/-- Raw real symplectic normal form for the `C`/`Ctilda` linear data.

This is the compatible symplectic Gram-Schmidt core: on `V^J`, the form
`ω(x,y)=B(x,y)` and metric `g(x,y)=B(Lx,y)` produce an adapted basis
`e_i,f_i=-Le_i`. -/
theorem symplecticNormalFormIso (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.pos)
    (L : LStructure Sign.neg V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r)
    (hcompat : JLCompatible J L) :
    Nonempty
      { e : FormedSpaceIso Sign.neg V (PairVec r) //
          (∀ v : V, e.toLinearEquiv (J v) = sympRealJ r (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = sympL r (e.toLinearEquiv v)) } := by
  rcases symplecticAdaptedBasis_exists r V J L hfin hcompat with ⟨A⟩
  exact A.toNormalFormIso

/-- Normal form for the `C` family.

Blueprint content: on the real form `V^J`, put
`ω(x,y)=B(x,y)` and `g(x,y)=B(Lx,y)`.  Then `ω` is real symplectic, `g` is
positive definite, and `L` is a compatible complex structure.  A symplectic
Gram-Schmidt construction gives a basis `e_i,f_i=-Le_i`. -/
theorem normalForm_C (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.C.eps V]
    (J : JStructure ClassicalStar.C.eps V ClassicalStar.C.jSign)
    (L : LStructure ClassicalStar.C.eps V ClassicalStar.C.dotEps)
    (hV : IsClassicalSpace ClassicalStar.C r r V J L) :
    Nonempty (ClassicalSpaceIso ClassicalStar.C V (PairVec r) J L (sympRealJ r) (sympL r)) := by
  rcases symplecticNormalFormIso r V J L (isClassicalSpace_finrank hV)
      (isClassicalSpace_compatible hV) with ⟨e, hJ, hL⟩
  exact ⟨{ toFormedSpaceIso := e, intertwines_J := hJ, intertwines_L := hL }⟩

/-- Normal form for the `Ctilda` family.

The metaplectic cover is not part of the `J,L` data, so the linear normal form
is the same as for `C`. -/
theorem normalForm_Ctilda (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.Ctilda.eps V]
    (J : JStructure ClassicalStar.Ctilda.eps V ClassicalStar.Ctilda.jSign)
    (L : LStructure ClassicalStar.Ctilda.eps V ClassicalStar.Ctilda.dotEps)
    (hV : IsClassicalSpace ClassicalStar.Ctilda r r V J L) :
    Nonempty
      (ClassicalSpaceIso ClassicalStar.Ctilda V (PairVec r) J L (sympRealJ r) (sympL r)) := by
  have hC : IsClassicalSpace ClassicalStar.C r r V J L := by
    simpa [IsClassicalSpace, IsClassicalSignature, LSignatureCondition] using hV
  rcases normalForm_C r V J L hC with ⟨e⟩
  exact ⟨{ toFormedSpaceIso := e.toFormedSpaceIso
           intertwines_J := e.intertwines_J
           intertwines_L := e.intertwines_L }⟩

/-! ## Quaternionic normal forms: `C*` and `D*` -/

/-- Quaternionic Gram-Schmidt for a finite-dimensional complex inner-product
space with an antiunitary operator squaring to `-1`. -/
private theorem quaternionicCompatibleFamily_exists :
    ∀ (n : ℕ), ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
      [FiniteDimensional ℂ F],
      (J : F ≃ₛₗ[starRingEnd ℂ] F) →
      (∀ x : F, J (J x) = -x) →
      (∀ x y : F, inner ℂ (J x) (J y) = inner ℂ y x) →
      Module.finrank ℂ F = 2 * n →
      ∃ e : Fin n → F,
        (∀ i j, inner ℂ (e i) (e j) = if i = j then 1 else 0) ∧
          (∀ i j, inner ℂ (J (e i)) (e j) = 0) := by
  intro n
  induction n with
  | zero =>
      intro F _ _ _ J hsq hanti hfin
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      constructor <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
      intro F _ _ _ J hsq hanti hfin
      classical
      have hpos : 0 < Module.finrank ℂ F := by
        rw [hfin]
        omega
      let b₀ : OrthonormalBasis (Fin (Module.finrank ℂ F)) ℂ F :=
        stdOrthonormalBasis ℂ F
      let i₀ : Fin (Module.finrank ℂ F) := ⟨0, hpos⟩
      let v : F := b₀ i₀
      have hvv : inner ℂ v v = 1 := by
        simp [v, b₀]
      have hv_Jv : inner ℂ v (J v) = 0 := by
        have h := hanti (J v) v
        rw [hsq v] at h
        simp at h
        have hadd : inner ℂ v (J v) + inner ℂ v (J v) = 0 := by
          calc
            inner ℂ v (J v) + inner ℂ v (J v) = -inner ℂ v (J v) + inner ℂ v (J v) := by
              rw [h]
            _ = 0 := by simp
        have htwo : (2 : ℂ) * inner ℂ v (J v) = 0 := by
          simpa [two_mul] using hadd
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hJv_v : inner ℂ (J v) v = 0 := by
        have hstar := congrArg (starRingEnd ℂ) hv_Jv
        simpa [inner_conj_symm] using hstar
      have hJvJv : inner ℂ (J v) (J v) = 1 := by
        have h := hanti v v
        rw [hvv] at h
        exact h
      let pair : Fin 2 → F := ![v, J v]
      have hpair : Orthonormal ℂ pair := by
        rw [orthonormal_iff_ite]
        intro i j
        fin_cases i <;> fin_cases j
        · simpa [pair] using hvv
        · simpa [pair] using hv_Jv
        · simpa [pair] using hJv_v
        · simpa [pair] using hJvJv
      let P : Submodule ℂ F := Submodule.span ℂ (Set.range pair)
      have hvP : v ∈ P := by
        exact Submodule.subset_span ⟨0, by simp [pair]⟩
      have hJvP : J v ∈ P := by
        exact Submodule.subset_span ⟨1, by simp [pair]⟩
      have hfinP : Module.finrank ℂ P = 2 := by
        have hli : LinearIndependent ℂ pair := hpair.linearIndependent
        simpa [P] using (finrank_span_eq_card (R := ℂ) hli)
      have hJP : ∀ u : F, u ∈ P → J u ∈ P := by
        intro u hu
        refine Submodule.span_induction (p := fun x _ => J x ∈ P) ?_ ?_ ?_ ?_ hu
        · intro x hx
          rcases hx with ⟨i, rfl⟩
          fin_cases i
          · exact hJvP
          · simpa [pair, hsq v] using P.neg_mem hvP
        · simp
        · intro x y hx hy hxJ hyJ
          simpa [map_add] using P.add_mem hxJ hyJ
        · intro a x hx hxJ
          have hsmul : J (a • x) = (starRingEnd ℂ) a • J x := by
            simpa using J.map_smulₛₗ a x
          rw [hsmul]
          exact P.smul_mem ((starRingEnd ℂ) a) hxJ
      let K : Submodule ℂ F := Pᗮ
      have hJK_mem : ∀ x : K, J x.1 ∈ K := by
        intro x
        rw [Submodule.mem_orthogonal]
        intro u hu
        have hJu : J u ∈ P := hJP u hu
        have horth : inner ℂ (J u) x.1 = 0 :=
          Submodule.inner_right_of_mem_orthogonal (K := P) hJu x.2
        have htmp : inner ℂ (J x.1) u = 0 := by
          have h := hanti u (J x.1)
          rw [hsq x.1] at h
          simp [horth] at h
          exact h.symm
        have hstar : (starRingEnd ℂ) (inner ℂ u (J x.1)) = 0 := by
          rw [inner_conj_symm]
          exact htmp
        have hgoal := congrArg (starRingEnd ℂ) hstar
        simpa using hgoal
      have hmapK : K.map (J : F →ₛₗ[starRingEnd ℂ] F) = K := by
        ext y
        rw [Submodule.mem_map]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hJK_mem ⟨x, hx⟩
        · intro hy
          refine ⟨-J y, ?_, ?_⟩
          · exact K.neg_mem (hJK_mem ⟨y, hy⟩)
          · simp [map_neg, hsq y]
      let JK : K ≃ₛₗ[starRingEnd ℂ] K := J.ofSubmodules K K hmapK
      have hsqK : ∀ x : K, JK (JK x) = -x := by
        intro x
        ext
        simpa [JK] using hsq x.1
      have hantiK : ∀ x y : K, inner ℂ (JK x) (JK y) = inner ℂ y x := by
        intro x y
        simpa [JK] using hanti x.1 y.1
      have hfinK : Module.finrank ℂ K = 2 * n := by
        have hsum : Module.finrank ℂ P + Module.finrank ℂ K = Module.finrank ℂ F := by
          simpa [K] using Submodule.finrank_add_finrank_orthogonal P
        rw [hfinP, hfin] at hsum
        omega
      rcases ih JK hsqK hantiK hfinK with ⟨tail, htailON, htailJorth⟩
      let e : Fin (n + 1) → F := Fin.cases v (fun i => (tail i : F))
      refine ⟨e, ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · simpa [e] using hvv
          · intro j
            have horth : inner ℂ v (tail j : F) = 0 :=
              Submodule.inner_right_of_mem_orthogonal (K := P) hvP (tail j).2
            simpa [e] using horth
        · intro i
          refine Fin.cases ?_ ?_ j
          · have horth : inner ℂ (tail i : F) v = 0 :=
              Submodule.inner_left_of_mem_orthogonal (K := P) hvP (tail i).2
            simpa [e] using horth
          · intro j
            simpa [e] using htailON i j
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · simpa [e] using hJv_v
          · intro j
            have horth : inner ℂ (J v) (tail j : F) = 0 :=
              Submodule.inner_right_of_mem_orthogonal (K := P) hJvP (tail j).2
            simpa [e] using horth
        · intro i
          refine Fin.cases ?_ ?_ j
          · have horth : inner ℂ (J (tail i : F)) v = 0 :=
              Submodule.inner_left_of_mem_orthogonal (K := P) hvP (hJK_mem (tail i))
            simpa [e] using horth
          · intro j
            simpa [e, JK] using htailJorth i j

/-- Basis index for the `C*` model:
positive `e,f` block followed by negative `e,f` block. -/
abbrev CstarIndex (a b : ℕ) : Type :=
  (Fin a ⊕ Fin a) ⊕ (Fin b ⊕ Fin b)

/-- The target Gram matrix for a `C*` adapted basis. -/
def cstarGram (a b : ℕ) : CstarIndex a b → CstarIndex a b → ℂ
  | Sum.inl (Sum.inl i), Sum.inl (Sum.inr j) => if i = j then 1 else 0
  | Sum.inl (Sum.inr i), Sum.inl (Sum.inl j) => if i = j then -1 else 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr j) => if i = j then -1 else 0
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inl j) => if i = j then 1 else 0
  | _, _ => 0

/-- Coordinate equivalence from the nested `C*` basis-index functions to the
explicit product model `(PairVec a) × (PairVec b)`. -/
noncomputable def cstarCoordLinearEquiv (a b : ℕ) :
    (CstarIndex a b → ℂ) ≃ₗ[ℂ] CstarVec a b :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a ⊕ Fin a) (Fin b ⊕ Fin b) ℂ ℂ).trans
    (LinearEquiv.prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin a) ℂ ℂ)
      (LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin b) ℂ ℂ))

private theorem star_pi_single_one {ι : Type*} [DecidableEq ι] (i k : ι) :
    (starRingEnd ℂ) (((Pi.single i (1 : ℂ) : ι → ℂ) k)) =
      ((Pi.single i (1 : ℂ) : ι → ℂ) k) := by
  by_cases h : k = i
  · subst k
    simp
  · simp [Pi.single_eq_of_ne h]

private theorem dot_pi_single_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    dot (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) = if i = j then 1 else 0 := by
  rw [dot_single_left]
  by_cases h : i = j
  · subst i
    simp
  · rw [if_neg h]
    simp [Pi.single_eq_of_ne h]

private theorem fs_cstar_pos_e_pos_e {a b : ℕ} (i k : Fin a) :
    (Finsupp.single (Sum.inl (Sum.inl i) : CstarIndex a b) (1 : ℂ))
        (Sum.inl (Sum.inl k)) =
      ((Pi.single i (1 : ℂ) : Fin a → ℂ) k) := by
  by_cases h : k = i
  · subst k
    simp
  · have hsum : (Sum.inl (Sum.inl i) : CstarIndex a b) ≠ Sum.inl (Sum.inl k) := by
      intro h'
      exact h (Sum.inl.inj (Sum.inl.inj h')).symm
    simp [Finsupp.single_eq_of_ne' hsum, Pi.single_eq_of_ne h]

private theorem fs_cstar_pos_f_pos_f {a b : ℕ} (i k : Fin a) :
    (Finsupp.single (Sum.inl (Sum.inr i) : CstarIndex a b) (1 : ℂ))
        (Sum.inl (Sum.inr k)) =
      ((Pi.single i (1 : ℂ) : Fin a → ℂ) k) := by
  by_cases h : k = i
  · subst k
    simp
  · have hsum : (Sum.inl (Sum.inr i) : CstarIndex a b) ≠ Sum.inl (Sum.inr k) := by
      intro h'
      exact h (Sum.inr.inj (Sum.inl.inj h')).symm
    simp [Finsupp.single_eq_of_ne' hsum, Pi.single_eq_of_ne h]

private theorem fs_cstar_neg_e_neg_e {a b : ℕ} (i k : Fin b) :
    (Finsupp.single (Sum.inr (Sum.inl i) : CstarIndex a b) (1 : ℂ))
        (Sum.inr (Sum.inl k)) =
      ((Pi.single i (1 : ℂ) : Fin b → ℂ) k) := by
  by_cases h : k = i
  · subst k
    simp
  · have hsum : (Sum.inr (Sum.inl i) : CstarIndex a b) ≠ Sum.inr (Sum.inl k) := by
      intro h'
      exact h (Sum.inl.inj (Sum.inr.inj h')).symm
    simp [Finsupp.single_eq_of_ne' hsum, Pi.single_eq_of_ne h]

private theorem fs_cstar_neg_f_neg_f {a b : ℕ} (i k : Fin b) :
    (Finsupp.single (Sum.inr (Sum.inr i) : CstarIndex a b) (1 : ℂ))
        (Sum.inr (Sum.inr k)) =
      ((Pi.single i (1 : ℂ) : Fin b → ℂ) k) := by
  by_cases h : k = i
  · subst k
    simp
  · have hsum : (Sum.inr (Sum.inr i) : CstarIndex a b) ≠ Sum.inr (Sum.inr k) := by
      intro h'
      exact h (Sum.inr.inj (Sum.inr.inj h')).symm
    simp [Finsupp.single_eq_of_ne' hsum, Pi.single_eq_of_ne h]

private theorem cstarCoord_pos_e (a b : ℕ) (i : Fin a) :
    cstarCoordLinearEquiv a b
        (Finsupp.single (Sum.inl (Sum.inl i) : CstarIndex a b) (1 : ℂ)) =
      ((Pi.single i 1, 0), 0) := by
  ext k <;> simp [cstarCoordLinearEquiv, LinearEquiv.prodCongr_apply,
    fs_cstar_pos_e_pos_e]

private theorem cstarCoord_pos_f (a b : ℕ) (i : Fin a) :
    cstarCoordLinearEquiv a b
        (Finsupp.single (Sum.inl (Sum.inr i) : CstarIndex a b) (1 : ℂ)) =
      ((0, Pi.single i 1), 0) := by
  ext k <;> simp [cstarCoordLinearEquiv, LinearEquiv.prodCongr_apply,
    fs_cstar_pos_f_pos_f]

private theorem cstarCoord_neg_e (a b : ℕ) (i : Fin b) :
    cstarCoordLinearEquiv a b
        (Finsupp.single (Sum.inr (Sum.inl i) : CstarIndex a b) (1 : ℂ)) =
      (0, (Pi.single i 1, 0)) := by
  ext k <;> simp [cstarCoordLinearEquiv, LinearEquiv.prodCongr_apply,
    fs_cstar_neg_e_neg_e]

private theorem cstarCoord_neg_f (a b : ℕ) (i : Fin b) :
    cstarCoordLinearEquiv a b
        (Finsupp.single (Sum.inr (Sum.inr i) : CstarIndex a b) (1 : ℂ)) =
      (0, (0, Pi.single i 1)) := by
  ext k <;> simp [cstarCoordLinearEquiv, LinearEquiv.prodCongr_apply,
    fs_cstar_neg_f_neg_f]

/-- A family with the standard `C*` Gram matrix is linearly independent. -/
private theorem cstar_gram_linearIndependent
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {a b : ℕ} {v : CstarIndex a b → V}
    (hgram : ∀ i j, FormedSpace.B Sign.neg V (v i) (v j) = cstarGram a b i j) :
    LinearIndependent ℂ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  rcases k with (_ | _) | (_ | _)
  · rename_i i
    have hBsum_zero :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl (Sum.inr i))) = 0 := by
      rw [hsum]
      simp
    have hcalc :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl (Sum.inr i))) =
          c (Sum.inl (Sum.inl i)) := by
      simp [hgram, cstarGram, Finset.sum_ite_eq', Finset.mem_univ]
    rw [← hcalc]
    exact hBsum_zero
  · rename_i i
    have hBsum_zero :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl (Sum.inl i))) = 0 := by
      rw [hsum]
      simp
    have hcalc :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inl (Sum.inl i))) =
          -c (Sum.inl (Sum.inr i)) := by
      simp [hgram, cstarGram, Finset.sum_ite_eq', Finset.mem_univ]
    have hneg : -c (Sum.inl (Sum.inr i)) = 0 := by
      rw [← hcalc]
      exact hBsum_zero
    simpa using neg_eq_zero.mp hneg
  · rename_i i
    have hBsum_zero :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr (Sum.inr i))) = 0 := by
      rw [hsum]
      simp
    have hcalc :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr (Sum.inr i))) =
          -c (Sum.inr (Sum.inl i)) := by
      simp [hgram, cstarGram, Finset.sum_ite_eq', Finset.mem_univ]
    have hneg : -c (Sum.inr (Sum.inl i)) = 0 := by
      rw [← hcalc]
      exact hBsum_zero
    simpa using neg_eq_zero.mp hneg
  · rename_i i
    have hBsum_zero :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr (Sum.inl i))) = 0 := by
      rw [hsum]
      simp
    have hcalc :
        FormedSpace.B Sign.neg V (∑ j, c j • v j) (v (Sum.inr (Sum.inl i))) =
          c (Sum.inr (Sum.inr i)) := by
      simp [hgram, cstarGram, Finset.sum_ite_eq', Finset.mem_univ]
    rw [← hcalc]
    exact hBsum_zero

/-- Promote a standard `C*` Gram family to a basis when the cardinality matches
the complex dimension. -/
private noncomputable def basisOfCstarGram
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {a b : ℕ} (v : CstarIndex a b → V)
    (hfin : Module.finrank ℂ V = 2 * a + 2 * b)
    (hgram : ∀ i j, FormedSpace.B Sign.neg V (v i) (v j) = cstarGram a b i j) :
    Module.Basis (CstarIndex a b) ℂ V := by
  classical
  have hli : LinearIndependent ℂ v := cstar_gram_linearIndependent hgram
  refine Module.Basis.mk hli ?_
  have hcard : Fintype.card (CstarIndex a b) = Module.finrank ℂ V := by
    rw [hfin]
    simp [CstarIndex]
    omega
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  rw [hspan]

/-- Adapted quaternionic basis data for the `C*` normal form. -/
structure CstarAdaptedBasis (a b : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg) (L : LStructure Sign.neg V Sign.pos) where
  /-- The adapted complex basis. -/
  basis : Module.Basis (CstarIndex a b) ℂ V
  /-- `J` sends positive `e` to positive `f`. -/
  J_pos_e : ∀ i, J (basis (Sum.inl (Sum.inl i))) = basis (Sum.inl (Sum.inr i))
  /-- `J` sends positive `f` to `-e`. -/
  J_pos_f : ∀ i, J (basis (Sum.inl (Sum.inr i))) = -basis (Sum.inl (Sum.inl i))
  /-- `J` sends negative `e` to negative `f`. -/
  J_neg_e : ∀ i, J (basis (Sum.inr (Sum.inl i))) = basis (Sum.inr (Sum.inr i))
  /-- `J` sends negative `f` to `-e`. -/
  J_neg_f : ∀ i, J (basis (Sum.inr (Sum.inr i))) = -basis (Sum.inr (Sum.inl i))
  /-- `L=+1` on the positive quaternionic block. -/
  L_pos_e : ∀ i, L (basis (Sum.inl (Sum.inl i))) = basis (Sum.inl (Sum.inl i))
  /-- `L=+1` on the positive quaternionic block. -/
  L_pos_f : ∀ i, L (basis (Sum.inl (Sum.inr i))) = basis (Sum.inl (Sum.inr i))
  /-- `L=-1` on the negative quaternionic block. -/
  L_neg_e : ∀ i, L (basis (Sum.inr (Sum.inl i))) = -basis (Sum.inr (Sum.inl i))
  /-- `L=-1` on the negative quaternionic block. -/
  L_neg_f : ∀ i, L (basis (Sum.inr (Sum.inr i))) = -basis (Sum.inr (Sum.inr i))
  /-- The Gram matrix is the standard `C*` Gram matrix. -/
  form_basis :
    ∀ i j, FormedSpace.B Sign.neg V (basis i) (basis j) = cstarGram a b i j

namespace CstarAdaptedBasis

/-- Coordinate equivalence associated to an adapted `C*` basis. -/
noncomputable def toLinearEquiv {a b : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.neg} {L : LStructure Sign.neg V Sign.pos}
    (A : CstarAdaptedBasis a b V J L) : V ≃ₗ[ℂ] CstarVec a b :=
  A.basis.equivFun.trans (cstarCoordLinearEquiv a b)

/-- The coordinate map attached to an adapted `C*` basis intertwines `L`. -/
theorem intertwines_L {a b : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.neg} {L : LStructure Sign.neg V Sign.pos}
    (A : CstarAdaptedBasis a b V J L) :
    ∀ v : V, A.toLinearEquiv (L v) = cstarL a b (A.toLinearEquiv v) := by
  let f₁ : V →ₗ[ℂ] CstarVec a b :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap.comp L.toLinearMap
  let f₂ : V →ₗ[ℂ] CstarVec a b :=
    (cstarL a b).toLinearMap.comp (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    rcases idx with (_ | _) | (_ | _)
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_pos_e, cstarL,
        prodSignLinearEquiv, cstarCoord_pos_e]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_pos_f, cstarL,
        prodSignLinearEquiv, cstarCoord_pos_f]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_neg_e, cstarL,
        prodSignLinearEquiv, cstarCoord_neg_e]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_neg_f, cstarL,
        prodSignLinearEquiv, cstarCoord_neg_f]
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an adapted `C*` basis intertwines `J`. -/
theorem intertwines_J {a b : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.neg} {L : LStructure Sign.neg V Sign.pos}
    (A : CstarAdaptedBasis a b V J L) :
    ∀ v : V, A.toLinearEquiv (J v) = cstarJ a b (A.toLinearEquiv v) := by
  let f₁ : V →ₛₗ[starRingEnd ℂ] CstarVec a b :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap.comp J.toSemilinearMap
  let f₂ : V →ₛₗ[starRingEnd ℂ] CstarVec a b :=
    (cstarJ a b).toSemilinearMap.comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    rcases idx with (_ | _) | (_ | _)
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.J_pos_e, cstarJ,
        cstarJSemilinearEquiv, quatJEquiv, cstarCoord_pos_e, cstarCoord_pos_f,
        star_pi_single_one]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.J_pos_f, cstarJ,
        cstarJSemilinearEquiv, quatJEquiv, cstarCoord_pos_e, cstarCoord_pos_f,
        star_pi_single_one]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.J_neg_e, cstarJ,
        cstarJSemilinearEquiv, quatJEquiv, cstarCoord_neg_e, cstarCoord_neg_f,
        star_pi_single_one]
    · ext k <;> simp [f₁, f₂, toLinearEquiv, A.J_neg_f, cstarJ,
        cstarJSemilinearEquiv, quatJEquiv, cstarCoord_neg_e, cstarCoord_neg_f,
        star_pi_single_one]
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an adapted `C*` basis preserves the bilinear
forms. -/
theorem preserves_form {a b : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.neg} {L : LStructure Sign.neg V Sign.pos}
    (A : CstarAdaptedBasis a b V J L) :
    ∀ u v : V,
      FormedSpace.B Sign.neg (CstarVec a b) (A.toLinearEquiv u) (A.toLinearEquiv v) =
        FormedSpace.B Sign.neg V u v := by
  let Bpull : LinearMap.BilinForm ℂ V :=
    (FormedSpace.B Sign.neg (CstarVec a b)).comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap
      (A.toLinearEquiv : V ≃ₗ[ℂ] CstarVec a b).toLinearMap
  have hB : Bpull = FormedSpace.B Sign.neg V := by
    apply LinearMap.BilinForm.ext_basis A.basis
    intro i j
    rcases i with (_ | _) | (_ | _) <;> rcases j with (_ | _) | (_ | _) <;>
      simp [Bpull, toLinearEquiv, FormedSpace.B, cstarFormedSpace, cstarForm_apply,
        sympForm_apply, A.form_basis, cstarGram, cstarCoord_pos_e, cstarCoord_pos_f,
        cstarCoord_neg_e, cstarCoord_neg_f, dot_pi_single_single, dot_zero_left',
        dot_zero_right']
    all_goals
      split_ifs <;> ring
  intro u v
  have h := congrArg (fun B : LinearMap.BilinForm ℂ V => B u v) hB
  simpa [Bpull] using h

/-- An adapted `C*` basis gives the required coordinate isomorphism. -/
theorem toNormalFormIso {a b : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {J : JStructure Sign.neg V Sign.neg} {L : LStructure Sign.neg V Sign.pos}
    (A : CstarAdaptedBasis a b V J L) :
    Nonempty
      { e : FormedSpaceIso Sign.neg V (CstarVec a b) //
          ((∀ v : V, e.toLinearEquiv (J v) = cstarJ a b (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = cstarL a b (e.toLinearEquiv v))) } := by
  let e : FormedSpaceIso Sign.neg V (CstarVec a b) :=
    { toLinearEquiv := A.toLinearEquiv, preserves_form := A.preserves_form }
  exact ⟨⟨e, ⟨A.intertwines_J, A.intertwines_L⟩⟩⟩

end CstarAdaptedBasis

/-- Build a `C*` adapted basis from quaternionic orthonormal families in the
`L=+1` and `L=-1` eigenspaces. -/
private theorem cstarAdaptedBasis_of_quaternionic_families
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    {a b : ℕ} (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (hfin : Module.finrank ℂ V = 2 * a + 2 * b)
    (hcompat : JLCompatible J L)
    (ePlus : Fin a → V) (eMinus : Fin b → V)
    (hPlus_mem : ∀ i, ePlus i ∈ linearEigenspace L.toLinearEquiv 1)
    (hMinus_mem : ∀ i, eMinus i ∈ linearEigenspace L.toLinearEquiv (-1))
    (hPlus_iso : ∀ i j, FormedSpace.B Sign.neg V (ePlus i) (ePlus j) = 0)
    (hPlus_pair : ∀ i j,
      FormedSpace.B Sign.neg V (ePlus i) (J (ePlus j)) = if i = j then 1 else 0)
    (hMinus_iso : ∀ i j, FormedSpace.B Sign.neg V (eMinus i) (eMinus j) = 0)
    (hMinus_pair : ∀ i j,
      FormedSpace.B Sign.neg V (eMinus i) (J (eMinus j)) =
        if i = j then -1 else 0) :
    Nonempty (CstarAdaptedBasis a b V J L) := by
  classical
  let v : CstarIndex a b → V
    | Sum.inl (Sum.inl i) => ePlus i
    | Sum.inl (Sum.inr i) => J (ePlus i)
    | Sum.inr (Sum.inl i) => eMinus i
    | Sum.inr (Sum.inr i) => J (eMinus i)
  have hJPlus_mem :
      ∀ i, J (ePlus i) ∈ linearEigenspace L.toLinearEquiv 1 := by
    intro i
    exact linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) (hPlus_mem i)
  have hJMinus_mem :
      ∀ i, J (eMinus i) ∈ linearEigenspace L.toLinearEquiv (-1) := by
    intro i
    exact linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) (hMinus_mem i)
  have hPlus_JJ :
      ∀ i j, FormedSpace.B Sign.neg V (J (ePlus i)) (J (ePlus j)) = 0 := by
    intro i j
    have h := J.preserves_form (ePlus i) (ePlus j)
    rw [hPlus_iso i j] at h
    simpa using h
  have hMinus_JJ :
      ∀ i j, FormedSpace.B Sign.neg V (J (eMinus i)) (J (eMinus j)) = 0 := by
    intro i j
    have h := J.preserves_form (eMinus i) (eMinus j)
    rw [hMinus_iso i j] at h
    simpa using h
  have hPlus_J_e :
      ∀ i j,
        FormedSpace.B Sign.neg V (J (ePlus i)) (ePlus j) =
          if i = j then -1 else 0 := by
    intro i j
    have hsym := FormedSpace.eps_symm (eps := Sign.neg) (V := V)
      (J (ePlus i)) (ePlus j)
    by_cases hij : i = j
    · subst j
      simpa [hPlus_pair i i] using hsym
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hij, hji, hPlus_pair j i] using hsym
  have hMinus_J_e :
      ∀ i j,
        FormedSpace.B Sign.neg V (J (eMinus i)) (eMinus j) =
          if i = j then 1 else 0 := by
    intro i j
    have hsym := FormedSpace.eps_symm (eps := Sign.neg) (V := V)
      (J (eMinus i)) (eMinus j)
    by_cases hij : i = j
    · subst j
      simpa [Sign.toComplex_neg, hMinus_pair i i] using hsym
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [Sign.toComplex_neg, hij, hji, hMinus_pair j i] using hsym
  have hpos_neg :
      ∀ i j, FormedSpace.B Sign.neg V (ePlus i) (eMinus j) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (1 : ℂ) * (-1) ≠ 1)
      (hPlus_mem i) (hMinus_mem j)
  have hpos_Jneg :
      ∀ i j, FormedSpace.B Sign.neg V (ePlus i) (J (eMinus j)) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (1 : ℂ) * (-1) ≠ 1)
      (hPlus_mem i) (hJMinus_mem j)
  have hJpos_neg :
      ∀ i j, FormedSpace.B Sign.neg V (J (ePlus i)) (eMinus j) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (1 : ℂ) * (-1) ≠ 1)
      (hJPlus_mem i) (hMinus_mem j)
  have hJpos_Jneg :
      ∀ i j, FormedSpace.B Sign.neg V (J (ePlus i)) (J (eMinus j)) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (1 : ℂ) * (-1) ≠ 1)
      (hJPlus_mem i) (hJMinus_mem j)
  have hneg_pos :
      ∀ i j, FormedSpace.B Sign.neg V (eMinus i) (ePlus j) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (-1 : ℂ) * 1 ≠ 1)
      (hMinus_mem i) (hPlus_mem j)
  have hneg_Jpos :
      ∀ i j, FormedSpace.B Sign.neg V (eMinus i) (J (ePlus j)) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (-1 : ℂ) * 1 ≠ 1)
      (hMinus_mem i) (hJPlus_mem j)
  have hJneg_pos :
      ∀ i j, FormedSpace.B Sign.neg V (J (eMinus i)) (ePlus j) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (-1 : ℂ) * 1 ≠ 1)
      (hJMinus_mem i) (hPlus_mem j)
  have hJneg_Jpos :
      ∀ i j, FormedSpace.B Sign.neg V (J (eMinus i)) (J (ePlus j)) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L (by norm_num : (-1 : ℂ) * 1 ≠ 1)
      (hJMinus_mem i) (hJPlus_mem j)
  have hgram : ∀ i j, FormedSpace.B Sign.neg V (v i) (v j) = cstarGram a b i j := by
    intro i j
    rcases i with (_ | _) | (_ | _) <;> rcases j with (_ | _) | (_ | _) <;>
      simp [v, cstarGram, hPlus_iso, hPlus_pair, hPlus_J_e, hPlus_JJ, hMinus_iso,
        hMinus_pair, hMinus_J_e, hMinus_JJ, hpos_neg, hpos_Jneg, hJpos_neg,
        hJpos_Jneg, hneg_pos, hneg_Jpos, hJneg_pos, hJneg_Jpos]
  let basis : Module.Basis (CstarIndex a b) ℂ V := basisOfCstarGram v hfin hgram
  refine ⟨
    { basis := basis
      J_pos_e := ?_
      J_pos_f := ?_
      J_neg_e := ?_
      J_neg_f := ?_
      L_pos_e := ?_
      L_pos_f := ?_
      L_neg_e := ?_
      L_neg_f := ?_
      form_basis := ?_ }⟩
  · intro i
    simp [basis, basisOfCstarGram, v]
  · intro i
    have hsq : J (J (ePlus i)) = -ePlus i := by
      simpa [Sign.toComplex_neg] using J.sq (ePlus i)
    simp [basis, basisOfCstarGram, v, hsq]
  · intro i
    simp [basis, basisOfCstarGram, v]
  · intro i
    have hsq : J (J (eMinus i)) = -eMinus i := by
      simpa [Sign.toComplex_neg] using J.sq (eMinus i)
    simp [basis, basisOfCstarGram, v, hsq]
  · intro i
    have hL : L (ePlus i) = ePlus i := by
      simpa using linearEigenspace_apply_eq L (a := (1 : ℂ)) (hPlus_mem i)
    simp [basis, basisOfCstarGram, v, hL]
  · intro i
    have hL : L (J (ePlus i)) = J (ePlus i) := by
      rw [hcompat.commute (ePlus i)]
      have hLe : L (ePlus i) = ePlus i := by
        simpa using linearEigenspace_apply_eq L (a := (1 : ℂ)) (hPlus_mem i)
      rw [hLe]
    simp [basis, basisOfCstarGram, v, hL]
  · intro i
    have hL : L (eMinus i) = -eMinus i := by
      simpa using linearEigenspace_apply_eq L (a := (-1 : ℂ)) (hMinus_mem i)
    simp [basis, basisOfCstarGram, v, hL]
  · intro i
    have hL : L (J (eMinus i)) = -J (eMinus i) := by
      rw [hcompat.commute (eMinus i)]
      have hLe : L (eMinus i) = -eMinus i := by
        simpa using linearEigenspace_apply_eq L (a := (-1 : ℂ)) (hMinus_mem i)
      rw [hLe]
      simp
    simp [basis, basisOfCstarGram, v, hL]
  · intro i j
    simpa [basis, basisOfCstarGram] using hgram i j

/-- Existence of an adapted `C*` basis from the `C*` hypotheses. -/
theorem cstarAdaptedBasis_exists (a b : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (hfin : Module.finrank ℂ V = 2 * a + 2 * b)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = 2 * a ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = 2 * b) :
    Nonempty (CstarAdaptedBasis a b V J L) := by
  /-
  Proof target:
  * use `Cstar_J_stable_plus/minus`-type arguments to get quaternionic
    `L=±1` subspaces;
  * run quaternionic Gram-Schmidt separately on the positive and negative
    blocks for the Cartan Hermitian form;
  * record the resulting basis in `CstarAdaptedBasis`.
  -/
  classical
  let Eplus := linearEigenspace L.toLinearEquiv 1
  let Eminus := linearEigenspace L.toLinearEquiv (-1)
  let core : InnerProductSpace.Core ℂ V := cartanInnerCore V J L hcompat.cartan_positive
  letI : InnerProductSpace.Core ℂ V := core
  letI : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hanti_global :
      ∀ x y : V, inner ℂ (J x) (J y) = inner ℂ y x := by
    intro x y
    change
      FormedSpace.B Sign.neg V (L (J y)) (J (J x)) =
        FormedSpace.B Sign.neg V (L x) (J y)
    have hLJy : L (J y) = J (L y) := hcompat.commute y
    have hJJx : J (J x) = -x := by
      simpa [Sign.toComplex_neg] using J.sq x
    have hLLx : L (L x) = x := by
      simpa [Sign.toComplex_pos] using L.sq x
    have hpres :
        FormedSpace.B Sign.neg V x (J (L y)) =
          FormedSpace.B Sign.neg V (L x) (J y) := by
      have h := L.preserves_form (L x) (J y)
      rw [hLLx, hcompat.commute y] at h
      exact h
    calc
      FormedSpace.B Sign.neg V (L (J y)) (J (J x))
          = FormedSpace.B Sign.neg V (J (L y)) (-x) := by
            rw [hLJy, hJJx]
      _ = -FormedSpace.B Sign.neg V (J (L y)) x := by simp
      _ = FormedSpace.B Sign.neg V x (J (L y)) := by
            have hsym := FormedSpace.eps_symm (eps := Sign.neg) (V := V) (J (L y)) x
            rw [hsym]
            simp [Sign.toComplex_neg]
      _ = FormedSpace.B Sign.neg V (L x) (J y) := hpres
  have hJplus_map : Eplus.map (J.toSemilinearEquiv : V →ₛₗ[starRingEnd ℂ] V) = Eplus := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) hx
    · intro hy
      refine ⟨-J y, ?_, ?_⟩
      · exact Eplus.neg_mem (linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) hy)
      · simp [map_neg, J.sq y, Sign.toComplex_neg]
  have hJminus_map :
      Eminus.map (J.toSemilinearEquiv : V →ₛₗ[starRingEnd ℂ] V) = Eminus := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) hx
    · intro hy
      refine ⟨-J y, ?_, ?_⟩
      · exact Eminus.neg_mem (linearEigenspace_J_mem_of_star_eq J L hcompat (by simp) hy)
      · simp [map_neg, J.sq y, Sign.toComplex_neg]
  let Jplus : Eplus ≃ₛₗ[starRingEnd ℂ] Eplus :=
    J.toSemilinearEquiv.ofSubmodules Eplus Eplus hJplus_map
  let Jminus : Eminus ≃ₛₗ[starRingEnd ℂ] Eminus :=
    J.toSemilinearEquiv.ofSubmodules Eminus Eminus hJminus_map
  have hsqPlus : ∀ x : Eplus, Jplus (Jplus x) = -x := by
    intro x
    ext
    simpa [Jplus, Sign.toComplex_neg] using J.sq x.1
  have hsqMinus : ∀ x : Eminus, Jminus (Jminus x) = -x := by
    intro x
    ext
    simpa [Jminus, Sign.toComplex_neg] using J.sq x.1
  have hantiPlus : ∀ x y : Eplus, inner ℂ (Jplus x) (Jplus y) = inner ℂ y x := by
    intro x y
    simpa [Jplus] using hanti_global x.1 y.1
  have hantiMinus : ∀ x y : Eminus, inner ℂ (Jminus x) (Jminus y) = inner ℂ y x := by
    intro x y
    simpa [Jminus] using hanti_global x.1 y.1
  have hfinPlus : Module.finrank ℂ Eplus = 2 * a := by
    simpa [Eplus] using hLsig.1
  have hfinMinus : Module.finrank ℂ Eminus = 2 * b := by
    simpa [Eminus] using hLsig.2
  rcases quaternionicCompatibleFamily_exists a Jplus hsqPlus hantiPlus hfinPlus with
    ⟨ePlusF, hPlusON, hPlusJorth⟩
  rcases quaternionicCompatibleFamily_exists b Jminus hsqMinus hantiMinus hfinMinus with
    ⟨eMinusF, hMinusON, hMinusJorth⟩
  let ePlus : Fin a → V := fun i => (ePlusF i : V)
  let eMinus : Fin b → V := fun i => (eMinusF i : V)
  have hPlus_mem : ∀ i, ePlus i ∈ linearEigenspace L.toLinearEquiv 1 := by
    intro i
    exact (ePlusF i).2
  have hMinus_mem : ∀ i, eMinus i ∈ linearEigenspace L.toLinearEquiv (-1) := by
    intro i
    exact (eMinusF i).2
  have hPlus_iso : ∀ i j, FormedSpace.B Sign.neg V (ePlus i) (ePlus j) = 0 := by
    intro i j
    have h := hPlusJorth i j
    change
      FormedSpace.B Sign.neg V (L (ePlusF j : V)) (J (J (ePlusF i : V))) = 0 at h
    have hLj : L (ePlusF j : V) = (ePlusF j : V) := by
      simpa using linearEigenspace_apply_eq L (a := (1 : ℂ)) (ePlusF j).2
    have hJJi : J (J (ePlusF i : V)) = -(ePlusF i : V) := by
      simpa [Sign.toComplex_neg] using J.sq (ePlusF i : V)
    rw [hLj, hJJi] at h
    have hji : FormedSpace.B Sign.neg V (ePlusF j : V) (ePlusF i : V) = 0 := by
      simpa using h
    calc
      FormedSpace.B Sign.neg V (ePlus i) (ePlus j)
          = Sign.neg.toComplex *
              FormedSpace.B Sign.neg V (ePlusF j : V) (ePlusF i : V) :=
            FormedSpace.eps_symm (eps := Sign.neg) (V := V) (ePlus i) (ePlus j)
      _ = 0 := by simp [hji]
  have hPlus_pair :
      ∀ i j,
        FormedSpace.B Sign.neg V (ePlus i) (J (ePlus j)) =
          if i = j then 1 else 0 := by
    intro i j
    have h := hPlusON j i
    change
      FormedSpace.B Sign.neg V (L (ePlusF i : V)) (J (ePlusF j : V)) =
        if j = i then 1 else 0 at h
    have hLi : L (ePlusF i : V) = (ePlusF i : V) := by
      simpa using linearEigenspace_apply_eq L (a := (1 : ℂ)) (ePlusF i).2
    rw [hLi] at h
    by_cases hij : i = j
    · subst j
      simpa [ePlus] using h
    · have hji : j ≠ i := fun hji => hij hji.symm
      simpa [ePlus, hij, hji] using h
  have hMinus_iso : ∀ i j, FormedSpace.B Sign.neg V (eMinus i) (eMinus j) = 0 := by
    intro i j
    have h := hMinusJorth i j
    change
      FormedSpace.B Sign.neg V (L (eMinusF j : V)) (J (J (eMinusF i : V))) = 0 at h
    have hLj : L (eMinusF j : V) = -(eMinusF j : V) := by
      simpa using linearEigenspace_apply_eq L (a := (-1 : ℂ)) (eMinusF j).2
    have hJJi : J (J (eMinusF i : V)) = -(eMinusF i : V) := by
      simpa [Sign.toComplex_neg] using J.sq (eMinusF i : V)
    rw [hLj, hJJi] at h
    have hji : FormedSpace.B Sign.neg V (eMinusF j : V) (eMinusF i : V) = 0 := by
      simpa using h
    calc
      FormedSpace.B Sign.neg V (eMinus i) (eMinus j)
          = Sign.neg.toComplex *
              FormedSpace.B Sign.neg V (eMinusF j : V) (eMinusF i : V) :=
            FormedSpace.eps_symm (eps := Sign.neg) (V := V) (eMinus i) (eMinus j)
      _ = 0 := by simp [hji]
  have hMinus_pair :
      ∀ i j,
        FormedSpace.B Sign.neg V (eMinus i) (J (eMinus j)) =
          if i = j then -1 else 0 := by
    intro i j
    have h := hMinusON j i
    change
      FormedSpace.B Sign.neg V (L (eMinusF i : V)) (J (eMinusF j : V)) =
        if j = i then 1 else 0 at h
    have hLi : L (eMinusF i : V) = -(eMinusF i : V) := by
      simpa using linearEigenspace_apply_eq L (a := (-1 : ℂ)) (eMinusF i).2
    rw [hLi] at h
    have hB :
        FormedSpace.B Sign.neg V (eMinus i) (J (eMinus j)) =
          -(if j = i then 1 else 0 : ℂ) := by
      simpa [eMinus] using congrArg Neg.neg h
    by_cases hij : i = j
    · subst j
      simp [hB]
    · have hji : j ≠ i := fun hji => hij hji.symm
      simpa [hij, hji] using hB
  exact cstarAdaptedBasis_of_quaternionic_families J L hfin hcompat ePlus eMinus
    hPlus_mem hMinus_mem hPlus_iso hPlus_pair hMinus_iso hMinus_pair

/-- Raw quaternionic normal form for `C*`.

This isolates the quaternionic Gram-Schmidt statement on the `J`-stable
`L=±1` eigenspaces. -/
theorem cstarNormalFormIso (a b : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (hfin : Module.finrank ℂ V = 2 * a + 2 * b)
    (hcompat : JLCompatible J L)
    (hLsig :
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv 1) = 2 * a ∧
        Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-1)) = 2 * b) :
    Nonempty
      { e : FormedSpaceIso Sign.neg V (CstarVec a b) //
          (∀ v : V, e.toLinearEquiv (J v) = cstarJ a b (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = cstarL a b (e.toLinearEquiv v)) } := by
  rcases cstarAdaptedBasis_exists a b V J L hfin hcompat hLsig with ⟨A⟩
  exact A.toNormalFormIso

/-- Basis index for the `D*` model. -/
abbrev DstarIndex (r : ℕ) : Type :=
  Fin r ⊕ Fin r

/-- The target Gram matrix for a `D*` adapted basis. -/
def dstarGram (r : ℕ) : DstarIndex r → DstarIndex r → ℂ
  | Sum.inl i, Sum.inr j => if i = j then -Complex.I else 0
  | Sum.inr i, Sum.inl j => if i = j then -Complex.I else 0
  | _, _ => 0

/-- A family with the standard `D*` Gram matrix is linearly independent. -/
private theorem dstar_gram_linearIndependent
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {r : ℕ} {v : DstarIndex r → V}
    (hgram : ∀ i j, FormedSpace.B Sign.pos V (v i) (v j) = dstarGram r i j) :
    LinearIndependent ℂ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  cases k with
  | inl i =>
      have hBsum_zero :
          FormedSpace.B Sign.pos V (∑ j, c j • v j) (v (Sum.inr i)) = 0 := by
        rw [hsum]
        simp
      have hcalc :
          FormedSpace.B Sign.pos V (∑ j, c j • v j) (v (Sum.inr i)) =
            c (Sum.inl i) * (-Complex.I) := by
        simp [hgram, dstarGram, Finset.sum_ite_eq', Finset.mem_univ]
      have hci : c (Sum.inl i) * (-Complex.I) = 0 := by
        rw [← hcalc]
        exact hBsum_zero
      exact (mul_eq_zero.mp hci).resolve_right (by simp)
  | inr i =>
      have hBsum_zero :
          FormedSpace.B Sign.pos V (∑ j, c j • v j) (v (Sum.inl i)) = 0 := by
        rw [hsum]
        simp
      have hcalc :
          FormedSpace.B Sign.pos V (∑ j, c j • v j) (v (Sum.inl i)) =
            c (Sum.inr i) * (-Complex.I) := by
        simp [hgram, dstarGram, Finset.sum_ite_eq', Finset.mem_univ]
      have hci : c (Sum.inr i) * (-Complex.I) = 0 := by
        rw [← hcalc]
        exact hBsum_zero
      exact (mul_eq_zero.mp hci).resolve_right (by simp)

/-- Promote a standard `D*` Gram family to a basis when the cardinality matches
the complex dimension. -/
private noncomputable def basisOfDstarGram
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {r : ℕ} (v : DstarIndex r → V)
    (hfin : Module.finrank ℂ V = r + r)
    (hgram : ∀ i j, FormedSpace.B Sign.pos V (v i) (v j) = dstarGram r i j) :
    Module.Basis (DstarIndex r) ℂ V := by
  classical
  have hli : LinearIndependent ℂ v := dstar_gram_linearIndependent hgram
  refine Module.Basis.mk hli ?_
  have hcard : Fintype.card (DstarIndex r) = Module.finrank ℂ V := by
    rw [hfin]
    simp [DstarIndex]
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  rw [hspan]

/-- Adapted basis data for the `D*` normal form. -/
structure DstarAdaptedBasis (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg) (L : LStructure Sign.pos V Sign.neg) where
  /-- The adapted complex basis. -/
  basis : Module.Basis (DstarIndex r) ℂ V
  /-- `J` sends the `A=+1` block to the `A=-1` block. -/
  J_inl : ∀ i, J (basis (Sum.inl i)) = basis (Sum.inr i)
  /-- `J` sends the second block back to minus the first. -/
  J_inr : ∀ i, J (basis (Sum.inr i)) = -basis (Sum.inl i)
  /-- `L` acts by `i` on the first block. -/
  L_inl : ∀ i, L (basis (Sum.inl i)) = Complex.I • basis (Sum.inl i)
  /-- `L` acts by `-i` on the second block. -/
  L_inr : ∀ i, L (basis (Sum.inr i)) = (-Complex.I) • basis (Sum.inr i)
  /-- The Gram matrix is the standard `D*` Gram matrix. -/
  form_basis :
    ∀ i j, FormedSpace.B Sign.pos V (basis i) (basis j) = dstarGram r i j

namespace DstarAdaptedBasis

/-- Coordinate equivalence associated to an adapted `D*` basis. -/
noncomputable def toLinearEquiv {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.neg} {L : LStructure Sign.pos V Sign.neg}
    (A : DstarAdaptedBasis r V J L) : V ≃ₗ[ℂ] PairVec r :=
  A.basis.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) ℂ ℂ)

/-- The coordinate map attached to an adapted `D*` basis intertwines `L`. -/
theorem intertwines_L {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.neg} {L : LStructure Sign.pos V Sign.neg}
    (A : DstarAdaptedBasis r V J L) :
    ∀ v : V, A.toLinearEquiv (L v) = dstarL r (A.toLinearEquiv v) := by
  let f₁ : V →ₗ[ℂ] PairVec r :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap.comp L.toLinearMap
  let f₂ : V →ₗ[ℂ] PairVec r :=
    (dstarL r).toLinearMap.comp (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k <;> simp [f₁, f₂, toLinearEquiv, A.L_inl, dstarL, iLinearEquiv,
          LinearEquiv.sumArrowLequivProdArrow]
    | inr j =>
        ext k
        · simp [f₁, f₂, toLinearEquiv, A.L_inr, dstarL, iLinearEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
        · by_cases hkj : k = j
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.L_inr, dstarL, iLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inr j : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hkj (Sum.inr.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.L_inr, dstarL, iLinearEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' (b := Complex.I) hsum,
              Finsupp.single_eq_of_ne' (b := (1 : ℂ)) hsum]
            simp
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an adapted `D*` basis intertwines `J`. -/
theorem intertwines_J {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.neg} {L : LStructure Sign.pos V Sign.neg}
    (A : DstarAdaptedBasis r V J L) :
    ∀ v : V, A.toLinearEquiv (J v) = dstarJ r (A.toLinearEquiv v) := by
  let f₁ : V →ₛₗ[starRingEnd ℂ] PairVec r :=
    (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap.comp J.toSemilinearMap
  let f₂ : V →ₛₗ[starRingEnd ℂ] PairVec r :=
    (dstarJ r).toSemilinearMap.comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have h : f₁ = f₂ := by
    apply A.basis.ext
    intro idx
    cases idx with
    | inl i =>
        ext k
        · simp [f₁, f₂, toLinearEquiv, A.J_inl, dstarJ, quatJEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
        · by_cases hki : k = i
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_inl, dstarJ, quatJEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hki (Sum.inr.inj h).symm
            have hsum' : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl k := by
              intro h
              exact hki (Sum.inl.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_inl, dstarJ, quatJEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' (b := (1 : ℂ)) hsum,
              Finsupp.single_eq_of_ne' (b := (1 : ℂ)) hsum']
            simp
    | inr j =>
        ext k
        · by_cases hkj : k = j
          · subst k
            simp [f₁, f₂, toLinearEquiv, A.J_inr, dstarJ, quatJEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
          · have hsum : (Sum.inl j : Fin r ⊕ Fin r) ≠ Sum.inl k := by
              intro h
              exact hkj (Sum.inl.inj h).symm
            have hsum' : (Sum.inr j : Fin r ⊕ Fin r) ≠ Sum.inr k := by
              intro h
              exact hkj (Sum.inr.inj h).symm
            simp [f₁, f₂, toLinearEquiv, A.J_inr, dstarJ, quatJEquiv,
              LinearEquiv.sumArrowLequivProdArrow]
            rw [Finsupp.single_eq_of_ne' (b := (1 : ℂ)) hsum,
              Finsupp.single_eq_of_ne' (b := (1 : ℂ)) hsum']
            simp
        · simp [f₁, f₂, toLinearEquiv, A.J_inr, dstarJ, quatJEquiv,
            LinearEquiv.sumArrowLequivProdArrow]
  intro v
  exact LinearMap.congr_fun h v

/-- The coordinate map attached to an adapted `D*` basis preserves the bilinear
forms. -/
theorem preserves_form {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.neg} {L : LStructure Sign.pos V Sign.neg}
    (A : DstarAdaptedBasis r V J L) :
    ∀ u v : V,
      FormedSpace.B Sign.pos (PairVec r) (A.toLinearEquiv u) (A.toLinearEquiv v) =
        FormedSpace.B Sign.pos V u v := by
  let Bpull : LinearMap.BilinForm ℂ V :=
    (FormedSpace.B Sign.pos (PairVec r)).comp
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
      (A.toLinearEquiv : V ≃ₗ[ℂ] PairVec r).toLinearMap
  have hB : Bpull = FormedSpace.B Sign.pos V := by
    apply LinearMap.BilinForm.ext_basis A.basis
    intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, dstarFormedSpace, dstarForm_apply,
              dot, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_basis, dstarGram]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, dstarFormedSpace, dstarForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_basis, dstarGram]
            rw [dot_sum_single_inl_inr i j]
            by_cases hij : i = j <;> simp [hij, dot]
    | inr i =>
        cases j with
        | inl j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, dstarFormedSpace, dstarForm_apply,
              LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_basis, dstarGram]
            rw [dot_sum_single_inr_inl i j]
            by_cases hij : i = j <;> simp [hij, dot]
        | inr j =>
            simp [Bpull, toLinearEquiv, FormedSpace.B, dstarFormedSpace, dstarForm_apply,
              dot, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
              A.form_basis, dstarGram]
  intro u v
  have h := congrArg (fun B : LinearMap.BilinForm ℂ V => B u v) hB
  simpa [Bpull] using h

/-- An adapted `D*` basis gives the required coordinate isomorphism. -/
theorem toNormalFormIso {r : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {J : JStructure Sign.pos V Sign.neg} {L : LStructure Sign.pos V Sign.neg}
    (A : DstarAdaptedBasis r V J L) :
    Nonempty
      { e : FormedSpaceIso Sign.pos V (PairVec r) //
          ((∀ v : V, e.toLinearEquiv (J v) = dstarJ r (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = dstarL r (e.toLinearEquiv v))) } := by
  let e : FormedSpaceIso Sign.pos V (PairVec r) :=
    { toLinearEquiv := A.toLinearEquiv, preserves_form := A.preserves_form }
  exact ⟨⟨e, ⟨A.intertwines_J, A.intertwines_L⟩⟩⟩

end DstarAdaptedBasis

/-- The projection onto the `L = i` eigenspace in the `D*` case. -/
private noncomputable def DstarIPlusPart
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) (v : V) : V :=
  ((1 / 2 : ℂ) : ℂ) • (v - Complex.I • L v)

/-- The projection onto the `L = -i` eigenspace in the `D*` case. -/
private noncomputable def DstarIMinusPart
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) (v : V) : V :=
  ((1 / 2 : ℂ) : ℂ) • (v + Complex.I • L v)

private theorem DstarIPlusPart_mem_eig_i
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) (v : V) :
    DstarIPlusPart L v ∈ linearEigenspace L.toLinearEquiv Complex.I := by
  rw [linearEigenspace, LinearMap.mem_ker]
  apply sub_eq_zero.mpr
  rw [DstarIPlusPart]
  change L (((1 / 2 : ℂ) : ℂ) • (v - Complex.I • L v)) =
    Complex.I • (((1 / 2 : ℂ) : ℂ) • (v - Complex.I • L v))
  rw [map_smul, map_sub, map_smul, L.sq v]
  simp only [Sign.toComplex_neg]
  simp only [smul_sub, smul_smul]
  ring_nf
  simp [Complex.I_mul_I, pow_two, sub_eq_add_neg, add_comm]
  rw [← neg_smul]
  congr 1
  ring

private theorem DstarIMinusPart_mem_eig_neg_i
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) (v : V) :
    DstarIMinusPart L v ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
  rw [linearEigenspace, LinearMap.mem_ker]
  apply sub_eq_zero.mpr
  rw [DstarIMinusPart]
  change L (((1 / 2 : ℂ) : ℂ) • (v + Complex.I • L v)) =
    (-Complex.I) • (((1 / 2 : ℂ) : ℂ) • (v + Complex.I • L v))
  rw [map_smul, map_add, map_smul, L.sq v]
  simp only [Sign.toComplex_neg]
  simp only [smul_add, smul_smul]
  ring_nf
  simp [Complex.I_mul_I, pow_two, add_comm]
  rw [← neg_smul]
  congr 1
  ring

private theorem DstarIPlusPart_add_IMinusPart
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) (v : V) :
    DstarIPlusPart L v + DstarIMinusPart L v = v := by
  simp only [DstarIPlusPart, DstarIMinusPart, smul_add, smul_sub]
  module

private theorem linearEigenspace_i_neg_i_disjoint
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    Disjoint (linearEigenspace L.toLinearEquiv Complex.I)
      (linearEigenspace L.toLinearEquiv (-Complex.I)) := by
  rw [Submodule.disjoint_def]
  intro x hx hxn
  have hxL : L x = Complex.I • x := by simpa using linearEigenspace_apply_eq L hx
  have hxnL : L x = (-Complex.I) • x := by simpa using linearEigenspace_apply_eq L hxn
  have hEq : Complex.I • x = (-Complex.I) • x := by rw [← hxL, ← hxnL]
  have htwo : ((2 : ℂ) * Complex.I) • x = 0 := by
    calc
      ((2 : ℂ) * Complex.I) • x = Complex.I • x - (-Complex.I) • x := by module
      _ = 0 := by rw [hEq]; simp
  rcases smul_eq_zero.mp htwo with hscalar | hx_zero
  · norm_num at hscalar
  · exact hx_zero

private theorem linearEigenspace_i_neg_i_sup_eq_top
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    linearEigenspace L.toLinearEquiv Complex.I ⊔
      linearEigenspace L.toLinearEquiv (-Complex.I) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  exact ⟨DstarIPlusPart L v, DstarIPlusPart_mem_eig_i L v,
    DstarIMinusPart L v, DstarIMinusPart_mem_eig_neg_i L v,
    DstarIPlusPart_add_IMinusPart L v⟩

private theorem linearEigenspace_i_neg_i_isCompl
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    IsCompl (linearEigenspace L.toLinearEquiv Complex.I)
      (linearEigenspace L.toLinearEquiv (-Complex.I)) := by
  exact IsCompl.of_eq
    (linearEigenspace_i_neg_i_disjoint L).eq_bot
    (linearEigenspace_i_neg_i_sup_eq_top L)

private theorem linearEigenspace_i_finrank_eq
    (r : ℕ) {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg) (L : LStructure Sign.pos V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r) (hcompat : JLCompatible J L) :
    Module.finrank ℂ (linearEigenspace L.toLinearEquiv Complex.I) = r := by
  let Ei := linearEigenspace L.toLinearEquiv Complex.I
  let En := linearEigenspace L.toLinearEquiv (-Complex.I)
  have hcompl : IsCompl Ei En := by
    simpa [Ei, En] using linearEigenspace_i_neg_i_isCompl L
  have hsum : Module.finrank ℂ Ei + Module.finrank ℂ En = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have heq : Module.finrank ℂ Ei = Module.finrank ℂ En := by
    simpa [Ei, En] using eig_i_finrank_eq_eig_neg_i_finrank J L hcompat
  rw [hfin] at hsum
  change Module.finrank ℂ Ei = r
  omega

/-- Build a `D*` adapted basis from an orthonormal basis of the `L = i`
eigenspace for the Cartan inner product. -/
private theorem dstarAdaptedBasis_of_i_orthonormal
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    {r : ℕ} (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r) (hcompat : JLCompatible J L)
    (e : Fin r → V)
    (hmem : ∀ i, e i ∈ linearEigenspace L.toLinearEquiv Complex.I)
    (hpair : ∀ i j,
      FormedSpace.B Sign.pos V (e i) (J (e j)) = if i = j then -Complex.I else 0) :
    Nonempty (DstarAdaptedBasis r V J L) := by
  classical
  let v : DstarIndex r → V
    | Sum.inl i => e i
    | Sum.inr i => J (e i)
  have hJ_mem : ∀ i, J (e i) ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
    intro i
    exact linearEigenspace_J_mem_i_to_neg_i J L hcompat (hmem i)
  have hplus_iso : ∀ i j, FormedSpace.B Sign.pos V (e i) (e j) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L
      (by norm_num [Complex.I_mul_I] : Complex.I * Complex.I ≠ (1 : ℂ))
      (hmem i) (hmem j)
  have hminus_iso : ∀ i j, FormedSpace.B Sign.pos V (J (e i)) (J (e j)) = 0 := by
    intro i j
    exact L_eigenspaces_form_orthogonal L
      (by norm_num [Complex.I_mul_I] : (-Complex.I) * (-Complex.I) ≠ (1 : ℂ))
      (hJ_mem i) (hJ_mem j)
  have hJ_e :
      ∀ i j, FormedSpace.B Sign.pos V (J (e i)) (e j) =
        if i = j then -Complex.I else 0 := by
    intro i j
    have hsym := FormedSpace.eps_symm (eps := Sign.pos) (V := V) (J (e i)) (e j)
    by_cases hij : i = j
    · subst j
      simpa [Sign.toComplex_pos, hpair i i] using hsym
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [Sign.toComplex_pos, hij, hji, hpair j i] using hsym
  have hgram : ∀ i j, FormedSpace.B Sign.pos V (v i) (v j) = dstarGram r i j := by
    intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j => simp [v, dstarGram, hplus_iso]
        | inr j => simp [v, dstarGram, hpair]
    | inr i =>
        cases j with
        | inl j => simp [v, dstarGram, hJ_e]
        | inr j => simp [v, dstarGram, hminus_iso]
  let basis : Module.Basis (DstarIndex r) ℂ V := basisOfDstarGram v hfin hgram
  refine ⟨
    { basis := basis
      J_inl := ?_
      J_inr := ?_
      L_inl := ?_
      L_inr := ?_
      form_basis := ?_ }⟩
  · intro i
    simp [basis, basisOfDstarGram, v]
  · intro i
    have hsq : J (J (e i)) = -e i := by
      simpa [Sign.toComplex_neg] using J.sq (e i)
    simp [basis, basisOfDstarGram, v, hsq]
  · intro i
    have hL : L (e i) = Complex.I • e i := by
      simpa using linearEigenspace_apply_eq L (a := Complex.I) (hmem i)
    simp [basis, basisOfDstarGram, v, hL]
  · intro i
    have hL : L (J (e i)) = (-Complex.I) • J (e i) := by
      rw [hcompat.commute (e i)]
      have hLe : L (e i) = Complex.I • e i := by
        simpa using linearEigenspace_apply_eq L (a := Complex.I) (hmem i)
      rw [hLe]
      simpa using J.toSemilinearEquiv.map_smulₛₗ Complex.I (e i)
    simp [basis, basisOfDstarGram, v, hL]
  · intro i j
    simpa [basis, basisOfDstarGram] using hgram i j

/-- Existence of an adapted `D*` basis from the `D*` hypotheses. -/
theorem dstarAdaptedBasis_exists (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r)
    (hcompat : JLCompatible J L) :
    Nonempty (DstarAdaptedBasis r V J L) := by
  /-
  Proof target:
  * use `A=-iL`, its two eigenspaces, and the `Dstar_*` lemmas from
    `Lemmas.lean`;
  * choose an orthonormal basis of the `A=+1` eigenspace for the Cartan
    Hermitian form;
  * pair it with its `J`-image and record the standard Gram matrix.
  -/
  classical
  let Ei := linearEigenspace L.toLinearEquiv Complex.I
  let core : InnerProductSpace.Core ℂ V := cartanInnerCore V J L hcompat.cartan_positive
  letI : InnerProductSpace.Core ℂ V := core
  letI : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hdim : Module.finrank ℂ Ei = r := by
    simpa [Ei] using linearEigenspace_i_finrank_eq r J L hfin hcompat
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℂ Ei)) ℂ Ei :=
    stdOrthonormalBasis ℂ Ei
  let bON : OrthonormalBasis (Fin r) ℂ Ei := b₀.reindex (finCongr hdim)
  let e : Fin r → V := fun i => (bON i : V)
  have hmem : ∀ i, e i ∈ linearEigenspace L.toLinearEquiv Complex.I := by
    intro i
    exact (bON i).2
  have hpair :
      ∀ i j,
        FormedSpace.B Sign.pos V (e i) (J (e j)) =
          if i = j then -Complex.I else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp bON.orthonormal) j i
    change FormedSpace.B Sign.pos V (L (e i)) (J (e j)) =
      if j = i then 1 else 0 at h
    have hLi : L (e i) = Complex.I • e i := by
      simpa using linearEigenspace_apply_eq L (a := Complex.I) (hmem i)
    rw [hLi] at h
    have hI :
        Complex.I * FormedSpace.B Sign.pos V (e i) (J (e j)) =
          if j = i then 1 else 0 := by
      simpa [e] using h
    have hB :
        FormedSpace.B Sign.pos V (e i) (J (e j)) =
          (-Complex.I) * (if j = i then 1 else 0 : ℂ) := by
      calc
        FormedSpace.B Sign.pos V (e i) (J (e j)) =
            ((-Complex.I) * Complex.I) *
              FormedSpace.B Sign.pos V (e i) (J (e j)) := by
              simp [Complex.I_mul_I]
        _ = (-Complex.I) *
            (Complex.I * FormedSpace.B Sign.pos V (e i) (J (e j))) := by ring
        _ = (-Complex.I) * (if j = i then 1 else 0 : ℂ) := by rw [hI]
    by_cases hij : i = j
    · subst j
      simpa using hB
    · have hji : j ≠ i := fun hji => hij hji.symm
      simpa [hij, hji] using hB
  exact dstarAdaptedBasis_of_i_orthonormal J L hfin hcompat e hmem hpair

/-- Normal form for the `C*` family.

Blueprint content: `J²=-1` makes `V` quaternionic.  The `L=±1` eigenspaces are
`J`-stable quaternionic subspaces of complex dimensions `2a` and `2b`; applying
quaternionic Gram-Schmidt gives the standard `Sp(a,b)` model. -/
theorem normalForm_Cstar (a b : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.Cstar.eps V]
    (J : JStructure ClassicalStar.Cstar.eps V ClassicalStar.Cstar.jSign)
    (L : LStructure ClassicalStar.Cstar.eps V ClassicalStar.Cstar.dotEps)
    (hV : IsClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) V J L) :
    Nonempty
      (ClassicalSpaceIso ClassicalStar.Cstar V (CstarVec a b) J L (cstarJ a b) (cstarL a b)) := by
  rcases cstarNormalFormIso a b V J L (isClassicalSpace_finrank hV)
      (isClassicalSpace_compatible hV)
      (by simpa [LSignatureCondition] using isClassicalSpace_LSignature hV) with ⟨e, hJ, hL⟩
  exact ⟨{ toFormedSpaceIso := e, intertwines_J := hJ, intertwines_L := hL }⟩

/-- Raw quaternionic normal form for `D*`.

This isolates the `A=-iL` adapted-basis statement. -/
theorem dstarNormalFormIso (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (hfin : Module.finrank ℂ V = r + r)
    (hcompat : JLCompatible J L) :
    Nonempty
      { e : FormedSpaceIso Sign.pos V (PairVec r) //
          (∀ v : V, e.toLinearEquiv (J v) = dstarJ r (e.toLinearEquiv v)) ∧
            (∀ v : V, e.toLinearEquiv (L v) = dstarL r (e.toLinearEquiv v)) } := by
  rcases dstarAdaptedBasis_exists r V J L hfin hcompat with ⟨A⟩
  exact A.toNormalFormIso

/-- Normal form for the `D*` family.

Blueprint content: set `A=-iL`; its `±1` eigenspaces are `H`-orthogonal,
interchanged by `J`, and have dimension `r`.  An `H`-orthonormal basis of the
`A=+1` eigenspace paired with its `J`-image gives the standard model. -/
theorem normalForm_Dstar (r : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace ClassicalStar.Dstar.eps V]
    (J : JStructure ClassicalStar.Dstar.eps V ClassicalStar.Dstar.jSign)
    (L : LStructure ClassicalStar.Dstar.eps V ClassicalStar.Dstar.dotEps)
    (hV : IsClassicalSpace ClassicalStar.Dstar r r V J L) :
    Nonempty
      (ClassicalSpaceIso ClassicalStar.Dstar V (PairVec r) J L (dstarJ r) (dstarL r)) := by
  rcases dstarNormalFormIso r V J L (isClassicalSpace_finrank hV)
      (isClassicalSpace_compatible hV) with ⟨e, hJ, hL⟩
  exact ⟨{ toFormedSpaceIso := e, intertwines_J := hJ, intertwines_L := hL }⟩

end ClassicalGroup
