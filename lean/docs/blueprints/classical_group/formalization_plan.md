# ClassicalGroup Lean formalization plan

## Scope

This is a standalone formalization task for `classicalgroup.md`.
It is not part of the induced-orbit formalization.

Authoritative informal inputs:

1. `problem.md` — copied from repository root `classicalgroup.md`.
2. `blueprint.md` — copied from the verified Rethlas blueprint for the same problem.

The Lean namespace should be `ClassicalGroup`, not `InducedOrbitToy.ClassicalGroup`.

## Target theorem

Formalize the existence and uniqueness portion of the theorem in `classicalgroup.md`:

- for every classical signature `(star, p, q)`, construct a finite-dimensional complex
  vector space with an `ε`-symmetric nondegenerate complex bilinear form, a conjugate-linear
  form-preserving operator `J`, and a complex-linear form-preserving operator `L`;
- prove `J^2 = ε dotε`, `L^2 = dotε`, `LJ = JL`, positivity of
  `H(u,v) = B(Lu,Jv)`, and the required eigenspace dimensions when `dotε = 1`;
- state uniqueness as existence of a complex-linear isomorphism preserving the form and
  intertwining `J` and `L`.

The group-identification assertion should initially be isolated from the core existence theorem,
because real Lie group APIs for `O(p,q)`, `Sp(2p,R)`, `Sp(a,b)`, and `O*(2p)` may require
extra Mathlib infrastructure or local definitions.

## File layout

```text
lean/
  ClassicalGroup.lean               -- standalone root module
  ClassicalGroup/
    Basic.lean                      -- signs, signatures, core predicates and structures
    Models/
      BD.lean                       -- explicit B,D standard model
      C.lean                        -- explicit C,C~ standard model
      CStar.lean                    -- explicit C* standard model
      DStar.lean                    -- explicit D* standard model
    Existence.lean                  -- dispatch over signatures
    Uniqueness.lean                 -- normal-form uniqueness statements/proof skeleton
    Groups.lean                     -- group-identification layer
    Main.lean                       -- final exported theorems
    problem.md                      -- copied problem statement
    blueprint.md                    -- copied verified blueprint
    formalization_plan.md           -- this plan
```

Start with `Basic.lean`, then add model files one at a time.

## Core data structures

Use unbundled vector spaces with typeclasses, so users can ask whether supplied data form a
classical space.

```lean
inductive Sign where | pos | neg
inductive ClassicalStar where | B | C | D | Ctilda | Cstar | Dstar

def IsClassicalSignature (star : ClassicalStar) (p q : ℕ) : Prop := ...

class FormedSpace (eps : Sign) (V : Type*)
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] where
  form : LinearMap.BilinForm ℂ V
  nondegenerate : form.Nondegenerate
  eps_symm : ∀ u v, form u v = eps.toComplex * form v u

structure JStructure (eps : Sign) (V : Type*) ... (jSign : Sign) where
  toSemilinearEquiv : V ≃ₛₗ[starRingEnd ℂ] V
  sq : ∀ v, toSemilinearEquiv (toSemilinearEquiv v) = jSign.toComplex • v
  preserves_form : ∀ u v, B (J u) (J v) = starRingEnd ℂ (B u v)

structure LStructure (eps : Sign) (V : Type*) ... (lSign : Sign) where
  toLinearEquiv : V ≃ₗ[ℂ] V
  sq : ∀ v, toLinearEquiv (toLinearEquiv v) = lSign.toComplex • v
  preserves_form : ∀ u v, B (L u) (L v) = B u v

structure JLCompatible (J : JStructure ...) (L : LStructure ...) : Prop where
  commute : ∀ v, L (J v) = J (L v)
  cartan_positive : PositiveDefiniteHermitian J L

def IsClassicalSpace (star : ClassicalStar) (p q : ℕ) (V : Type*) ...
    (J : JStructure ...) (L : LStructure ...) : Prop := ...
```

Keep these design points:

- `FormedSpace` is a class on an externally supplied finite-dimensional complex vector space.
- `JStructure` and `LStructure` are independent structures over `V`.
- form preservation belongs inside `JStructure` and `LStructure`.
- `JLCompatible` contains only genuinely paired conditions: `LJ = JL` and positivity.
- `IsClassicalSpace` is a proposition about supplied `V`, `J`, and `L`.
- A bundled witness can be added later for convenience, but the proposition interface is primary.

## Required intermediate lemmas

These should be formalized before attacking the full standard-model proofs.

1. `J` sends an `L`-eigenvector of eigenvalue `a` to an `L`-eigenvector of eigenvalue
   `conj a`, assuming `LJ = JL`.
2. If `dotε = -1`, then the `i` and `-i` eigenspaces of `L` have equal complex dimension.
   This is a theorem from conjugate-linearity and compatibility, not a design axiom.
3. Distinct `L`-eigenspaces are orthogonal for the bilinear form when the product of
   eigenvalues is not `1`.
4. In the `B,D` case, the `+1` and `-1` eigenspaces of `L` have positive and negative
   form signs on the `J`-fixed real form.
5. In the `C*` case, the `±1` eigenspaces of `L` are `J`-stable, and their dimensions match
   the even signature data.
6. In the `D*` case, with `A = -i L`, the `A = ±1` eigenspaces correspond to the `L = ±i`
   eigenspaces, `J` swaps them, and both are totally isotropic for the symmetric form.

## Standard models to formalize

### B,D

Use `V = Fin (p+q) → ℂ`, form matrix `diag(1,...,1,-1,...,-1)`, `J =` entrywise conjugation,
and `L =` multiplication by the same diagonal signs.

### C,Ctilda

Use `V = (Fin r → ℂ) × (Fin r → ℂ)`, alternating form
`B((z,w),(z',w')) = zᵀw' - wᵀz'`, `J =` entrywise conjugation,
and `L(z,w) = (w,-z)`.

### Cstar

For `p=2a`, `q=2b`, use `V = (Fin (a+b) → ℂ) × (Fin (a+b) → ℂ)`, alternating form with
signature matrix `S_{a,b}`, `J(z,w)=(-conj w, conj z)`, and `L(z,w)=(S z, S w)`.

### Dstar

Use `V = (Fin r → ℂ) × (Fin r → ℂ)`, symmetric form
`B((z,w),(z',w')) = -i (zᵀw' + wᵀz')`, `J(z,w)=(-conj w,conj z)`, and
`L(z,w)=(i z, -i w)`.

## Uniqueness strategy

Formalize uniqueness as `Nonempty (ClassicalSpaceIso ...)`, not as definitional equality or
subsingletonness.

Proof blueprint:

- `B,D`: pass to the `J`-fixed real form, decompose into `L=±1` real eigenspaces, choose
  orthonormal bases, and compare with the `S_{p,q}` model.
- `C,Ctilda`: pass to the `J`-fixed real symplectic space with positive metric `H`; construct
  an adapted symplectic basis by Gram-Schmidt.
- `Cstar`: use the quaternionic structure from `J^2=-1`; choose quaternionic orthonormal bases
  on the `L=±1` eigenspaces.
- `Dstar`: use `A=-iL`; choose an `H`-orthonormal basis of `A=+1` and pair it with its image
  under `J`.

These normal-form basis-construction theorems may initially be stated as separate lemmas with
proof comments if Mathlib lacks the exact classification API.

## Group-identification layer

Keep group identification in `Groups.lean` and do not let it block the core existence theorem.
At first, define abstract predicates/types for the four real groups if Mathlib does not already
provide the required Lie group objects. Later replace them with Mathlib-native definitions.

The `Ctilda` case should identify only the underlying real symplectic group; the metaplectic
cover is external to the construction.

## Verification discipline

- No custom `axiom` or `constant` for mathematical content without explicit approval.
- `sorry` is acceptable only during the skeleton stage and must be tracked by `rg "sorry"`.
- Every source lemma that is not proved immediately must retain a comment explaining the
  corresponding blueprint argument.
- Build target for this standalone task should be:

```bash
cd /Users/hoxide/mycodes/unipotentrepn/lean
lake build CombUnipotent.ClassicalGroup
```
