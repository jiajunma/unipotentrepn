# ClassicalGroup blueprint

Source: `/Users/hoxide/mydoc/inducedorbittoy/Rethlas/agents/generation/results/classicalgroup/blueprint_verified.md`

# proposition prop:completeness-check

## statement
The problem statement is complete after the following minimal convention fixes.

1. `\(\mathrm O(p,q)\)` means the full real orthogonal group preserving a real symmetric bilinear form of signature `\((p,q)\)`.
2. `\(\mathrm{Sp}(a,b)\)` means the quaternionic-linear isometry group of a quaternionic Hermitian form of signature `\((a,b)\)`.
3. `\(\mathrm O^*(2p)\)` means the quaternionic-linear isometry group of a non-degenerate quaternionic skew-Hermitian form on `\(\mathbb H^p\)`.
4. In the quaternionic cases we use the convention that quaternionic forms are linear in the first variable and conjugate-linear in the second.

No further repair is needed.

## proof
The only possible ambiguities are the connectedness convention for `\(\mathrm O(p,q)\)` and the linearity convention for quaternionic forms. Once those are fixed as above, every group appearing in the theorem has a standard meaning, and the rest of the statement is unambiguous.

# theorem thm:classicalgroup

## statement
For every classical signature
\[
\mathsf s=(\star,p,q),
\]
there exists a quadruple
\[
(V,\langle\ ,\ \rangle,J,L)
\]
with the following properties:

1. \(V\) is a complex vector space of dimension \(|\mathsf s|\).
2. \(\langle\ ,\ \rangle\) is a non-degenerate \(\epsilon\)-symmetric complex bilinear form on \(V\).
3. \(J:V\to V\) is conjugate-linear and satisfies
   \[
   J^2=\epsilon\dot\epsilon.
   \]
4. \(L:V\to V\) is complex-linear and satisfies
   \[
   L^2=\dot\epsilon.
   \]
5. For all \(u,v\in V\),
   \[
   \langle Ju,Jv\rangle=\overline{\langle u,v\rangle}.
   \]
6. For all \(u,v\in V\),
   \[
   \langle Lu,Lv\rangle=\langle u,v\rangle.
   \]
7. \(LJ=JL\).
8. The Hermitian form
   \[
   H(u,v):=\langle Lu,Jv\rangle
   \]
   is positive definite.
9. If \(\dot\epsilon=1\), then
   \[
   \dim\{v\in V:Lv=v\}=p,
   \qquad
   \dim\{v\in V:Lv=-v\}=q.
   \]
10. With
    \[
    G_{\mathbb C}=\operatorname{Isom}_{\mathbb C}(V,\langle\ ,\ \rangle),
    \qquad
    G_{\mathbb C}^{J}=Z_{G_{\mathbb C}}(J),
    \]
    one has an isomorphism of real Lie groups
    \[
    G_{\mathbb C}^{J}\simeq
    \begin{cases}
    \mathrm O(p,q),&\star=B\text{ or }D,\\
    \mathrm {Sp}_{2p}(\mathbb R),&\star=C\text{ or }\widetilde C,\\
    \mathrm {Sp}(p/2,q/2),&\star=C^*,\\
    \mathrm O^*(2p),&\star=D^*.
    \end{cases}
    \]

11. (**Uniqueness**) If another quadruple \((V',\langle\ ,\ \rangle',J',L')\) satisfies the same conditions for the same \(\mathsf s\), then there exists a complex-linear isomorphism \(\phi:V\to V'\) such that \(\phi\) carries \(\langle\ ,\ \rangle\) to \(\langle\ ,\ \rangle'\), \(J\) to \(J'\), and \(L\) to \(L'\).

## proof
We first fix the conventions from Proposition `prop:completeness-check`. In particular, in the quaternionic cases we view a complex vector space with a conjugate-linear operator `\(J\)` satisfying `\(J^2=-1\)` as a right `\(\mathbb H\)`-module by
\[
v\cdot(a+bj):=va+J(v)b
\qquad(a,b\in\mathbb C).
\]
We now construct the required quadruple in the four sign patterns.

### Case 1: `\(\star=B,D\)`

Here `\((\epsilon,\dot\epsilon)=(1,1)\)`. Let
\[
V=\mathbb C^{p+q},
\qquad
S_{p,q}:=\operatorname{diag}(I_p,-I_q),
\]
with standard basis `\(e_1,\dots,e_{p+q}\)`. Define
\[
\langle u,v\rangle:=u^T S_{p,q}v,
\qquad
J(u):=\overline u,
\qquad
L(u):=S_{p,q}u.
\]

Then `\(\dim_{\mathbb C}V=p+q=|\mathsf s|\)`. Since `\(S_{p,q}^T=S_{p,q}\)`, the form is symmetric. It is non-degenerate because `\(S_{p,q}\)` is invertible. Also `\(J\)` is conjugate-linear, `\(J^2=1=\epsilon\dot\epsilon\)`, `\(L^2=1=\dot\epsilon\)`, and `\(LJ=JL\)` because `\(S_{p,q}\)` is real.

For `\(u,v\in V\)`,
\[
\langle Ju,Jv\rangle
=\overline u^{\,T}S_{p,q}\overline v
=\overline{u^TS_{p,q}v}
=\overline{\langle u,v\rangle},
\]
and
\[
\langle Lu,Lv\rangle
=u^TS_{p,q}^3v
=u^TS_{p,q}v
=\langle u,v\rangle.
\]
Moreover
\[
H(u,v)=\langle Lu,Jv\rangle
=u^TS_{p,q}^2\overline v
=u^T\overline v,
\]
so `\(H\)` is the standard positive-definite Hermitian form on `\(\mathbb C^{p+q}\)`.

The `\((+1)\)`-eigenspace of `\(L\)` is spanned by `\(e_1,\dots,e_p\)`, hence has dimension `\(p\)`, and the `\((-1)\)`-eigenspace is spanned by `\(e_{p+1},\dots,e_{p+q}\)`, hence has dimension `\(q\)`.

Finally, `\(G_{\mathbb C}\)` is the complex orthogonal group of `\(u^TS_{p,q}v\)`. An element `\(g\in G_{\mathbb C}\)` satisfies `\(gJ=Jg\)` exactly when all matrix entries of `\(g\)` are real. Thus
\[
G_{\mathbb C}^J
=\{g\in\operatorname{GL}_{p+q}(\mathbb R):g^TS_{p,q}g=S_{p,q}\}
=\mathrm O(p,q).
\]
So properties (1)-(10) hold in the `\(B,D\)` case.

### Case 2: `\(\star=C,\widetilde C\)`

Here `\((\epsilon,\dot\epsilon)=(-1,-1)\)` and `\(p=q\)`. Write `\(r:=p=q\)`. Let
\[
V=\mathbb C^{2r}=\mathbb C^r\oplus\mathbb C^r,
\]
with basis
\[
e_1,\dots,e_r,f_1,\dots,f_r,
\]
where `\(e_i\)` is the `\(i\)`-th vector in the first summand and `\(f_i\)` is the `\(i\)`-th vector in the second summand. Define
\[
\langle (z,w),(z',w')\rangle:=z^Tw'-w^Tz',
\]
\[
J(z,w):=(\overline z,\overline w),
\qquad
L(z,w):=(w,-z).
\]

The form is alternating, hence `\((-1)\)`-symmetric, and it is non-degenerate. The map `\(J\)` is conjugate-linear and `\(J^2=1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and
\[
L^2(z,w)=L(w,-z)=(-z,-w)=- (z,w),
\]
so `\(L^2=-1=\dot\epsilon\)`. Because `\(J\)` is entrywise conjugation, `\(LJ=JL\)`.

For `\(u=(z,w)\)` and `\(v=(z',w')\)`,
\[
\langle Ju,Jv\rangle
=\overline z^{\,T}\overline w'-\overline w^{\,T}\overline z'
=\overline{z^Tw'-w^Tz'}
=\overline{\langle u,v\rangle},
\]
and
\[
\langle Lu,Lv\rangle
=\langle (w,-z),(w',-z')\rangle
=w^T(-z')-(-z)^Tw'
=z^Tw'-w^Tz'
=\langle u,v\rangle.
\]
Furthermore
\[
H((z,w),(z',w'))
=\langle (w,-z),(\overline z',\overline w')\rangle
=w^T\overline w'+z^T\overline z',
\]
which is the standard positive-definite Hermitian form.

Thus properties (1)-(8) hold. Property (9) is vacuous here because `\(\dot\epsilon=-1\)`.

For the group identification, `\(G_{\mathbb C}\)` is the complex symplectic group of the standard alternating form. The condition `\(gJ=Jg\)` says exactly that the matrix of `\(g\)` is real. Hence
\[
G_{\mathbb C}^J
=\{g\in\operatorname{GL}_{2r}(\mathbb R):g^T\Omega_rg=\Omega_r\}
=\mathrm{Sp}_{2r}(\mathbb R)
=\mathrm{Sp}_{2p}(\mathbb R),
\]
where
\[
\Omega_r=
\begin{pmatrix}
0&I_r\\
-I_r&0
\end{pmatrix}.
\]
The same calculation applies to `\(\widetilde C\)`: the metaplectic double cover is not part of the present construction, so here one only obtains `\(\mathrm{Sp}_{2p}(\mathbb R)\)`.

### Case 3: `\(\star=C^*\)`

Here `\((\epsilon,\dot\epsilon)=(-1,1)\)` and `\(p,q\)` are even. Write
\[
p=2a,\qquad q=2b,\qquad m:=a+b,
\]
and let
\[
S_{a,b}:=\operatorname{diag}(I_a,-I_b).
\]
Set
\[
V=\mathbb C^{2m}=\mathbb C^m\oplus\mathbb C^m,
\]
with basis `\(e_1,\dots,e_m,f_1,\dots,f_m\)` as above. Define
\[
\langle (z,w),(z',w')\rangle:=z^TS_{a,b}w'-w^TS_{a,b}z',
\]
\[
J(z,w):=(-\overline w,\overline z),
\qquad
L(z,w):=(S_{a,b}z,S_{a,b}w).
\]

The form is alternating because its matrix is
\[
\begin{pmatrix}
0&S_{a,b}\\
-S_{a,b}&0
\end{pmatrix}.
\]
It is non-degenerate because `\(S_{a,b}\)` is invertible. The map `\(J\)` is conjugate-linear and
\[
J^2(z,w)=J(-\overline w,\overline z)=(-z,-w)=-(z,w),
\]
so `\(J^2=-1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and `\(L^2=1=\dot\epsilon\)`. Since `\(S_{a,b}\)` is real, `\(LJ=JL\)`.

Now compute
\[
\langle Ju,Jv\rangle
=\langle (-\overline w,\overline z),(-\overline w',\overline z')\rangle
=\overline z^{\,T}S_{a,b}\overline w'
-\overline w^{\,T}S_{a,b}\overline z'
=\overline{\langle u,v\rangle}.
\]
Also
\[
\langle Lu,Lv\rangle
=z^TS_{a,b}^3w'-w^TS_{a,b}^3z'
=\langle u,v\rangle,
\]
because `\(S_{a,b}^2=I_m\)`. Finally
\[
H((z,w),(z',w'))
=\langle (S_{a,b}z,S_{a,b}w),(-\overline w',\overline z')\rangle
=z^T\overline z'+w^T\overline w',
\]
so `\(H\)` is again the standard positive-definite Hermitian form.

The `\((+1)\)`-eigenspace of `\(L\)` is
\[
\mathbb C^a\oplus 0\oplus \mathbb C^a\oplus 0,
\]
which has complex dimension `\(2a=p\)`, and the `\((-1)\)`-eigenspace has complex dimension `\(2b=q\)`. Thus property (9) holds.

To identify the group, use the quaternionic structure coming from `\(J\)`. Regard `\(V\)` as a right `\(\mathbb H\)`-module by `\(v\cdot j:=Jv\)`. Define
\[
h(u,v):=\langle u,Jv\rangle+\langle u,v\rangle j.
\]
Because `\(J\)` is conjugate-linear and `\(J^2=-1\)`, this is `\(\mathbb H\)`-linear in the first variable and conjugate-linear in the second. In coordinates,
\[
h((z,w),(z',w'))
=z^TS_{a,b}\overline z'+w^TS_{a,b}\overline w'
+(z^TS_{a,b}w'-w^TS_{a,b}z')j.
\]
Its diagonal values on the quaternionic basis `\(q_r:=e_r\)` are
\[
h(q_r,q_r)=
\begin{cases}
1,&1\le r\le a,\\
-1,&a<r\le a+b,
\end{cases}
\]
so `\(h\)` is the standard quaternionic Hermitian form of signature `\((a,b)\)`.

Moreover, if `\(g\in G_{\mathbb C}^J\)`, then `\(g\)` commutes with `\(J\)`, hence is quaternionic-linear, and
\[
h(gu,gv)
=\langle gu,Jgv\rangle+\langle gu,gv\rangle j
=\langle gu,gJv\rangle+\langle gu,gv\rangle j
=h(u,v).
\]
So `\(G_{\mathbb C}^J\)` is contained in the quaternionic isometry group of `\(h\)`. Conversely, if a quaternionic-linear map preserves `\(h\)`, then it preserves both the complex part `\(\langle u,Jv\rangle\)` and the `\(j\)`-part `\(\langle u,v\rangle\)`, hence it preserves `\(\langle\ ,\ \rangle\)` and commutes with `\(J\)`. Therefore
\[
G_{\mathbb C}^J\simeq \mathrm{Sp}(a,b)=\mathrm{Sp}(p/2,q/2).
\]
So properties (1)-(10) hold in the `\(C^*\)` case.

### Case 4: `\(\star=D^*\)`

Here `\((\epsilon,\dot\epsilon)=(1,-1)\)` and `\(p=q\)`. Write `\(r:=p=q\)`. Let
\[
V=\mathbb C^{2r}=\mathbb C^r\oplus\mathbb C^r,
\]
with basis `\(e_1,\dots,e_r,f_1,\dots,f_r\)`. Define
\[
\langle (z,w),(z',w')\rangle:=-i(z^Tw'+w^Tz'),
\]
\[
J(z,w):=(-\overline w,\overline z),
\qquad
L(z,w):=(iz,-iw).
\]

The matrix of the form is
\[
-i
\begin{pmatrix}
0&I_r\\
I_r&0
\end{pmatrix},
\]
so the form is symmetric and non-degenerate. Again `\(J\)` is conjugate-linear and `\(J^2=-1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and
\[
L^2(z,w)=(-z,-w)=-(z,w),
\]
so `\(L^2=-1=\dot\epsilon\)`. A direct check gives `\(LJ=JL\)`.

For `\(u=(z,w)\)` and `\(v=(z',w')\)`,
\[
\langle Ju,Jv\rangle
=-i\bigl((-\overline w)^T\overline z'+\overline z^{\,T}(-\overline w')\bigr)
=\overline{-i(z^Tw'+w^Tz')}
=\overline{\langle u,v\rangle}.
\]
Also
\[
\langle Lu,Lv\rangle
=-i\bigl((iz)^T(-iw')+(-iw)^T(iz')\bigr)
=-i(z^Tw'+w^Tz')
=\langle u,v\rangle.
\]
Finally
\[
H((z,w),(z',w'))
=\langle (iz,-iw),(-\overline w',\overline z')\rangle
=z^T\overline z'+w^T\overline w',
\]
so `\(H\)` is positive definite. Thus properties (1)-(8) hold, and property (9) is again vacuous.

As in the `\(C^*\)` case, `\(J\)` gives a right `\(\mathbb H\)`-module structure on `\(V\)`. Define
\[
\kappa(u,v):=\langle u,Jv\rangle+\langle u,v\rangle j.
\]
Because the bilinear form is symmetric and `\(J^2=-1\)`, one has
\[
\kappa(v,u)=-\overline{\kappa(u,v)},
\]
so `\(\kappa\)` is quaternionic skew-Hermitian. In coordinates,
\[
\kappa((z,w),(z',w'))
=-i(z^T\overline z'-w^T\overline w')
-i(z^Tw'+w^Tz')j.
\]
Its values on the quaternionic basis `\(q_r:=e_r\)` satisfy
\[
\kappa(q_r,q_s)=-i\,\delta_{rs},
\]
so this is the standard non-degenerate quaternionic skew-Hermitian form on `\(\mathbb H^r\)`.

If `\(g\in G_{\mathbb C}^J\)`, then `\(g\)` is quaternionic-linear and
\[
\kappa(gu,gv)
=\langle gu,Jgv\rangle+\langle gu,gv\rangle j
=\kappa(u,v).
\]
Conversely, a quaternionic-linear isometry of `\(\kappa\)` preserves both `\(\langle u,Jv\rangle\)` and `\(\langle u,v\rangle\)`, so it belongs to `\(G_{\mathbb C}^J\)`. Therefore
\[
G_{\mathbb C}^J\simeq \mathrm O^*(2r)=\mathrm O^*(2p).
\]
This proves properties (1)-(10) in the `\(D^*\)` case.

### Uniqueness

Let a quadruple mean a tuple `(V,\langle\ ,\ \rangle,J,L)` satisfying properties
(1)--(9) for a fixed classical signature.  In every case we prove the stronger
normal-form statement: every quadruple is isomorphic to the corresponding
standard model constructed above.  If two quadruples are both identified with
that standard model, composing one identification with the inverse of the other
produces the required isomorphism between them.  Thus it is enough to prove the
normal form in the four sign patterns.

We use the following elementary facts throughout.

1. If `J` is conjugate-linear and `J^2=1`, then
   \[
   V_{\mathbb R}:=V^J=\{v:Jv=v\}
   \]
   is a real vector space and every `v\in V` has the unique decomposition
   \[
   v=x+i y,
   \qquad
   x={1\over2}(v+Jv),\qquad
   y={1\over 2i}(v-Jv),
   \]
   with `x,y\in V_{\mathbb R}`.  Hence
   `V\simeq V_{\mathbb R}\otimes_{\mathbb R}\mathbb C`, and a complex-linear
   map commuting with `J` is determined by its restriction to `V_{\mathbb R}`.
2. A positive-definite real symmetric form admits an orthonormal basis, and a
   positive-definite Hermitian form admits an orthonormal basis.  These are just
   Gram-Schmidt.
3. If `J^2=-1`, then `V` is a right quaternionic vector space by
   `v\cdot j=Jv`.  A complex subspace stable under `J` has even complex
   dimension; a quaternionic line generated by a nonzero vector `e` has complex
   basis `e,Je`.  Orthogonal complements for the positive Hermitian form `H` are
   again `J`-stable in the situations below, so Gram-Schmidt can be run
   quaternionically.

For the Lean formalization we split each normal-form proof into two layers.

* **Adapted basis existence.**  This is the actual mathematical normal-form
  work: construct a basis satisfying explicit identities for the bilinear form,
  `J`, and `L`.
* **Adapted basis to coordinate isomorphism.**  Once such a basis is available,
  define the map to the standard coordinate model by taking basis coordinates.
  Preservation of the bilinear form is checked on basis vectors and extended by
  bilinearity; intertwining with `J` and `L` is checked on basis vectors and
  extended by semilinearity/linearity.

Concretely, in the `B,D` case the adapted basis data consists of a complex basis
\[
b:\operatorname{Fin}(p)\sqcup\operatorname{Fin}(q)\to V
\]
such that, writing `e_i=b(\operatorname{inl} i)` and
`f_j=b(\operatorname{inr} j)`,
\[
Je_i=e_i,\qquad Jf_j=f_j,\qquad Le_i=e_i,\qquad Lf_j=-f_j,
\]
and
\[
\langle e_i,e_j\rangle=\delta_{ij},\qquad
\langle f_i,f_j\rangle=-\delta_{ij},\qquad
\langle e_i,f_j\rangle=\langle f_j,e_i\rangle=0.
\]
The coordinate map
\[
\Phi:V\to \mathbb C^p\oplus\mathbb C^q,\qquad
v\mapsto ((b^{-1}v)_{\operatorname{inl} i},
          (b^{-1}v)_{\operatorname{inr} j})
\]
is a complex-linear equivalence.  The displayed identities imply
\[
\langle \Phi u,\Phi v\rangle_{p,q}=\langle u,v\rangle,\qquad
\Phi(Jv)=J_{\mathrm{std}}\Phi(v),\qquad
\Phi(Lv)=L_{\mathrm{std}}\Phi(v).
\]
This is the exact content of the Lean conversion from an
`OrthogonalAdaptedBasis` to `orthogonalNormalFormIso`.

In the `C,\widetilde C` case the adapted basis is
`e_1,\ldots,e_r,f_1,\ldots,f_r`, indexed by
`\operatorname{Fin}(r)\sqcup\operatorname{Fin}(r)`, with
\[
Je_i=e_i,\quad Jf_i=f_i,\quad Le_i=-f_i,\quad Lf_i=e_i,
\]
and
\[
\omega(e_i,f_j)=\delta_{ij},\qquad
\omega(f_i,e_j)=-\delta_{ij},\qquad
\omega(e_i,e_j)=\omega(f_i,f_j)=0.
\]
The same coordinate construction gives the standard symplectic model.

In the `C^*` case the adapted quaternionic basis is
\[
e_1,Je_1,\ldots,e_a,Je_a,\quad e'_1,Je'_1,\ldots,e'_b,Je'_b,
\]
where the first block lies in the `L=+1` eigenspace and the second block in the
`L=-1` eigenspace.  The bilinear pairings are
`\langle e_i,Je_j\rangle=\delta_{ij}` on the positive block and
`\langle e'_i,Je'_j\rangle=-\delta_{ij}` on the negative block, all same-type
and cross-block pairings being zero.  Coordinate extraction in this basis gives
the standard `C^*` model.

In the `D^*` case the adapted basis is
\[
e_1,\ldots,e_r,Je_1,\ldots,Je_r,
\]
where `e_i` is an orthonormal basis of the `A=+1` eigenspace for `A=-iL`.
Then `Le_i=i e_i`, `L(Je_i)=-iJe_i`, the two eigenspaces are totally isotropic,
and
\[
\langle e_i,Je_j\rangle=-i\delta_{ij}.
\]
Again the coordinate map in this basis is the required isomorphism to the
standard `D^*` model.

#### Uniqueness for `\(B,D\)`

Here `(\epsilon,\dot\epsilon)=(1,1)`, so `J^2=1` and `L^2=1`.  Put
\[
V_{\mathbb R}:=V^J.
\]
For `x,y\in V_{\mathbb R}` we have
\[
\langle x,y\rangle=\langle Jx,Jy\rangle
=\overline{\langle x,y\rangle},
\]
so the restriction
\[
B_{\mathbb R}(x,y):=\langle x,y\rangle
\]
actually takes values in `\mathbb R`; it is a real symmetric bilinear form.
Since `LJ=JL`, `L` preserves `V_{\mathbb R}`.  Let
\[
E_+^{\mathbb R}:=\ker(L-1)\cap V_{\mathbb R},
\qquad
E_-^{\mathbb R}:=\ker(L+1)\cap V_{\mathbb R}.
\]
The complex eigenspaces `\widetilde E_\pm:=\ker(L\mp1)` are `J`-stable.  If
`v\in\widetilde E_+` and `v=x+i y` is the real-form decomposition above, then
`Jv=x-i y` is also in `\widetilde E_+`; hence both
\[
 x={1\over2}(v+Jv),\qquad y={1\over2i}(v-Jv)
\]
lie in `E_+^{\mathbb R}`.  Thus
`\widetilde E_+=E_+^{\mathbb R}\otimes_{\mathbb R}\mathbb C`.  The same
argument gives
`\widetilde E_-=E_-^{\mathbb R}\otimes_{\mathbb R}\mathbb C`.  Property (9)
therefore implies
\[
\dim_{\mathbb R}E_+^{\mathbb R}=p,
\qquad
\dim_{\mathbb R}E_-^{\mathbb R}=q.
\]
Because `L^2=1`, every real vector decomposes as
\[
x={1\over2}(x+Lx)+{1\over2}(x-Lx),
\]
with the two summands in `E_+^{\mathbb R}` and `E_-^{\mathbb R}` respectively;
therefore
\[
V_{\mathbb R}=E_+^{\mathbb R}\oplus E_-^{\mathbb R}.
\]
If `x\in E_+^{\mathbb R}` and `y\in E_-^{\mathbb R}`, then form preservation by
`L` gives
\[
B_{\mathbb R}(x,y)=B_{\mathbb R}(Lx,Ly)=B_{\mathbb R}(x,-y)=-B_{\mathbb R}(x,y),
\]
so `B_{\mathbb R}(x,y)=0`.  Thus the two real eigenspaces are orthogonal.
For `x\in E_+^{\mathbb R}\setminus0`,
\[
H(x,x)=\langle Lx,Jx\rangle=\langle x,x\rangle=B_{\mathbb R}(x,x)>0.
\]
For `y\in E_-^{\mathbb R}\setminus0`,
\[
H(y,y)=\langle Ly,Jy\rangle=\langle -y,y\rangle=-B_{\mathbb R}(y,y)>0.
\]
Hence `B_{\mathbb R}` is positive definite on `E_+^{\mathbb R}` and negative
definite on `E_-^{\mathbb R}`.

Choose a `B_{\mathbb R}`-orthonormal basis
`e_1,\ldots,e_p` of `E_+^{\mathbb R}` and a `(-B_{\mathbb R})`-orthonormal
basis `f_1,\ldots,f_q` of `E_-^{\mathbb R}`.  In the complexified basis
\[
e_1,\ldots,e_p,f_1,\ldots,f_q
\]
of `V`, the matrix of the bilinear form is `\operatorname{diag}(I_p,-I_q)`,
`J` is entrywise complex conjugation because the basis vectors are `J`-fixed,
and `L` is `+1` on the `e_i` and `-1` on the `f_j`.  This is exactly the
standard `B,D` model.  Therefore every `B,D` quadruple is isomorphic to the
standard model.

#### Uniqueness for `\(C,\widetilde C\)`

Here `(\epsilon,\dot\epsilon)=(-1,-1)`, so `J^2=1` and `L^2=-1`.  Again put
`V_{\mathbb R}:=V^J`.  The restriction
\[
\omega(x,y):=\langle x,y\rangle\qquad(x,y\in V_{\mathbb R})
\]
is a real alternating form.  It is non-degenerate on `V_{\mathbb R}`: if
`\omega(x,y)=0` for every real `y`, then by complex bilinearity and the real-form
decomposition the complex form pairs `x` trivially with every vector of `V`, so
`x=0` by non-degeneracy over `\mathbb C`.

Define
\[
g(x,y):=H(x,y)=\langle Lx,Jy\rangle=\omega(Lx,y)
\qquad(x,y\in V_{\mathbb R}).
\]
The Hermitian symmetry of `H` and the fact that `x,y` are `J`-fixed imply that
`g` is a real symmetric bilinear form; positivity of `H` gives positive
definiteness of `g`.  Since `L` preserves `\omega` and `L^2=-1`,
\[
g(Lx,Ly)=\omega(L^2x,Ly)=\omega(-x,Ly)=\omega(Lx,y)=g(x,y),
\]
so `L` is `g`-orthogonal.  Also
\[
g(x,Lx)=\omega(Lx,Lx)=0
\]
because `\omega` is alternating.

We now construct an adapted basis by induction.  Choose a `g`-unit vector `e_1`
and set
\[
f_1:=-Le_1.
\]
Then `f_1` is also `g`-unit, `g(e_1,f_1)=0`, and
\[
\omega(e_1,f_1)=\omega(e_1,-Le_1)=\omega(Le_1,e_1)=g(e_1,e_1)=1,
\]
where the middle equality uses alternation of `\omega`.  Let
`P_1=\operatorname{span}_{\mathbb R}\{e_1,f_1\}` and let
`P_1^{\perp_g}` be its `g`-orthogonal complement.  This complement is
`L`-stable: if `x\perp_g e_1,f_1`, then, using `L^{-1}=-L` and `Lf_1=e_1`,
\[
g(Lx,e_1)=g(x,L^{-1}e_1)=g(x,f_1)=0,
\qquad
 g(Lx,f_1)=g(x,L^{-1}f_1)=g(x,-e_1)=0.
\]
It is also symplectic: if `x\in P_1^{\perp_g}` and
`\omega(x,y)=0` for every `y\in P_1^{\perp_g}`, then `x` pairs trivially with
`P_1` as well because `P_1` is generated by `e_1` and `-Le_1`, and the
relations above give the required pairings.  Thus non-degeneracy of `\omega`
forces `x=0`.

Repeating the construction on the `L`-stable complement gives a `g`-orthonormal
basis
\[
e_1,\ldots,e_p,f_1,\ldots,f_p
\]
of `V_{\mathbb R}` with `f_i=-Le_i` and
\[
\omega(e_i,f_j)=\delta_{ij},
\qquad
\omega(e_i,e_j)=0,
\qquad
\omega(f_i,f_j)=0.
\]
Indeed, vectors from later induction steps lie in the `g`-orthogonal complement
of earlier pairs, and since `g(x,y)=\omega(Lx,y)` this also gives the vanishing
of the unwanted `\omega`-pairings.

In the associated complex basis of `V`, the form is the standard symplectic
form, `J` is entrywise conjugation, and `L(e_i)=-f_i`, `L(f_i)=e_i`, which is
exactly the standard model after the harmless convention `f_i=-Le_i`.  Hence
every `C,\widetilde C` quadruple is isomorphic to the standard model.

#### Uniqueness for `\(C^*\)`

Here `(\epsilon,\dot\epsilon)=(-1,1)`, so `J^2=-1` and `L^2=1`.  The operator
`J` makes `V` a right quaternionic vector space.  Put
\[
E_+:=\ker(L-1),
\qquad
E_-:=\ker(L+1).
\]
Since `LJ=JL`, both `E_+` and `E_-` are stable under `J`, hence are
quaternionic subspaces.  Property (9) says
\[
\dim_{\mathbb C}E_+=2a,
\qquad
\dim_{\mathbb C}E_-=2b,
\]
so their quaternionic dimensions are `a` and `b`.  Since `L^2=1`,
`V=E_+\oplus E_-`.

If `x\in E_+` and `y\in E_-`, form preservation by `L` gives
\[
\langle x,y\rangle=\langle Lx,Ly\rangle=\langle x,-y\rangle=-\langle x,y\rangle,
\]
so `\langle x,y\rangle=0`.  Also `Jy\in E_-`, so the same argument gives
`\langle x,Jy\rangle=0`.  Therefore `E_+` and `E_-` are orthogonal both for the
complex bilinear form and for the quaternionic Hermitian form
\[
h(u,v):=\langle u,Jv\rangle+\langle u,v\rangle j.
\]

On `E_+`,
\[
\langle x,Jy\rangle=\langle Lx,Jy\rangle=H(x,y),
\]
whereas on `E_-`,
\[
\langle x,Jy\rangle=-H(x,y).
\]
The positive-definite Hermitian form `H` is compatible with `J`: for vectors in
one of the eigenspaces, `H(Jx,Jy)=\overline{H(x,y)}`.  This follows by expanding
`H(Jx,Jy)=\langle LJx,J(Jy)\rangle`, using `LJ=JL`, `J^2=-1`, and
`\langle Ju,Jv\rangle=\overline{\langle u,v\rangle}`.  In particular, if `e` is
`H`-unit in either eigenspace, then `Je` is also `H`-unit, and
\[
H(e,Je)=\langle Le,J(Je)\rangle=\mp\langle e,e\rangle=0
\]
because the form is alternating.  Thus the complex span of `e,Je` is an
orthonormal quaternionic line.

Now apply quaternionic Gram-Schmidt.  Choose `H`-unit vectors
`e_1,\ldots,e_a\in E_+` so that
\[
 e_1,Je_1,\ldots,e_a,Je_a
\]
is an `H`-orthonormal complex basis of `E_+`; at each step the `H`-orthogonal
complement of the quaternionic line is `J`-stable by the compatibility just
mentioned.  Similarly choose `H`-unit vectors
`e_{a+1},\ldots,e_{a+b}\in E_-` such that
\[
 e_{a+1},Je_{a+1},\ldots,e_{a+b},Je_{a+b}
\]
is an `H`-orthonormal complex basis of `E_-`.  Put
\[
f_r:=Je_r.
\]

For `1\le r,s\le a`,
\[
\langle e_r,f_s\rangle
=\langle e_r,Je_s\rangle
=H(e_r,e_s)=\delta_{rs}.
\]
For `a<r,s\le a+b`,
\[
\langle e_r,f_s\rangle
=\langle e_r,Je_s\rangle
=-H(e_r,e_s)=-\delta_{rs}.
\]
If `r` and `s` lie in different blocks, the same pairing is zero by the
orthogonality of `E_+` and `E_-`.  Also
\[
\langle e_r,e_s\rangle=0
\]
inside each block because the form is alternating and across blocks by the
orthogonality just proved.  Finally
\[
\langle f_r,f_s\rangle
=\langle Je_r,Je_s\rangle
=\overline{\langle e_r,e_s\rangle}=0.
\]
In the complex basis
\[
e_1,\ldots,e_{a+b},f_1,\ldots,f_{a+b}
\]
the form has matrix
`\begin{pmatrix}0&S_{a,b}\\-S_{a,b}&0\end{pmatrix}`, `J(e_r)=f_r`,
`J(f_r)=-e_r` up to entrywise conjugation on complex coefficients, and `L` is
`+1` on the first `a` quaternionic lines and `-1` on the last `b`.  This is
exactly the standard `C^*` model.  Therefore every `C^*` quadruple is
isomorphic to the standard model.

#### Uniqueness for `\(D^*\)`

Here `(\epsilon,\dot\epsilon)=(1,-1)`, so `J^2=-1` and `L^2=-1`.  Set
\[
A:=-iL.
\]
Then `A` is complex-linear and `A^2=1`.  It is self-adjoint for the positive
Hermitian form `H`.  Indeed,
\[
H(Lu,v)=\langle L^2u,Jv\rangle=-\langle u,Jv\rangle,
\]
and, using `LJ=JL` and preservation of the bilinear form by `L`,
\[
H(u,Lv)=\langle Lu,JLv\rangle=\langle Lu,LJv\rangle=\langle u,Jv\rangle.
\]
Thus `H(Lu,v)=-H(u,Lv)`, and consequently
\[
H(Au,v)=-iH(Lu,v)=iH(u,Lv)=H(u,Av),
\]
with the last equality using conjugate-linearity of `H` in its second variable.
Let
\[
E_+:=\ker(A-1),
\qquad
E_-:=\ker(A+1).
\]
Since `A^2=1`, `V=E_+\oplus E_-`; since `A` is `H`-self-adjoint, this
decomposition is `H`-orthogonal.  Also
\[
JA u=J(-iLu)=iLJu=-AJu,
\]
so `J` maps `E_+` conjugate-linearly isomorphically onto `E_-`.  Hence
\[
\dim_{\mathbb C}E_+=\dim_{\mathbb C}E_-.
\]
Property (1) gives `\dim_{\mathbb C}V=2r`, so both dimensions are `r`.

If `x,y\in E_+`, then `Lx=i x` and `Ly=i y`, whence
\[
\langle x,y\rangle
=\langle Lx,Ly\rangle
=\langle ix,iy\rangle
=-\langle x,y\rangle,
\]
so `\langle x,y\rangle=0`.  The same argument for `E_-`, where `L=-i`, shows
that `E_-` is also totally isotropic.

Choose an `H`-orthonormal basis `e_1,\ldots,e_r` of `E_+` and set
\[
f_s:=Je_s\in E_-.
\]
The vectors `f_s` form an `H`-orthonormal basis of `E_-`: expanding
`H(Je_r,Je_s)` and using `J^2=-1`, `LJ=JL`, and
`\langle Ju,Jv\rangle=\overline{\langle u,v\rangle}` gives
\[
H(Je_r,Je_s)=\overline{H(e_r,e_s)}=\delta_{rs}.
\]
The two blocks are `H`-orthogonal by the self-adjoint decomposition above, so
\[
e_1,\ldots,e_r,f_1,\ldots,f_r
\]
is an `H`-orthonormal basis of `V` adapted to `A` and `J`.

Since `e_r\in E_+`, `Le_r=i e_r`.  Therefore
\[
\delta_{rs}
=H(e_r,e_s)
=\langle Le_r,Je_s\rangle
=\langle i e_r,f_s\rangle
=i\langle e_r,f_s\rangle,
\]
so
\[
\langle e_r,f_s\rangle=-i\delta_{rs}.
\]
The two eigenspaces are totally isotropic, hence
\[
\langle e_r,e_s\rangle=0,
\qquad
\langle f_r,f_s\rangle=0.
\]
Thus the matrix of the symmetric bilinear form in this basis is
\[
-i\begin{pmatrix}0&I_r\\ I_r&0\end{pmatrix},
\]
`L` acts by `i` on the `e`-block and by `-i` on the `f`-block, and `J(e_r)=f_r`,
`J(f_r)=-e_r` up to conjugation on coefficients.  This is exactly the standard
`D^*` model.  Therefore every `D^*` quadruple is isomorphic to the standard
model.

Combining the four normal-form results, any two quadruples for the same
classical signature are both isomorphic to the same standard model.  Composing
one standard-model isomorphism with the inverse of the other yields a
complex-linear isomorphism preserving the bilinear form and intertwining both
`J` and `L`.  This proves uniqueness.
