# ClassicalGroup problem source

Source: `lean/docs/blueprints/classical_group/problem.md`

# Problem: Construct classical spaces and identify the associated classical groups

## Background and notation

Throughout
\[
\star\in\{B,C,D,\widetilde C,C^*,D^*\}.
\]
Attach signs
\[
(\epsilon,\dot\epsilon)=
\begin{cases}
(1,1),&\star=B,D,\\
(-1,-1),&\star=C,\widetilde C,\\
(-1,1),&\star=C^*,\\
(1,-1),&\star=D^*.
\end{cases}
\]
A **classical signature** is a triple
\[
\mathsf s=(\star,p,q)
\]
satisfying
\[
\begin{cases}
p+q\text{ is odd},&\star=B,\\
p+q\text{ is even},&\star=D,\\
p=q,&\star=C,\widetilde C,D^*,\\
p,q\text{ are even},&\star=C^*.
\end{cases}
\]
Write
\[
|\mathsf s|:=p+q.
\]

All vector spaces below are finite-dimensional complex vector spaces.  A complex bilinear form
\(\langle\ ,\ \rangle\) is called \(\epsilon\)-symmetric if
\[
\langle u,v\rangle=\epsilon\langle v,u\rangle.
\]
Thus \(\epsilon=1\) means symmetric and \(\epsilon=-1\) means alternating.

If \((V,\langle\ ,\ \rangle)\) is such a space, let
\[
G_{\mathbb C}:=\operatorname{Isom}_{\mathbb C}(V,\langle\ ,\ \rangle)
\]
be its complex isometry group.

For a conjugate-linear operator \(J:V\to V\), define
\[
G_{\mathbb C}^{J}:=\{g\in G_{\mathbb C}:gJ=Jg\}.
\]
For a linear operator \(L:V\to V\), define
\[
G_{\mathbb C}^{L}:=\{g\in G_{\mathbb C}:gL=Lg\}.
\]

The expected real classical groups are
\[
\begin{cases}
\mathrm O(p,q),&\star=B\text{ or }D,\\
\mathrm {Sp}_{2p}(\mathbb R),&\star=C\text{ or }\widetilde C,\\
\mathrm {Sp}(p/2,q/2),&\star=C^*,\\
\mathrm O^*(2p),&\star=D^*.
\end{cases}
\]
Here the notation uses the above signature restrictions: for \(\star=C,\widetilde C,D^*\) one has \(p=q\), and for \(\star=C^*\) one has \(p,q\) even.

## Given facts / allowed inputs

Do not use Ohta's construction as a black box.  The task is to give an explicit construction and verification.

You may use only standard elementary linear algebra facts, for example:

1. every non-degenerate symmetric complex bilinear form has an orthonormal basis;
2. every non-degenerate alternating complex bilinear form has a symplectic basis;
3. a conjugate-linear involution defines a real form;
4. a conjugate-linear operator squaring to \(-1\) defines a quaternionic structure;
5. the usual definitions of
   \(\mathrm O(p,q)\),
   \(\mathrm{Sp}_{2p}(\mathbb R)\),
   \(\mathrm{Sp}(a,b)\), and
   \(\mathrm O^*(2p)\).

If any of these standard facts need a particular convention, state the convention explicitly.

## Target claims

Prove the following theorem.

**Theorem.**  For every classical signature \(\mathsf s=(\star,p,q)\), there exists a quadruple
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

## Required construction or proof details

The proof must include explicit models for \((V,\langle\ ,\ \rangle,J,L)\) in all four sign cases:

1. \(\star=B,D\), where \((\epsilon,\dot\epsilon)=(1,1)\);
2. \(\star=C,\widetilde C\), where \((\epsilon,\dot\epsilon)=(-1,-1)\) and \(p=q\);
3. \(\star=C^*\), where \((\epsilon,\dot\epsilon)=(-1,1)\) and \(p,q\) are even;
4. \(\star=D^*\), where \((\epsilon,\dot\epsilon)=(1,-1)\) and \(p=q\).

For each case, the solver must:

1. specify a basis of \(V\);
2. write the bilinear form \(\langle\ ,\ \rangle\) in that basis;
3. define the conjugate-linear map \(J\) explicitly;
4. define the complex-linear map \(L\) explicitly;
5. verify properties (1)--(9) above by direct calculation;
6. identify \(G_{\mathbb C}^{J}\) with the corresponding real classical group in property (10).

In the quaternionic cases \(C^*\) and \(D^*\), the proof must make explicit how the condition \(J^2=-1\) gives a quaternionic structure and how the bilinear form corresponds to the standard quaternionic Hermitian or skew-Hermitian form whose isometry group is respectively \(\mathrm{Sp}(p/2,q/2)\) or \(\mathrm O^*(2p)\).

In the metaplectic case \(\star=\widetilde C\), only identify
\(G_{\mathbb C}^{J}\simeq \mathrm{Sp}_{2p}(\mathbb R)\).  The metaplectic double cover is an additional external cover convention and is not part of the construction of \(J,L\).

## Completeness check requested

Before proving, check whether the problem statement is complete.  In particular, verify whether the following conventions are sufficient:

1. whether \(\mathrm O(p,q)\) means the full orthogonal group rather than \(\mathrm{SO}(p,q)\) or the identity component;
2. whether \(\mathrm O^*(2p)\) is being used with the standard convention as the real form of \(\mathrm O(2p,\mathbb C)\) preserving a quaternionic skew-Hermitian structure;
3. whether \(\mathrm{Sp}(p/2,q/2)\) is being used with the standard convention as the quaternionic unitary group preserving a quaternionic Hermitian form of signature \((p/2,q/2)\);
4. whether any additional convention is needed for sesquilinearity of quaternionic forms.

If the statement is incomplete or ambiguous, state the minimal repairs before attempting the proof.

## Expected output

Return a self-contained solution with:

1. a short completeness check;
2. explicit constructions of \(V,\langle\ ,\ \rangle,J,L\) in each case;
3. direct verification of all listed properties;
4. identification of \(G_{\mathbb C}^{J}\) in each case;
5. a proof of uniqueness up to isomorphism.
