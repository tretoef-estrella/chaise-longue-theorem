# THE CHAISE LONGUE THEOREM AND THE CENTRALIZER OF A REGULAR UNIPOTENT ELEMENT
## A dictionary, with attributions

**Rafael Amichis Luengo**

Madrid, Spain · tretoef@gmail.com · 1 October 2026 · version 1

A supplement to *The Chaise Longue Theorem*, version 10 (doi:10.5281/zenodo.22961150), cited below as [CL]. In this note `Z` is the ring of integers and `𝒵` is a centralizer.

---
## Summary

This note places the two counts of [CL] in Lie theory, and says what in them belongs to whom.

1. **The dictionary.** The box ring `F[x_1, …, x_n]/(x_i^r)` is the tensor power `V^{⊗n}` of `V = F[x]/(x^r)`. With the natural form on `V`, multiplication by `x` is a regular nilpotent element `e` of `so_r` (odd `r`) or `sp_r` (even `r`). Over an infinite field, the ring of Theorem A of [CL] is the space of coinvariants of the centralizer of a regular unipotent element in `V^{⊗n}`. The generators `D_J` of Theorem B of [CL] are the invariant tensors of the group (the Brauer matchings).
2. **Theorem A, as a count, is not ours.** In characteristic `0` it follows from a theorem of Kostant (1963). In odd characteristic it follows from a proposition of Bezrukavnikov, Riche and Rider (2020). [CL] v9 credited Kostant and said that no version in positive characteristic was known to us; that was wrong, and [CL] v10 corrects it. What [CL] contributes to Theorem A is the dictionary and an elementary proof.
3. **Theorem B in this language.** Theorem B of [CL], which for degree `p^v` is the algebraic form of Conjecture 1.2 of Degtyarev and Shimada, says: *the invariant tensors of `Sp_{q−1}` generate, under the `N` commuting copies of `e`, a subspace of `V^{⊗N}` whose dimension is that of the zero weight space, over every field.* With the proposition of Bezrukavnikov–Riche–Rider, that subspace is, in characteristic `≠ 2`, the whole space of invariants of the centralizer (as an algebraic group). In characteristic `0` there is also a derivation from Kostant's theorem and the first fundamental theorem of invariant theory (§4.3, a sketch). In characteristic `p` we know no derivation from the literature; the proof is that of [CL].
4. **What is open.** The same statement for the orthogonal group (the odd box) holds in characteristic `0` and at every cell we computed, and is not proved in characteristic `p`. The analogue of Theorem A for even `q` and odd `n` is not proved either.
5. **Two things that are ours and small.** A statistic on lattice walks whose generating function is the Hilbert series of the ring of Theorem A (a theorem, given Appendix A of [CL]; that appendix also gives, for every weight `μ`, an ideal whose colength is the multiplicity of `μ`); and the observation, computed and not proved, that the ideals `K_μ` of that appendix have the Hilbert series of Lusztig's `t`-analogues of weight multiplicities.

§8 is a table of what belongs to whom. §9 lists what was read in the original and what was not.

---
## 1. The dictionary

Let `F` be a field with `2 ∈ F^×`, let `r ≥ 2`, and let `V := F[x]/(x^r)` with the bilinear form

`⟨x^a, x^b⟩ := (−1)^a` if `a + b = r − 1`, and `0` otherwise.

The form is nondegenerate. It is symmetric if `r` is odd and alternating if `r` is even, because `⟨x^b, x^a⟩ = (−1)^b = (−1)^{r−1}(−1)^a`. Let `e` be multiplication by `x`. Then `⟨eu, v⟩ = −⟨u, ev⟩`, and `e` is nilpotent with a single Jordan block.

**Lemma 1.1.** *An endomorphism of `V` commutes with `e` iff it is a polynomial `f(e)`. It preserves the form iff `f(e)f(−e) = 1`. The centralizer of `e` in the group `G` of isometries of determinant `1` is `𝒵` for odd `r` and `{±1} × 𝒵` for even `r`, where*

`𝒵 := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`,

*a commutative unipotent group. For `t ∈ F^×` the Cayley transform `g_t := (1 + te)(1 − te)^{−1}` is an element of `𝒵` with a single Jordan block, and its centralizer in `G` is the centralizer of `e`.*

*Proof.* `V` is a cyclic module for `F[e]`, so the commutant of `e` is `F[e]`. The adjoint of `e` for the form is `−e`, so the adjoint of `f(e)` is `f(−e)`. The constant term of `f(e)f(−e) = 1` gives `f(0) = ±1`, and `det f(e) = f(0)^r`. For `g_t`: `g_t(e)g_t(−e) = 1` is clear, `g_t − 1 = 2te(1 − te)^{−1}` has rank `r − 1`, and `e = (g_t − 1)·(t(g_t + 1))^{−1}` is a polynomial in `g_t`. ∎

So `g_t` is a regular unipotent element of `SO_r` (odd `r = 2m + 1`) or `Sp_r` (even `r = 2m`), and `e` is a regular nilpotent element of the Lie algebra.

**The tensor power.** For a set `L` of `n` variables, `B_r(L) := F[L]/(x^r : x ∈ L) = V^{⊗n}`. The element `f(e)`, acting diagonally, is multiplication by `Π_{x∈L} f(x)`. Put `E(t) := Π_{x∈L}(1 + tx) = Σ_j e_j(L)t^j`.

**Proposition 1.2 (the dictionary).** *Let `F` be infinite. The subspace of `B_r(L)` spanned by the elements `(g − 1)v` with `g ∈ 𝒵` is the ideal `(e_j(L) : j odd)`. So*

`F[L]/((e_j(L) : j odd) + (x^r : x ∈ L)) = (V^{⊗n})_𝒵`,

*the space of coinvariants of `𝒵`, and its dimension is `dim (V^{⊗n})^𝒵`.*

*Proof.* `g_t` acts as `E(t)/E(−t)`, and `E(t)/E(−t) − 1 = 2(Σ_{j odd} e_j t^j)·E(−t)^{−1}`, a polynomial in `t` with coefficients in `B_r(L)`. The coefficient of `t^i` is `2e_i` plus a combination of the `e_j` with `j < i` odd, so the coefficients generate `(e_j : j odd)`; for infinite `F` the values at `t ∈ F` span the same space as the coefficients. For a general `f(e) ∈ 𝒵` put `h := 1 + f`; then `h(0) = 2` is a unit and `f(x) = h(x)/h(−x)`, because `f(x)·(1 + f(−x)) = f(x) + 1`. So `Π_x f(x) − 1 = (H − H^−)/H^−` with `H := Π_x h(x)`, `H^− := Π_x h(−x)`. `H − H^−` is twice the sum of the homogeneous components of odd degree of the symmetric polynomial `H`, and every symmetric polynomial of odd degree lies in `(e_j : j odd)`, since a monomial of odd weight in the `e_j` contains an `e_j` with `j` odd. Finally `V^{⊗n}` is isomorphic to its dual as a `𝒵`-module, through the form, and the dual of the coinvariants of a module is the space of invariants of its dual. ∎

*Remarks.* (1) In characteristic `0` the invariants of `𝒵` are the vectors killed by its Lie algebra, which has basis `e, e^3, e^5, …` (the odd powers below `r`); `e^j` acts as multiplication by the power sum `p_j(L)`, and `(p_j : j odd) = (e_j : j odd)` by Newton's identities. The numbers `1, 3, 5, …` are the exponents of the root systems `B_m` and `C_m`: this is why the odd elementary symmetric polynomials appear. (2) The weights of `V` are `0, ±ε_1, …, ±ε_m` for odd `r` and `±ε_1, …, ±ε_m` for even `r`. A weight vector of `V^{⊗n}` is a walk of length `n` on the lattice `Z^m`, with a loop for the weight `0`. The zero weight space has dimension the number of closed walks: `N_r(n) := n!·[y^n] e^y I_0(2y)^m` for odd `r`, and `n!·[y^n] I_0(2y)^m` for even `r`. (3) The hypothesis that `F` is infinite cannot be dropped. Over `F_3` the group `𝒵` is finite, and its coinvariants have dimension `9`, `27` and `19` at `(r, n) = (3, 3), (3, 4)` and `(5, 3)`, against `7`, `19` and `13` for the ring (computed; at `(3, 3)` and `(5, 3)` over `F_5` the two numbers agree). Over a finite field the proposition holds for the centralizer as an algebraic group, that is, after extension of scalars to an infinite field; the dimension of the ring does not change under such an extension.

## 2. Theorem A is a count for this centralizer

**Theorem A** ([CL, §8]). *Let `char F ≠ 2`, `q` odd, `|L| = n`. Then `dim_F F[L]/((e_j(L) : j odd) + (x^q)) = N_q(n)`.*

By Proposition 1.2 this says: `dim (V^{⊗n})^𝒵 = dim (V^{⊗n})^T`, the dimension of the zero weight space, for the vector representation of `SO_q`.

**2.1 Characteristic `0`: Kostant.** For a connected semisimple group `G` over `C` and a finite-dimensional `G`-module `W` whose weights lie in the root lattice, `x ↦ dim W^{𝔤^x}` is constant on the regular elements of `𝔤` (Kostant [Kos], as stated in [Gin, Proposition 4.2]). At a regular semisimple `x` the space `W^{𝔤^x}` is the zero weight space. The weights of `V^{⊗n}` lie in the root lattice of `so_{2m+1}`. So Theorem A in characteristic `0` follows from Kostant's theorem.

**2.2 Odd characteristic: Bezrukavnikov–Riche–Rider.** Let `K` be algebraically closed of characteristic `ℓ`, `G` connected reductive over `K` with simply connected derived subgroup, `ℓ` good for `G`, and `X^*(T)/ZR` without `ℓ`-torsion. Then [BRR, Proposition 2.12]:

> *For any finite-dimensional `G`-module `W` which admits a good filtration and any regular unipotent element `u ∈ G`, `dim W^{Z_G(u)} = dim W^T`.*

Their proof uses the Springer and Grothendieck resolutions: `(W ⊗ O(g̃))^G` is free over `O(𝔱)`; its fibre at `0` is `W^{Z_G(u)}`, by the vanishing and the good filtration of Kumar–Lauritzen–Thomsen [KLT], and its fibre over the regular semisimple locus is `W^T`.

Take `G = Spin_{2m+1}` and `ℓ` odd. Then `ℓ` is good for `G` (the only bad prime of type `B_m`, `m ≥ 2`, is `2`, and type `A_1` has none), and `X^*(T)/ZR ≅ Z/2`. The vector representation is the Weyl module of highest weight `ε_1`, simple for `ℓ ≠ 2`, hence tilting ([BRR, proof of Lemma 2.13]; for `m = 1` it is the Weyl module of highest weight `2` of `SL_2`). Tensor products of modules with a good filtration have a good filtration [Jan, II.4.21], [Mat]. `Z_G(u)` is smooth [BRR, Proposition 2.2], the centre of `G` acts trivially on `V`, and the image of `Z_G(u)` in `SO(V)` is the centralizer of the image of `u` (a lift `g̃` of a commuting element satisfies `g̃ug̃^{−1} = ±u`, and `−u` is not unipotent). So `dim (V^{⊗n})^𝒵 = dim (V^{⊗n})^T = N_q(n)` over `K`, hence over every field of odd characteristic, since the dimension of the ring does not change under extension of scalars.

**So Theorem A is, in every characteristic `≠ 2`, a consequence of the literature and of Proposition 1.2.** Corollary 8.2 of [CL] (the group `Z[L]/((e_j : j odd) + (x^q))` has no odd torsion) follows from Theorem A over the fields `Q` and `F_p`, so it follows too. (Logically, characteristic `0` follows from one odd prime `p`: the dimension over `Q` is the rank of that group, which is at most the dimension over `F_p`, and the lower bound of [CL, Proposition A.5] is elementary. Kostant's theorem is the origin of the statement, and we keep the reference.)

**2.3 What [CL] adds.** (a) Proposition 1.2 itself, which we have not found written. (b) A second proof of the count (Appendix A of [CL]), elementary and self-contained: no algebraic groups, no good filtrations, no Frobenius splitting. (c) For every partition `μ` with at most `m` parts an explicit ideal `K_μ(L)`, with `K_∅(L) = (e_j : j odd) + (x^q)`, such that `dim F[L]/K_μ(L)` is the multiplicity of the weight `Σμ_iε_i` in `V^{⊗n}`, and such that the rows of `K_μ` in a new variable are the ideals of the `q` neighbouring weights ([CL, Theorem A.15 and Corollary A.17]; computed independently at `178` cells).

**2.4 For `q = 3` this was already in the project.** `SO_3 = PGL_2`, `V` is the Steinberg module of `SL_2` in characteristic `3`, and the count is the «Steinberg bridge» of the earlier notes of the project ([CL, Remark 8.3(2)]). An attempt to extend that bridge to `q = 9, 27, …` *with the same group `SL_2`* failed, and it had to fail: the group changes with `q`. It is `SO_q`.

## 3. Even `q`

For even `q = 2m` the group is `Sp_{2m}`: simply connected, with every odd prime good, `X^*(T)/ZR ≅ Z/2`, and `V` a simple Weyl module in every characteristic. The centralizer of `g_1` is `{±1} × 𝒵`, and `−1` acts on `V^{⊗n}` as `(−1)^n`.

**Proposition 3.1** (modulo [BRR, Proposition 2.12]). *Let `char F ≠ 2`, `q = 2m` and `n` even. Then `dim F[x_1, …, x_n]/((e_j : j odd) + (x_i^q)) = n!·[y^n] I_0(2y)^m`, the number of closed walks of length `n` on `Z^m` with steps `±ε_i`.*

In odd characteristic this is [BRR, Proposition 2.12] with Proposition 1.2. In characteristic `0` it is a case of Kostant's theorem; it also follows from the case of one odd prime, because the dimension over `Q` is at most the dimension over `F_p`, and Proposition 4.1(iii) with Theorem 4.2(i) below gives the lower bound. [CL] v9 listed this as an open problem. For even `n` it is a consequence of the literature.

**Odd `n`: not proved.** The zero weight space is `0`, and the ring is the space of coinvariants of `𝒵` alone. In the cells with odd `n` that we computed — `(q, n) = (2, 3), (2, 5), (2, 7), (4, 3), (4, 5), (6, 3), (6, 5), (8, 3)` in characteristic `0`, and `(2, 5), (4, 3)` in characteristics `3, 5, 7` — the dimension is the number of walks from `0` to `ε_1`, which is the multiplicity of the minuscule weight; the cold reader of this note found the same at `(2, 3), (2, 5), (4, 3), (4, 5), (6, 3)` in characteristics `3, 5, 7` and `1000003`. In characteristic `0` we expect this to follow from the description of the functions on the universal cover of the regular nilpotent orbit [Gra], which we have not read.

## 4. Theorem B is a statement about invariant tensors

**4.1 The copairing.** Put `D_r(a, b) := Σ_{u=0}^{r−1} (−1)^u a^u b^{r−1−u} ∈ F[a,b]/(a^r, b^r) = V ⊗ V`. The basis dual to `(x^u)` for the form is `((−1)^u x^{r−1−u})`, so `D_r` is the element of `V ⊗ V` dual to the form: it is invariant under every isometry. For a perfect matching `J` of `N = 2s` variables put `D_{r,J} := Π_{{a<b}∈J} D_r(x_a, x_b)`; these are the invariant tensors given by the Brauer diagrams with no through strands. For `r = q − 1`, `D_r` is the polynomial `D` of [CL, §2.3]. For `r = q = p^v` in characteristic `p`, `D_q(a, b) = (a + b)^{q−1}`.

Let `C_r := F[x_1, …, x_N]/(x_i^r) = V^{⊗N}`. It acts on itself by multiplication, and this is the action of the `N` commuting copies of `e`, one in each factor. Let `I_J := (x_a + x_b : {a,b} ∈ J)`.

**Proposition 4.1** ([CL, Proposition 8.5]). *Over every field: (i) `ann_{C_r}(D_{r,J}) = I_J C_r`; (ii) `dim Σ_J D_{r,J}C_r = dim F[x]/⋂_J (I_J + (x_i^r))`; (iii) `Σ_J D_{r,J}C_r ⊆ ann_{C_r}(e_j : j odd)`.*

For `char F ≠ 2` and `F` infinite, the right-hand side of (iii) is the space of invariants `(V^{⊗N})^𝒵`: a vector is invariant iff it is killed by the elements `Π_x f(x) − 1`, `f(e) ∈ 𝒵`, and by Proposition 1.2 these generate the ideal `(e_j : j odd)`. So the subspace generated by the invariant tensors under the copies of `e` always lies in the invariants of the centralizer. The question is whether it is all of it.

**4.2 The even box: this is Theorem B.**

**Theorem 4.2** ([CL, Corollary 8.6]). *Let `q ≥ 3` be odd, `N = 2k + 2`, `r = q − 1`.*
- *(i) Over every field, `dim Σ_J D_{q−1,J}C_{q−1} = Q_k(q)`, the number of closed walks of length `N` on `Z^{(q−1)/2}` with steps `±ε_i`.*
- *(ii) Modulo [BRR, Proposition 2.12]: in characteristic `≠ 2`, `Σ_J D_{q−1,J}C_{q−1} = ann_{C_{q−1}}(e_j : j odd)`, which is `(V^{⊗N})^𝒵` when `F` is infinite, and `⋂_J (I_J + (x_i^{q−1})) = (e_j : j odd) + (x_i^{q−1})`.*

(i) is Theorem B of [CL], moved from `2k + 1` to `2k + 2` variables by an elementary argument. (ii) combines (i) with Proposition 3.1.

**In words.** *For the symplectic group `Sp_{q−1}` and the tensor power `V^{⊗(2k+2)}` of its natural representation, the invariants of the centralizer of a regular unipotent element are generated, under the commuting copies of the regular nilpotent `e`, by the invariant tensors of the group. This holds, modulo [BRR, Proposition 2.12], over every infinite field of characteristic `≠ 2` (over a finite field, for the centralizer as an algebraic group); and the generated space has the right dimension over every field, so the lattice it spans over the integers is saturated.*

By [CL, Proposition 2.5 and Theorem 0], for `k ≥ 1` Conjecture 1.2 of Degtyarev–Shimada for the Fermat variety of degree `p^v` and dimension `2k` is equivalent to (i) over `F_p` with `q = p^v`. For the odd degrees that are not prime powers the algebraic form of the conjecture is Main Theorem′ of [CL], which needs more than Theorem B.

**4.3 Characteristic `0`: a derivation from classical theorems (sketch).** Let `W = V^{⊗N}` with `N` even, and let `G` be `SO_r` (odd `r`) or `Sp_r` (even `r`); the centralizer `G^e` is `𝒵` or `{±1} × 𝒵`, and `−1` acts trivially on `W`.
- *Kostant.* The restriction `C[𝔤] → C[𝒩]` to the nilpotent cone is surjective, `𝒩` is normal, and the regular orbit `G/G^e` has a complement of codimension `2`; so `C[𝒩] = Ind_{G^e}^G C`, and evaluation at `e` maps `(W ⊗ C[𝔤])^G` onto `W^{G^e}`.
- *First fundamental theorem.* `𝔤 ⊆ V ⊗ V`, and the invariants of `G` in `V^{⊗N} ⊗ 𝔤^{⊗d}` are spanned by the complete contractions with the form. (For odd `r`, `O_r = {±1} × SO_r`, and `−1` acts trivially on this tensor power, whose degree `N + 2d` is even; so the invariants of `SO_r` in it are those of `O_r`.)
- *Evaluation.* A complete contraction, evaluated at `e` in the `d` copies of `𝔤`, is a product over the pairs `{a, b}` of a matching of terms `x_a^{j}D_r(x_a, x_b)`, times traces of powers of `e`, which are `0`.

Hence `W^{G^e} = Σ_J D_{r,J}C_r` in characteristic `0`, for both parities of `r`. The sources of this sketch were not read in the original, and [CL] does not use it. For even `r` the resulting dimension agrees with Theorem B over `Q`.

**4.4 Characteristic `p`.** Each ingredient has an analogue for modules with a good filtration in good characteristic: the evaluation is surjective by the argument of [BRR, Proposition 2.12], and the tensor invariants of the classical groups are described in a characteristic-free way by De Concini and Procesi [DCP]. Passing from tensor powers to polynomial functions on `𝔤` in small characteristic is a real step, and we have not carried it out. **We do not know whether Theorem B in odd characteristic can be derived from this theory. The proof we have is the one in [CL, §5], which is elementary and also covers characteristic `2`.**

## 5. The odd box: an open problem

For odd `r = q` and even `N` the corresponding statement is

**(O)** `dim_F Σ_J D_{q,J}C_q = N_q(N)`, equivalently `⋂_J (I_J + (x_i^q)) = (e_j : j odd) + (x_i^q)` (for `char F ≠ 2`, by Theorem A).

- `≤` holds over every field. In characteristic `≠ 2` it is Proposition 4.1(iii) with Theorem A. In characteristic `2` the two ideals differ (colengths `19` and `21` at `(q, N) = (3, 4)`), and the point-counting argument of [CL, Proposition 9.1] does not apply; but `Σ_J D_{q,J}C_q` is spanned by vectors with integer coordinates, so its dimension over any field is at most its dimension over `Q`.
- (O) holds in characteristic `0`, by §4.3 (a sketch).
- (O) holds at every cell we computed: `30` pairs (cell, characteristic) with `q ∈ {3, 5, 7, 9}`, `N ∈ {2, 4, 6}`, in characteristics `3, 5, 7, 32003`, and `4` cells in characteristic `2`. Over `F_3` and for `q = 3` the earlier notes of the project had it for `N ≤ 10`.
- **(O) is not proved in positive characteristic.**

For `F = F_p` and `q = p^v`, (O) says `dim F_p[x_0, …, x_{2k+1}]/⋂_J (I_J + (x_i^q)) = P_k(q)`. In the working notes of the project this was called «the bone». For several months the project took the count of Theorem A to be the algebraic form of Conjecture 1.2 ([CL, §1.8]), and the bone was the statement it tried to prove on the way to that count. Neither is the conjecture: the conjecture is the statement at the even box `q − 1` (§4.2). The reading of §4 explains why the two look alike: they are the same statement for `Sp_{q−1}` and for `SO_q`.

Two routes are open: adapt the induction of [CL, §5] to the box `q`; or prove §4.4.

## 6. The graded count (computed)

In `27` cells (`3 ≤ q ≤ 13`, `n ≤ 9`) the Hilbert series of the ring of Theorem A is

`Σ_λ c_λ · t^{mn} m^0_λ(t^{−1})`,

where `V^{⊗n} = ⊕ V_λ^{c_λ}` in characteristic `0` and `m^0_λ` is Lusztig's `t`-analogue of the zero weight multiplicity; in `56` cases the graded character of the symmetric group agrees too, with the Schur–Weyl–Brauer multiplicity spaces in place of the `c_λ`. For the ideals `K_μ` of [CL, Appendix A] the Hilbert series is, in `133 + 18` cases, the same expression with Lusztig's analogue at the weight `μ`.

In characteristic `0` this is what one expects from the theory of generalized exponents (Kostant, Hesselink) and of the Brylinski–Kostant filtration [Bry]; for tilting modules in good characteristic the filtration is treated in [Liu]. **We claim nothing here**: the statement is recorded as a computation, and of those sources only the introduction of [Liu] was read. Since the Hilbert function of the ring is the same in every characteristic `≠ 2` (by semicontinuity over `Z` and Theorem A), the computation in characteristic `0` gives the Hilbert series in every characteristic `≠ 2`.

A negative result: there is no model of the ring with one graded piece per `S_n`-orbit of walks built from Garsia–Procesi modules. An exhaustive search at `n = 6`, `q = 3, 5`, over all shifts, has no solution. The pieces are indexed by the irreducible constituents `λ`, not by the kinds of walk.

## 7. A statistic on walks

Let `q` be odd or even and `m = ⌊q/2⌋`. A walk `w = (s_1, …, s_n)` has steps in `{0, ±ε_i}` (`q` odd) or `{±ε_i}` (`q` even); it is at `p_j` after `j` steps. Let `N_j(p)` be the number of walks of length `j` from `0` to `p`.

**Definition (fibre rank).** At time `j`, order the possible last steps `c` by `N_{j−1}(p_j − c)`, decreasing, with any fixed rule for ties, and let `r_j(w)` be the position of the actual step `s_j` in that order, starting from `0`. Put `stat(w) := Σ_j r_j(w)`.

**Theorem 7.1** (a consequence of [CL, Theorem A, Theorem A.12 and Theorem A.15]; see [CL, Corollary A.17]). *For odd `q` and `char F ≠ 2`, the Hilbert series of `F[L]/((e_j : j odd) + (x^q))` is `Σ_w t^{stat(w)}`, the sum over the closed walks of length `n`. The sum does not depend on the rule for ties.*

*Proof.* For a partition `μ` with at most `m` parts, `N_μ(n)` is the number of walks of length `n` from `0` to the point `Σμ_iε_i`, and the `q` children of `μ` in [CL, Definition A.2] are the shapes of the `q` points from which that point is reached in one step ([CL, Lemma A.3]). In the proof of [CL, Theorem A.15] there is a chain `dim F[L∪z]/K_μ(L∪z) = Σ_a dim F[L]/R_a ≤ Σ_a dim F[L]/K_{child_a(μ)}(L) ≤ Σ_a N_{child_a(μ)}(n) = N_μ(n+1)`, where `R_a` is the row of index `a` (the coefficient ideal of `z^a`) and `K_{child_a(μ)}(L) ⊆ R_a`. For `μ = ∅` the two ends are equal for every `n`, by Theorem A. So every inequality is an equality: `R_a = K_{child_a(∅)}(L)` and `dim F[L]/K_{child_a(∅)}(L) = N_{child_a(∅)}(n)`, for every `n`. The same argument then applies to each child, again for every `n`, and so on; every `μ` with at most `m` parts is reached. So for every `μ` equality holds and the rows are the ideals of the children; this is [CL, Corollary A.17]. The ideals are homogeneous, so `HS(F[L∪z]/K_μ(L∪z)) = Σ_a t^a·HS(F[L]/R_a)`. Rows are nested, `R_0 ⊆ R_1 ⊆ ⋯`, so the numbers `N_{child_a(μ)}(n)` do not increase with `a`, and two rows with the same number are equal ideals. Hence the row of index `a` belongs to a step of rank `a` in the definition, whatever the rule for ties. Induct on `n`. ∎

- **Explicit order of the steps** (it is the order of [CL, Definition A.2], so it is proved by the argument above; it was also compared with the definition in `3 605` profiles): from the position `p`, first the steps that came from closer to the origin in a coordinate `i`, largest `|p_i|` first; then the loop; then the steps that came from farther, smallest `|p_i|` first.
- **For `q = 3`:** `stat(w) = n − #{j : p_j = 0 and p_{j−1} ∈ {0, −1}}`.
- Checked at `24` cells with `q` odd and `16` with `q` even.
- **Not compared** with the energy statistic of one-dimensional sums of Kirillov–Reshetikhin crystals (Lecouvey–Okado–Shimozono), which has the same generating function in the stable range. We do not claim that the statistic is new.

*Roots of unity.* Let `A_d` be the piece of degree `d` of the ring. Then `Σ_d ω^d dim A_d = 1` for every `(q−1)`-th root of unity `ω ≠ 1` (checked at `24` cells). In characteristic `0` it follows from Theorem A: take the point set of the lower bound with `C = {0} ∪ μ_{q−1}`; the group `μ_{q−1}` acts on it by scaling and fixes only the origin, and the graded ring is isomorphic, as a representation of that group, to the functions on the point set. This is an instance of the cyclic sieving phenomenon with a single fixed point. We do not claim it as a result.

## 8. Whose is what

| item | owner | status |
|---|---|---|
| the count of Theorem A, characteristic `0` | Kostant 1963 | classical |
| the count of Theorem A, odd characteristic | Bezrukavnikov–Riche–Rider 2020, Prop. 2.12 (with [KLT], [Jan]) | follows, through §1 |
| no odd torsion in `Z[L]/((e_j : j odd) + (x^q))` | follows from the two lines above | — |
| the analogue for even `q`, even `n` | Kostant; Bezrukavnikov–Riche–Rider | follows, through §1 |
| graded count, characteristic `0` | Kostant, Hesselink, Lusztig, Brylinski | classical; here only computed |
| the dictionary of §1 (ring = coinvariants of the centralizer) | this project | proved; elementary; not found written |
| an elementary proof of Theorem A, with ideals `K_μ` of colength `N_μ(n)` for every weight `μ` | this project ([CL, Appendix A]) | proved |
| **Theorem B (every field, every odd `q`); Conjecture 1.2 of [DS] for every odd degree** | **this project ([CL])** | **Theorem B and Main Theorem′ proved and Lean-checked; the conjecture proved modulo Pham's theorem and [DS, Theorem 2.2]** |
| Theorem B read as «invariant tensors generate the invariants of the centralizer» | this project | proved (§4.1–§4.2); (ii) modulo [BRR] |
| the same in characteristic `0`, from Kostant + FFT | classical ingredients; the combination is ours | sketch |
| the odd box (O) | this project, as a problem | open in characteristic `p`; computed |
| even `q`, odd `n` | this project, as a problem | open; computed |
| the fibre-rank statistic | this project | theorem given [CL, App. A]; not compared with energy |
| `K_μ` and Lusztig's analogue at `μ` | this project, as an observation | computed |

## 9. What was read, and what was not

- **Read in the arXiv source:** [BRR] §2.1–§2.6 (in particular Propositions 2.2 and 2.12, Lemmas 2.7, 2.8 and 2.13) and the introduction; [Ric], introduction and §2.2; [Gin], §4; [Liu], introduction and the start of §2.
- **[Ric]** extends Kostant's results on the universal centralizer (the Kostant section, smoothness of the regular centralizer, its Lie algebra) to positive characteristic and to integral coefficients. We did not find the count in it (we read its introduction and §2.2, and searched its source).
- **Not read in the original:** [Kos], [KLT], [Bry], [Lus], [Gra], Hesselink's paper on generalized exponents, the papers of Lecouvey–Okado–Shimozono, and the cyclic sieving paper of Reiner–Stanton–White.
- **This note has not been refereed.** It was read cold on 1 October 2026, together with the new material of [CL] v10, by a separate instance of the AI system used in this project, working alone and with its own code. Its verdict was «holds», with one gap (the inequality of §5 in characteristic `2`), three errors (a false sentence in the sketch of §4.3, the hypothesis of [Gin, Proposition 4.2], and the row of Theorem B in the table of §8) and thirteen points of presentation, among them the remark (3) after Proposition 1.2 and the equality for every `μ` of §2.3(c). All are incorporated, with the texts and the arguments that the reader proposed. See [CL, §12.6].

## 10. Verification record

Every engine ran under a guard of 1.2 GB and 10 minutes.
- The dictionary: `(e_j : j odd) + box = (p_j : j odd) + box` in characteristic `0` at `6` cells; the coefficients of `E(t)/E(−t) − 1` generate `(e_j : j odd)` in characteristics `3, 5, 7` at `5` cells. The coinvariants of the points of `𝒵` over `F_3` and `F_5` at `5` cells (remark (3) of §1), by the cold reader and again by the author with separate code.
- §4 and §5: `dim Σ_J D_{r,J}C_r` against the number of closed walks at `13` cells `(r, N)` in characteristics `3, 5, 7, 32003` (`50` of `50`) and at `9` cells in characteristic `2` (`9` of `9`). The first engine was stopped by the guard at the cell `(5, 6)` (1.36 GB); it was rewritten and rerun.
- §3: `8` cells in characteristics `0, 3, 5, 7` and `2`.
- §6: `27` cells, `56` graded traces, `133 + 18` profiles.
- §7: `24 + 16` cells; `3 605` profiles for the explicit order.

Engines and logs: github.com/tretoef-estrella/chaise-longue-theorem, `engines/theorem-a-kostant/`.

## References

- **[BRR]** R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583 (v2, 4 July 2024).
- **[Bry]** R. K. Brylinski, *Limits of weight spaces, Lusztig's `q`-analogs, and fiberings of adjoint orbits*, J. Amer. Math. Soc. **2** (1989), 517–533.
- **[CL]** R. Amichis Luengo, *The Chaise Longue Theorem*, version 10, Zenodo (2026). doi:10.5281/zenodo.22961150.
- **[DCP]** C. De Concini, C. Procesi, *A characteristic free approach to invariant theory*, Adv. Math. **21** (1976), 330–354.
- **[DS]** A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties*, J. Math. Soc. Japan **68** (2016), 975–996.
- **[Gin]** V. Ginzburg, *Loop Grassmannian cohomology, the principal nilpotent and Kostant theorem*, arXiv:math/9803141 (v2).
- **[Gra]** W. Graham, *Functions on the universal cover of the principal nilpotent orbit*, Invent. Math. **108** (1992), 15–27.
- **[Jan]** J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Amer. Math. Soc., 2003.
- **[KLT]** S. Kumar, N. Lauritzen, J. F. Thomsen, *Frobenius splitting of cotangent bundles of flag varieties*, Invent. Math. **136** (1999), 603–621.
- **[Kos]** B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. **85** (1963), 327–404.
- **[Liu]** L. Liu, *Filtrations of tilting modules and costalks of parity sheaves*, arXiv:2007.12444.
- **[Lus]** G. Lusztig, *Singularities, character formulas, and a `q`-analog of weight multiplicities*, Astérisque **101–102** (1983), 208–229.
- **[Mat]** O. Mathieu, *Filtrations of G-modules*, Ann. Sci. École Norm. Sup. (4) **23** (1990), 625–644.
- **[Ric]** S. Riche, *Kostant section, universal centralizer, and a modular derived Satake equivalence*, arXiv:1411.3112 (v4, 19 May 2015).
