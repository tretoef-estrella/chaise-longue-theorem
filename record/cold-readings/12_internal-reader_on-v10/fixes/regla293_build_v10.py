# -*- coding: utf-8 -*-
# PAPER_OFICIAL_v10 = PAPER_OFICIAL_v9 (Zenodo 10.5281/zenodo.23085319)
#   + a second correction of attribution of Theorem A: in odd characteristic the count follows from
#     [BRR, Proposition 2.12] (Bezrukavnikov-Riche-Rider) and the dictionary of Remark 8.4 (rewritten);
#   + Proposition 8.5, Corollary 8.6 and Remark 8.7: Theorem B in the language of the regular unipotent centralizer,
#     the equality of the two ideals at the even box (modulo [BRR]), and the odd box as an open problem;
#   + problem 6 of section 13 restated (even n is now a consequence of [BRR]), and a new problem 7.
# No statement and no proof of the Main Theorem, of Theorems A, B, C or of the corollaries H, W changes.
# Grepy, 2026-10-01. Every replacement asserts its anchor.
import os, sys
os.chdir('/Users/rafa/Desktop/ARBOLYAML/VIVOS/MISIONES_TRAS_BARRIDO')
t = open('PAPER_OFICIAL_v9.md', encoding='utf-8').read()
COLD = open('/Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/regla293_cold_sentence.txt', encoding='utf-8').read().strip()

def rep(old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (n, count, old[:100])
    t = t.replace(old, new)

def cut(start, end, new):
    """replace the text from `start` (inclusive) up to `end` (exclusive) by `new`"""
    global t
    assert t.count(start) == 1, (t.count(start), start[:80])
    i = t.index(start)
    j = t.index(end, i)
    assert t.count(end, i) >= 1
    t = t[:i] + new + t[j:]

# ---------------------------------------------------------------- header
rep("Madrid, Spain · tretoef@gmail.com · 1 October 2026 · version 9",
    "Madrid, Spain · tretoef@gmail.com · 1 October 2026 · version 10")

# ---------------------------------------------------------------- abstract
rep("In characteristic `0` this count follows from a theorem of Kostant on the centralizer of a principal nilpotent element (Remark 8.4); what Theorem A adds is the same count in every odd characteristic, with no relation between `q` and the characteristic, and hence the absence of odd torsion over `Z`.",
    "As a count, Theorem A is not new: the ring is the space of coinvariants of the centralizer of a regular unipotent element of `SO_q` in a tensor power of the vector representation, and the count follows in characteristic `0` from a theorem of Kostant and in odd characteristic from a proposition of Bezrukavnikov, Riche and Rider (Remark 8.4). What this paper contributes there is that dictionary and an elementary, self-contained proof. In the same language, Theorem B says that the invariant tensors of `Sp_{q−1}` generate, under the commuting copies of a regular nilpotent element, a space of the dimension of the zero weight space (§8).")

# ---------------------------------------------------------------- §1.6
rep("In characteristic `0`, Theorem A is a consequence of a classical theorem of Kostant [Kos] (Remark 8.4); its new content is the statement in every characteristic `≠ 2`.",
    "**As a count, Theorem A is not new**: in characteristic `0` it is a consequence of a classical theorem of Kostant [Kos], and in odd characteristic of a proposition of Bezrukavnikov, Riche and Rider [BRR] on modules with a good filtration, through the dictionary of Remark 8.4. The proof of Appendix A is elementary and independent of both.")

# ---------------------------------------------------------------- §1.8
rep("Again no statement and no proof changes.",
    "Again no statement and no proof changes. "
    "Version 10 (the present one) corrects the attribution of Theorem A a second time: version 9 said that we knew no version of Kostant's theorem in positive characteristic that gives the count, and there is one, [BRR, Proposition 2.12], which we had not read (Remark 8.4(3)). "
    "It also adds the reading of Theorem B in the same language (Proposition 8.5, Corollary 8.6, Remark 8.7), restates problem 6 of §13 and adds problem 7. No statement and no proof of the earlier versions changes.")

# ---------------------------------------------------------------- Remark 8.3(2)
rep("Theorem A contains all of these, in every characteristic `≠ 2` and for every odd `q`. **In characteristic `0`, however, Theorem A is not new: it follows from a theorem of Kostant (Remark 8.4).** (3)",
    "Theorem A contains all of these, in every characteristic `≠ 2` and for every odd `q`. **As a count, however, Theorem A is not new: it follows from a theorem of Kostant in characteristic `0` and from a proposition of Bezrukavnikov, Riche and Rider in odd characteristic (Remark 8.4).** (3)")

# ---------------------------------------------------------------- Remark 8.4 rewritten; Proposition 8.5, Corollary 8.6, Remark 8.7
R84 = r"""**Remark 8.4 (the centralizer of a regular unipotent element; as a count, Theorem A is not new).** Let `q = 2m + 1 ≥ 3`.

(1) *A dictionary.* Let `F` be a field of characteristic `≠ 2`, and let `V := F[x]/(x^q)` with the bilinear form `⟨x^a, x^b⟩ := (−1)^a` if `a + b = q − 1`, and `0` otherwise. The form is nondegenerate, and it is symmetric because `a + b` is even. Multiplication by `x`, which we call `e`, satisfies `⟨e u, v⟩ = −⟨u, e v⟩`, and it is nilpotent with a single Jordan block. An endomorphism of `V` that commutes with `e` is a polynomial `f(e)`, and `f(e)` preserves the form exactly when `f(e)f(−e) = 1`; its determinant is `f(0)^q = f(0)`. So the centralizer of `e` in `SO(V) ≅ SO_{2m+1}` is the commutative unipotent group

`Z := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`.

For `t ∈ F` the Cayley transform `g_t := (1 + te)(1 − te)^{−1}` lies in `Z`, and for `t ≠ 0` it has a single Jordan block: it is a regular unipotent element of `SO(V)`, and `Z` is its centralizer. The ring `F[L]/(x^q : x ∈ L)` is `V^{⊗n}`, and `f(e) ∈ Z` acts on it as multiplication by `Π_{x∈L} f(x)`. In particular `g_t` acts as `E(t)/E(−t)`, where `E(t) := Π_{x∈L}(1 + tx) = Σ_j e_j(L) t^j`. Since `E(t) − E(−t) = 2 Σ_{j odd} e_j(L) t^j` and `E(−t)` is invertible, the elements `E(t)/E(−t) − 1` lie in the ideal `(e_j(L) : j odd)`, and when `F` is infinite they generate it (they are polynomials in `t` whose coefficients generate it). For a general `f(e) ∈ Z` put `h := 1 + f`; then `h(0) = 2` is a unit, `f(x) = h(x)/h(−x)`, and `Π_x f(x) − 1 = (H − H^−)/H^−` with `H := Π_x h(x)` and `H^− := Π_x h(−x)`. Here `H − H^−` is twice the sum of the homogeneous components of odd degree of the symmetric polynomial `H`, and a symmetric polynomial of odd degree lies in `(e_j(L) : j odd)`. Hence, for `F` infinite,

`F[L]/I_q(L) = V^{⊗n} / ⟨(g − 1)v : g ∈ Z, v ∈ V^{⊗n}⟩`,

the coinvariants of the centralizer of a regular unipotent element on the `n`-th tensor power of the vector representation of `SO_{2m+1}`. Since `V^{⊗n}` is isomorphic to its dual as a representation of `Z`, this space has the dimension of the invariants `(V^{⊗n})^Z`. In characteristic `0` the invariants of `Z` are those of its Lie algebra, which has basis `e, e^3, …, e^{2m−1}`; `e^j` acts as multiplication by the power sum `p_j(L)`, and `(p_j(L) : j odd) = (e_j(L) : j odd)` by Newton's identities.

(2) *Characteristic `0`: Kostant's theorem.* Let `G` be a connected reductive group over `C` and `W` a finite-dimensional rational `G`-module whose weights lie in the root lattice. Then `x ↦ dim W^{𝔤^x}` is constant on the regular elements of `𝔤` [Kos]; we quote the statement from [Gin, Proposition 4.2]. At a regular semisimple `x` the centralizer `𝔤^x` is a Cartan subalgebra, and `W^{𝔤^x}` is the zero weight space of `W`. The weights of `V` are `0, ±ε_1, …, ±ε_m`, which span the root lattice of `so_{2m+1}`. So `dim (V^{⊗n})^{𝔤^e}` is the dimension of the zero weight space of `V^{⊗n}`: the number of closed walks of length `n` on `Z^m` with steps `0, ±ε_i`, which is `N_q(n)`. **So in characteristic `0`, Theorem A follows from Kostant's theorem and (1).**

(3) *Odd characteristic: a proposition of Bezrukavnikov, Riche and Rider.* Let `K` be an algebraically closed field of characteristic `ℓ`, and let `G` be a connected reductive group over `K` with simply connected derived subgroup, such that `ℓ` is good for `G` and `X^*(T)/ZR` has no `ℓ`-torsion (`T` a maximal torus, `R` the roots). Then [BRR, Proposition 2.12]: *for every finite-dimensional `G`-module `W` which admits a good filtration and every regular unipotent element `u ∈ G`, `dim W^{Z_G(u)} = dim W^T`.* We read this statement and its proof in the arXiv version of 4 July 2024; the proof rests on the vanishing theorem and the good filtration of [KLT]. Take `G = Spin_{2m+1}` and `ℓ` odd. The only bad prime of type `B_m` is `2`, and `X^*(T)/ZR ≅ Z/2`, so the hypotheses hold. The vector representation `V` is the Weyl module of highest weight `ε_1`; it is simple for `ℓ ≠ 2`, hence tilting ([BRR, proof of Lemma 2.13] for `m ≥ 2`; for `m = 1`, `G = SL_2` and `V` is the Weyl module of highest weight `2`), and a tensor product of modules with a good filtration has a good filtration [Jan, II.4.21], [Mat]. The group scheme `Z_G(u)` is smooth [BRR, Proposition 2.2], so its invariants are those of its group of `K`-points. The centre of `G` acts trivially on `V`, and the image of `Z_G(u)` in `SO(V)` is the centralizer of the image of `u`: if `g ∈ SO(V)` commutes with it, a lift `g̃` satisfies `g̃ug̃^{−1} = ±u`, and `−u` is not unipotent. Finally `(V^{⊗n})^T` is the zero weight space. So for `F = K`, `dim F[L]/I_q(L) = dim (V^{⊗n})^Z = N_q(n)`; the dimension does not change under extension of scalars, so the same holds over every field of odd characteristic. **So in odd characteristic, too, Theorem A follows from the literature, through (1): from [BRR, Proposition 2.12].** Corollary 8.2 then follows as in Appendix A.8. Version 9 of this paper said: «we do not know a version of Kostant's theorem in positive characteristic that gives this». There is one; we had not read it. The count of Theorem A should be credited to Kostant in characteristic `0` and to [BRR] in odd characteristic. A related paper, [Ric], extends Kostant's results on the centralizers of regular elements to positive characteristic and to integral coefficients; it describes the centralizer group scheme and does not contain the count. We have not found the dictionary (1), or the statement of Theorem A for this ring, in the literature. For `q = 3` the statement is the one recalled in Remark 8.3(2).

(4) *What Appendix A contributes.* The proof of Appendix A is a second, independent proof of the count. It is elementary and self-contained: it uses no algebraic groups, no good filtrations and no Frobenius splitting, only `2 ∈ F^×`. It also gives slightly more than the count: to every partition `μ` with at most `m` parts, read as the dominant weight `Σ μ_iε_i`, it attaches an explicit ideal `K_μ(L)`, with `K_∅(L) = I_q(L)`, such that `dim F[L]/K_μ(L)` is at most the multiplicity `N_μ(n)` of the weight `μ` in `V^{⊗n}` (Theorem A.15; equality is proved for `μ = ∅` and computed at `178` cells, §12.5), and each row of `K_μ(L ∪ z)` contains the ideal of the corresponding neighbouring weight (Theorem A.12). The lower bound (Proposition A.5) is the classical method of degenerating the ideal of a finite set of points (the «orbit harmonics» of [GP]).

(5) *Computed, not claimed.* In the `27` cells `(q, n)` that we computed (`3 ≤ q ≤ 13`, `n ≤ 9`), the Hilbert series of `F[L]/I_q(L)` is `Σ_λ c_λ·t^{mn} m^0_λ(t^{−1})`, where `λ` runs over the irreducible constituents `V_λ` of `V^{⊗n}` in characteristic `0`, `c_λ` is the multiplicity, and `m^0_λ` is Lusztig's `t`-analogue of the zero weight multiplicity [Lus]; in `56` cases the same holds for the graded character of the symmetric group (pairs of a cell with `q ∈ {3, 5}`, `n ≤ 6` and a cycle type), with the multiplicity spaces in place of the `c_λ`. In characteristic `0` this is what the theory of generalized exponents and of the Brylinski–Kostant filtration predicts [Bry]; for tilting modules in good characteristic see [Liu]. Of these sources we have read only the introduction of [Liu], and we record the statement as a computation (§12.5).

(6) *Even `q`.* For even `q = 2m` the form of (1) is alternating, and the same dictionary holds with `Sp(V) ≅ Sp_{2m}`: the centralizer of the regular unipotent element `g_1` is `{±1} × Z`, and `−1` acts on `V^{⊗n}` as `(−1)^n`. The group `Sp_{2m}` is simply connected, its only bad prime is `2`, `X^*(T)/ZR ≅ Z/2`, and `V` is a simple Weyl module in every characteristic. So for **even `n`** and every field of characteristic `≠ 2`, [Kos] and [BRR, Proposition 2.12] give

`dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q) = n!·[y^n] I_0(2y)^m`,

the number of closed walks of length `n` on `Z^m` with steps `±ε_i`. Version 9 listed this as an open problem; for even `n` it is a consequence of the literature. For odd `n` the zero weight space is `0` and the proposition says nothing about the invariants of `Z` alone. In `8` cells `(q, n)` with `q ∈ {2, 4, 6, 8}`, of both parities of `n`, the dimension in characteristics `3`, `5` and `7` equals the dimension in characteristic `0`, and for odd `n` it is the number of such walks from `0` to `ε_1`; in characteristic `2` it is larger in all `8` cells. The case of odd `n` is not proved (§13).

**Proposition 8.5 (the invariant copairing).** *Let `F` be a field, `r ≥ 2`, `N = 2s ≥ 2`, and `C_r := F[x_1, …, x_N]/(x_1^r, …, x_N^r)`. Put `D_r(a, b) := Σ_{u=0}^{r−1} (−1)^u a^u b^{r−1−u}`, and for a perfect matching `J` of `{1, …, N}` put `D_{r,J} := Π_{{a<b} ∈ J} D_r(x_a, x_b)` and `I_J := (x_a + x_b : {a,b} ∈ J)`. Then:*
- *(i) `(x_a + x_b)·D_r(x_a, x_b) = 0` in `C_r`, and `ann_{C_r}(D_{r,J}) = I_J C_r`;*
- *(ii) `dim_F Σ_J D_{r,J} C_r = dim_F F[x_1, …, x_N]/⋂_J (I_J + (x_i^r))`;*
- *(iii) `e_j · D_{r,J} = 0` for every odd `j`. So `Σ_J D_{r,J} C_r ⊆ ann_{C_r}(e_j : j odd)`, and `dim_F Σ_J D_{r,J} C_r ≤ dim_F F[x_1, …, x_N]/((e_j : j odd) + (x_i^r))`.*

*Proof.* (i) The product `(a + b)·Σ_u (−1)^u a^u b^{r−1−u}` telescopes to `b^r + (−1)^{r−1}a^r`, which is `0` in the box. In `F[a,b]/(a^r, b^r)`, multiplication by `D_r(a,b)` therefore factors through the quotient by `(a + b)`, which is `F[b]/(b^r)`, of dimension `r`. The elements `D_r(a,b)·b^i`, `0 ≤ i ≤ r−1`, are non-zero (the term `u = r − 1` survives) and homogeneous of different degrees, so the image has dimension at least `r`. Hence the annihilator of `D_r(a,b)` is exactly `(a + b)`. The ring `C_r` is the tensor product, over the pairs of `J`, of such rings, and `D_{r,J}` is the tensor product of the elements `D_r`; the kernel of a tensor product of linear maps is the sum of the kernels in each factor, which gives `ann(D_{r,J}) = I_J C_r`. (ii) Let `⟨f, g⟩` be the coefficient of `Π_i x_i^{r−1}` in `fg`; as in the proof of Proposition 2.6, the pairing is non-degenerate, `dim ann(I) = dim C_r − dim I` for every ideal `I`, and the annihilator of a sum of ideals is the intersection of their annihilators. So `dim Σ_J D_{r,J}C_r = dim C_r − dim ⋂_J I_J C_r`. (iii) By (i), `x_a D_{r,J} = −x_b D_{r,J}` for each pair, so `Π_i(1 + x_i t)·D_{r,J} = Π_{{a<b}∈J}(1 − x_b^2 t^2)·D_{r,J}`, which is even in `t`. The last inequality is `dim ann(I) = dim C_r − dim I` for `I = (e_j : j odd)C_r`. ∎

**Corollary 8.6 (Theorem B at `2k + 2` variables; both ends of the sandwich).** *Let `q ≥ 3` be odd, `k ≥ 0`, `N = 2k + 2`, and `r = q − 1`.*
- *(i) For every field `F`, `dim_F Σ_J D_{q−1,J} C_{q−1} = Q_k(q)`.*
- *(ii) Modulo [BRR, Proposition 2.12]: if `char F ≠ 2`, then `Σ_J D_{q−1,J} C_{q−1} = ann_{C_{q−1}}(e_j : j odd)`, `⋂_J (I_J + (x_i^{q−1})) = (e_j : j odd) + (x_i^{q−1})`, and `dim_F F[x_1, …, x_N]/((e_j : j odd) + (x_i^{q−1})) = Q_k(q)`. So both inequalities of Proposition 9.1 are equalities.*

*Proof.* (i) Write the variables as `x_0, y_1, …, y_{2k+1}`, and let `C` be the ring of Theorem B in the `y_i`. Every element `f` of `M := Σ_J D_{q−1,J}C_{q−1}` is killed by `e_1 = x_0 + σ`, `σ := Σ_i y_i`, by Proposition 8.5(iii). Write `f = Σ_{u=0}^{r−1} x_0^u f_u` with `f_u ∈ C`; comparing the coefficients of `x_0^u` in `x_0 f = −σf` gives `f_{u−1} = −σ f_u` for `u ≥ 1`. So `f` is determined by `f_{r−1}`, and the linear map `θ : M → C`, `f ↦ f_{r−1}`, is injective. If `k_0` is the partner of `0` in `J`, the coefficient of `x_0^{r−1}` in `D_{q−1}(x_0, y_{k_0})` is `(−1)^{r−1}`, so `θ(D_{q−1,J}·g) = ±D_J·g` for `g ∈ C`, with `D_J` as in §2.3. Moreover `x_0·D_{q−1,J} = −y_{k_0}D_{q−1,J}`, so `M = Σ_J D_{q−1,J}C`. Hence `θ(M) = (D_J : J ∈ 𝒥)C`, and `dim M = Q_k(q)` by Theorem B. (ii) By Remark 8.4(6), which rests on [BRR, Proposition 2.12] (on [Kos] in characteristic `0`), `dim F[x]/((e_j : j odd) + (x_i^{q−1})) = N!·[y^N] I_0(2y)^{(q−1)/2} = Q_k(q)`. By Proposition 8.5(iii) and (i), `M` is a subspace of `ann(e_j : j odd)` of the same dimension, so they are equal. Taking annihilators, `⋂_J I_J C_{q−1} = (e_j : j odd)C_{q−1}`. ∎

*Remark 8.7 (what this says).* (1) *Invariant tensors.* Let `V_r := F[x]/(x^r)` with the form `⟨x^a, x^b⟩ = (−1)^a [a + b = r − 1]`, which is symmetric for odd `r` and alternating for even `r`. Then `D_r(a, b) = Σ_u x^u ⊗ (−1)^u x^{r−1−u}` is the element of `V_r ⊗ V_r` dual to the form, so every `D_{r,J}` is a tensor of `V_r^{⊗N}` invariant under the whole group `G` of isometries (`Sp_r` for even `r`, `O_r` for odd `r`). The ring `C_r` acts on `V_r^{⊗N}` through the `N` commuting copies of `e`, one in each factor. In these terms, Corollary 8.6 reads: **Theorem B says that the invariant tensors `D_{q−1,J}` of `Sp_{q−1}` generate, under the commuting copies of a regular nilpotent element, a space of the dimension of the zero weight space of `V^{⊗(2k+2)}`, over every field; in characteristic `≠ 2` that space is the whole space of invariants of the centralizer of a regular unipotent element.** By Proposition 2.5, for `m = p^v` Conjecture 1.2 of [DS] is equivalent to this statement over `F_p` for `Sp_{m−1}`. We did not find this formulation in the literature, and we do not know whether Theorem B in odd characteristic can be derived from the theory of modules with a good filtration.

(2) *Characteristic `0`.* There the equality `Σ_J D_{r,J}C_r = ann_{C_r}(e_j : j odd)` can be derived from classical invariant theory, for both parities of `r` and even `N`. We give the argument as a sketch; we have not read its sources in the original, and nothing in this paper uses it. By Kostant's theorem the evaluation at a regular nilpotent `e` maps the `G`-equivariant polynomial maps `𝔤 → W` onto `W^{𝔤^e}` [Kos]. By the first fundamental theorem, the equivariant maps `𝔤 → V_r^{⊗N}` of degree `d` are spanned by the complete contractions of `V_r^{⊗N} ⊗ 𝔤^{⊗d}` with the form (for odd `r` the group is `SO_r`; an invariant involving the determinant would leave an odd number `N + 2d − r` of factors to be paired, so none occurs). Evaluated at `e`, a contraction is a product, over the pairs `{a, b}` of some matching, of elements `x_a^{j}·D_r(x_a, x_b)`, times traces of powers of `e`, which vanish. Over the rationals the dimension of `Σ_J D_{r,J}C_r` is therefore that of the zero weight space; for even `r` this agrees with Theorem B over `Q`.

(3) *The odd box.* For odd `r = q` the same statement would read `dim_F Σ_J D_{q,J} C_q = N_q(N)`, that is, `⋂_J (I_J + (x_i^q)) = (e_j : j odd) + (x_i^q)` by Theorem A. For `F = F_p` and `q = p^v`, `D_q(a, b) = (a + b)^{q−1}` and `N_q(N) = P_k(q)`. The inequality `≤` holds over every field, by the argument of Proposition 9.1, and by (2) there is equality in characteristic `0`. In positive characteristic we computed equality at `30` pairs of a cell and a characteristic, with `q ∈ {3, 5, 7, 9}`, `N ∈ {2, 4, 6}` and characteristics `3, 5, 7` and `32003`, and at `4` cells in characteristic `2` (§12.5); the earlier notes of this project had it over `F_3` for `q = 3`, `k ≤ 4` [Rep]. **We do not prove it** (§13, problem 7). It cannot follow from Theorem A by an argument that is valid for subfamilies of matchings: for `14` of the `15` matchings at `q = 3`, `k = 2`, over `F_3`, the sum count is `141`, the number of points, and the intersection count is `140` (computed in the earlier notes of this project [Rep]).

"""
cut("**Remark 8.4 (Kostant's theorem, and what is new in Theorem A).**", "---\n\n## 9. Why the full family is needed", R84)

# ---------------------------------------------------------------- §9.1: both ends of the sandwich
rep("So the Main Theorem is the **left** equality. It is not a consequence of Corollary 8.1, which is an equality of the right-hand kind at a different box.",
    "So the Main Theorem is the **left** equality. It is not a consequence of Corollary 8.1, which is an equality of the right-hand kind at a different box. "
    "The right-hand inequality is in fact an equality too: it is the analogue of Theorem A at the even box `q − 1`, which follows from [BRR, Proposition 2.12] (Remark 8.4(6)). So the two ideals `⋂_J (I_J + (x_i^{q−1}))` and `E + (x_i^{q−1})` coincide (Corollary 8.6(ii)). This does not make the Main Theorem a consequence of a count of the kind of Theorem A: the count gives the right-hand equality only, and the equality of the two ideals is what the Main Theorem adds to it.")

# ---------------------------------------------------------------- §12.5
rep("For Remark 8.4(4): the Hilbert series against Lusztig's `t`-analogues at `27` cells and the graded characters of the symmetric group at `56` cycle types (`q = 3, 5`, `n ≤ 6`); "
    "the even-`q` rings at `8` cells in characteristics `0, 3, 5, 7` (equal dimensions) and `2` (larger in all `8`). Engines and logs: [Rep], `engines/theorem-a-kostant/`.",
    "For Remark 8.4(5)–(6): the Hilbert series against Lusztig's `t`-analogues at `27` cells and the graded characters of the symmetric group at `56` cycle types (`q = 3, 5`, `n ≤ 6`); "
    "the even-`q` rings at `8` cells in characteristics `0, 3, 5, 7` (equal dimensions) and `2` (larger in all `8`). "
    "For Corollary 8.6 and Remark 8.7(3): `dim Σ_J D_{r,J}C_r` against the number of closed walks at `13` cells `(r, N)` — `r ∈ {3, 5, 7, 9}` and `r ∈ {2, 4, 6}`, `N ∈ {2, 4, 6}` — in characteristics `3, 5, 7, 32003` (`50` of `50`, with `(5, 6)` in characteristics `3` and `5` only) and at `9` cells in characteristic `2` (`9` of `9`). "
    "One run of the first engine was stopped by the memory guard at the cell `(5, 6)` and rerun with a corrected engine. Engines and logs: [Rep], `engines/theorem-a-kostant/`.")

# ---------------------------------------------------------------- §12.6: limits
rep("- **Version 9.** Remark 8.4 and the other changes of this version have not been read cold by an independent reader. Kostant's theorem is quoted from [Gin, Proposition 4.2]; [Kos] was not read in the original.",
    "- **Versions 9 and 10.** " + COLD + " Kostant's theorem is quoted from [Gin, Proposition 4.2]; [Kos] was not read in the original. [BRR, §2] and the introduction of [Ric] were read in the arXiv sources; [KLT], [Bry] and [Lus] were not read.")

# ---------------------------------------------------------------- §13
cut("6. **Theorem A for even `q`.**", "\n## 14. Exact status",
    "6. **Theorem A for even `q` and odd `n`.** Prove that for every field of characteristic `≠ 2`, every even `q = 2m` and every odd `n`, `dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q)` is the number of walks of length `n` on `Z^m` with steps `±ε_i` from `0` to `ε_1`. For even `n` the corresponding statement (closed walks) follows from [Kos] and [BRR, Proposition 2.12] (Remark 8.4(6)); for odd `n` the weights are not in the root lattice, and the statement is computed in a few cells only. The proof of Theorem A uses the value `0` of the grid, which an even `q` does not have.\n"
    "7. **The odd box.** Prove that for every field `F`, every odd `q` and every `k`, `dim_F Σ_J D_{q,J}C_q = N_q(2k+2)` (Remark 8.7(3)); for `F = F_p` and `q = p^v` this is `dim F_p[x_0, …, x_{2k+1}]/⋂_J (I_J + (x_i^q)) = P_k(q)`, the intersection statement at the odd box. It is the analogue of Theorem B for the orthogonal group; it holds in characteristic `0` (Remark 8.7(2), a sketch) and at every cell we computed. Either adapt the induction of §5 to the box `q`, or derive it, together with Theorem B in odd characteristic, from the theory of modules with a good filtration.\n")

# ---------------------------------------------------------------- §14
rep("In characteristic `0` it follows from Kostant's theorem [Kos] (Remark 8.4); the statement in characteristic `p ≠ 2` and Corollary 8.2 are what this paper adds.",
    "**As a count it is not new:** it follows from Kostant's theorem [Kos] in characteristic `0` and from [BRR, Proposition 2.12] in odd characteristic, through the dictionary of Remark 8.4. What this paper adds is that dictionary and the elementary proof of Appendix A, with its ideals `K_μ`.\n"
    "- **PROVED:** Proposition 8.5 and Corollary 8.6(i) (Theorem B in `2k + 2` variables). **PROVED, modulo [BRR, Proposition 2.12]:** Corollary 8.6(ii) (at the even box `q − 1` and in characteristic `≠ 2`, the two ideals of Proposition 9.1 coincide), and the analogue of Theorem A for even `q` and even `n` (Remark 8.4(6)).")
rep("the Hilbert series of the ring of Theorem A as a sum of Lusztig's `t`-analogues, and the analogue of Theorem A for even `q` in odd characteristic (Remark 8.4(4)).",
    "the Hilbert series of the ring of Theorem A as a sum of Lusztig's `t`-analogues (Remark 8.4(5)); the analogue of Theorem A for even `q` and odd `n` (Remark 8.4(6)); the analogue of Theorem B at the odd box (Remark 8.7(3)).")

# ---------------------------------------------------------------- references
rep("- **[CLO]**",
    "- **[BRR]** R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer, I*, arXiv:2005.05583 (v2, 4 July 2024). (Remark 8.4, Corollary 8.6; §2.2–§2.6 were read in the arXiv source, in particular Proposition 2.12 and the proof of Lemma 2.13.)\n"
    "- **[Bry]** R. K. Brylinski, *Limits of weight spaces, Lusztig's `q`-analogs, and fiberings of adjoint orbits*, J. Amer. Math. Soc. **2** (1989), no. 3, 517–533. (Remark 8.4(5) only; not read in the original.)\n"
    "- **[CLO]**")
rep("- **[Gin]** V. Ginzburg, *Loop Grassmannian cohomology, the principal nilpotent and Kostant theorem*, arXiv:math/9803141 (v2). (Remark 8.4 only; Proposition 4.2 was read in the arXiv version.)",
    "- **[Gin]** V. Ginzburg, *Loop Grassmannian cohomology, the principal nilpotent and Kostant theorem*, arXiv:math/9803141 (v2). (Remark 8.4 only; §4 was read in the arXiv source.)")
rep("- **[Jan]** J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and Monographs **107**, American Mathematical Society, 2003. (Remark 8.3(2) only.)",
    "- **[Jan]** J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and Monographs **107**, American Mathematical Society, 2003. (Remarks 8.3(2) and 8.4(3) only.)")
rep("- **[Kos]** B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. **85** (1963), 327–404. (Remark 8.4 only; quoted through [Gin]; not read in the original.)\n- **[LC]**",
    "- **[KLT]** S. Kumar, N. Lauritzen, J. F. Thomsen, *Frobenius splitting of cotangent bundles of flag varieties*, Invent. Math. **136** (1999), 603–621. (Remark 8.4(3) only; quoted through [BRR]; not read in the original.)\n"
    "- **[Kos]** B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. **85** (1963), 327–404. (Remarks 8.4 and 8.7 only; quoted through [Gin]; not read in the original.)\n"
    "- **[LC]**")
rep("- **[Lus]** G. Lusztig, *Singularities, character formulas, and a `q`-analog of weight multiplicities*, Astérisque **101–102** (1983), 208–229. (Remark 8.4(4) only; not read in the original.)\n- **[Mat]** O. Mathieu, *Filtrations of G-modules*, Ann. Sci. École Norm. Sup. (4) **23** (1990), no. 4, 625–644. (Remark 8.3(2) only.)",
    "- **[Liu]** L. Liu, *Filtrations of tilting modules and costalks of parity sheaves*, arXiv:2007.12444 (24 July 2020). (Remark 8.4(5) only; the introduction was read.)\n"
    "- **[Lus]** G. Lusztig, *Singularities, character formulas, and a `q`-analog of weight multiplicities*, Astérisque **101–102** (1983), 208–229. (Remark 8.4(5) only; not read in the original.)\n"
    "- **[Mat]** O. Mathieu, *Filtrations of G-modules*, Ann. Sci. École Norm. Sup. (4) **23** (1990), no. 4, 625–644. (Remarks 8.3(2) and 8.4(3) only.)")
rep("- **[SK]**",
    "- **[Ric]** S. Riche, *Kostant section, universal centralizer, and a modular derived Satake equivalence*, arXiv:1411.3112. (Remark 8.4(3) only; the introduction and §2.2 were read in the arXiv source.)\n"
    "- **[SK]**")

rep("138. (Appendix A, remark after Definition A.11; Complement to Theorem 5.9.)", "138. (Remark 8.4(4); Appendix A, remark after Definition A.11; Complement to Theorem 5.9.)")

# ---------------------------------------------------------------- notation table
rep("| `E`, `A_k(q)`, `P_k(q)` | odd symmetric ideal; the sum count and the point count of Theorem A | §1.6, §8 |",
    "| `E`, `A_k(q)`, `P_k(q)` | odd symmetric ideal; the sum count and the point count of Theorem A | §1.6, §8 |\n"
    "| `C_r`, `D_r(a,b)`, `D_{r,J}` | the box ring `(x_i^r)` in `2s` variables; the copairing and its products over a matching (Proposition 8.5) | §8 |")

open('PAPER_OFICIAL_v10.md', 'w', encoding='utf-8').write(t)
print('written PAPER_OFICIAL_v10.md', len(t), 'chars;', t.count('\n'), 'lines')
