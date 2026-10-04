# Part 3: §8 — intro, §8.3 (explicit signs, attributions, any commutative ring),
# §8.4 (zero patterns), §8.5 (the rank-two route, Lemma 8.7′), §8.6 (ϑ), Corollary 8.13
# (upper bound by a pairing), Theorem 8.15 (the letter J), §1.9 (η).
import pathlib
SRC = (pathlib.Path(__file__).parent / "v11_source.md").read_text(encoding="utf-8")

def block(start, end):
    assert SRC.count(start) == 1, start
    assert SRC.count(end) == 1, end
    i = SRC.index(start); j = SRC.index(end, i)
    return SRC[i:j]

OLD_83 = block("### 8.3 Bordered Pfaffians\n", "### 8.4 Patterns and the ideals `V_Λ`")
NEW_83 = """### 8.3 Bordered Pfaffians
Let `A = (a_{xy})` be an alternating matrix (`a_{xx} = 0`, `a_{yx} = −a_{xy}`) over a commutative ring, indexed by a totally ordered finite set `X`, and write `p_x ∈ {0, 1, 2, …}` for the position of `x ∈ X`, counted from `0`. The **Pfaffian** of `A` is `Pf(A) := Σ_π sgn(π)·Π_{{x<y} ∈ π} a_{xy}`, the sum over the perfect matchings `π` of `X`, where `sgn(π)` is the sign of the permutation that lists the pairs of `π` one after the other, each pair in increasing order (it does not depend on the order of the pairs, and it is `(−1)` to the number of crossings of `π`). So `Pf(A) = 1` for `X = ∅` and `Pf(A) = 0` for `|X|` odd. Three properties follow from the definition [Knu, (0.1), (0.4), (2.0)], [Oka, §2.1]:
- (i) a simultaneous permutation of rows and columns multiplies `Pf` by the sign of the permutation;
- (ii) if two indices `x ≠ x'` have equal rows, then `Pf(A) = 0`: exchanging `x` and `x'` is an involution of the matchings that do not pair them, which changes the sign and keeps the product, and a matching that pairs them has the factor `a_{xx'} = a_{x'x'} = 0`;
- (iii) for a fixed index `x`, `Pf(A) = Σ_{z ≠ x} ε(x, z)·a_{xz}·Pf(A^{x,z})`, where `A^{x,z}` is `A` without the indices `x, z`, and `ε(x, z) = (−1)^{p_x+p_z+1}` if `x < z`, `ε(x, z) = (−1)^{p_x+p_z}` if `z < x`. In particular `Pf` is additive in the row-and-column of `x`.

None of them needs a division or a hypothesis on `2`-torsion: they hold over every commutative ring, characteristic `2` included. All the rings below are polynomial rings over `Z` and their quotients, and the identities are proved there and then reduced to any field.

**Definition.** *Let `a` be an alternating matrix indexed by a finite ordered set `N` of `n` indices, and `c = (c_1, …, c_s)` a list of «border columns», each a function from `N` to the ring. `Pf(a; c)` is the Pfaffian of the alternating matrix indexed by `N ⊔ {1, …, s}` (first `N`, then the borders) whose block on `N` is `a`, whose entry in the row of `i ∈ N` and the column of the border `k` is `c_k(i)`, and whose block on the borders is `0`. For a set `N` of indices of variables, `a_N := (D^−(y_i, y_j))_{i,j ∈ N}` (alternating, by (8.1)), `Pf(N; c) := Pf(a_N; c)`, and, for a finite set `E = {e_1 < ⋯ < e_s}` of exponents, `Pf_E(N) := Pf(N; y^{e_1}, …, y^{e_s})`, where `y^e` is the column `i ↦ y_i^e`.*

In (F1)–(F7), `n = |N|`, `s` is the number of borders, and `a^{(b)}` is `a` without the index `b`, the columns being restricted to `N ∖ b`.
- **(F1)** `Pf(a; c)` changes sign under a transposition of two indices of `N` together with the corresponding entries of the borders, and under a transposition of two border columns (by (i)).
- **(F2)** `Pf(a; c)` is additive and homogeneous in each border column, and it vanishes if two border columns are equal (by (iii) and (ii)). Expanding along the last border: `Pf(a; c_1, …, c_s) = Σ_{b ∈ N} η_b·c_s(b)·Pf(a^{(b)}; c_1, …, c_{s−1})` with `η_b := (−1)^{n+s+p_b}`.
- **(F3)** If `n = s`, then `Pf(a; c) = (−1)^{s(s−1)/2}·det(c_k(i))_{i ∈ N, k ≤ s}` (rows indexed by `N` in its order); it does not depend on `a`. In particular `Pf_{{0, 1, …, s−1}}(N) = (−1)^{s(s−1)/2}·Δ(N)` for `|N| = s`. (A matching with a non-zero product pairs every border with an element of `N`, so it is a bijection from `N` to the borders.)
- **(F4)** *Expansion along an index `x ∈ N`.* Split the row-and-column of `x` into its entries against `N ∖ x` and its entries against the borders. By (iii),
  `Pf(a; c) = ϑ·Pf(a^{(x)}; c, a_x) + Σ_{k=1}^{s} (−1)^{p_x+n+k}·c_k(x)·Pf(a^{(x)}; c without c_k)`,   `ϑ := (−1)^{p_x+n+s}`,
  where `a_x` is the border column `b ↦ a_{xb}` on `N ∖ x`; for `a = a_N` it is `D^−(y_x, ·)`, the column `b ↦ D^−(y_x, y_b)`. (In the first part, `x` is moved to the last place and becomes a border.)
- **(F5)** By (8.4) and (F2), for a set `E` of exponents:
  `Pf(N'; y^E, D^−(y_x, ·)) = −Σ_{u=0}^{r−2} (−1)^u y_x^{r−2−u}·Pf(N'; y^E, y^u)`,
  `Pf(N'; y^E, D(y_x, ·)) = Σ_{u=0}^{r−1} (−1)^u y_x^{r−1−u}·Pf(N'; y^E, y^u)`,
  and `Pf(N'; y^E, y^u) = 0` if `u ∈ E`, while it is `(−1)^{#{e ∈ E : e > u}}·Pf_{E ∪ {u}}(N')` if `u ∉ E`. By (8.2), `Pf(N'; y^E, D(y_x, ·)) = Pf(N'; y^E, y^{r−1}) − y_x·Pf(N'; y^E, D^−(y_x, ·))`.
- **(F6)** (Lemma 5.7(ii).) For `S = {b_1 < ⋯ < b_ρ}` and `ε_{b_c} := (−1)^{ρ+c}`: `Σ_{b ∈ S} ε_b Δ(S ∖ b) y_b^u` is `0` for `0 ≤ u ≤ ρ − 2` and `Δ(S)` for `u = ρ − 1`.
- **(F7)** *Laplace.* For an alternating matrix `a` on `N` and `n = s + 2κ`,
  `Pf(a; c) = (−1)^{s(s−1)/2}·Σ_{S ⊆ N, |S| = s} sgn(S)·det(c_k(i))_{i ∈ S, k ≤ s}·Pf(a|_{N∖S})`,
  where `sgn(S) = (−1)^{Σ_{i ∈ S} p_i − s(s−1)/2}` is the sign of the shuffle that puts `S` before `N ∖ S`, and `a|_{N∖S}` is the restriction of `a`. This is the case of [Oka, Proposition 2.3] in which the block on the borders is `0`. (A matching with a non-zero product consists of a bijection from a subset `S` of `N` onto the borders and of a perfect matching of `N ∖ S`.)

The signs in (iii) and (F2)–(F7) are those of the Lean proof (§14.8); only their form matters below, except where the text says otherwise.

"""

OLD_85 = block("### 8.5 The membership lemma\n", "### 8.6 (P3) Every pattern of a layer lies in the right slice")
NEW_85 = """### 8.5 The membership lemma
**Lemma 8.7.** *Let `ℓ ≥ 0`, `t ≥ 0`, and let `B_0` be a set of `ℓ + 1 + 2t` indices. In `Z[y_i : i ∈ B_0]/(y_i^r)`,*

`Pf_{E_ℓ}(B_0) ∈ 𝔘_ℓ(B_0) := ( Δ(S)·D_Q : S ⊆ B_0, |S| = ℓ + 1, Q a perfect matching of B_0 ∖ S )`.

We prove a more general statement, in which the borders are arbitrary powers. For a finite set `N` of indices, `𝔘_ℓ(N)` is defined in the same way, with `|S| = ℓ + 1`.

**Lemma 8.7′ (the membership lemma, any exponents).** *Let `N` be a set of `n` indices, `t ≥ 0`, and `e_1, …, e_s ≥ 0` any exponents. In `Z[y_i : i ∈ N]/(y_i^r)`:*
- *(a) if `n = s + 2(t + 1)`, then `Pf(N; y^{e_1}, …, y^{e_s}) ∈ 𝔘_{s+1}(N)`;*
- *(b) if `n = s + 1 + 2t`, then `Pf(N; y^{e_1}, …, y^{e_s}, y^{r−1}) ∈ 𝔘_s(N)`.*

Lemma 8.7 is the case `s = ℓ − 1`, `(e_1, …, e_s) = (0, 1, …, ℓ − 2)` of (a) for `ℓ ≥ 1`, and the case `s = 0` of (b) for `ℓ = 0`. The proof takes the rest of this subsection; the symbols `ω_s`, `Ev`, `Od`, `W_σ`, `H` and the variable `ζ` are local to it.

**(a) Three polynomials.** For odd `s`, `1 ≤ s ≤ 2r − 3`, put `ω_s(a, b) := Σ (−1)^u a^u b^{s−u}`, the sum over the `u` with `0 ≤ u ≤ r − 1` and `0 ≤ s − u ≤ r − 1`. The set of these `u` is stable under `u ↦ s − u`, which exchanges the terms of `ω_s(a, b)` and of `ω_s(b, a)` and changes the sign `(−1)^u`, because `s` is odd; so `ω_s(b, a) = −ω_s(a, b)`, and `ω_s(a, a) = 0` (the terms `u` and `s − u ≠ u` cancel; no division by `2` is involved).
- `ω_{r−2} = D^−` (for `s = r − 2` the conditions are `0 ≤ u ≤ r − 2`).
- For odd `i`, `1 ≤ i ≤ r − 2`: `ω_{r−1+i}(a, b) = b^i·D(a, b)` modulo `(a^r, b^r)`. (In `b^i D(a, b) = Σ_u (−1)^u a^u b^{r−1−u+i}` the terms with `u < i` have `b`-exponent at least `r`; the others are the terms of `ω_{r−1+i}`.)
- In `Z[a, b][ζ]`, with `Ev(a) := Σ_{α=0}^{h} ζ^α a^{2α}` and `Od(a) := Σ_{β=0}^{h−1} ζ^β a^{2β+1}`:

  `Σ_{σ=0}^{2h−1} ζ^σ ω_{2σ+1}(a, b) = Ev(a)·Od(b) − Ev(b)·Od(a)`.   (8.6)

  Indeed, in `ω_{2σ+1}(a, b)` the terms with `u = 2α` even have `b`-exponent `2β + 1` with `α + β = σ`, and the sign `+`; the terms with `u = 2β + 1` odd have `b`-exponent `2α`, and the sign `−`. Every pair `(α, β)` with `0 ≤ α ≤ h`, `0 ≤ β ≤ h − 1` occurs exactly once, with `σ = α + β`.

So the matrix `(Σ_σ ζ^σ ω_{2σ+1}(y_i, y_j))_{i,j}` has rank two: it is `Ev·Odᵀ − Od·Evᵀ` for the columns `Ev = (Ev(y_i))_i` and `Od = (Od(y_i))_i`. This is the one fact behind the lemma.

**Lemma 8.8 (two operations on bordered Pfaffians).** *Let `a` be an alternating matrix on `N`, `c = (c_1, …, c_s)` border columns, and `E, O` two more columns, over a commutative ring.*
- *(i) (border shift) For every function `λ` on `N` and every `k ≤ s`: `Pf(a'; c) = Pf(a; c)`, where `a'_{ij} := a_{ij} + λ_i c_k(j) − λ_j c_k(i)`.*
- *(ii) (rank-two update) `Pf(a + E·Oᵀ − O·Eᵀ; c) = Pf(a; c) − Pf(a; c, E, O)`.*

*Proof.* We use one elementary operation: for two indices `x ≠ w` of an alternating matrix `A` and an element `λ`, adding `λ` times the row of `x` to the row of `w`, and `λ` times the column of `x` to the column of `w`, does not change `Pf(A)`. Indeed, by the additivity of (iii) in the row-and-column of `w`, the Pfaffian changes by `λ·Pf(A'')`, where `A''` is `A` with the row and the column of `w` replaced by those of `x` (and `A''_{ww} = 0`); the rows of `w` and `x` in `A''` are equal, so `Pf(A'') = 0` by (ii).

(i) In the bordered matrix of `(a; c)`, the row of the border `k` is `−c_k` on `N` and `0` on the borders. For each `w ∈ N`, add `−λ_w` times the row and the column of the border `k` to those of `w`: the entry `(w, j)`, `j ∈ N`, becomes `a_{wj} + λ_w c_k(j)`, the entry `(i, w)` becomes `a_{iw} − λ_w c_k(i)`, and the border columns do not change. After all `w` the matrix is the bordered matrix of `(a'; c)`.

(ii) Let `X_θ` be the bordered matrix of `(a; c, E, O)` with the entry `θ` in the row of the border `E` and the column of the border `O` (and `−θ` in the symmetric place). Expanding along the index `O` by (iii), the only term that contains `θ` is the one of `z = E`, with `ε(O, E) = −1` (the borders `E` and `O` are the last two indices), and it is `θ·Pf(a; c)`; so `Pf(X_θ) = Pf(a; c, E, O) + θ·Pf(a; c)`. Now take `θ = 1` and, for each `w ∈ N`, add `E_w` times the row and the column of `O` to those of `w`. The row of `O` is `−O` on `N`, `0` on the borders of `c` and `−1` at `E`; so the block on `N` becomes `a − E·Oᵀ + O·Eᵀ`, the entry of `w` in the column of `E` becomes `E_w − E_w = 0`, and nothing else changes. Then the row of `E` is `0` except for the entry `1` at `O`; for each `w ∈ N`, adding `−O_w` times the row and the column of `E` to those of `w` clears the column of `O` on `N`. The final matrix is the bordered matrix of `(a − E·Oᵀ + O·Eᵀ; c)` together with the block `[[0, 1], [−1, 0]]` on the last two indices, and its Pfaffian, expanded along `O`, is `Pf(a − E·Oᵀ + O·Eᵀ; c)`. Hence `Pf(a − E·Oᵀ + O·Eᵀ; c) = Pf(a; c) + Pf(a; c, E, O)`; replacing `O` by `−O` and using (F2) gives (ii). ∎

There is no sign that depends on `n` or `s`. Two more facts follow at once from the definition of the Pfaffian as a sum over matchings, in which a matching with a non-zero product uses one entry of each border and `κ := (n − s)/2` entries of `a`: **(homogeneity)** `Pf(τ·a; c) = τ^κ·Pf(a; c)` for every scalar `τ`; and **(top coefficients)** if `a` and `c` have entries in a polynomial ring `A[ζ]`, those of `a` of degree at most `d` and those of the border `c_k` of degree at most `d_k`, then `Pf(a; c)` has degree at most `κd + Σ_k d_k` in `ζ`, and its coefficient there is `Pf(a^{top}; c^{top})`, the bordered Pfaffian of the coefficients of the degrees `d` and `d_k`.

**Corollary 8.9 (the closed forms).** *Let `A` be a commutative ring, `y_i ∈ A` (`i ∈ N`), `W_σ := (ω_{2σ+1}(y_i, y_j))_{i,j ∈ N}`, `H := Σ_{τ=0}^{h−1} ζ^τ W_{h+τ}` over `A[ζ]`, and `Ev`, `Od` the columns of (8.6) at the `y_i`. For border columns `c = (c_1, …, c_s)` over `A`:*
- *(a) if `n = s + 2(t + 1)`, then `Pf(N; c) = (−1)^{t+1}·[ζ^{h−1−t}] Pf(H; c, Ev, Od)` for `t ≤ h − 1`, and `Pf(N; c) = 0` for `t ≥ h`;*
- *(b) if `n = s + 1 + 2t`, then `Pf(N; c, y^{r−1}) = (−1)^t·[ζ^{h−t}] Pf(H; c, Ev)` for `t ≤ h`, and `Pf(N; c, y^{r−1}) = 0` for `t > h`.*

*Proof.* Put `L := Σ_{σ=0}^{h−1} ζ^σ W_σ`. By (8.6), `L + ζ^h H = Ev·Odᵀ − Od·Evᵀ`, entry by entry. The entries of `L` have degree at most `h − 1` in `ζ`, with top coefficient `W_{h−1} = a_N`. (a) By Lemma 8.8(ii) with `a := −ζ^h H` and homogeneity,
`Pf(L; c) = Pf(−ζ^h H; c) − Pf(−ζ^h H; c, Ev, Od) = (−ζ^h)^{t+1}·Pf(H; c) − (−ζ^h)^t·Pf(H; c, Ev, Od)`.
Take the coefficient of `ζ^{(h−1)(t+1)}`: on the left it is `Pf(a_N; c) = Pf(N; c)`, by the top coefficients; the first term on the right is a multiple of `ζ^{h(t+1)}`, so it contributes `0`; the second contributes `(−1)^{t+1}·[ζ^{h−1−t}] Pf(H; c, Ev, Od)` if `ht ≤ (h−1)(t+1)`, i.e. `t ≤ h − 1`, and `0` otherwise. (b) By Lemma 8.8(i), applied to `a := −ζ^h H`, the last border `Ev` and `λ := −Od`, `Pf(−ζ^h H; c, Ev) = Pf(−ζ^h H + Ev·Odᵀ − Od·Evᵀ; c, Ev) = Pf(L; c, Ev)`; and `Pf(−ζ^h H; c, Ev) = (−ζ^h)^t·Pf(H; c, Ev)`. The border `Ev` has degree `h` with top coefficient `y^{2h} = y^{r−1}`; take the coefficient of `ζ^{(h−1)t + h}`: on the left it is `Pf(N; c, y^{r−1})`, and on the right `(−1)^t·[ζ^{h−t}] Pf(H; c, Ev)` if `t ≤ h`, and `0` otherwise. ∎

*Proof of Lemma 8.7′.* Work in `A := Z[y_i : i ∈ N]/(y_i^r)`. Since `2(h + τ) + 1 = (r − 1) + (2τ + 1)`, the second item of (a) gives `H_{ij} = Σ_τ ζ^τ y_j^{2τ+1} D(y_i, y_j) = D(y_i, y_j)·Od(y_j)` in `A[ζ]`. By the definition of the Pfaffian as a sum over matchings, `Pf(H|_{N'})` therefore lies, for every subset `N'`, in the ideal of `A[ζ]` generated by the products `D_Q`, `Q` a perfect matching of `N'`. (a) Expand `Pf(H; y^{e_1}, …, y^{e_s}, Ev, Od)` by (F7). Its `s + 2` borders are values `P_k(y_i)` of polynomials `P_k ∈ Z[ζ][T]` in one variable; so for each `S ⊆ N` with `|S| = s + 2`, `det(P_k(y_i))_{i ∈ S}` is an alternating polynomial in the variables `y_i`, `i ∈ S`, and hence a multiple of `Δ(S)` in `Z[ζ][y_i : i ∈ S]`. So every coefficient of every power of `ζ` in `Pf(H; y^{e_1}, …, y^{e_s}, Ev, Od)` is a combination of products `Δ(S)·D_Q`, with `|S| = s + 2` and `Q` a perfect matching of `N ∖ S`: it lies in `𝔘_{s+1}(N)`. By Corollary 8.9(a), so does `Pf(N; y^{e_1}, …, y^{e_s})`. (b) The same with the `s + 1` borders `y^{e_1}, …, y^{e_s}, Ev` and Corollary 8.9(b). ∎

*Remarks.* (1) The smallest non-trivial case of Lemma 8.7, `(ℓ, t) = (0, 1)`, says `y_3^{r−1}D^−(y_1, y_2) − y_2^{r−1}D^−(y_1, y_3) + y_1^{r−1}D^−(y_2, y_3) ∈ (D(y_1, y_2), D(y_1, y_3), D(y_2, y_3))`; for `r = 3` it reads `Δ(y_1, y_2, y_3) = y_1D(y_1, y_2) − y_1D(y_1, y_3) + y_2D(y_2, y_3)` modulo the cubes. (2) *Some patterns are zero.* By Corollary 8.9, `Pf_{E_ℓ}(B_0) = 0` when `ℓ ≥ 1` and `t ≥ h`, and when `ℓ = 0` and `t > h`; such patterns of Definition 8.6 contribute nothing, and do no harm. (3) *The border `y^{r−1}` in (b) cannot be dropped:* at `r = 5`, `n = 3`, `Pf(N; y^2)` does not lie in `𝔘_0(N)` (§14.9). (4) *Version 11* proved Lemma 8.7 in the exterior algebra on a free module with basis `v_0, …, v_{r−1}`, with divided powers of `2`-forms: there (8.6) says that the generating function of the `2`-forms of the `ω_s` is the product of two `1`-forms, and Lemma 8.8(ii) is the formula `γ_κ(φ + E ∧ O) = γ_κ(φ) + γ_{κ−1}(φ) ∧ E ∧ O` for the divided powers `γ_κ` of a `2`-form `φ` and two `1`-forms `E`, `O`. The proof printed here is the one that was formalized (§14.8); it uses no exterior algebra, no divided powers and no torsion-freeness, and it proves Lemma 8.7′, the statement for other border sets that problem 7(c) of version 11 asked for.

"""

EDITS = [
    ("8 intro",
     "and the place of Lemma 5.7(ii) is taken, in one of the seven cases, by a membership lemma (Lemma 8.7) that is proved in an exterior algebra.",
     "and the place of Lemma 5.7(ii) is taken, in one of the seven cases, by a membership lemma (Lemma 8.7), which is proved by a rank-two update of bordered Pfaffians (§8.5)."),
    ("8.3", OLD_83, NEW_83),
    ("8.4 zero patterns",
     "On the side of the points, the marked block carries the unpaired zero, the `ℓ` values of the first column of `λ`, and `t` «absorbed» pairs.",
     "On the side of the points, the marked block carries the unpaired zero, the `ℓ` values of the first column of `λ`, and `t` «absorbed» pairs. (Some of these products are `0`, by §8.5, Remark (2); this does no harm.)"),
    ("8.5", OLD_85, NEW_85),
    ("8.10 (M) f",
     "  with `θ = ±1` the sign of (F4) for `N = B_0 ∪ {1}`, `x = 1`.",
     "  with `ϑ = ±1` the sign of (F4) for `N = B_0 ∪ {1}`, `x = 1`."),
    ("8.10 (M) f def",
     "`f := ( y_1·Pf_{E^+}(B_0 ∪ {1}) + θ·Pf(B_0; y^{E^+}, D(y_1, ·)) )·D_P·R`",
     "`f := ( y_1·Pf_{E^+}(B_0 ∪ {1}) + ϑ·Pf(B_0; y^{E^+}, D(y_1, ·)) )·D_P·R`"),
    ("8.10 (M) degree",
     "`Pf_{E^+}(B_0 ∪ {1}) = θ·Pf(B_0; y^{E^+}, D^−(y_1, ·)) + Σ_{e ∈ E^+} ± y_1^e Pf_{E^+ ∖ e}(B_0)`",
     "`Pf_{E^+}(B_0 ∪ {1}) = ϑ·Pf(B_0; y^{E^+}, D^−(y_1, ·)) + Σ_{e ∈ E^+} ± y_1^e Pf_{E^+ ∖ e}(B_0)`"),
    ("8.10 (M) whatever",
     "So the two terms with `D^−(y_1, ·)` cancel, whatever the value of `θ`:",
     "So the two terms with `D^−(y_1, ·)` cancel, whatever the value of `ϑ`:"),
    ("8.10 (M) quotient",
     "`f/(D_P R) = Σ_{e ∈ E^+} ± y_1^{e+1} Pf_{E^+ ∖ e}(B_0) + θ·Pf(B_0; y^{E^+}, y^{r−1})`.",
     "`f/(D_P R) = Σ_{e ∈ E^+} ± y_1^{e+1} Pf_{E^+ ∖ e}(B_0) + ϑ·Pf(B_0; y^{E^+}, y^{r−1})`."),
    ("8.10 (M) l=0",
     "`f/(D_P R) = θ·Pf_{{r−1}}(B_0) = ±Pf_{E_0}(B_0)`",
     "`f/(D_P R) = ϑ·Pf_{{r−1}}(B_0) = ±Pf_{E_0}(B_0)`"),
    ("8.13 upper bound by a pairing",
     "For the upper bound, let first `F = Q` and `T := {−h, …, h} ⊂ Q`. By Proposition 10.5(ii), `dim Σ_P D_P·C_N = dim Q[x]/⋂_P (I_P + (x_i^r))`, with `I_P := (x_a + x_b : {a, b} ∈ P)`.",
     "For the upper bound, let first `F = Q` and `T := {−h, …, h} ⊂ Q`, and put `I_P := (x_a + x_b : {a, b} ∈ P)` and `ℳ := Σ_P D_P·C_N`. On `C_N` let `⟨f, g⟩` be the coefficient of `Π_i x_i^{r−1}` in `fg`; as in the proof of Proposition 2.6 the pairing is perfect, so `dim V + dim V^⊥ = dim C_N` for every subspace `V`, and the annihilator of an ideal is contained in its orthogonal. By (8.3), `(x_a + x_b)·D(x_a, x_b) = 0` in the box, so `I_P·C_N` annihilates `D_P`, and `⋂_P I_P·C_N` annihilates `ℳ`. Hence `dim ℳ ≤ dim C_N − dim ⋂_P I_P·C_N = dim Q[x]/⋂_P (I_P + (x_i^r))`."),
    ("8.15 the letter J (reader note 5)",
     "In particular `I(2k + 1, 1) = (D_J : J ∈ 𝒥)C_{2k+1}` and `|Z_1^{(2k+1)}| = N_3(2k + 2)`: this is Theorem O, `≥`, at `r = 3`.",
     "In particular `I(2k + 1, 1)` is the ideal generated by the `D_P`, `P ∈ 𝒥`, in `C_{2k+1}`, and `|Z_1^{(2k+1)}| = N_3(2k + 2)`: this is Theorem O, `≥`, at `r = 3`."),
    ("1.9 letters eta",
     "`η` is `e^{πi/m}` in Appendix B;",
     "`η` is `e^{πi/m}` in Appendix B, and `η_b` are the signs of (F2) in §8.3 and §8.6;"),
]
