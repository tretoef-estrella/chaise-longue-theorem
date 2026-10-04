# The odd box — a proof of (O)≥ for every odd `r`, and what follows for the even degrees

Written by Grepy Skies, the pilot of «Grepy is in the Sky», 2 October 2026, as a companion of `REPORT.md` (Leg C). English throughout.

**Status of this document.** It contains a pencil proof, with every line written, of the lower bound in the statement (O) of `MISSION.md` §3 (R4) — problem 7 of §13 of the paper — for every odd `r ≥ 3`, every field and every `k`, together with a short independent proof of the case `r = 3` (§8). Combined with Proposition B5 of `REPORT.md` it gives Conjecture 1.2 of Degtyarev–Shimada for every even degree (§9). **It was produced in one flight, by one pilot, and has been read by nobody else.** It is gated by exact computations (§10), which is not a refereeing. The joints where I would attack it first are listed in §11.

«The paper» is `material/THE_CHAISE_LONGUE_THEOREM_v10.md`.

---
## 0. Statements

Throughout, `r = 2h + 1 ≥ 3` is odd, `F` is a field, and

`C_m := F[y_1, …, y_m]/(y_1^r, …, y_m^r)`.

`D(a, b) := Σ_{u=0}^{r−1} (−1)^u a^u b^{r−1−u}` and `B(a, b) := Σ_{u=0}^{r−2} (−1)^u a^u b^{r−2−u}` are polynomials with integer coefficients (`D = D_r` and `B = D_{r−1}` in the notation of the mission; `B` is the `D` of Theorem B of the paper for the odd number `r`).

> **Theorem O.** For every field `F`, every odd `r ≥ 3` and every `k ≥ 0`,
> `dim_F (D_J : J ∈ 𝒥)·C_{2k+1} ≥ N_r(2k + 2)`,
> where `D_J := Π D(y_a, y_b)` over the `k` pairs of the matching `J` of `{0, …, 2k+1}` that avoid `0`.

With the upper bound of the paper (Remark 8.7(3): `≤` holds over every field) this is (O) with equality. Theorem O is the root case of Theorem 6.1 below, a statement about a family of ideals indexed by «interlaced pairs of down-sets», proved by peeling one variable, as §5 of the paper.

> **Theorem E** (§9). For every even `m ≥ 4` and every `k ≥ 1`, `H_{2k}(X; Z)/L(X)` is torsion free for the Fermat variety `X` of degree `m` and dimension `2k`. With the Main Theorem of the paper (odd `m`): Conjecture 1.2 of [DS] holds for every degree `m ≥ 3` in every even dimension.

**What the proofs rest on.**
- Theorem O: Lemma 5.1 (peeling), Lemma 5.5, Proposition 5.6 and Lemma 5.7(ii) of the paper (all statements about partitions or polynomial identities, used as stated there, for the odd number `q = r`), and what is written here. No topology, no computer.
- Theorem E: Theorem O; Proposition B5 of `REPORT.md` (Leg B), which rests on Theorem 0 of [DS] through Proposition 2.1 of the paper, on §6 of the paper re-read for `p = 2` and for an even cofactor, on Theorem 5.3 of the paper, and on Theorem C of the paper at the boxes `q = p^v` **including `q = 2^v` in characteristic `2`** (§7 of the paper re-read with `q` even).

---
## 1. Elementary identities

In `Z[a, b]`:

- **(1.1)** `D(b, a) = D(a, b)` and `B(b, a) = −B(a, b)` (because `r − 1` is even and `r − 2` is odd).
- **(1.2)** `D(a, b) = b^{r−1} − a·B(a, b)`. (Indeed `−a·B(a, b) = Σ_{u=0}^{r−2} (−1)^{u+1} a^{u+1} b^{r−2−u} = Σ_{w=1}^{r−1} (−1)^w a^w b^{r−1−w}`.)
- **(1.3)** `(a + b)·D(a, b) = a^r + b^r` and `(a + b)·B(a, b) = b^{r−1} − a^{r−1}` (telescoping).
- **(1.4)** For `0 ≤ u ≤ r − 1`, the coefficient of `a^{r−1−u}` in `D(a, b)` is `(−1)^u b^u`. For `0 ≤ u ≤ r − 2`, the coefficient of `a^{r−2−u}` in `B(a, b)` is `−(−1)^u b^u`.

For a set `P` of pairwise disjoint pairs of indices, `D_P := Π_{(a,b) ∈ P} D(y_a, y_b)`. For a finite set `S` of indices, `Δ(S)` is the Vandermonde determinant of the variables `y_s`, `s ∈ S` (`Δ(∅) = Δ({s}) = 1`).

**Peeling** (Lemma 5.1 of the paper, with the box `r`; its proof does not use the size of the box). Write `C_m = C_{m−1}[y_1]/(y_1^r)`, `C_{m−1}` in the variables `y_2, …, y_m`. For an ideal `V ⊆ C_m` and `0 ≤ j ≤ r − 1`, `W_j(V) := {[y_1^j] f : f ∈ V, deg_{y_1} f ≤ j}`. Then `W_j(V)` is an ideal of `C_{m−1}`, `W_j ⊆ W_{j+1}`, and `dim V = Σ_{j=0}^{r−1} dim W_j(V)`. For `Z ⊆ T^m` (`|T| = r`), with `Z_{>i}` the set of tails with more than `i` completions, `|Z| = Σ_{i=0}^{r−1} |Z_{>i}|`.

---
## 2. Points: shapes, interlaced pairs, layers

Let `T` be a set of `r` elements with an involution `u ↦ −u` with exactly one fixed point, written `0`; so `T ∖ {0}` consists of `h` classes `{u, −u}`.

**Shapes.** Let `𝒫_n` be the set of partitions `λ` with at most `h` parts, `|λ| ≤ n` and `|λ| ≡ n (mod 2)` (the set `Par_n^{(h)}` of the paper). For `M ∈ T^m`: in each class with multiplicities `a, ā` keep the number `|a − ā|`; `λ(M)` is the partition formed by the non-zero ones, and `ε(M) ∈ {0, 1}` is the parity of the number of entries equal to `0`. The **shape** of `M` is `(λ(M), ε(M))`. Since `m = 2·(number of disjoint pairs {u, −u} and {0, 0}) + |λ(M)| + ε(M)`, the shape lies in

`Sh_m := {(λ, 0) : λ ∈ 𝒫_m} ∪ {(λ, 1) : λ ∈ 𝒫_{m−1}}`.

`≼` is weak dominance (§5.2 of the paper), `λ − e_j`, `λ + e_j`, `λ ⊔ 1` are as in §5.4 of the paper, and `ℓ = ℓ(λ)`.

**Lemma 2.1 (options; this is (P1)).** Let `M' ∈ T^{m−1}` have shape `(μ, ε)`, `ℓ = ℓ(μ)`, with residual values `u_1, …, u_ℓ` (`u_j` of multiplicity `μ_j`). The `r` values `y ∈ T` give the shapes of `(y, M')`:
- `y = −u_j`: `(μ − e_j, ε)`; `y = u_j`: `(μ + e_j, ε)` (`j = 1, …, ℓ`);
- `y ≠ 0` in one of the `h − ℓ` classes absent from the residue: `(μ ⊔ 1, ε)` (`2(h − ℓ)` values);
- `y = 0`: `(μ, 1 − ε)`.

*Proof.* As §5.4 of the paper for the non-zero values; a new zero changes the parity of the number of zeros and nothing else. The count is `2ℓ + 2(h − ℓ) + 1 = r`. ∎

For `Λ ⊆ Sh_m` put `Λ^0 := {λ : (λ, 0) ∈ Λ} ⊆ 𝒫_m`, `Λ^1 := {λ : (λ, 1) ∈ Λ} ⊆ 𝒫_{m−1}`, `Z_Λ := {M ∈ T^m : shape(M) ∈ Λ}`, and for `σ = (μ, ε) ∈ Sh_{m−1}` let `F_Λ(σ)` be the number of `y ∈ T` such that the shape of `(y, M')` lies in `Λ` (well defined by Lemma 2.1). Explicitly

`F_Λ(μ, ε) = F^*_{Λ^ε}(μ) + [μ ∈ Λ^{1−ε}]`,   (2.1)

`F^*_{Λ'}(μ) := #{j : μ − e_j ∈ Λ'} + #{j : μ + e_j ∈ Λ'} + (r − 1 − 2ℓ)·[μ ⊔ 1 ∈ Λ']`,

which is the function `F_{Λ'}(μ)` of §5.4 of the paper for the odd number `q = r` (there `T` has `q − 1 = r − 1` elements and `h` classes).

**Definition 2.2.** `Λ ⊆ Sh_m` is an **interlaced pair** if
- **(D1)** `Λ^0` is a `≼`-down-set of `𝒫_m` and `Λ^1` is a `≼`-down-set of `𝒫_{m−1}`;
- **(D2)** if `(ν, ε) ∈ Λ` and `1 ≤ j ≤ ℓ(ν)`, then `(ν − e_j, 1 − ε) ∈ Λ`.

(`(ν − e_j, 1 − ε)` is a shape of level `m`: its size has the right parity.)

**Lemma 2.3 (chain).** Let `Λ` be an interlaced pair of level `m` and `(μ, ε) ∈ Sh_{m−1}`, `ℓ = ℓ(μ)`. List the `r` options of Lemma 2.1 as

`(μ − e_1, ε), …, (μ − e_ℓ, ε); (μ, 1 − ε); (μ ⊔ 1, ε) [2(h − ℓ) times]; (μ + e_ℓ, ε), …, (μ + e_1, ε)`.

Then the options lying in `Λ` form an initial segment of this list, of length `F_Λ(μ, ε)`.

*Proof.* Within the removals and within the additions this is Lemma 5.5 of the paper and (D1). If `(μ, 1 − ε) ∈ Λ`, then by (D2) every `(μ − e_j, ε) ∈ Λ`. If `(μ ⊔ 1, ε) ∈ Λ`, then by (D2), removing the new row, `(μ, 1 − ε) ∈ Λ`. If `(μ + e_j, ε) ∈ Λ`, then `(μ ⊔ 1, ε) ∈ Λ` when `ℓ < h` (because `μ ⊔ 1 ≼ μ + e_j`, Lemma 5.5 of the paper, and (D1)), and `(μ, 1 − ε) ∈ Λ` by (D2), removing the box just added. ∎

As in §5.5 of the paper, rows of equal length give equal options; so the removals in `Λ` are those of the rows `1, …, ρ`, where `ρ = 0` or `ρ` is the last row of its length, and the additions in `Λ` are those of the rows `j_0, …, ℓ`, where `j_0` is the first row of its length.

**Lemma 2.4 (layers; this is (P2)).** Let `Λ` be an interlaced pair of level `m ≥ 1`, and for `0 ≤ i ≤ r − 1` let `Λ_i := {σ ∈ Sh_{m−1} : F_Λ(σ) > i}`. Then `Λ_i` is an interlaced pair of level `m − 1`, and `(Z_Λ)_{>i} = Z_{Λ_i}`.

*Proof.* The last assertion is Lemma 2.1.

(D1). Let `μ ≼ μ̃` in `𝒫_{m−1}`. By Proposition 5.6 of the paper (for `q = r`, the down-set `Λ^0 ⊆ Par_m^{(h)}`, tails in `Par_{m−1}^{(h)}`), `F^*_{Λ^0}(μ) ≥ F^*_{Λ^0}(μ̃)`; and `[μ ∈ Λ^1] ≥ [μ̃ ∈ Λ^1]` because `Λ^1` is a down-set of `𝒫_{m−1}`. By (2.1), `F_Λ(μ, 0) ≥ F_Λ(μ̃, 0)`. The same argument, with `Λ^1 ⊆ Par_{m−1}^{(h)}`, tails in `𝒫_{m−2} = Par_{m−2}^{(h)}`, and `𝒫_{m−2} ⊆ 𝒫_m`, gives `F_Λ(μ, 1) ≥ F_Λ(μ̃, 1)` for `μ ≼ μ̃` in `𝒫_{m−2}`. So both components of `Λ_i` are down-sets.

(D2). Let `(ν, ε) ∈ Sh_{m−1}`, `1 ≤ j ≤ ℓ := ℓ(ν)`, `ν' := ν − e_j`, and write `A := Λ^ε`, `A' := Λ^{1−ε}`. We show `F_Λ(ν', 1 − ε) ≥ F_Λ(ν, ε)`, i.e.

`F^*_{A'}(ν') + [ν' ∈ A] ≥ F^*_A(ν) + [ν ∈ A']`.

By (D2) for `Λ`: if a partition `κ` lies in `A` then `κ − e_i ∈ A'` for every row `i` of `κ`, and symmetrically.

*Case `ν_j ≥ 2`.* The rows of `ν'` correspond to the rows of `ν`. If `ν − e_i ∈ A`, then `(ν − e_i) − e_j = ν' − e_i ∈ A'`; if `ν ⊔ 1 ∈ A`, then `(ν ⊔ 1) − e_j = ν' ⊔ 1 ∈ A'`; if `ν + e_i ∈ A`, then `(ν + e_i) − e_j = ν' + e_i ∈ A'`. The number of middle values is the same for `ν` and `ν'`. So `F^*_{A'}(ν') ≥ F^*_A(ν)`. And `ν ∈ A'` implies `ν' = ν − e_j ∈ A`.

*Case `ν_j = 1`.* Then `ν'` has the rows of `ν` other than `j`, and `ν' ⊔ 1 = ν`. For `i ≠ j`: `ν − e_i ∈ A` implies `ν' − e_i ∈ A'`, and `ν + e_i ∈ A` implies `ν' + e_i ∈ A'`. The removal `ν − e_j = ν'` lies in `A` iff `[ν' ∈ A] = 1`. It remains to compare `(r − 1 − 2ℓ)[ν ⊔ 1 ∈ A] + [ν + e_j ∈ A] + [ν ∈ A']` with the middle term of `ν'`, which is `(r − 1 − 2(ℓ − 1))[ν ∈ A'] = (r + 1 − 2ℓ)[ν ∈ A']`. If `ν ∈ A'` the first is at most `(r − 1 − 2ℓ) + 2`. If `ν ∉ A'`: `ν ⊔ 1 ∈ A` would give `(ν ⊔ 1) − e_{ℓ+1} = ν ∈ A'`, and `ν + e_j ∈ A` would give `(ν + e_j) − e_j = ν ∈ A'`; so the first is `0`. ∎

**The root.** For `m = 2k + 1`, `Λ_{root} := {((1), 0), (∅, 1)}` is an interlaced pair (`(1)` is the minimum of `𝒫_{2k+1}`, `∅` of `𝒫_{2k}`, and `(1) − e_1 = ∅`). `Z_{root}` is the set of the `(2k+1)`-tuples with exactly one unpaired value, zero or not; appending the opposite of that value is a bijection onto the `(2k+2)`-tuples that split into pairs `{u, −u}`, `{0, 0}`; so `|Z_{root}| = N_r(2k + 2)` (the count B1 of `REPORT.md`).

---
## 3. Bordered Pfaffians

Let `A = (a_{xy})` be an alternating matrix (`a_{xx} = 0`, `a_{yx} = −a_{xy}`) over a commutative ring, indexed by a totally ordered finite set `X`. `Pf(A)` is its Pfaffian (`1` for `X = ∅`, `0` for `|X|` odd). We use: (i) simultaneous permutation of rows and columns multiplies `Pf` by the sign of the permutation; (ii) if two indices have equal rows, `Pf = 0`; (iii) for a fixed index `x`, `Pf(A) = Σ_{z ≠ x} ± a_{xz}·Pf(A^{x,z})`, where `A^{x,z}` is `A` without the indices `x, z`, and the signs depend only on the positions of `x` and `z` (they alternate in `z`); in particular `Pf` is linear in the row-and-column of `x`.

**Definition.** Let `N` be a finite ordered set of indices of variables and `c = (c_1, …, c_s)` a list of «border columns», each a function `N → R` (`R` the polynomial ring). `Pf(N; c)` is the Pfaffian of the alternating matrix indexed by `N ⊔ {1, …, s}` (first `N`, then the borders) with entries `B(y_i, y_j)` for `i < j` in `N`, `c_k(i)` for `i ∈ N` and a border `k`, and `0` between two borders. For a finite set `E = {e_1 < ⋯ < e_s}` of exponents, `Pf_E(N) := Pf(N; y^{e_1}, …, y^{e_s})`, where `y^e` is the column `i ↦ y_i^e`.

- **(F1)** `Pf(N; c)` changes sign under a transposition of two variables of `N` (apply (i) and the antisymmetry of `B`), and under a transposition of two border columns.
- **(F2)** `Pf(N; c)` is linear in each border column, and vanishes if two border columns are equal. Expanding along the last border: `Pf(N; c_1, …, c_s) = Σ_{b ∈ N} η_b·c_s(b)·Pf(N ∖ b; c_1, …, c_{s−1})`, with signs `η_b` that do not depend on the column `c_s`.
- **(F3)** If `|N| = s`, then `Pf(N; c) = ± det(c_k(i))_{i ∈ N, k ≤ s}`; if `|N| < s`, then `Pf(N; c) = 0`. In particular `Pf_{{0, 1, …, s−1}}(N) = ± Δ(N)` for `|N| = s`. (The matrix is `[[*, C], [−C^t, 0]]` with `C` of size `|N| × s`.)
- **(F4)** *Expansion along a variable `x ∈ N`.* By (iii), separating the entries `B(y_x, y_b)` (`b ∈ N ∖ x`) from the border entries `c_k(x)`:
  `Pf(N; c) = θ·Pf(N ∖ x; c, B(y_x, ·)) + Σ_k ± c_k(x)·Pf(N ∖ x; c without c_k)`,
  where `θ = ±1` and `B(y_x, ·)` is the border column `b ↦ B(y_x, y_b)`. (The first term collects the summands of (iii) with `z ∈ N`: they are the expansion (F2) of the Pfaffian in which `x` is moved to the end and treated as a border.)
- **(F5)** By (1.4) and the linearity (F2), for a set `E` of exponents:
  `Pf(N'; y^E, B(y_x, ·)) = −Σ_{u=0}^{r−2} (−1)^u y_x^{r−2−u}·Pf(N'; y^E, y^u)`,
  `Pf(N'; y^E, D(y_x, ·)) = Σ_{u=0}^{r−1} (−1)^u y_x^{r−1−u}·Pf(N'; y^E, y^u)`,
  and `Pf(N'; y^E, y^u) = 0` if `u ∈ E`, while it is `± Pf_{E ∪ {u}}(N')` if `u ∉ E`. By (1.2), `Pf(N'; y^E, D(y_x, ·)) = Pf(N'; y^E, y^{r−1}) − y_x·Pf(N'; y^E, B(y_x, ·))`.
- **(F6)** (Lemma 5.7(ii) of the paper.) For `S = {b_1 < ⋯ < b_ρ}` and `ε_{b_c} := (−1)^{ρ+c}`: `Σ_{b ∈ S} ε_b Δ(S ∖ b) y_b^u` is `0` for `0 ≤ u ≤ ρ − 2` and `Δ(S)` for `u = ρ − 1`.
- **(F7)** *Laplace.* For `E = {e_1 < ⋯ < e_s}` and `|N| = s + 2κ`: `Pf_E(N) = ± Σ_{S ⊆ N, |S| = s} sgn(S)·det(y_i^{e_k})_{i ∈ S}·Pf(B(y_i, y_j))_{i,j ∈ N ∖ S}`, the signs `sgn(S)` being those of the shuffles. (Expand along the `s` borders with (F2), one after the other.)

---
## 4. Patterns and the ideals `V_Λ`

For a partition `λ`, `λ'_c` is the length of its `c`-th column (`λ'_1 = ℓ(λ)`). For `ℓ ≥ 0` put

`E_0 := {r − 1}`,   `E_ℓ := {0, 1, …, ℓ − 2}` for `ℓ ≥ 1` (so `E_1 = ∅`).

**Definition 4.1 (patterns).** Let `I` be a set of `m` indices and `(λ, ε) ∈ Sh_m`, `ℓ = ℓ(λ)`.
- `ε = 0`: a pattern consists of a set `P` of `(m − |λ|)/2` disjoint pairs of `I` and of disjoint blocks `B_1, …, B_{λ_1}` with `|B_c| = λ'_c` covering the rest. Its **product** is `D_P·Π_c Δ(B_c)`. (These are the tight patterns of the paper, with `D = D_r`.)
- `ε = 1`: a pattern consists of a set `P` of disjoint pairs, of disjoint blocks `B_2, …, B_{λ_1}` with `|B_c| = λ'_c`, and of a **marked block** `M` with `|M| = ℓ + 1 + 2t` for some `t ≥ 0`, which together partition `I`. Its product is `D_P·Pf_{E_ℓ}(M)·Π_{c ≥ 2} Δ(B_c)`.

(Meaning, on a grid: the marked block carries the unpaired zero, the `ℓ` values of the first column of `λ`, and `t` «absorbed» pairs.)

For `Λ ⊆ Sh_m`, `V_Λ ⊆ C_m` is the ideal generated by the products of all the patterns on `{1, …, m}` of all the shapes of `Λ`. All these products have integer coefficients. A permutation of the indices maps every product to `±` a product (by (1.1), (F1) and the antisymmetry of `Δ`), so `V_Λ` is stable under relabelling.

*Examples.* `(∅, 1)` on one index: `y^{r−1}`. `(∅, 1)` on three indices: `y_c^{r−1}D(y_a, y_b)` and `Pf_{{r−1}}({1,2,3}) = ±(y_3^{r−1}B(y_1, y_2) − y_2^{r−1}B(y_1, y_3) + y_1^{r−1}B(y_2, y_3))`. `((1), 1)` on two indices: `B(y_1, y_2)`. `((1,1), 1)` on three indices: `±(B(y_1, y_2) − B(y_1, y_3) + B(y_2, y_3))`.

---
## 5. The membership lemma

**Lemma 5.1.** Let `ℓ ≥ 0`, `t ≥ 0`, and let `M` be a set of `ℓ + 1 + 2t` indices. In `Z[y_i : i ∈ M]/(y_i^r)`,

`Pf_{E_ℓ}(M) ∈ 𝔘_ℓ(M) := ( Δ(S)·D_Q : S ⊆ M, |S| = ℓ + 1, Q a perfect matching of M ∖ S )`.

The proof takes the rest of this section. It is done in an exterior algebra.

**5.1 Alternating polynomials.** Let `V` be the free `Z`-module with basis `v_0, …, v_{r−1}`. For `n ≥ 0` let `𝒜_n ⊆ Z[y_1, …, y_n]` be the group of the alternating polynomials all of whose exponents are `≤ r − 1`. The map `Λ^n(V) → 𝒜_n`, `v_{a_1} ∧ ⋯ ∧ v_{a_n} ↦ det(y_i^{a_j})_{i,j}`, is an isomorphism of groups (an alternating polynomial is determined by the coefficients of its monomials with increasing exponents, and these exponents are distinct). Under it the product `∧` becomes the shuffle product: for `f ∈ 𝒜_p`, `g ∈ 𝒜_q`,

`(f ∧ g)(y_1, …, y_{p+q}) = Σ_{X ⊆ [p+q], |X| = p} sgn(X)·f(y_X)·g(y_{X^c})`   (5.1)

(Laplace expansion of a determinant). `𝒜_n` embeds in `Z[y]/(y_i^r)`, because its monomials have exponents `≤ r − 1`.

**5.2 Divided powers.** `Λ^{ev}(V)` is a commutative ring without `Z`-torsion. For a `2`-form `φ`, written as a sum of *terms* `φ = Σ_τ φ_τ` with each `φ_τ` an integer multiple of some `v_u ∧ v_{u'}`, put `γ_k(φ) := Σ φ_{τ_1} ∧ ⋯ ∧ φ_{τ_k}`, the sum over the `k`-subsets `{τ_1, …, τ_k}` of terms. Since `φ_τ ∧ φ_τ = 0`, `k!·γ_k(φ) = φ^{∧k}`; hence `γ_k(φ)` does not depend on the way `φ` is written, and (multiply by factorials and use torsion-freeness) `γ_n(φ + φ') = Σ_{i+j=n} γ_i(φ) ∧ γ_j(φ')`, `γ_n(cφ) = c^n γ_n(φ)`, `γ_i(φ) ∧ γ_j(φ) = C(i+j, i)·γ_{i+j}(φ)`. The same holds with coefficients in `Z[ζ]`. If `φ ↔ f ∈ 𝒜_2`, then, by (5.1) applied repeatedly,

`γ_k(φ) ↔ Σ_{π} sgn(π)·Π_{(i<j) ∈ π} f(y_i, y_j) = Pf(f(y_i, y_j))_{i,j ≤ 2k}`,   (5.2)

the sum over the perfect matchings `π` of `{1, …, 2k}`.

**5.3 Stable ideals.** Let `𝔘` be an ideal of `Z[y_1, …, y_n]/(y_i^r)` stable under the permutations of the variables. Let `g ∈ 𝒜_p`, `f_1, …, f_κ ∈ 𝒜_2`, `n = p + 2κ`, and suppose that the polynomial `g(y_1, …, y_p)·Π_{i=1}^{κ} f_i(y_{p+2i−1}, y_{p+2i})` lies in `𝔘`. Then the element of `𝒜_n` corresponding to `g ∧ φ_1 ∧ ⋯ ∧ φ_κ` lies in `𝔘`; and if `f_1 = ⋯ = f_{k_1}`, `f_{k_1+1} = ⋯ = f_{k_1+k_2}`, …, so does the element corresponding to `g ∧ γ_{k_1}(φ_1) ∧ γ_{k_2}(φ_{k_1+1}) ∧ ⋯`. *Proof.* By (5.1) and (5.2) each of them is a sum, with signs, of images of that polynomial under permutations of the variables. ∎

**5.4 The pair forms.** For odd `s`, `1 ≤ s ≤ 2r − 3`, put `ω_s(a, b) := Σ (−1)^u a^u b^{u'}`, the sum over `u + u' = s`, `0 ≤ u, u' ≤ r − 1`. It is antisymmetric (`(−1)^{u'} = −(−1)^u`), so `ω_s ∈ 𝒜_2`, and it corresponds to `Ω_s := Σ_{u < u', u + u' = s} (−1)^u v_u ∧ v_{u'}`.
- `ω_{r−2} = B`.
- For odd `i`, `1 ≤ i ≤ r − 2`: `ω_{r−1+i}(a, b) = b^i·D(a, b)` modulo `(a^r, b^r)`. (In `b^i D(a, b) = Σ_u (−1)^u a^u b^{r−1−u+i}` the terms with `u < i` have `b`-exponent `≥ r`; the others are the terms of `ω_{r−1+i}`.) So `ω_s ∈ D(a, b)·Z[a, b]/(a^r, b^r)` for every odd `s ≥ r`.

Split the basis by parity: `e_a := v_{2a}` (`0 ≤ a ≤ h`) and `o_b := v_{2b+1}` (`0 ≤ b ≤ h − 1`). For `u < u'` with `u + u' = s` odd, `(−1)^u v_u ∧ v_{u'} = (even one) ∧ (odd one)`: if `u` is even this is clear, and if `u` is odd, `−v_u ∧ v_{u'} = v_{u'} ∧ v_u`. Hence, with `s = 2σ + 1`,

`Ω_{2σ+1} = J_σ := Σ_{a + b = σ} e_a ∧ o_b`   (`0 ≤ a ≤ h`, `0 ≤ b ≤ h − 1`; `0 ≤ σ ≤ 2h − 1`).

So `B ↔ J_{h−1}`, and the forms `J_σ` with `σ ≥ h` («high») correspond to polynomials in the ideal `(D(a, b))`.

**5.5 The key fact: the generating function is decomposable.** In `Λ(V) ⊗ Z[ζ]` put `E(ζ) := Σ_{a=0}^{h} ζ^a e_a`, `O(ζ) := Σ_{b=0}^{h−1} ζ^b o_b`. Then

`J(ζ) := Σ_{σ=0}^{2h−1} J_σ ζ^σ = E(ζ) ∧ O(ζ)`.

Consequently `E(ζ) ∧ J(ζ) = 0`, and `J(ζ) ∧ J(ζ) = 0`, so `n!·γ_n(J(ζ)) = 0` and, by torsion-freeness,

`γ_n(J(ζ)) = 0` for every `n ≥ 2`.   (5.3)

Write `J(ζ) = L(ζ) + ζ^h U(ζ)` with `L(ζ) := Σ_{σ<h} J_σ ζ^σ` (the low part) and `U(ζ) := Σ_{σ ≥ h} J_σ ζ^{σ−h}` (the high part). Let `𝔥_t ⊆ Λ^{2t}(V)` be the `Z`-span of the products `Π_{σ=h}^{2h−1} γ_{k_σ}(J_σ)` with `Σ k_σ = t` (`𝔥_0 = Z`). Then `γ_j(U(ζ)) ∈ 𝔥_j[ζ]` (binomial formula) and `𝔥_i ∧ 𝔥_j ⊆ 𝔥_{i+j}`.

**Lemma 5.2.** For every `n ≥ 1` there are `A_{n−1} ∈ 𝔥_{n−1}[ζ]` and `A'_n ∈ 𝔥_n[ζ]` with

`γ_n(L(ζ)) = ζ^{h(n−1)}·L(ζ) ∧ A_{n−1} + ζ^{hn}·A'_n`.

*Proof.* `n = 1`: `A_0 = 1`, `A'_1 = 0`. For `n ≥ 2`, by (5.3) and the binomial formula, `0 = Σ_{j=0}^{n} ζ^{hj} γ_{n−j}(L) ∧ γ_j(U)`, i.e. `γ_n(L) = −Σ_{j=1}^{n−1} ζ^{hj} γ_{n−j}(L) ∧ γ_j(U) − ζ^{hn} γ_n(U)`. Insert the statement for `n − j` (`1 ≤ n − j < n`): `ζ^{hj} γ_{n−j}(L) ∧ γ_j(U) = ζ^{h(n−1)} L ∧ (A_{n−j−1} ∧ γ_j(U)) + ζ^{hn} A'_{n−j} ∧ γ_j(U)`. ∎

**Corollary 5.3.** (a) For `t ≥ 0`: `γ_{t+1}(J_{h−1}) ∈ Σ_{σ < h} J_σ ∧ 𝔥_t`. (b) For `t ≥ 0`: `e_h ∧ γ_t(J_{h−1}) ∈ V ∧ 𝔥_t`.

*Proof.* (a) `L(ζ)` has degree `h − 1` in `ζ`, with top coefficient `J_{h−1}`; so the coefficient of `ζ^{(t+1)(h−1)}` in `γ_{t+1}(L(ζ))` is `γ_{t+1}(J_{h−1})`. By Lemma 5.2 it is the coefficient of `ζ^{(t+1)(h−1)}` in `ζ^{ht} L ∧ A_t + ζ^{h(t+1)} A'_{t+1}`; the second term has no power of `ζ` below `h(t+1) > (t+1)(h−1)`, and every coefficient of the first lies in `Σ_{σ<h} J_σ ∧ 𝔥_t`.
(b) For `t = 0` it is trivial. For `t ≥ 1`: `E(ζ)` has degree `h` with top coefficient `e_h`, so `e_h ∧ γ_t(J_{h−1})` is the coefficient of `ζ^{h + t(h−1)}` in `E(ζ) ∧ γ_t(L(ζ))`. By Lemma 5.2 and `E ∧ L = E ∧ (J − ζ^h U) = −ζ^h E ∧ U`,
`E ∧ γ_t(L) = ζ^{h(t−1)} E ∧ L ∧ A_{t−1} + ζ^{ht} E ∧ A'_t = ζ^{ht} E ∧ (A'_t − U ∧ A_{t−1})`,
and `A'_t − U ∧ A_{t−1} ∈ 𝔥_t[ζ]`. ∎

**5.6 Proof of Lemma 5.1.** Number the indices of `M` as `1, …, n`, `n = ℓ + 1 + 2t`.

*The left side.* By (F7) and (5.1)–(5.2), `Pf_E(M)` corresponds, up to sign, to `v_{e_1} ∧ ⋯ ∧ v_{e_s} ∧ γ_κ(Ω_{r−2})` for `E = {e_1 < ⋯ < e_s}`, `n = s + 2κ`. So `Pf_{E_ℓ}(M) ↔ ± v_0 ∧ ⋯ ∧ v_{ℓ−2} ∧ γ_{t+1}(J_{h−1})` for `ℓ ≥ 1`, and `Pf_{E_0}(M) ↔ ± v_{r−1} ∧ γ_t(J_{h−1}) = ± e_h ∧ γ_t(J_{h−1})` for `ℓ = 0` (`r − 1 = 2h`).

*The right side.* `𝔘_ℓ(M)` is stable under the permutations of `M`. Let `x ∈ Λ^{ℓ+1}(V)` correspond to `g ∈ 𝒜_{ℓ+1}`, and let `μ = Π_σ γ_{k_σ}(J_σ) ∈ 𝔥_t`. An alternating polynomial is divisible by the Vandermonde determinant in `Z[y]`, so `g(y_S) ∈ Δ(S)·Z[y_S]` for `S = {1, …, ℓ+1}`; and each `ω_{2σ+1}(a, b)` with `σ ≥ h` lies in `D(a, b)·Z[a, b]/(a^r, b^r)` (5.4). So the polynomial `g(y_S)·Π ω_{2σ+1}(y_a, y_b)`, the product over `t` disjoint pairs of `M ∖ S`, lies in `Δ(S)·D_Q·Z[y]/(y^r) ⊆ 𝔘_ℓ(M)`. By 5.3, the element corresponding to `x ∧ μ` lies in `𝔘_ℓ(M)`. Hence `𝔘_ℓ(M)` contains (the polynomials corresponding to) `Λ^{ℓ+1}(V) ∧ 𝔥_t`.

*Conclusion.* For `ℓ ≥ 1`: by Corollary 5.3(a), `v_0 ∧ ⋯ ∧ v_{ℓ−2} ∧ γ_{t+1}(J_{h−1}) ∈ Σ_{σ<h} (v_0 ∧ ⋯ ∧ v_{ℓ−2} ∧ J_σ) ∧ 𝔥_t ⊆ Λ^{ℓ+1}(V) ∧ 𝔥_t`. For `ℓ = 0`: by Corollary 5.3(b), `e_h ∧ γ_t(J_{h−1}) ∈ V ∧ 𝔥_t = Λ^1(V) ∧ 𝔥_t`. ∎

*Remarks.* (1) For `t = 0` the lemma is trivial. (2) `Pf_{E_ℓ}(M) = 0` when `ℓ + t > h` (an alternating polynomial of degree less than that of the Vandermonde determinant is zero); so only finitely many pairs `(ℓ, t)` matter for a given `r`. (3) The smallest non-trivial case, `(ℓ, t) = (0, 1)`, says `y_3^{r−1}B(y_1, y_2) − y_2^{r−1}B(y_1, y_3) + y_1^{r−1}B(y_2, y_3) ∈ (D(y_1, y_2), D(y_1, y_3), D(y_2, y_3))`; for `r = 3` it reads `Δ(y_1, y_2, y_3) = y_1D(y_1, y_2) − y_1D(y_1, y_3) + y_2D(y_2, y_3)` modulo the cubes. (4) The case `(ℓ, t) = (1, 1)` is the identity `γ_2(J_{h−1}) = −Σ_{j ≥ 1} J_{h−1−j} ∧ J_{h−1+j}`, the coefficient of `ζ^{2h−2}` in `γ_2(J(ζ)) = 0`.

---
## 6. The lifting proposition (this is (P3))

**Proposition 6.1.** Let `Λ` be an interlaced pair of level `m ≥ 1` and `0 ≤ i ≤ r − 1`. Then `V_{Λ_i} ⊆ W_{r−1−i}(V_Λ)`, where `V_{Λ_i} ⊆ C_{m−1}` is built on the indices `2, …, m`.

*Proof.* `W_{r−1−i}(V_Λ)` is an ideal, so it suffices to treat a generator: let `σ = (μ, ε) ∈ Λ_i`, `ℓ = ℓ(μ)`, `Φ := F_Λ(σ) ≥ i + 1`, and let `G` be the product of a pattern of `σ` on `{2, …, m}`. Since the slices are nested it is enough to find `f ∈ V_Λ` with `deg_{y_1} f ≤ r − Φ` and `[y_1^{r−Φ}] f = ±G`. Write `G = D_P·Δ(B_1)·R` if `ε = 0` and `G = D_P·Pf_{E_ℓ}(M)·R` if `ε = 1`, where `R := Π_{c ≥ 2} Δ(B_c)`. By Lemma 2.3 the options in `Λ` are an initial segment of the chain; we split according to the last one.

**(A) The last option in `Λ` is an addition.** Let `j_0` be the smallest `j` with `(μ + e_j, ε) ∈ Λ`; it is the first row of its length, and `Φ = ℓ + 1 + 2(h − ℓ) + (ℓ − j_0 + 1) = r − j_0 + 1`. The column `c^* := μ_{j_0} + 1 ≥ 2` of `μ` has height `j_0 − 1`; put the index `1` into its block `B_{c^*}` (a new block if `c^*` is a new column). This is a pattern of `(μ + e_{j_0}, ε)` (for `ε = 1` the marked block is unchanged, since the first column is). Its product is `G·Π_{c ∈ B_{c^*}} (y_c − y_1)` up to sign: `y_1`-degree `j_0 − 1 = r − Φ` (non-zero in the box, as `j_0 − 1 < r`), top coefficient `±G`.

**(M) The last option in `Λ` is the middle one** (so `ℓ < h` and `Φ = ℓ + 1 + 2(h − ℓ) = r − ℓ`).
- `ε = 0`: put the index `1` into `B_1` (height `ℓ`): a pattern of `(μ ⊔ 1, 0)`, with product of `y_1`-degree `ℓ = r − Φ` and top coefficient `±G`.
- `ε = 1`: here `(μ ⊔ 1, 1) ∈ Λ` and `(μ, 0) ∈ Λ` (the zero option precedes the middle one). Put `E^+ := E_{ℓ+1} = {0, …, ℓ − 1}` and
  `f := ( y_1·Pf_{E^+}(M ∪ {1}) + θ·Pf(M; y^{E^+}, D(y_1, ·)) )·D_P·R`,
  with `θ = ±1` the sign of (F4) for `N = M ∪ {1}`, `x = 1`.
  *`f ∈ V_Λ`.* `Pf_{E^+}(M ∪ {1})·D_P·R` is the product of a pattern of `(μ ⊔ 1, 1)`: marked block `M ∪ {1}` of size `(ℓ + 1) + 1 + 2t`, the same blocks `B_c` (`c ≥ 2`) and pairs. By (F2), `Pf(M; y^{E^+}, D(y_1, ·)) = Σ_{b ∈ M} η_b D(y_1, y_b)·Pf_{E^+}(M ∖ b)`. If `t ≥ 1`, `D(y_1, y_b)·Pf_{E^+}(M ∖ b)·D_P·R` is the product of a pattern of `(μ ⊔ 1, 1)` with marked block `M ∖ b` (size `(ℓ + 2) + 2(t − 1)`) and pairs `P ∪ {(1, b)}`. If `t = 0`, `|M ∖ b| = ℓ = |E^+|` and `Pf_{E^+}(M ∖ b) = ±Δ(M ∖ b)` by (F3), so it is `±` the product of a pattern of `(μ, 0)`: first block `M ∖ b`, pairs `P ∪ {(1, b)}`.
  *Degree.* By (F4), `Pf_{E^+}(M ∪ {1}) = θ·Pf(M; y^{E^+}, B(y_1, ·)) + Σ_{e ∈ E^+} ± y_1^e Pf_{E^+ ∖ e}(M)`, and by (F5), `Pf(M; y^{E^+}, D(y_1, ·)) = Pf(M; y^{E^+}, y^{r−1}) − y_1 Pf(M; y^{E^+}, B(y_1, ·))`. So the terms with `B(y_1, ·)` cancel:
  `f/(D_P R) = Σ_{e ∈ E^+} ± y_1^{e+1} Pf_{E^+ ∖ e}(M) + θ·Pf(M; y^{E^+}, y^{r−1})`.
  The last term does not contain `y_1`. If `ℓ ≥ 1` the `y_1`-degree is `ℓ`, with top coefficient `±Pf_{E^+ ∖ {ℓ−1}}(M) = ±Pf_{E_ℓ}(M)`. If `ℓ = 0`, `E^+ = ∅` and `f/(D_P R) = θ·Pf_{{r−1}}(M) = ±Pf_{E_0}(M)`. In both cases `deg_{y_1} f = ℓ = r − Φ` and the top coefficient is `±G`.

**(Z) The last option in `Λ` is the zero option** (`Φ = ℓ + 1`).
- `ε = 0`: here `(μ, 1) ∈ Λ`. If `ℓ = 0`, `f := y_1^{r−1}·G` is the product of a pattern of `(∅, 1)` with marked block `{1}` (`Pf_{{r−1}}({1}) = y_1^{r−1}`), of `y_1`-degree `r − 1 = r − Φ`. If `ℓ ≥ 1`, `f := Pf_{E_ℓ}(B_1 ∪ {1})·D_P·R` is the product of a pattern of `(μ, 1)` with marked block `B_1 ∪ {1}` (size `ℓ + 1`, `t = 0`). By (F4) and (F5),
  `Pf_{E_ℓ}(B_1 ∪ {1}) = ∓ Σ_{u=0}^{r−2} (−1)^u y_1^{r−2−u} Pf(B_1; y^{E_ℓ}, y^u) + Σ_{e ∈ E_ℓ} ± y_1^e Pf_{E_ℓ ∖ e}(B_1)`.
  `Pf(B_1; y^{E_ℓ}, y^u) = 0` for `u ≤ ℓ − 2`, and for `u = ℓ − 1` it is `±Pf_{{0, …, ℓ−1}}(B_1) = ±Δ(B_1)` by (F3). So the first sum has `y_1`-degree `r − 2 − (ℓ − 1) = r − ℓ − 1` with top coefficient `±Δ(B_1)`; the second has `y_1`-degree `≤ ℓ − 2 < r − ℓ − 1` (as `ℓ ≤ h`). So `deg_{y_1} f = r − ℓ − 1 = r − Φ` with top coefficient `±G`.
- `ε = 1`: here `(μ, 0) ∈ Λ`. For `S ⊆ M` with `|S| = ℓ + 1` and a perfect matching `Q` of `M ∖ S` put, with the signs of (F6),
  `f_{S,Q} := Σ_{b ∈ S} ε_b Δ(S ∖ b)·D(y_1, y_b)·D_Q·D_P·R`.
  Each summand is the product of a pattern of `(μ, 0)`: first block `S ∖ b` (size `ℓ`), blocks `B_c` (`c ≥ 2`), pairs `P ∪ Q ∪ {(1, b)}`; so `f_{S,Q} ∈ V_Λ`. By (1.4) and (F6), `[y_1^{r−1−u}] f_{S,Q} = (−1)^u (Σ_b ε_b Δ(S ∖ b) y_b^u)·D_Q D_P R` vanishes for `u ≤ ℓ − 1` and is `±Δ(S)·D_Q·D_P R` for `u = ℓ`. Hence `Δ(S) D_Q·D_P R ∈ W_{r−1−ℓ}(V_Λ)` for all `S, Q`. As `W_{r−1−ℓ}(V_Λ)` is an ideal, it contains `𝔘_ℓ(M)·D_P R`, and by **Lemma 5.1** it contains `Pf_{E_ℓ}(M)·D_P R = G`. And `r − 1 − ℓ = r − Φ`.

**(R) The last option in `Λ` is a removal.** Then the removals in `Λ` are those of the rows `1, …, ρ`, with `ρ ≥ 1` the last row of its length, and `Φ = ρ`.
- `ε = 0`, or `ε = 1` and `μ_ρ ≥ 2`: the column `c_0 := μ_ρ` of `μ` has height `ρ`, and its block `S := B_{c_0}` is an ordinary block (`c_0 ≥ 2` if `ε = 1`). Write `G = Δ(S)·G'`. As in case (γ) of Proposition 5.8 of the paper, `f := Σ_{b ∈ S} ε_b Δ(S ∖ b)·D(y_1, y_b)·G'` is a sum of products of patterns of `(μ − e_ρ, ε)` (pairs `P ∪ {(1, b)}`, the block of the column `c_0` replaced by `S ∖ b`; for `ε = 1` the first column, hence the marked block, is unchanged). By (1.4) and (F6), `[y_1^{r−1−u}] f` vanishes for `u ≤ ρ − 2` and is `±G` for `u = ρ − 1`: `deg_{y_1} f = r − ρ = r − Φ`.
- `ε = 1` and `μ_ρ = 1`: then `ρ = ℓ`. Put `E' := E_{ℓ−1}` and `f := Pf_{E'}(M ∪ {1})·D_P·R`. It is the product of a pattern of `(μ − e_ℓ, 1)`: the first column of `μ − e_ℓ` has `ℓ − 1` rows, the marked block `M ∪ {1}` has size `((ℓ − 1) + 1) + 2(t + 1)`, and the other columns are those of `μ`. By (F4) and (F5),
  `Pf_{E'}(M ∪ {1}) = ∓ Σ_{u=0}^{r−2} (−1)^u y_1^{r−2−u} Pf(M; y^{E'}, y^u) + Σ_{e ∈ E'} ± y_1^e Pf_{E' ∖ e}(M)`.
  If `ℓ ≥ 2`: `E' = {0, …, ℓ − 3}`; the first sum vanishes for `u ≤ ℓ − 3`, and for `u = ℓ − 2` gives `±y_1^{r−ℓ} Pf_{E_ℓ}(M)`; the second sum has `y_1`-degree `≤ ℓ − 3 < r − ℓ`. If `ℓ = 1`: `E' = {r − 1}`; the first sum has `y_1`-degree `≤ r − 2`, and the second is `±y_1^{r−1} Pf_∅(M) = ±y_1^{r−1} Pf_{E_1}(M)`. In both cases `deg_{y_1} f = r − ℓ = r − Φ`, with top coefficient `±G`. ∎

*Remark (no slack).* In every case the construction lands exactly in the slice `r − Φ`. The absorbed pairs (`t ≥ 1`) are produced by the second case of (R): a removal that empties the first column of a marked tail turns a pair `D` outside the marked block into a pair `B` inside it.

---
## 7. The theorem

**Theorem 6.1.** *For every field `F`, every odd `r ≥ 3`, every `m ≥ 0` and every interlaced pair `Λ ⊆ Sh_m`: `dim_F V_Λ ≥ |Z_Λ|`.*

*Proof.* Induction on `m`. For `m = 0`, `Sh_0 = {(∅, 0)}`: if `Λ = ∅` both sides are `0`; otherwise `V_Λ = F` (the empty product) and `Z_Λ` is one point. Let `m ≥ 1`. By the peeling lemma, Proposition 6.1, the induction hypothesis applied to the interlaced pairs `Λ_i` (Lemma 2.4; `V_{Λ_i}` is stable under relabelling, so the variables `y_2, …, y_m` may be used), and Lemma 2.4 again:

`dim V_Λ = Σ_{i=0}^{r−1} dim W_{r−1−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = Σ_i |(Z_Λ)_{>i}| = |Z_Λ|`. ∎

**Proof of Theorem O.** Take `m = 2k + 1` and `Λ = Λ_{root} = {((1), 0), (∅, 1)}`. The patterns of `((1), 0)` are a set `P` of `k` disjoint pairs and one block of one element; their products are the `D_P`, i.e. the `D_J`, `J ∈ 𝒥`. The patterns of `(∅, 1)` have products `Pf_{{r−1}}(M)·D_{P'}` with `|M| = 1 + 2t`; by Lemma 5.1 with `ℓ = 0`, `Pf_{{r−1}}(M) ∈ (D_Q : Q` a perfect matching of `M` minus one index`)`, so the product lies in `(D_J : J ∈ 𝒥)`. Hence `V_{Λ_{root}} = (D_J : J ∈ 𝒥)·C_{2k+1}`, and Theorem 6.1 gives `dim ≥ |Z_{root}| = N_r(2k + 2)`. ∎

**Corollary 6.2.** (i) (O) holds, with equality, for every odd `r`, every field and every `k` (the inequality `≤` is Remark 8.7(3) of the paper). (ii) The same for the form of Proposition 8.5 of the paper in `2k + 2` variables, `dim Σ_J D_{r,J}·C_r = N_r(2k + 2)`: this is Theorem 6.1 for `Λ = {(∅, 0)}` at level `2k + 2`, whose patterns are the perfect matchings.

---
## 8. The case `r = 3`, written out without Pfaffians (an independent proof)

For `r = 3` (`h = 1`) the theory collapses to a family with one parameter, and every step is a one-line identity. `T = {−1, 0, 1}`; the shape of `M` is determined by `j(M) := |Σ_i M_i|` (the mark is the parity of `m − j`), and the interlaced pairs are the sets `{j ≤ J}`. Put `D(a, b) = y_a^2 − y_a y_b + y_b^2`, and for `0 ≤ J ≤ m`:

- `Z_J^{(m)} := {M ∈ {−1, 0, 1}^m : |Σ M_i| ≤ J}`;
- if `J ≡ m (mod 2)`: `I(m, J) := (D_P : |P| = (m − J)/2)`;
- if `J ≢ m (mod 2)` and `J ≥ 1`: `I(m, J) := ((y_b − y_a)·D_P : |P| = (m − 1 − J)/2; D_{P^+} : |P^+| = (m + 1 − J)/2)`;
- if `J = 0` and `m` is odd: `I(m, 0) := (y_c^2·D_P : P` a perfect matching of the rest`; Δ(y_a, y_b, y_c)·D_{P'} : P'` a perfect matching of the rest`)`.

**Theorem T3.** `dim_F I(m, J) ≥ |Z_J^{(m)}|` for every field `F` and all `0 ≤ J ≤ m`. In particular `I(2k + 1, 1) = (D_J : J ∈ 𝒥)` and `|Z_1^{(2k+1)}| = N_3(2k + 2)`: (O)≥ at `r = 3`.

*Proof.* Induction on `m`; `I(0, 0) = F`. For `J = m` the ideal is the unit ideal and `Z` is everything. Counting: a tail with `|Σ| = j'` has `3` completions if `j' ≤ J − 1`, `2` if `j' = J ≥ 1`, `1` if `j' = J + 1` or `j' = J = 0`, and none otherwise. So `|Z_J^{(m)}| = |Z_{J+1}^{(m−1)}| + |Z_J^{(m−1)}| + |Z_{J−1}^{(m−1)}|` for `J ≥ 1` and `|Z_0^{(m)}| = |Z_1^{(m−1)}|` (with `Z_J^{(m−1)}` everything for `J ≥ m − 1` and `I(m − 1, J)` the unit ideal there). It suffices to show, for the slices of `I(m, J)` (peeling `y_1`):

`W_2 ⊇ I(m−1, J+1)`, `W_1 ⊇ I(m−1, J)`, `W_0 ⊇ I(m−1, J−1)` for `J ≥ 1`;  `W_2 ⊇ I(m−1, 1)` for `J = 0`.

Write `D(1, b)` for `D(y_1, y_b) = y_1^2 − y_1 y_b + y_b^2`; `P, P', P^+` denote sets of disjoint pairs inside `{2, …, m}`, and «free» means an index of `{2, …, m}` outside them.

*Case I: `J ≡ m`, `1 ≤ J ≤ m − 2`, `p := (m − J)/2 ≥ 1`; `I(m, J) = (D_P : |P| = p)`.*
- `W_2 ⊇ I(m−1, J+1) = (D_{P'} : |P'| = p − 1)`: there are `J + 1 ≥ 2` free indices; for a free `b`, `D(1, b)·D_{P'} ∈ I(m, J)` has `y_1^2`-coefficient `D_{P'}`.
- `W_1 ⊇ I(m−1, J) = ((y_b − y_a)D_{P'} : |P'| = p − 1; D_{P''} : |P''| = p)`: `(D(1, b) − D(1, a))·D_{P'} = (−y_1(y_b − y_a) + y_b^2 − y_a^2)·D_{P'} ∈ I(m, J)`; and `D_{P''} ∈ I(m, J)` does not contain `y_1`.
- `W_0 ⊇ I(m−1, J−1) = (D_{P''} : |P''| = p)`: these are generators of `I(m, J)` without `y_1`.

*Case II: `J ≢ m`, `1 ≤ J ≤ m − 1`, `p := (m − 1 − J)/2`; `I(m, J) = ((y_b − y_a)D_P : |P| = p; D_{P^+} : |P^+| = p + 1)`.*
- `W_2 ⊇ I(m−1, J+1)`. If `p = 0` this is the unit ideal, and `D(1, b) ∈ I(m, J)` has `y_1^2`-coefficient `1`. If `p ≥ 1` its generators are `(y_b − y_a)D_{P'}` (`|P'| = p − 1`) and `D_P` (`|P| = p`); there is a free index `c` besides `a, b` in the first case (`J ≥ 1` of them) and a free `b` in the second, and `D(1, c)(y_b − y_a)D_{P'}`, `D(1, b)D_P` lie in `I(m, J)` with `y_1^2`-coefficients the generators.
- `W_1 ⊇ I(m−1, J) = (D_P : |P| = p)`: for a free `b`, `(y_b − y_1)·D_P ∈ I(m, J)` has `y_1`-coefficient `−D_P`.
- `W_0 ⊇ I(m−1, J−1)`. If `J ≥ 2` its generators `(y_b − y_a)D_P` (`|P| = p`), `D_{P^+}` (`|P^+| = p + 1`) are generators of `I(m, J)` without `y_1`. If `J = 1` (`m` even) it is `I(m − 1, 0) = (y_c^2 D_P, Δ(y_a, y_b, y_c) D_{P'})`, and
  `y_c^2 = y_1·(y_c − y_1) + D(1, c)`,
  `Δ(y_a, y_b, y_c) = D(1, a)(y_c − y_b) − D(1, b)(y_c − y_a) + D(1, c)(y_b − y_a)`
  (in the second identity the coefficients of `y_1^2` and of `y_1` cancel, and the constant term is `y_a^2(y_c − y_b) − y_b^2(y_c − y_a) + y_c^2(y_b − y_a) = Δ`). So `y_c^2 D_P` and `Δ·D_{P'}` lie in `I(m, 1)` and do not contain `y_1`.

*Case III: `J = 0`.* If `m` is even, `I(m, 0) = (D_{P^+} : P^+` a perfect matching`)` and `I(m − 1, 1) = (D_{P'} : |P'| = (m − 2)/2)`: with the free index `b`, `D(1, b)D_{P'}` has `y_1^2`-coefficient `D_{P'}`. If `m` is odd, `I(m − 1, 1) = ((y_b − y_a)D_{P'}; D_{P^+})` with `P^+` a perfect matching of `{2, …, m}` and `P'` one of `{2, …, m} ∖ {a, b}`: `y_1^2·D_{P^+} ∈ I(m, 0)`, and `Δ(y_1, y_a, y_b)·D_{P'} = (y_a − y_1)(y_b − y_1)(y_b − y_a)D_{P'} ∈ I(m, 0)` has `y_1^2`-coefficient `(y_b − y_a)D_{P'}`.

The last sentence of the theorem: the `D_P` with `|P| = k` in `2k + 1` variables are the `D_J`; and deleting the last entry is a bijection from the `(2k+2)`-tuples in `{−1, 0, 1}` of sum `0` onto `Z_1^{(2k+1)}`. ∎

This proof uses nothing from §2–§7.

---
## 9. Conjecture 1.2 for the even degrees

**Theorem E.** *Let `m ≥ 4` be even and `k ≥ 1`. Then `H_{2k}(X; Z)/L(X)` is torsion free for the Fermat variety of degree `m` and dimension `2k`.*

*Proof.* By Proposition B5 of `REPORT.md`, Conjecture 1.2 at `(k, m)` holds as soon as (i) for every odd prime `p` with `p^v ∥ m` and every `k' ≤ k`, (O) holds at `(k', p^v, F_p)`, and (ii′) if `4 | m`, with `2^v ∥ m`, (O)≥ holds at `(k'', 2^v − 1, F_2)` for every `k'' ≤ k`. Both are Corollary 6.2(i), since `p^v` and `2^v − 1` are odd. ∎

For `m = 4` the proof uses only §8 (Theorem T3 over `F_2`) and step B2 of `REPORT.md`. For `m = 6` and `m = 12` it uses §8 (over `F_2` and `F_3`) and the colour reduction; no Pfaffian.

With the Main Theorem of the paper for odd `m`: **Conjecture 1.2 of Degtyarev–Shimada holds for every `m ≥ 3` and every even dimension** — modulo everything listed in §0 and in §14 of the paper, and modulo the audit of this document.

---
## 10. Gates (exact computations; scripts and logs in `checks/`)

- **Theorem O, root:** (O) measured with equality at `(k, r, p)` = `(1, 3..11, 2)`, `(2, 3..9, 2)`, `(3, 3, 2)`, `(1,3,3)`, `(2,3,3)`, `(3,3,3)`, `(1,5,3)`, `(2,5,3)`, `(1,5,5)`, `(2,5,5)`, `(1,7,7)`, `(2,7,7)`, `(1,9,3)`, `(2,9,3)` (runs a04, b04), and `(4,3,2)`, `(3,5,2)`, `(2,15,2)`, `(2,11,11)` (run c11, predicted before the run).
- **Theorem 6.1 with equality, every interlaced pair:** `V_Λ = gr J(Z_Λ)` (top forms of the functions supported on `Z_Λ` on a grid) for all the 78 interlaced pairs of 18 cells `(r, m, p)`, `r ≤ 7` (run c05); every node of the slice tree of the root equals `V_Λ` in characteristics `2`, `3`, `101` (11 trees, runs c05 and c12). Control: without the absorbed pairs the equality fails in 7 of the 18 cells.
- **Lemma 2.4 and Lemma 2.3:** layers of interlaced pairs are interlaced, options form an initial segment (run c03, every interlaced pair of 18 cells); for pairs of down-sets that are **not** interlaced the peeling fails (first failure `r = 3`, `m = 3`).
- **Proposition 6.1:** each construction (A), (M), (Z), (R), with its sub-cases, checked on every pattern of every tail shape of every interlaced pair in 19 cells `(r, m, p)` with `r ≤ 9`, `m ≤ 5` — membership in `V_Λ`, `y_1`-degree, top coefficient: `0` failures (runs c07, c13, c14; the largest cell, `(5, 5, 2)`, has `926` cases).
- **Lemma 5.1:** the membership itself in 46 instances over `F_p` (runs c08); the identities of §5.5 (decomposability, Lemma 5.2, Corollary 5.3) with exact integers for `r = 3, 5, 7, 9, 11` (run c09).
- **§8:** `dim I(m, J) = |Z_J^{(m)}|` and every slice containment, `m ≤ 7`, characteristics `2`, `3`, `101` (run c06); control with the wrong sign.
- **Theorem E in cells not in [DS, §5]:** `(n, m) = (6, 6)`: the prime `2` directly in the literal group ring (run c10: `18733`), the prime `3` directly, colouring by colouring, from the literal generators (run b05: `18733`).

---
## 11. Where to attack

1. **Lemma 5.1 (§5).** The dictionary between Pfaffians and exterior products ((F7), (5.1), (5.2)), in particular the divided powers when two pair forms coincide (5.3); the claim `ω_{r−1+i} = b^i D` modulo the box; the decomposability `J(ζ) = E(ζ) ∧ O(ζ)` (a sign check on `(−1)^u v_u ∧ v_{u'}`); and the bookkeeping of the powers of `ζ` in Corollary 5.3.
2. **Proposition 6.1, case (M), `ε = 1`,** where two Pfaffians are combined so that the terms with `B(y_1, ·)` cancel; and case (Z), `ε = 1`, where the lemma is used.
3. **Lemma 2.4, (D2),** the case `ν_j = 1`; and the use of Proposition 5.6 of the paper for the two components.
4. **Definition 4.1:** that the patterns of a marked shape are what the constructions of §6 need and produce (sizes of the marked block; `E_ℓ`).
5. **The reduction B5** (in `REPORT.md`): Theorem C of the paper at `q = 2^v` in characteristic `2`; the block of colour `−1`; Lemma B.0.
6. The author of this document is the same system as the authors and readers of the paper; nobody else has read it.
