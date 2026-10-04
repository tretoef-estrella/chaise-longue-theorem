# The odd box: identities, shapes with a mark, interlaced pairs, and the chain

This file uses, unchanged:
- `q_chain_lemma.md`: partitions (`ChainLemma.Partition`), `ℓ(μ)` (`len`), the rows `μ_i` (`row`), weak dominance `≼`, the options `μ − e_j` (`subE`), `μ + e_j` (`addE`), `μ ⊔ 1` (`addOne`), the list `opt_p(μ)`, `p = 1, …, L` (`opt`), and its parts (a), (b), (c).
- `q_P2_monotone_options.md`: the size `|μ|` (`size`).
- `q_P1_fibres.md`: the residue partition of a tuple, the count `cnt`, and `F_Λ(μ) := #{p ∈ {1, …, 2h} : opt_p(μ) ∈ Λ}` (`Fibres.FLam h Λ μ`, with `L = 2h`).
- `q_P3_lifts.md`: `Par_n := {λ : |λ| ≤ n, |λ| ≡ n (mod 2), ℓ(λ) ≤ h}` (`Lifts.Par h n`) and "down-set of `Par_n`" (`Lifts.IsDownSetPar h n Λ`: `Λ ⊆ Par_n`, and `λ ∈ Par_n`, `λ ≼ μ ∈ Λ` imply `λ ∈ Λ`).
- `q_peeling_lemma.md`, part (iv): the tuple `(t, M')` (`Peel.consTuple`), the fibre `F(M')` (`Peel.fiber`) and `Z_{>i}` (`Peel.Zgt`).
- `q_col_one.md`: for elements `a`, `b` of a commutative ring and an integer `q`, `Dab q a b := Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}` (`ColOne.Dab`).

It is the first piece of §8 of the paper (the odd box). Nothing here uses a field: Part A is about polynomial identities over any commutative ring, and Parts B and C are combinatorics.

## Part A. Elementary identities

Let `A` be a commutative ring, `a, b ∈ A`, and `r ≥ 1` an integer. Put

`D(a, b) := Σ_{u=0}^{r−1} (−1)^u a^u b^{r−1−u} = Dab (r+1) a b`,   `D^−(a, b) := Σ_{u=0}^{r−2} (−1)^u a^u b^{r−2−u} = Dab r a b`.

**(A0) (every `r ≥ 1`, no parity)** For every integer `q ≥ 1`: `(a + b)·Dab q a b = b^{q−1} − (−a)^{q−1}`.

**(A1) (every `r ≥ 1`, no parity)** `D(a, b) = b^{r−1} − a·D^−(a, b)`; that is, `Dab (r+1) a b = b^{r−1} − a·Dab r a b`.

From now on `r` is **odd**.

**(A2)** `D(b, a) = D(a, b)` and `D^−(b, a) = −D^−(a, b)`.

**(A3)** `(a + b)·D(a, b) = a^r + b^r` and `(a + b)·D^−(a, b) = b^{r−1} − a^{r−1}`.

**(A4)** `D(a, b) = Σ_{u=0}^{r−1} (−1)^u b^u a^{r−1−u}` and `D^−(a, b) = −Σ_{u=0}^{r−2} (−1)^u b^u a^{r−2−u}`. In terms of coefficients: in the polynomial ring `A[X]`, with `b ∈ A`, the polynomial `Dab (r+1) X b` has, for `0 ≤ u ≤ r − 1`, the coefficient `(−1)^u b^u` at `X^{r−1−u}`; and the polynomial `Dab r X b` has, for `0 ≤ u ≤ r − 2`, the coefficient `−(−1)^u b^u` at `X^{r−2−u}`. (Here `b` is seen in `A[X]` as a constant.)

### Proofs

(A0) `(a + b)·Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u} = Σ_{u=0}^{q−2} (−1)^u a^{u+1} b^{q−2−u} + Σ_{u=0}^{q−2} (−1)^u a^u b^{q−1−u}`. In the first sum put `w = u + 1`: it is `−Σ_{w=1}^{q−1} (−1)^w a^w b^{q−1−w}`. The terms `1 ≤ u ≤ q − 2` cancel; what is left is the term `u = 0` of the second sum, `b^{q−1}`, and the term `w = q − 1` of the first, `−(−1)^{q−1} a^{q−1} = −(−a)^{q−1}`. (For `q = 1` both sides are `0`: `Dab 1 a b` is an empty sum and `b^0 − (−a)^0 = 0`.)

(A1) `−a·D^−(a, b) = Σ_{u=0}^{r−2} (−1)^{u+1} a^{u+1} b^{r−2−u} = Σ_{w=1}^{r−1} (−1)^w a^w b^{r−1−w}`, which is `D(a, b)` without its term `w = 0`, namely `b^{r−1}`.

(A2) In `D(b, a) = Σ_u (−1)^u b^u a^{r−1−u}` substitute `w = r − 1 − u`: since `r − 1` is even, `(−1)^u = (−1)^w`, and the sum is `D(a, b)`. In `D^−(b, a)` substitute `w = r − 2 − u`: since `r − 2` is odd, `(−1)^u = −(−1)^w`, and the sum is `−D^−(a, b)`.

(A3) By (A0) with `q = r + 1`: `(a + b)·D(a, b) = b^r − (−a)^r = b^r + a^r` because `r` is odd. By (A0) with `q = r`: `(a + b)·D^−(a, b) = b^{r−1} − (−a)^{r−1} = b^{r−1} − a^{r−1}` because `r − 1` is even.

(A4) The two displayed formulas are (A2) written out (`D(a, b) = D(b, a)` and `D^−(a, b) = −D^−(b, a)`). The coefficients are read off them.

## Part B. Shapes with a mark, and the options

### Setting

Let `h ≥ 1`, `r := 2h + 1`, and let `T` be a finite set with `|T| = r`, together with an involution `u ↦ −u` (`−(−u) = u`) that has **exactly one fixed point**, written `0` (`−0 = 0`, and `−u ≠ u` for `u ≠ 0`). So `T ∖ {0}` splits into `h` classes `{u, −u}`.

**Shape.** For a tuple `M ∈ T^m`:
- `λ(M)` is the residue partition, defined as in `q_P1_fibres.md`: its parts are the numbers `|a − ā|` over the classes `{u, −u}`, `u ≠ 0`, with `a ≠ ā`, where `a = #{i : M_i = u}` and `ā = #{i : M_i = −u}`; in weakly decreasing order. (Formally, as in `Fibres.FibreSetting.resPart`: the positive values of the truncated differences `cnt M u − cnt M (−u)` over all `u ∈ T`; the fixed point `u = 0` contributes `0`.)
- `δ(M) ∈ {0, 1}` is the parity of `#{i : M_i = 0}`. We call it the **mark**.
- The **shape** of `M` is the pair `(λ(M), δ(M))`.

A *shape* in general is a pair `(λ, δ)` of a partition and a mark `δ ∈ {0, 1}`; `1 − δ` is the other mark.

**The sets `Sh_m`.** For `m ≥ 0`:

`Sh_m := {(λ, 0) : λ ∈ Par_m} ∪ {(λ, 1) : λ ∈ Par_{m−1}}`,

where the second set is **empty for `m = 0`** (there is no `Par_{−1}`). So `Sh_0 = {(∅, 0)}`. Equivalently: `(λ, δ) ∈ Sh_m` iff `ℓ(λ) ≤ h`, `|λ| + δ ≤ m` and `|λ| + δ ≡ m (mod 2)`.

**The list of options of a shape.** For a shape `(μ, δ)` with `ℓ := ℓ(μ) ≤ h` and `p = 1, …, r = 2h + 1` put

- `optS_p(μ, δ) := (μ − e_p, δ)` for `1 ≤ p ≤ ℓ`;
- `optS_p(μ, δ) := (μ, 1 − δ)` for `p = ℓ + 1`;
- `optS_p(μ, δ) := (μ ⊔ 1, δ)` for `ℓ + 1 < p ≤ 2h + 1 − ℓ`;
- `optS_p(μ, δ) := (μ + e_{2h+2−p}, δ)` for `2h + 1 − ℓ < p ≤ 2h + 1`.

In terms of the list `opt_p(μ)` of `q_chain_lemma.md` with `L = 2h`: `optS_p(μ, δ) = (opt_p(μ), δ)` for `p ≤ ℓ`, `optS_{ℓ+1}(μ, δ) = (μ, 1 − δ)`, and `optS_p(μ, δ) = (opt_{p−1}(μ), δ)` for `p ≥ ℓ + 2`. So the list is

`(μ − e_1, δ), …, (μ − e_ℓ, δ);  (μ, 1 − δ);  (μ ⊔ 1, δ) [2h − 2ℓ times];  (μ + e_ℓ, δ), …, (μ + e_1, δ)`.

**The function `F_Λ` on shapes.** For a set `Λ` of shapes put `Λ^0 := {λ : (λ, 0) ∈ Λ}`, `Λ^1 := {λ : (λ, 1) ∈ Λ}`, and

`F_Λ(μ, δ) := F_{Λ^δ}(μ) + [μ ∈ Λ^{1−δ}]`,   (8.5)

where `F_{Λ^δ}(μ)` is the function of `q_P1_fibres.md` (`Fibres.FLam h (Λ^δ) μ`) and `[·]` is `1` or `0`. Equivalently `F_Λ(μ, δ) = #{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) ∈ Λ}`.

`Z_Λ := {M ∈ T^m : the shape of M lies in Λ}`.

### Proposition B

**(B1)** For every `M ∈ T^m`, the shape of `M` lies in `Sh_m`: `ℓ(λ(M)) ≤ h`, `|λ(M)| + δ(M) ≤ m` and `|λ(M)| + δ(M) ≡ m (mod 2)`.

**(B2) (options; Lemma 8.1 of the paper)** Let `m ≥ 1` and `M' ∈ T^{m−1}`, with shape `(μ, δ)`. The multiset `{shape of (t, M') : t ∈ T}` (one entry for each of the `2h + 1` elements `t`) equals the multiset `{optS_p(μ, δ) : p = 1, …, 2h + 1}`. More precisely: `t = 0` gives `(μ, 1 − δ)`, and the `2h` values `t ≠ 0` give the multiset `{(opt_p(μ), δ) : p = 1, …, 2h}`.

**(B3)** If `(μ, δ) ∈ Sh_{m−1}` (`m ≥ 1`), then `optS_p(μ, δ) ∈ Sh_m` for every `p = 1, …, 2h + 1`.

**(B4)** For every set `Λ` of shapes, every `m ≥ 1` and every tail `M' ∈ T^{m−1}`: `#{t ∈ T : the shape of (t, M') lies in Λ} = F_Λ(shape of M')`. In the notation of `q_peeling_lemma.md`, with `Z = Z_Λ`: `|F(M')| = F_Λ(shape of M')`, and

`Z_{>i} = {M' ∈ T^{m−1} : F_Λ(shape of M') > i}` for every `i ≥ 0`.

**(B5)** `F_Λ(μ, δ) = #{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) ∈ Λ}` whenever `ℓ(μ) ≤ h`.

### Proofs

(B1) The classes with `a ≠ ā` are among the `h` classes of `T ∖ {0}`, so `ℓ(λ(M)) ≤ h`. Let `z := #{i : M_i = 0}`. Then `m = z + Σ_κ (a + ā)`, the sum over the `h` classes, and `|λ(M)| = Σ_κ |a − ā| ≤ Σ_κ (a + ā) = m − z`, with `|a − ā| ≡ a + ā (mod 2)`. So `|λ(M)| ≡ m − z (mod 2)` and `|λ(M)| ≤ m − z`. If `z` is even, `δ = 0` and `|λ| ≤ m`, `|λ| ≡ m`. If `z` is odd, `δ = 1`, `z ≥ 1`, `|λ| + 1 ≤ m` and `|λ| + 1 ≡ m`.

(B2) Adding the value `t = 0` does not change any count `cnt (·) u` with `u ≠ 0`, so `λ((0, M')) = λ(M') = μ`, and it changes the parity of the number of zeros: the shape is `(μ, 1 − δ)`. Adding a value `t ≠ 0` does not change the number of zeros, so the mark is `δ`; and the residue partition changes exactly as in part (ii) of `q_P1_fibres.md`, because the residue partition only involves the counts of the non-zero values, and `T ∖ {0}` with the restricted involution is a set with `2h` elements and a fixed-point-free involution: `t = −u_j` gives `μ − e_j`, `t = u_j` gives `μ + e_j`, and the `2(h − ℓ)` values `t` in the balanced classes give `μ ⊔ 1`. So the `2h` values `t ≠ 0` give the multiset `{opt_p(μ) : p = 1, …, 2h}` with the mark `δ`. Inserting `(μ, 1 − δ)` gives the multiset of the `optS_p(μ, δ)`.

(B3) If `δ = 0`: `μ ∈ Par_{m−1}`, so `|μ ± 1| ≤ m` with the parity of `m`, and `(μ − e_j, 0), (μ + e_j, 0), (μ ⊔ 1, 0) ∈ Sh_m` (the lengths are `≤ h`: `μ ⊔ 1` occurs in the list only if `2h − 2ℓ > 0`, that is `ℓ < h`); and `(μ, 1) ∈ Sh_m` because `μ ∈ Par_{m−1}`. If `δ = 1`: `m − 1 ≥ 1` and `μ ∈ Par_{m−2}`, so `|μ| ± 1 ≤ m − 1` with the parity of `m − 1`, and `(μ ∓ e_j, 1), (μ ⊔ 1, 1) ∈ Sh_m`; and `(μ, 0) ∈ Sh_m` because `|μ| ≤ m − 2 ≤ m` and `|μ| ≡ m (mod 2)`. (Alternatively: by (B1) and (B2), when `(μ, δ)` is the shape of some tail; (B3) as stated does not need that.)

(B4) Count the `t` with the shape of `(t, M')` in `Λ` using (B2): the `2h` non-zero values contribute `#{p ≤ 2h : (opt_p(μ), δ) ∈ Λ} = F_{Λ^δ}(μ)`, and `t = 0` contributes `[(μ, 1 − δ) ∈ Λ] = [μ ∈ Λ^{1−δ}]`. The rest is as in part (iii) of `q_P1_fibres.md`.

(B5) By the description of `optS_p` through `opt_p`: the indices `p ≠ ℓ + 1` are in bijection with `{1, …, 2h}` and contribute `F_{Λ^δ}(μ)`; the index `p = ℓ + 1` contributes `[μ ∈ Λ^{1−δ}]`.

## Part C. Interlaced pairs and the chain

### Definition (interlaced pair; Definition 8.2 of the paper)

A set `Λ` of shapes is an **interlaced pair of level `m`** if
- **(D0)** `Λ ⊆ Sh_m`;
- **(D1)** `Λ^0` is a down-set of `Par_m`, and `Λ^1` is a down-set of `Par_{m−1}` (for `m = 0`: `Λ^1 = ∅`, which follows from (D0));
- **(D2)** if `(ν, δ) ∈ Λ` and `1 ≤ j ≤ ℓ(ν)`, then `(ν − e_j, 1 − δ) ∈ Λ`.

In words: removing one box from a shape of `Λ` and switching the mark stays in `Λ`.

### Lemma C (chain; Lemma 8.3 of the paper)

**(C1)** For every `(ν, δ) ∈ Sh_m` and `1 ≤ j ≤ ℓ(ν)`: `(ν − e_j, 1 − δ) ∈ Sh_m`. (So (D2) makes sense inside `Sh_m`.)

**(C2)** Let `m ≥ 1`, let `Λ` be an interlaced pair of level `m`, and let `(μ, δ) ∈ Sh_{m−1}`. Then the set `{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) ∈ Λ}` is the initial segment `{1, …, F_Λ(μ, δ)}` of `{1, …, 2h + 1}`.

**(C3)** The following are interlaced pairs: the empty set (every level); `Sh_m` (level `m`); `{(∅, 0)}` at every **even** level `m`; and `{((1), 0), (∅, 1)}` at every **odd** level `m`. (Here `(1)` is the partition with one part equal to `1`.)

### Proofs

(C1) `|ν − e_j| + (1 − δ) = |ν| − 1 + 1 − δ = |ν| + δ − 2δ`, which is `|ν| + δ` if `δ = 0` and `|ν| + δ − 2` if `δ = 1`; in both cases it is `≤ m` and `≡ m (mod 2)`. The length does not grow.

(C2) Write `ℓ := ℓ(μ)`, `A := Λ^δ`, and `s_p := optS_p(μ, δ)`. By (B5) the set in question has `F_Λ(μ, δ)` elements, so it is enough to prove: **if `s_{p+1} ∈ Λ` then `s_p ∈ Λ`**, for `1 ≤ p ≤ 2h`. By (B3) all the `s_p` lie in `Sh_m`; in particular the partitions `opt_p(μ)`, `p = 1, …, 2h`, lie in the set `Par_m` (if `δ = 0`) or `Par_{m−1}` (if `δ = 1`) of which `A` is a down-set.
- *`p + 1 ≤ ℓ`* (two removals): `μ − e_p ≼ μ − e_{p+1}` by part (b) of `q_chain_lemma.md`, and `A` is a down-set.
- *`p = ℓ`, `ℓ ≥ 1`* (`s_{p+1} = (μ, 1 − δ)`, `s_p = (μ − e_ℓ, δ)`): by (D2) applied to `(μ, 1 − δ) ∈ Λ` and the row `ℓ`.
- *`p = ℓ + 1` and `2h − 2ℓ > 0`* (`s_{p+1} = (μ ⊔ 1, δ)`, `s_p = (μ, 1 − δ)`): by (D2) applied to `(μ ⊔ 1, δ) ∈ Λ` and its last row `ℓ + 1`, since `(μ ⊔ 1) − e_{ℓ+1} = μ`.
- *`p = ℓ + 1` and `2h − 2ℓ = 0`* (`s_{p+1} = (μ + e_ℓ, δ)`, `s_p = (μ, 1 − δ)`; this needs `ℓ ≥ 1`): by (D2) applied to `(μ + e_ℓ, δ) ∈ Λ` and the row where the box was added: if `j_0` is the first row of `μ` with `μ_{j_0} = μ_ℓ`, then `μ + e_ℓ` has its row `j_0` equal to `μ_ℓ + 1` and `(μ + e_ℓ) − e_{j_0} = μ`.
- *`ℓ + 2 ≤ p` and `p + 1 ≤ 2h + 1 − ℓ`* (two copies of `(μ ⊔ 1, δ)`): equal.
- *`p = 2h + 1 − ℓ`, `p ≥ ℓ + 2`, `ℓ ≥ 1`* (`s_{p+1} = (μ + e_ℓ, δ)`, `s_p = (μ ⊔ 1, δ)`): `μ ⊔ 1 ≼ μ + e_ℓ` by part (b) of `q_chain_lemma.md`, and `A` is a down-set.
- *`p > 2h + 1 − ℓ`* (two additions): `μ + e_{j+1} ≼ μ + e_j` by part (b) of `q_chain_lemma.md` (`j = 2h + 1 − p`), and `A` is a down-set.

(In the three cases that use part (b) of `q_chain_lemma.md`, these are the comparisons `opt_{p'}(μ) ≼ opt_{p'+1}(μ)` for the corresponding indices `p'` of the list with `L = 2h`.)

(C3) The empty set: clear. `Sh_m`: (D1) holds because `Par_m` and `Par_{m−1}` are down-sets of themselves, and (D2) is (C1). `{(∅, 0)}` at an even level `m`: `∅ ∈ Par_m`; every `λ ≼ ∅` is `∅`; `Λ^1 = ∅`; and `∅` has no rows. `{((1), 0), (∅, 1)}` at an odd level `m`: `(1) ∈ Par_m` and `∅ ∈ Par_{m−1}`; a partition `λ ∈ Par_m` with `λ ≼ (1)` has `|λ| ≤ 1` and `|λ|` odd, so `λ = (1)`; `{∅}` is a down-set of `Par_{m−1}`; and (D2) asks for `((1) − e_1, 1) = (∅, 1) ∈ Λ`, which holds.

## Remarks

1. Here `Par_n` has the parameter `h` with `r = 2h + 1`, the odd box; in the earlier files `h = (q − 1)/2` for an odd `q`. `F_{Λ'}` of `q_P1_fibres.md` with `L = 2h = r − 1` is the function written `F^*_{Λ'}` in the paper.
2. The two interlaced pairs of (C3) other than `∅` and `Sh_m` are the roots of the induction of the paper (Lemma 8.5); their point sets are counted in a later piece.
3. Checked by brute force before this file was written (`chkE6.py`, 93 checks, 0 failures): (A1)–(A4) for `r = 3, …, 13` and (A0) for `q ≤ 14`; (B1), (B2) for every tail with `h ≤ 3` and `m ≤ 6, 5, 4`; (B3) for every shape with `h ≤ 4`, `m ≤ 8`; (B4), (B5) on random `Λ`; (C2) for **all** 163 interlaced pairs with `(h, m)` up to `(1, 7)`, `(2, 6)`, `(3, 5)`; (C3) for `h ≤ 3`, `m ≤ 7`. Controls that fail as they should: even `r` in (A2)–(A4); the list without the switch of the mark; pairs of down-sets without (D2) (the chain breaks in every one of them); the zero option placed last; the two roots of (C3) at the wrong parity.
