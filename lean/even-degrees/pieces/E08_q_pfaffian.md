# Pfaffians and bordered Pfaffians

This file uses, unchanged:
- `q_col_one.md`: the polynomial `Dab q a b = Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}` (`ColOne.Dab`), for elements `a, b` of a commutative ring.
- `q_oddbox_shapes.md`, Part A: for odd `r`, `D(a, b) := Dab (r+1) a b` and `D^−(a, b) := Dab r a b`; (A2) `D^−(b, a) = −D^−(a, b)` (`OddShapes.A2_Dminus`); (A4) the expansions of `D` and `D^−` in powers of the first variable (`OddShapes.A4_D`, `OddShapes.A4_Dminus`); and `D(a, b) = b^{r−1} − a·D^−(a, b)` (`OddShapes.A1`, `OddShapes.A3_*` as needed).

It is the third piece of §8 of the paper (the odd box): §8.3, the Pfaffian of an alternating matrix and the bordered Pfaffians, properties (i)–(iii) and (F1)–(F5), (F7). Nothing here uses a field: `R` is an arbitrary commutative ring (the characteristic `2` is allowed; this is why «alternating» asks for a zero diagonal).

All indices are `0`-based: `Fin m = {0, 1, …, m−1}`.

## Part A. The Pfaffian

### Definitions

A matrix `A : Fin m × Fin m → R` is **alternating** if `A(i, i) = 0` and `A(j, i) = −A(i, j)` for all `i, j`.

For a matrix `A` on `Fin m` and two different indices `x, z`, `A^{x,z}` is the matrix on `Fin (m−2)` obtained by deleting the rows and the columns `x` and `z` and keeping the order of the other indices. (For one index `x`, `A^{x}` on `Fin (m−1)` is defined in the same way.) A minor of an alternating matrix is alternating.

The **Pfaffian** `pf(A) ∈ R` of a matrix `A` on `Fin m` is defined by recursion on `m`:

- `pf(A) = 1` for `m = 0`; `pf(A) = 0` for `m = 1`;
- for `m ≥ 2`: `pf(A) = Σ_{j=1}^{m−1} (−1)^{j+1}·A(0, j)·pf(A^{0,j})`.

(The definition makes sense for every matrix; all the statements below are for alternating matrices.)

### Theorem A

Let `A` be an alternating matrix on `Fin m` over a commutative ring `R`.

**(A0)** `pf(A) = 0` if `m` is odd. For `m = 2`: `pf(A) = A(0,1)`. For `m = 4`: `pf(A) = A(0,1)A(2,3) − A(0,2)A(1,3) + A(0,3)A(1,2)`.

**(A2) (simultaneous permutation; property (i) of the paper)** For every permutation `σ` of `Fin m`, the matrix `A^σ(i, j) := A(σ i, σ j)` is alternating and `pf(A^σ) = sgn(σ)·pf(A)`.

**(A3) (equal rows; property (ii))** If `x ≠ z` and `A(x, k) = A(z, k)` for every `k`, then `pf(A) = 0`. (Over any commutative ring, also with `2 = 0`.)

**(A4) (expansion along any index; property (iii))** For `m ≥ 2` and every index `x`:

`pf(A) = Σ_{z ≠ x} ε(x, z)·A(x, z)·pf(A^{x,z})`,   where `ε(x, z) = (−1)^{x+z+1}` if `x < z` and `ε(x, z) = (−1)^{x+z}` if `z < x`.

(For `x = 0` this is the definition.)

**(A5) (additive and homogeneous in the row-and-column of `x`)** Let `A, A', A''` be alternating matrices on `Fin m`, equal outside the row and the column of an index `x`, and `λ ∈ R`. If `A(x, k) = A'(x, k) + λ·A''(x, k)` for every `k`, then `pf(A) = pf(A') + λ·pf(A'')`.

**(A1) (the sum over perfect matchings; this is the definition printed in the paper)** A perfect matching of `Fin m` is an involution `π` of `Fin m` without fixed points; its number of crossings is `cr(π) := #{(x, y) : x < y < π(x) < π(y)}`. Then

`pf(A) = Σ_π (−1)^{cr(π)}·Π_{x : x < π(x)} A(x, π(x))`,

the sum over all perfect matchings of `Fin m`. (The paper writes the sign as the sign of the permutation that lists the pairs one after the other, each pair in increasing order; that sign is `(−1)^{cr(π)}`.) (A1) is not used by the other parts of this file nor by the later files; it is here because it is the paper's definition.

### Proofs

(A0): by the definition; for odd `m` by induction (`A^{0,j}` has `m − 2` indices).

(A4) and (A2), together, by induction on `m`. It is enough to prove (A2) for a transposition `(k, k+1)` of two neighbours.
- If `k ≥ 1`: expand both sides along the index `0` (the definition). For `j ∉ {k, k+1}` the entry `A(0, j)` and the sign are the same on both sides, and the minor of `A^σ` is the minor `A^{0,j}` with two neighbouring indices exchanged, so its Pfaffian changes sign by induction. The terms `j = k` and `j = k + 1` are exchanged: the entries are exchanged, the minors are equal, and the signs `(−1)^{k+1}`, `(−1)^{k+2}` are opposite.
- If `k = 0`: expand along `0` and then each minor along its first index (which is the index `1` of `A`): `pf(A) = A(0,1)·pf(A^{0,1}) + Σ_{j ≠ l, j, l ≥ 2} s(j, l)·A(0, j)·A(1, l)·pf(A^{0,1,j,l})`, where `s(j, l) = (−1)^{j+1}·(−1)^{l'+1}` and `l'` is the position of `l` in `A^{0,j}` (`l' = l − 1` if `l < j`, `l' = l − 2` if `l > j`). So `s(l, j) = −s(j, l)`. Exchanging the indices `0` and `1` replaces `A(0,1)` by `A(1,0) = −A(0,1)` and exchanges `A(0, j)A(1, l)` with `A(1, j)A(0, l)`, that is, the term `(j, l)` with the term `(l, j)`: every term changes sign.
Then (A4): move `x` to the first place by the cyclic permutation of `0, 1, …, x`, whose sign is `(−1)^x`, apply the definition and (A2). The index `z` is then at the place `z + 1` if `z < x` and at the place `z` if `z > x`; the minor is `A^{x,z}` in both cases.

(A3): by (A4) along `x`, and induction: in the term `z' ∉ {x, z}` the minor `A^{x,z'}`… has no longer the row `x`, so use instead the expansion along a third index `w ∉ {x, z}` when `m ≥ 3`: every minor `A^{w,z'}` with `z' ∉ {x, z}` still has two equal rows, and the two terms `z' = x` and `z' = z` have equal entries `A(w, x) = −A(x, w) = −A(z, w) = A(w, z)`, minors that differ by moving one index across the indices strictly between `x` and `z` (a cyclic permutation, use (A2)), and signs `ε(w, x)`, `ε(w, z)`: they cancel. For `m = 2`: `A(x, z) = A(z, z) = 0`. (Any other correct proof is fine; for instance by (A2) with the transposition `(x z)` when `2` is not a zero divisor, and in general by the universal case of the polynomial ring over `Z` in the entries.)

(A5): by (A4) along `x`: the minors `A^{x,z}` do not contain the row or the column of `x`.

(A1): by induction on `m` with the definition: a perfect matching `π` is the pair `{0, j}` together with a perfect matching `π'` of the other indices; the pair `{0, j}` crosses exactly the pairs of `π'` with one end among `1, …, j − 1`, and their number has the parity of `j − 1`.

## Part B. Bordered Pfaffians

### Definition

Let `n, s ≥ 0`, let `a` be an alternating matrix on `Fin n` and let `c = (c_0, …, c_{s−1})` be a list of `s` **border columns**, each a function `Fin n → R`. The bordered matrix `B(a; c)` is the matrix on `Fin (n + s)` (first the `n` «variables», then the `s` borders) with entries

`a(i, j)` for `i, j < n`;   `c_k(i)` at `(i, n + k)` and `−c_k(i)` at `(n + k, i)`, for `i < n`, `k < s`;   `0` at `(n + k, n + k')`.

It is alternating. `bpf(a; c) := pf(B(a; c))`.

For a variable `b < n`: `a^{(b)}` is `a` without the row and the column `b` (on `Fin (n−1)`), and `c^{(b)}` is the list of the columns `c_k` restricted to `Fin n ∖ {b}` (in order).

### Theorem B

**(B0)** `bpf(a; c) = 0` if `n + s` is odd, and if `s > n`.

**(B1) (signs; (F1) of the paper)** For a permutation `σ` of `Fin n`, with `a^σ(i, j) = a(σ i, σ j)` and `c^σ_k(i) = c_k(σ i)`: `bpf(a^σ; c^σ) = sgn(σ)·bpf(a; c)`. For a permutation `τ` of `Fin s`: `bpf(a; c_{τ 0}, …, c_{τ(s−1)}) = sgn(τ)·bpf(a; c)`.

**(B2) (the borders; (F2))** `bpf(a; c)` is additive and homogeneous in each border column `c_k` (the others fixed), and it is `0` if two border columns are equal. Expansion along the last border, for `s ≥ 1`:

`bpf(a; c_0, …, c_{s−1}) = Σ_{b < n} (−1)^{n+s+b}·c_{s−1}(b)·bpf(a^{(b)}; c_0^{(b)}, …, c_{s−2}^{(b)})`.

**(B3) (as many borders as variables; (F3))** If `n = s`: `bpf(a; c) = (−1)^{s(s−1)/2}·det(c_k(i))_{i, k < s}`. In particular it does not depend on `a`.

**(B4) (expansion along a variable; (F4))** For `n ≥ 1` and a variable `x < n`, let `a_x` be the column `b ↦ a(x, b)`. Then

`bpf(a; c) = (−1)^{x+n+s}·bpf(a^{(x)}; c_0^{(x)}, …, c_{s−1}^{(x)}, a_x^{(x)}) + Σ_{k < s} (−1)^{x+n+k+1}·c_k(x)·bpf(a^{(x)}; the columns c_j^{(x)} with j ≠ k)`.

(In the first term the variable `x` has become a last border.)

**(B5) (Laplace; (F7))** If `n = s + 2κ`:

`bpf(a; c) = (−1)^{s(s−1)/2}·Σ_{S ⊆ Fin n, |S| = s} sgn(S)·det(c_k(i))_{i ∈ S, k < s}·pf(a|_{Fin n ∖ S})`,

where the rows of the determinant are the elements of `S` in increasing order, `a|_{Fin n ∖ S}` is `a` restricted to the complement of `S` in increasing order, and `sgn(S) := (−1)^{Σ_{i ∈ S} i − s(s−1)/2}` is the sign of the shuffle that puts `S` before its complement.

### Proofs

(B0): (A0); if `s > n`, by (B2) expand along the borders one by one: after `n` steps there is no variable left and a border remains, and a bordered matrix with no variable and at least one border has Pfaffian `0` (it is the zero matrix on `s' ≥ 1` indices: by (A0) or by the definition).

(B1): (A2) for the permutation of `Fin (n + s)` that acts as `σ` on the variables and fixes the borders; then `B(a; c)^σ = B(a^σ; c^σ)`. The same with `τ` on the borders: `B(a; c)^τ = B(a; c∘τ)`.

(B2): additivity and homogeneity are (A5) for the index `n + k`. Equal borders: (A3). The expansion is (A4) along the last index `x = n + s − 1`: the terms `z = n + k` vanish (`A(x, z) = 0`); for `z = b < n`, `ε(x, b) = (−1)^{n+s−1+b}` and `A(x, b) = −c_{s−1}(b)`; the minor is `B(a^{(b)}; c_0^{(b)}, …, c_{s−2}^{(b)})`.

(B3): by induction on `s` with (B2): `bpf = Σ_b (−1)^{2s+b}·c_{s−1}(b)·(−1)^{(s−1)(s−2)/2}·det(minor without row b and last column)`, and the expansion of the determinant along its last column is `det = Σ_b (−1)^{b+s−1}·c_{s−1}(b)·det(minor)`; `(−1)^{(s−1)(s−2)/2}·(−1)^{s−1} = (−1)^{s(s−1)/2}`.

(B4): (A4) along `x`. The terms `z = n + k` give the sum (`ε(x, n + k) = (−1)^{x+n+k+1}`, the entry is `c_k(x)`, the minor is the bordered matrix without the variable `x` and the border `k`). The terms `z = b < n`, `b ≠ x`, are `ε(x, b)·a(x, b)·pf(B(a; c)^{x,b})`; by (B2), the expansion of `bpf(a^{(x)}; c^{(x)}, a_x^{(x)})` (which has `n − 1` variables and `s + 1` borders) along its last border is `Σ_{b'} (−1)^{n+s+b'}·a(x, b)·pf(B(a; c)^{x,b})`, where `b'` is the place of `b` in `Fin n ∖ {x}` (`b' = b` if `b < x`, `b' = b − 1` if `b > x`); in both cases `ε(x, b) = (−1)^{x+n+s}·(−1)^{n+s+b'}`.

(B5): by induction on `s` with (B2) (expand along the last border; the subsets `S` of the right side that contain `b` correspond to the subsets `S ∖ b` of the complement of `b`; expand each determinant along its last column). Or from (A1): a matching with a non-zero product is a bijection from a subset `S` to the borders together with a perfect matching of the complement.

## Part C. The Pfaffians of the odd box

Let `r` be odd, `A` a commutative ring, `y_0, …, y_{n−1} ∈ A`. By (A2) of `q_oddbox_shapes.md` and `D^−(a, a) = 0` (it is `a^{r−2}·Σ_{u=0}^{r−2} (−1)^u`, an even number of terms), the matrix `a_y(i, j) := D^−(y_i, y_j)` on `Fin n` is alternating. For a list `c` of border columns `Fin n → A`:

`Pf(y; c) := bpf(a_y; c)`,

and for a list of exponents `e = (e_0, …, e_{s−1})`: `Pf_e(y) := Pf(y; y^{e_0}, …, y^{e_{s−1}})`, where `y^e` is the column `i ↦ y_i^e`.

### Theorem C

Let `r` be odd, `x ∈ A`, `c` a list of `s` border columns.

**(C1)** `Pf(y; c, D^−(x, ·)) = −Σ_{u=0}^{r−2} (−1)^u·x^{r−2−u}·Pf(y; c, y^u)`, where `D^−(x, ·)` is the column `b ↦ D^−(x, y_b)`.

**(C2)** `Pf(y; c, D(x, ·)) = Σ_{u=0}^{r−1} (−1)^u·x^{r−1−u}·Pf(y; c, y^u)`.

**(C3)** `Pf(y; c, D(x, ·)) = Pf(y; c, y^{r−1}) − x·Pf(y; c, D^−(x, ·))`.

**(C4)** For a list of exponents `e` and an exponent `u`: `Pf(y; y^{e_0}, …, y^{e_{s−1}}, y^u) = 0` if `u` is one of the `e_k`. If `e_0 < ⋯ < e_{s−1}` and `u` is none of them, it is `(−1)^{#{k : e_k > u}}·Pf_{e'}(y)`, where `e'` is the increasing list of `{e_0, …, e_{s−1}, u}`.

**(C5)** If `n = s`: `Pf_{(0, 1, …, s−1)}(y) = (−1)^{s(s−1)/2}·Π_{i < j < s} (y_j − y_i)`.

**(C6)** For a permutation `σ` of `Fin n`: `Pf(y∘σ; c∘σ) = sgn(σ)·Pf(y; c)`; in particular `Pf_e(y∘σ) = sgn(σ)·Pf_e(y)`.

### Proofs

(C1), (C2): (B2) (additivity and homogeneity in the last border) and (A4) of `q_oddbox_shapes.md`: `D^−(x, b) = −Σ_{u=0}^{r−2} (−1)^u x^{r−2−u} b^u` and `D(x, b) = Σ_{u=0}^{r−1} (−1)^u x^{r−1−u} b^u`. (C3): (B2) and `D(x, b) = b^{r−1} − x·D^−(x, b)`. (C4): (B2) (equal borders) and (B1) (the cyclic permutation of the borders that moves the last one to its place has sign `(−1)^{#{k : e_k > u}}`). (C5): (B3) and the Vandermonde determinant `det(y_i^k)_{i,k<s} = Π_{i<j} (y_j − y_i)`. (C6): (B1).

## How this file is used later

The marked blocks of the patterns of the odd box (Definition 8.6 of the paper) have the product `Pf_{E_ℓ}(y)` with `E_0 = (r − 1)` and `E_ℓ = (0, 1, …, ℓ − 2)` for `ℓ ≥ 1`. (B5) links them with the exterior algebra (Lemma 8.7); (B4) with (C1)–(C5) gives the degree and the leading coefficient in a new variable (Proposition 8.10).
