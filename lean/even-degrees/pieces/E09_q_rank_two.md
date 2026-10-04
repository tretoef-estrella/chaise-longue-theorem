# The rank-two update of a bordered Pfaffian, and the closed forms of the odd box

This file uses, unchanged:
- `q_pfaffian.md` (namespace `Pfaffian`): alternating matrices (`IsAlt`), the Pfaffian `pf`, the bordered matrix `bmat a c` and `bpf a c := pf (bmat a c)`; (A3) `pf_eq_zero_of_rows`, (A4) `pf_expand`, (A5) `pf_add_row`; (B2) `bpf_add_border`, `bpf_expand_last`; (B5) `bpf_laplace`; and, in Part C, `ay`, `Pf`, `Pfe`.
- `q_col_one.md`: `Dab q a b = Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}` (`ColOne.Dab`). For odd `r`: `D(a, b) := Dab (r+1) a b` and `D^−(a, b) := Dab r a b`.

It is the fourth piece of §8 of the paper (the odd box). It contains what §8.5 of the paper obtains from an exterior algebra with divided powers (the key fact (e), Lemma 8.8 and Corollary 8.9), in the form of identities between bordered Pfaffians. No exterior algebra and no divided power is needed: everything follows from one general lemma, the **rank-two update** (R4) below.

All indices are `0`-based. `R` and `A` are arbitrary commutative rings (the characteristic `2` is allowed; nothing is ever divided). For a list `c = (c_0, …, c_{s−1})` of border columns and one more column `E`, `(c, E)` is the list with `E` appended as the last border (`Fin.snoc c E`); `(c, E, O)` appends `E` and then `O`.

## Part R. General lemmas

### Theorem R

Let `R` be a commutative ring.

**(R1) (elementary operation)** Let `A` be an alternating matrix on `Fin m`, `x ≠ w` two indices and `λ ∈ R`. Put

`A'(i, j) := A(i, j) + λ·( [i = w]·A(x, j) + [j = w]·A(i, x) )`

(«add `λ` times the row `x` to the row `w` and `λ` times the column `x` to the column `w`»). Then `A'` is alternating and `pf(A') = pf(A)`.

**(R2) (border shift)** Let `a` be an alternating matrix on `Fin n`, `c` a list of `s` border columns, `k < s` and `λ : Fin n → R`. Put

`a'(i, j) := a(i, j) + λ_i·c_k(j) − λ_j·c_k(i)`.

Then `a'` is alternating and `bpf(a'; c) = bpf(a; c)`.

**(R3) (homogeneity)** For every matrix `A` on `Fin (2κ)` and `t ∈ R`: `pf(t·A) = t^κ·pf(A)`. If `a` is alternating on `Fin n`, `c` is a list of `s` border columns and `n = s + 2κ`: `bpf(t·a; c) = t^κ·bpf(a; c)`.

**(R4) (rank-two update)** Let `a` be an alternating matrix on `Fin n`, `c` a list of `s` border columns, and `E, O : Fin n → R` two more columns. Put `M(i, j) := E_i·O_j − E_j·O_i` (an alternating matrix). Then

`bpf(a − M; c) = bpf(a; c) + bpf(a; c, E, O)`,

and, equivalently (replace `O` by `−O` and use (B2)),

`bpf(a + M; c) = bpf(a; c) − bpf(a; c, E, O)`.

There is no sign depending on `n` or `s`. (For `n + s` odd all three terms are `0`.)

**(R5) (top coefficient)** Let `R[ζ]` be the polynomial ring in one variable. Let `a` be an alternating matrix on `Fin n` over `R[ζ]` and `c` a list of `s` border columns over `R[ζ]`, with `n = s + 2κ`. Let `d ≥ 0` and `d_0, …, d_{s−1} ≥ 0` be such that every entry `a(i, j)` has degree at most `d` and every entry `c_k(i)` has degree at most `d_k`. Put `N := κ·d + Σ_k d_k`. Then `bpf(a; c)` has degree at most `N`, and

`[ζ^N] bpf(a; c) = bpf(a^{top}; c^{top})`,   where `a^{top}(i, j) := [ζ^d] a(i, j)` and `c^{top}_k(i) := [ζ^{d_k}] c_k(i)`

(`a^{top}` is an alternating matrix over `R`). In particular, for a matrix `A` on `Fin (2κ)` over `R[ζ]` with entries of degree at most `d`: `pf(A)` has degree at most `κd` and `[ζ^{κd}] pf(A) = pf([ζ^d] A)`.

### Proofs

(R1): `A'(w, w) = A(w, w) + λ(A(x, w) + A(w, x)) = 0`, and `A'(j, i) = −A'(i, j)` because `A` is alternating. Let `A''` be the matrix equal to `A` outside the row and the column of `w`, with `A''(w, k) := A(x, k)` and `A''(k, w) := A(k, x)` for `k ≠ w`, and `A''(w, w) := 0`. It is alternating, and `A, A', A''` are equal outside the row and the column of `w`. For every `k`: `A'(w, k) = A(w, k) + λ·A''(w, k)` (for `k = w` both sides are `0`). By (A5), `pf(A') = pf(A) + λ·pf(A'')`. The rows `w` and `x` of `A''` are equal: for `k ≠ w`, `A''(w, k) = A(x, k) = A''(x, k)`; for `k = w`, `A''(w, w) = 0` and `A''(x, w) = A(x, x) = 0`. By (A3), `pf(A'') = 0`.

(R2): for one variable `w` and `μ ∈ R`, apply (R1) to `B(a; c)` with the indices `x := n + k` (the border `k`) and `w` (the variable), and `λ := −μ`. The row of the border `k` is `B(n+k, j) = −c_k(j)` on the variables and `0` on the borders, and its column is `B(i, n+k) = c_k(i)`. So the new matrix is `B(a^{(w)}; c)` with `a^{(w)}(i, j) = a(i, j) + μ·([i = w]·c_k(j) − [j = w]·c_k(i))`: the border columns do not change (the entry at `(w, n+k')` changes by `−μ·B(n+k, n+k') = 0`). Doing this for every variable `w` with `μ = λ_w`, one after the other (the row of the border `k` never changes), gives `a'`.

(R3): the first statement by induction on `κ` with the recursion of the definition (each term has one entry of `t·A` and the Pfaffian of a minor of `t·A` of size `2κ − 2`). The second from (B5): `pf` of the restriction of `t·a` to the complement of `S`, which has `2κ` elements; or by induction on `s` with (B2).

(R4): let `N := n + s + 2`, and for `θ ∈ R` let `X_θ` be the matrix on `Fin N` equal to `B(a; c, E, O)` except for `X_θ(N−2, N−1) := θ` and `X_θ(N−1, N−2) := −θ` (the last two indices are the borders `E` and `O`). It is alternating.

*Step 1: `pf(X_θ) = bpf(a; c, E, O) + θ·bpf(a; c)`.* Expand along `x = N−1` by (A4). For `z ≠ N−2` the entry `X_θ(N−1, z)` and the minor `X_θ^{N−1,z}` do not contain `θ` (the two entries with `θ` are in the row and the column of `N−1`). The term `z = N−2` is `ε(N−1, N−2)·X_θ(N−1, N−2)·pf(X_θ^{N−1,N−2}) = (−1)^{2N−3}·(−θ)·pf(B(a; c)) = θ·bpf(a; c)`. So `pf(X_θ) − pf(X_0) = θ·bpf(a; c)`, and `pf(X_0) = bpf(a; c, E, O)`.

*Step 2: `pf(X_1) = bpf(a − M; c)`.* In `X_1` the row of `N−1` is `−O_j` on the variables, `0` on the borders of `c`, `−1` at `N−2` and `0` at `N−1`. For each variable `w`, apply (R1) with `x := N−1` and `λ := E_w`. The entry at `(w, N−2)` becomes `E_w + E_w·X(N−1, N−2) = 0`; the entries at `(w, j)`, `j` a variable, change by `−E_w·O_j`, and those at `(i, w)` by `+E_w·O_i`; the entries at `(w, n+k)` and at `(w, N−1)` do not change; the row of `N−1` does not change. After all the variables, the block of the variables is `a − M`, the column of the border `E` is `0`, and the rest is as before. Now the row of `N−2` is `0` except for the entry `1` at `N−1`. For each variable `w`, apply (R1) with `x := N−2` and `λ := −O_w`: the entry at `(w, N−1)` becomes `O_w − O_w = 0` and nothing else changes. The final matrix `Y` has the block `B(a − M; c)` on the first `n + s` indices, `Y(N−2, N−1) = 1`, `Y(N−1, N−2) = −1`, and `0` elsewhere in the last two rows and columns. By (R1), `pf(Y) = pf(X_1)`. Expanding `pf(Y)` along `N−1` by (A4), only `z = N−2` gives a term: `(−1)^{2N−3}·(−1)·pf(B(a − M; c)) = bpf(a − M; c)`.

Steps 1 and 2 with `θ = 1` give the first formula. For the second, apply the first to the columns `E` and `−O`: `M` becomes `−M`, and `bpf(a; c, E, −O) = −bpf(a; c, E, O)` by (B2).

(R5): first the statement for `pf`, by induction on `κ` with the recursion: `A(0, j)` has degree at most `d` and `pf(A^{0,j})` at most `(κ−1)d`, and for two polynomials `p, q` of degrees at most `α, β` the coefficient of `ζ^{α+β}` in `p·q` is `([ζ^α] p)·([ζ^β] q)`. Then `bpf` by induction on `s` with the expansion along the last border (B2): `bpf(a; c_0, …, c_{s−1}) = Σ_b (−1)^{n+s+b}·c_{s−1}(b)·bpf(a^{(b)}; c_0^{(b)}, …, c_{s−2}^{(b)})`, where `a^{(b)}` has `n − 1 = (s − 1) + 2κ` variables, the same `κ`; the degrees add: `d_{s−1} + (κd + Σ_{k<s−1} d_k) = N`. (For `s = 0` it is the statement for `pf`. For `s ≥ 1` and `n = 0` both sides are `0`.)

## Part S. The odd box

Let `h ≥ 1`, `r := 2h + 1`, `A` a commutative ring, and `ζ` the variable of `A[ζ]`.

### Definitions

For `s ≥ 0` and `a, b ∈ A`:

`ω_s(a, b) := Σ (−1)^u·a^u·b^{s−u}`,   the sum over the `u` with `0 ≤ u ≤ r − 1` and `0 ≤ s − u ≤ r − 1`.

For `y : Fin n → A` and `0 ≤ σ ≤ 2h − 1`, `W_σ(y)` is the matrix on `Fin n` over `A` with entries `ω_{2σ+1}(y_i, y_j)`. Over `A[ζ]`:

`L(y) := Σ_{σ=0}^{h−1} ζ^σ·W_σ(y)`,   `H(y) := Σ_{τ=0}^{h−1} ζ^τ·W_{h+τ}(y)`,

`Ev(y)_i := Σ_{α=0}^{h} ζ^α·y_i^{2α}`,   `Od(y)_i := Σ_{β=0}^{h−1} ζ^β·y_i^{2β+1}`

(two matrices on `Fin n` and two columns `Fin n → A[ζ]`). A column or a list of columns over `A` is also read over `A[ζ]` (constants).

### Theorem S

**(S0)** For odd `s`: `ω_s(b, a) = −ω_s(a, b)` and `ω_s(a, a) = 0`. So `W_σ(y)`, `L(y)` and `H(y)` are alternating.

**(S1)** `ω_{r−2}(a, b) = Dab r a b = D^−(a, b)`. So `W_{h−1}(y)` is the matrix `a_y` of `q_pfaffian.md`, Part C (`Pfaffian.ay r y`).

**(S2) (the key fact)** In `A[ζ]`: `Σ_{σ=0}^{2h−1} ζ^σ·ω_{2σ+1}(a, b) = Ev(a)·Od(b) − Ev(b)·Od(a)`, where `Ev(a) = Σ_{α=0}^{h} ζ^α a^{2α}` and `Od(b) = Σ_{β=0}^{h−1} ζ^β b^{2β+1}`. So, entry by entry,

`L(y) + ζ^h·H(y) = Ev(y)·Od(y)ᵀ − Od(y)·Ev(y)ᵀ`.

**(S3)** Let `i` be odd, `1 ≤ i ≤ r − 2`, and suppose `a^r = 0` and `b^r = 0`. Then `ω_{r−1+i}(a, b) = b^i·Dab (r+1) a b = b^i·D(a, b)`. (So, when `y_i^r = 0` for every `i`, each coefficient of each entry `H(y)(i, j)` is a multiple of `D(y_i, y_j)`: `2(h + τ) + 1 = r − 1 + (2τ + 1)`.)

**(S4)** For every `y : Fin n → A` and every list `c` of `s` border columns over `A[ζ]`:

- (i) `bpf(L(y); c) = bpf(−ζ^h·H(y); c) − bpf(−ζ^h·H(y); c, Ev(y), Od(y))`;
- (ii) `bpf(L(y); c, Ev(y)) = bpf(−ζ^h·H(y); c, Ev(y))`.

**(S5)** For every `y : Fin n → A` and every list `c` of `s` border columns over `A`, with `Pf(y; c) = bpf(a_y; c)` as in `q_pfaffian.md`, Part C (`Pfaffian.Pf r y c`):

- (a) if `n = s + 2(t + 1)`:   `Pf(y; c) = (−1)^{t+1}·[ζ^{h−1−t}] bpf(H(y); c, Ev(y), Od(y))` if `t ≤ h − 1`, and `Pf(y; c) = 0` if `t ≥ h`;
- (b) if `n = s + 1 + 2t`:   `Pf(y; c, y^{r−1}) = (−1)^t·[ζ^{h−t}] bpf(H(y); c, Ev(y))` if `t ≤ h`, and `Pf(y; c, y^{r−1}) = 0` if `t > h`,

where `y^{r−1}` is the column `i ↦ y_i^{r−1}`, appended as the last border.

### Proofs

(S0): the set of the `u` of the sum is stable under `u ↦ s − u`, which exchanges the terms of `ω_s(a, b)` and of `ω_s(b, a)` and changes the sign `(−1)^u` because `s` is odd. For `a = b` the terms `u` and `s − u` cancel (`u ≠ s − u`, as `s` is odd): pair `u < s − u`; no division by `2`.

(S1): for `s = r − 2` the conditions are `0 ≤ u ≤ r − 2`.

(S2): `Ev(a)·Od(b) = Σ_{α ≤ h, β ≤ h−1} ζ^{α+β} a^{2α} b^{2β+1}`. In `ω_{2σ+1}(a, b)` the terms with `u` even, `u = 2α`, have `s − u = 2β + 1` with `α + β = σ`, `α ≤ h`, `β ≤ h − 1`, and sign `+`; the terms with `u` odd, `u = 2β + 1`, have `s − u = 2α`, and sign `−`: they are the terms of `Ev(b)·Od(a)`. Every pair `(α, β)` with `0 ≤ α ≤ h`, `0 ≤ β ≤ h − 1` occurs once, with `σ = α + β ∈ {0, …, 2h − 1}`.

(S3): `b^i·D(a, b) = Σ_{u=0}^{r−1} (−1)^u a^u b^{r−1−u+i}`. The terms with `u < i` have the exponent of `b` at least `r` and vanish. The others, `i ≤ u ≤ r − 1`, have `0 ≤ r − 1 + i − u ≤ r − 1`: they are the terms of `ω_{r−1+i}`, whose conditions are `u ≤ r − 1` and `u ≥ i`.

(S4)(i): (R4), second form, with `a := −ζ^h·H(y)`, `E := Ev(y)`, `O := Od(y)`: by (S2), `a + M = L(y)`.

(S4)(ii): (R2) for the list `(c, Ev(y))`, its last border, `a := −ζ^h·H(y)` and `λ := −Od(y)`: `a'(i, j) = a(i, j) − Od_i·Ev_j + Od_j·Ev_i = a(i, j) + M(i, j) = L(y)(i, j)` by (S2).

(S5)(a): by (S4)(i) and (R3) (`n = s + 2(t+1) = (s + 2) + 2t`),

`bpf(L(y); c) = (−ζ^h)^{t+1}·bpf(H(y); c) − (−ζ^h)^t·bpf(H(y); c, Ev(y), Od(y))`.

Take the coefficient of `ζ^{(h−1)(t+1)}`. On the left, by (R5) with `d = h − 1`, `d_k = 0` and `κ = t + 1`, it is `bpf(W_{h−1}(y); c) = Pf(y; c)` by (S1). On the right, the first term is a multiple of `ζ^{h(t+1)}` and `h(t+1) > (h−1)(t+1)`: its coefficient is `0`. The second term is `−(−1)^t·ζ^{ht}·Q` with `Q := bpf(H(y); c, Ev(y), Od(y))`: its coefficient is `(−1)^{t+1}·[ζ^{(h−1)(t+1) − ht}] Q = (−1)^{t+1}·[ζ^{h−1−t}] Q` if `t ≤ h − 1`, and `0` if `ht > (h−1)(t+1)`, that is, if `t ≥ h`.

(S5)(b): by (S4)(ii) and (R3) (`n = (s + 1) + 2t`), `bpf(L(y); c, Ev(y)) = (−ζ^h)^t·bpf(H(y); c, Ev(y))`. Take the coefficient of `ζ^{(h−1)t + h}`. On the left, by (R5) with `d = h − 1`, `d_k = 0` for the columns of `c` and `d = h` for the last border (`[ζ^h] Ev(y)_i = y_i^{2h} = y_i^{r−1}`), it is `bpf(W_{h−1}(y); c, y^{r−1}) = Pf(y; c, y^{r−1})`. On the right it is `(−1)^t·[ζ^{(h−1)t + h − ht}] Q' = (−1)^t·[ζ^{h−t}] Q'` with `Q' := bpf(H(y); c, Ev(y))` if `t ≤ h`, and `0` if `t > h`.

## How this file is used later

Lemma 8.7 of the paper: in `Z[y]/(y_i^r)`, the product `Pf_{E_ℓ}(B_0)` of a marked block lies in the ideal generated by the `Δ(S)·D_Q`. With `E_ℓ = (0, 1, …, ℓ−2)` for `ℓ ≥ 1` it is (S5)(a) with `c = (y^0, …, y^{ℓ−2})`, and with `E_0 = (r−1)` it is (S5)(b) with no column `c`. By (B5), `bpf(H(y); c, Ev(y), Od(y))` is a sum over the subsets `S` with `|S| = s + 2` of `± det(c, Ev, Od)_S·pf(H(y)|_{S^c})`; each coefficient of the determinant is a combination of determinants `det(y_i^{e_k})_{i ∈ S}`, which are multiples of the Vandermonde determinant `Δ(S)`, and by (S3) each coefficient of `pf(H(y)|_{S^c})` is a combination of the products `D_Q`, `Q` a perfect matching of `S^c`. The same for (b).

In the language of §8.5 of the paper: (R4) is `γ_κ(φ + E ∧ O) = γ_κ(φ) + γ_{κ−1}(φ) ∧ E ∧ O`; (S2) is `Ω(ζ) = Ev(ζ) ∧ Od(ζ)`; (S4)(i) is the closed form `γ_κ(Ω_{lo}) = (−ζ^h)^{κ−1}·Ω ∧ γ_{κ−1}(Ω_{hi}) + (−ζ^h)^κ·γ_κ(Ω_{hi})` of Lemma 8.8, up to the sign convention of the two borders; (S5)(a), (b) are Corollary 8.9 (a), (b).
