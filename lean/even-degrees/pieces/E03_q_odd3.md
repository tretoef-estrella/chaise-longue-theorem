# The odd box `r = 3` (Theorem 8.15 of the paper: Theorem O, `≥`, at `r = 3`, without Pfaffians)

This file uses, unchanged:
- `q_peeling_lemma.md`, with its parameter `q := 4`: the ring `C_m := F[y_1, …, y_m]/(y_1^3, …, y_m^3)` over a field `F` (the box is `q − 1 = 3`); for an ideal `V ⊆ C_m` (`m ≥ 1`) and `0 ≤ j ≤ 2`, the slice `W_j(V) := {[y_1^j] f : f ∈ V, deg_{y_1} f ≤ j} ⊆ C_{m−1}` (`C_{m−1}` in the variables `y_2, …, y_m`); and the Lemma (peeling): (i) `W_j(V)` is an ideal of `C_{m−1}`; (ii) `W_0(V) ⊆ W_1(V) ⊆ W_2(V)`; (iii) `dim_F V = dim W_0(V) + dim W_1(V) + dim W_2(V)`; (iv) for a set `T` with `|T| = 3` and `Z ⊆ T^m`, `|Z| = |Z_{>0}| + |Z_{>1}| + |Z_{>2}|`, where `Z_{>i}` is the set of the tails `M' ∈ T^{m−1}` with more than `i` completions `(t, M') ∈ Z`.
- `q_P3_identities.md`, with `q := 4`: the divided difference `D(y_a, y_b) = Σ_{i=0}^{2} (−1)^i y_a^i y_b^{2−i} = y_a^2 − y_a y_b + y_b^2`, and the Vandermonde `Δ(y_a, y_b, y_c) = (y_b − y_a)(y_c − y_a)(y_c − y_b)` for `a < b < c`.
- `q_theorem_B_lower.md`, with `q := 4`: the matchings `J ∈ 𝒥` of `{0, 1, …, 2k+1}`, `D_J := Π D(y_a, y_b)` over the `k` pairs `{a < b}` of `J` that avoid `0`, and the ideal `(D_J : J ∈ 𝒥) ⊆ C_{2k+1}`. (That file proves a count for odd `q`; here only its definitions are used, at the even parameter `q = 4`, i.e. at the odd box `3`.)
- `q_even_count.md`: the number `Q^e_k(m)`, pointed point sets, closed tuples, and its part (iii).

## Setting

`F` is any field. `T := {−1, 0, 1}`. In `C_m`, write `D(a, b) := D(y_a, y_b) = y_a^2 − y_a y_b + y_b^2`; it is symmetric in `a, b`. For a set `P` of pairwise disjoint pairs of indices of `{1, …, m}` put `D_P := Π_{{a,b} ∈ P} D(a, b)` (`D_∅ = 1`). `P` is a *perfect matching* of a set `S` of indices if its pairs are contained in `S` and cover `S`.

**The point sets.** For `m ≥ 0` and `J ≥ 0`,

`Z_J^{(m)} := {M ∈ T^m : |M_1 + ⋯ + M_m| ≤ J}`   (the sum is taken in `Z`).

**The ideals.** For `m ≥ 0` and `J ≥ 0` the ideal `I(m, J) ⊆ C_m` is:
- if `J ≥ m`: `I(m, J) := C_m` (the unit ideal);
- if `J < m` and `J ≡ m (mod 2)`: `I(m, J) := (D_P : |P| = (m − J)/2)`;
- if `1 ≤ J < m` and `J ≢ m (mod 2)`: `I(m, J) := ( (y_b − y_a)·D_P : |P| = (m − 1 − J)/2, a ≠ b indices outside the pairs of P;  D_{P^+} : |P^+| = (m + 1 − J)/2 )`;
- if `J = 0` and `m` is odd: `I(m, 0) := ( y_c^2·D_P : c an index, P a perfect matching of the other indices;  Δ(y_a, y_b, y_c)·D_{P'} : a < b < c indices, P' a perfect matching of the other indices )`.

(For `J = m` the second line would give `(D_∅) = C_m`, and for `J = m + 1` the third line would give `(D_∅) = C_m`; so the first line agrees with the formulas there.)

## Theorem

**(i) (the count)** For `m ≥ 1`: `|Z_J^{(m)}| = |Z_{J+1}^{(m−1)}| + |Z_J^{(m−1)}| + |Z_{J−1}^{(m−1)}|` for every `J ≥ 1`, and `|Z_0^{(m)}| = |Z_1^{(m−1)}|`.

**(ii) (the slices)** Let `m ≥ 1` and `0 ≤ J ≤ m − 1`, and let `W_j := W_j(I(m, J)) ⊆ C_{m−1}`. Identify `C_{m−1}` (in the variables `y_2, …, y_m`) with the ring of the ideals `I(m − 1, ·)`. Then:
- if `J ≥ 1`: `W_2 ⊇ I(m − 1, J + 1)`, `W_1 ⊇ I(m − 1, J)` and `W_0 ⊇ I(m − 1, J − 1)`;
- if `J = 0`: `W_2 ⊇ I(m − 1, 1)`.

**(iii) (the dimension)** For every field `F`, every `m ≥ 0` and every `J ≥ 0`: `dim_F I(m, J) ≥ |Z_J^{(m)}|`.

**(iv) (the ideal of the matchings)** For `k ≥ 0`: `I(2k + 1, 1) = (D_J : J ∈ 𝒥)·C_{2k+1}`.

**(v) (the number)** For `k ≥ 0`: `|Z_1^{(2k+1)}| = Q^e_k(4)`.

**(vi) (Theorem O, `≥`, at `r = 3`)** For every field `F` and every `k ≥ 0`:

`dim_F (D_J : J ∈ 𝒥)·C_{2k+1} ≥ Q^e_k(4)`.

## Proof

(i) Write `M = (t, M')` with `t ∈ T` and `M' ∈ T^{m−1}`, and let `s'` be the sum of `M'`. For `J ≥ 1` the number of `t ∈ {−1, 0, 1}` with `|t + s'| ≤ J` is `3` if `|s'| ≤ J − 1`, `2` if `|s'| = J`, `1` if `|s'| = J + 1`, and `0` otherwise. So the number of completions is `[|s'| ≤ J + 1] + [|s'| ≤ J] + [|s'| ≤ J − 1]`, and summing over `M'` gives the first formula. For `J = 0`, `t = −s'` is possible exactly when `|s'| ≤ 1`, and then it is the only completion.

(ii) Below, the sets of pairs lie in `{2, …, m}`, «free» means an index of `{2, …, m}` outside them, and `D(1, b) = y_1^2 − y_1 y_b + y_b^2`. An element of `I(m, J)` of degree `≤ j` in `y_1` puts its coefficient of `y_1^j` in `W_j`; an element of `I(m, J)` that does not contain `y_1` lies in `W_0 ⊆ W_1 ⊆ W_2`. Since `W_j` is an ideal, it is enough to find the generators of the smaller ideal in `W_j`. If the smaller ideal is the unit ideal, it is enough to find `1` in `W_j`.

*Case I: `J ≡ m (mod 2)`, `1 ≤ J ≤ m − 2`.* Put `p := (m − J)/2 ≥ 1`; `I(m, J) = (D_P : |P| = p)`.
- `W_2 ⊇ I(m − 1, J + 1)`. Here `J + 1 ≡ m − 1` and `J + 1 ≤ m − 1`, so `I(m − 1, J + 1) = (D_{P'} : |P'| = p − 1)` (the unit ideal if `p = 1`). Given `P'`, there are `(m − 1) − 2(p − 1) = J + 1 ≥ 2` free indices; for a free `b`, `D(1, b)·D_{P'} = D_{P' ∪ {{1,b}}} ∈ I(m, J)` has degree `2` in `y_1`, with `y_1^2`-coefficient `D_{P'}`.
- `W_1 ⊇ I(m − 1, J)`. Here `J ≢ m − 1` and `1 ≤ J < m − 1`, so `I(m − 1, J) = ((y_b − y_a)D_{P'} : |P'| = p − 1;  D_{P''} : |P''| = p)`. For `P'` and free `a ≠ b`: `(D(1, b) − D(1, a))·D_{P'} = (−y_1(y_b − y_a) + y_b^2 − y_a^2)·D_{P'} ∈ I(m, J)` has degree `≤ 1` in `y_1`, with `y_1`-coefficient `−(y_b − y_a)D_{P'}`. And `D_{P''} ∈ I(m, J)` does not contain `y_1`.
- `W_0 ⊇ I(m − 1, J − 1)`. Here `J − 1 ≡ m − 1`, so `I(m − 1, J − 1) = (D_{P''} : |P''| = p)`; these are generators of `I(m, J)` that do not contain `y_1`.

*Case II: `J ≢ m (mod 2)`, `1 ≤ J ≤ m − 1`.* Put `p := (m − 1 − J)/2 ≥ 0`; `I(m, J) = ((y_b − y_a)D_P : |P| = p;  D_{P^+} : |P^+| = p + 1)`.
- `W_2 ⊇ I(m − 1, J + 1)`. If `p = 0` (i.e. `J = m − 1`) this is the unit ideal, `m ≥ 2`, and `D(1, 2) ∈ I(m, J)` has `y_1^2`-coefficient `1`. If `p ≥ 1`: `J + 1 ≢ m − 1` and `1 ≤ J + 1 < m − 1`, so `I(m − 1, J + 1) = ((y_b − y_a)D_{P'} : |P'| = p − 1;  D_P : |P| = p)`. For `(y_b − y_a)D_{P'}` there are `(m − 1) − 2(p − 1) − 2 = J ≥ 1` free indices other than `a, b`; for such a `c`, `D(1, c)·(y_b − y_a)·D_{P'} = (y_b − y_a)·D_{P' ∪ {{1,c}}} ∈ I(m, J)` has `y_1^2`-coefficient `(y_b − y_a)D_{P'}`. For `D_P` there are `(m − 1) − 2p = J ≥ 1` free indices; for a free `b`, `D(1, b)·D_P = D_{P ∪ {{1,b}}} ∈ I(m, J)` has `y_1^2`-coefficient `D_P`.
- `W_1 ⊇ I(m − 1, J)`. Here `J ≡ m − 1` and `J ≤ m − 1`, so `I(m − 1, J) = (D_P : |P| = p)`. There are `(m − 1) − 2p = J ≥ 1` free indices; for a free `b`, `(y_b − y_1)·D_P ∈ I(m, J)` has degree `1` in `y_1`, with `y_1`-coefficient `−D_P`.
- `W_0 ⊇ I(m − 1, J − 1)`. If `J ≥ 2`: `J − 1 ≢ m − 1` and `1 ≤ J − 1 < m − 1`, so `I(m − 1, J − 1) = ((y_b − y_a)D_P : |P| = p;  D_{P^+} : |P^+| = p + 1)`, and these are generators of `I(m, J)` that do not contain `y_1`. If `J = 1`: `m` is even and `m − 1` is odd, so `I(m − 1, 0) = (y_c^2·D_P;  Δ(y_a, y_b, y_c)·D_{P'})` with `P` a perfect matching of `{2, …, m} ∖ {c}` (`|P| = p`) and `P'` a perfect matching of `{2, …, m} ∖ {a, b, c}` (`|P'| = p − 1`). Two identities in `Z[y_1, y_a, y_b, y_c]`:

  `y_c^2 = y_1·(y_c − y_1) + D(1, c)`,

  `Δ(y_a, y_b, y_c) = D(1, a)·(y_c − y_b) − D(1, b)·(y_c − y_a) + D(1, c)·(y_b − y_a)`

  (in the second, the coefficients of `y_1^2` and of `y_1` cancel, and the rest is `y_a^2(y_c − y_b) − y_b^2(y_c − y_a) + y_c^2(y_b − y_a) = Δ(y_a, y_b, y_c)`). Hence `y_c^2·D_P = y_1·(y_c − y_1)D_P + D_{P ∪ {{1,c}}}` and `Δ(y_a, y_b, y_c)·D_{P'} = (y_c − y_b)D_{P' ∪ {{1,a}}} − (y_c − y_a)D_{P' ∪ {{1,b}}} + (y_b − y_a)D_{P' ∪ {{1,c}}}` lie in `I(m, 1)`; they do not contain `y_1`.

*Case III: `J = 0`, `m ≥ 1`.* We need `W_2 ⊇ I(m − 1, 1)`.
- `m` even: `I(m, 0) = (D_{P^+} : P^+ a perfect matching of {1, …, m})`, and `I(m − 1, 1) = (D_{P'} : |P'| = (m − 2)/2)` (as `1 ≡ m − 1`; the unit ideal if `m = 2`). Given `P'` there is exactly one free index `b`, and `D(1, b)·D_{P'} ∈ I(m, 0)` has `y_1^2`-coefficient `D_{P'}`.
- `m` odd, `m = 1`: `I(1, 0) = (y_1^2)` and `I(0, 1)` is the unit ideal; `y_1^2` has `y_1^2`-coefficient `1`.
- `m` odd, `m ≥ 3`: `I(m − 1, 1) = ((y_b − y_a)D_{P'} : P' a perfect matching of {2, …, m} ∖ {a, b};  D_{P^+} : P^+ a perfect matching of {2, …, m})`. `y_1^2·D_{P^+} ∈ I(m, 0)` (the first kind of generator, with `c = 1`) has `y_1^2`-coefficient `D_{P^+}`. And `Δ(y_1, y_a, y_b)·D_{P'} = (y_a − y_1)(y_b − y_1)(y_b − y_a)·D_{P'} ∈ I(m, 0)` (the second kind, with the indices `1 < a < b`) has `y_1^2`-coefficient `(y_b − y_a)D_{P'}`.

Cases I and II cover every `1 ≤ J ≤ m − 1` (if `J ≡ m` then `J ≤ m − 2`).

(iii) Induction on `m`. For `J ≥ m` (in particular for `m = 0`) the ideal is `C_m` and `Z_J^{(m)} = T^m`: both numbers are `3^m`. Let `m ≥ 1` and `0 ≤ J ≤ m − 1`. If `J ≥ 1`, by peeling (iii), by (ii), by induction and by (i):

`dim I(m, J) = dim W_0 + dim W_1 + dim W_2 ≥ dim I(m−1, J−1) + dim I(m−1, J) + dim I(m−1, J+1) ≥ |Z_{J−1}^{(m−1)}| + |Z_J^{(m−1)}| + |Z_{J+1}^{(m−1)}| = |Z_J^{(m)}|`.

If `J = 0`: `dim I(m, 0) ≥ dim W_2 ≥ dim I(m − 1, 1) ≥ |Z_1^{(m−1)}| = |Z_0^{(m)}|`.

(iv) For `k = 0` both ideals are `C_1` (`D_J = 1` for the only matching). For `k ≥ 1`, `1 ≡ 2k + 1` and `1 < 2k + 1`, so `I(2k + 1, 1) = (D_P : |P| = k)`. A set `P` of `k` pairwise disjoint pairs of `{1, …, 2k+1}` leaves exactly one index `b` free; `J := P ∪ {{0, b}}` is a matching of `{0, …, 2k+1}` with `D_J = D_P`. Conversely the pairs of a matching `J` that avoid `0` form such a `P`. So the two ideals have the same generators.

(v) `T = {−1, 0, 1}` with `u ↦ −u` is a pointed point set with `o = 0` and `|T| = 3 = 2·1 + 1`. A tuple `M ∈ T^{2k+2}` is closed if and only if `cnt_M(1) = cnt_M(−1)` and `cnt_M(0)` is even; since `cnt_M(0) = 2k + 2 − cnt_M(1) − cnt_M(−1)`, the second condition follows from the first, and the first says that the sum of `M` is `0`. By part (iii) of `q_even_count.md` (with `h = 1`), the number of `M ∈ T^{2k+2}` of sum `0` is `Q^e_k(4)`. Deleting the last entry is a bijection from these tuples onto `Z_1^{(2k+1)}`: the sum of the first `2k + 1` entries is minus the last entry, of absolute value `≤ 1`; conversely `M' ∈ Z_1^{(2k+1)}` is completed in exactly one way, by minus its sum.

(vi) By (iv), (iii) with `(m, J) = (2k + 1, 1)`, and (v). ∎

## Checks

See `chkE3.log` (195 checks, 0 failures). (A) The recursion of (i): 80 identities, `m ≤ 8`, `J ≤ 9`. (B) Over `F_2`, `F_3` (`m ≤ 6`) and `F_5`, `F_7` (`m ≤ 5`): for each of the 94 ideals `I(m, J)`, `0 ≤ J ≤ m`, the dimension equals `|Z_J^{(m)}|`, the three slices `W_0, W_1, W_2` were computed, their dimensions add up to `dim I(m, J)`, and the inclusions of (ii) hold (172 inclusions). For instance `dim I(5, 1) = 141 = 19 + 51 + 71` and `dim I(6, 1) = 393 = 51 + 141 + 201`. (C) The identities of the proof, over `F_10007`. (D) For `k = 0, 1, 2` and `p = 2, 3, 5`: the ideal generated by the `D_J` is `I(2k + 1, 1)`, of dimension `3, 19, 141 = |Z_1^{(2k+1)}| = Q^e_k(4)`. (E) Controls: `W_0 ⊇ I(m − 1, J)` (one step too far) is false in 30 cases of 30; `I(m, 0)` for odd `m` without its Vandermonde generators has dimension `6 < 7` (`m = 3`) and `45 < 51` (`m = 5`); with `a^2 + ab + b^2` in place of `D` the dimension of `I(5, 1)` changes over `F_3` (`138`), `F_5` and `F_7` (`151`), and does not change over `F_2` (where the two polynomials coincide) nor at `m = 3` over `F_5`, `F_7`.
