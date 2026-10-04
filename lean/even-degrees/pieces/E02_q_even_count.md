# The count for an even degree, and the upper bound (Lemma 9.1 and Theorem 0(b) of the paper for even `m`)

This file uses, unchanged:
- `q_col_upper.md`: for a field `K`, `m ≥ 1`, `k ≥ 0`, `d = 2k + 1`: the ring `K[G] := K[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)`; `V = {0, …, 2k+1}` and the matchings `J` of `V` (fixed-point-free involutions); `φ(u) := u^{m−1} + ⋯ + u + 1`; the elements `ψ_J ∈ K[G]`; the ideal `I_K := (ψ_J : J a matching of V)`; sets `μ_m ⊆ K` of `m` distinct `m`-th roots of unity (`X^m − 1 = Π_{ξ ∈ μ_m}(X − ξ)`); the evaluations `ev_a`, `a ∈ μ_m^d`; the set `Γ := {a ∈ μ_m^d : ev_a(ψ_J) ≠ 0 for some matching J}`; and its Theorem, parts (0), (i), (ii), which hold for every `m ≥ 1`: the monomial basis, the integer matrix `A = A(m, k)` with `dim_K I_K = rank_K(A)` for every field `K`, and `dim_K I_K = |Γ|` when `K` contains `μ_m`. Also the criterion in the proof of its part (iii), which uses only `m ≠ 0` in `K`: for `a ∈ μ_m^d` and a matching `J`, `ev_a(ψ_J) ≠ 0` if and only if `a_{J(x)} ≠ 1` for every pair `x < J(x)` of `J` and `a_x a_{J(x)} = 1` for every pair with `0 < x < J(x)`.
- `q_P1_fibres.md`, `q_theorem_B_lower.md`: point sets `T` with a fixed-point-free involution `u ↦ −u` and `|T| = 2h` (`h ≥ 1`); the number of entries `cnt_M(u)` of a tuple `M` equal to `u`; closed tuples (`cnt_M(u) = cnt_M(−u)` for every `u`); the number `Q_j(q) := Σ (2j+2)!/Π_{u=1}^{h}(b_u!)^2`, the sum over `(b_1, …, b_h) ∈ N^h` with `b_1 + ⋯ + b_h = j + 1`, `h = (q − 1)/2`; and Theorem (ii) of `q_theorem_B_lower.md`: for a point set `T` with `|T| = 2h`, `h = (q − 1)/2 ≥ 1`, the number of closed tuples in `T^{2j+2}` is `Q_j(q)`.
- `q_every_field.md`: `rank_K(A)` for an integer matrix `A` and a field `K`, and its part (ii): `rank_K(A) ≤ rank_ℚ(A)` for every field, with equality if `char K = 0`.

In `q_col_upper.md` the parts (iii) and (iv) assume that `m` is odd: then inversion on `μ_m ∖ {1}` has no fixed point. For even `m` it has exactly one, `−1`, and the count changes. This file gives the count and the upper bound for even `m`.

## Setting

**The number.** For `k ≥ 0` and an even `m ≥ 2` put `h := (m − 2)/2`, `N := 2k + 2` and

`Q^e_k(m) := Σ N! / ( (2c)! · Π_{u=1}^{h} (b_u!)^2 )`,

the sum over all `(c, b_1, …, b_h) ∈ N^{1+h}` with `c + b_1 + ⋯ + b_h = k + 1`. (Each term is an integer: it is the multinomial coefficient `N!/((2c)! Π (2b_u)!)` times `Π C(2b_u, b_u)`. In the paper this number is `N_{m−1}(2k+2) = N!·[x^N] cosh(x)·I_0(2x)^{(m−2)/2}`, and it is the value `Q_k(m)` for even `m`.)

**Pointed point sets.** A *pointed point set* is a finite set `T` with a map `u ↦ −u` such that `−(−u) = u` for every `u`, with exactly one fixed point `o` (`−o = o`, and `−u = u` only for `u = o`), and `|T| = 2h + 1` for an integer `h ≥ 0`. A tuple `M ∈ T^n` is *closed* if `cnt_M(u) = cnt_M(−u)` for every `u ∈ T` and `cnt_M(o)` is even. (Example: `T = Z/m ∖ {0}` for even `m`, with negation; `o = m/2`.)

## Theorem

**(i) (the number, by the multiplicity of the fixed point)** For `k ≥ 0` and even `m ≥ 2`,

`Q^e_k(m) = 1 + Σ_{c=0}^{k} C(2k+2, 2c) · Q_{k−c}(m − 1)`,

where `Q_j(m − 1)` is the number of `q_theorem_B_lower.md` at the odd number `m − 1` (for `m = 2` it is `0`, so `Q^e_k(2) = 1`).

**(ii) (closed tuples and matchings)** Let `T` be a pointed point set and `g ∈ T^{2k+2}`, indexed by `V = {0, …, 2k+1}`. Then `g` is closed if and only if there is a matching `J` of `V` with `g_{J(x)} = −g_x` for every `x ∈ V`.

**(iii) (the number of closed tuples)** Let `T` be a pointed point set with `|T| = 2h + 1`. The number of closed tuples in `T^{2k+2}` is `Q^e_k(2h + 2)`.

**(iv) (the points are the tuples that split into inverse pairs; every `m`)** Let `K` be a field containing a set `μ_m` of `m` distinct `m`-th roots of unity, with `m ≠ 0` in `K` (`m ≥ 1`, odd or even). Let `P` be the set of tuples `g = (g_0, g_1, …, g_d) ∈ (μ_m ∖ {1})^{2k+2}` for which there is a matching `J` of `V` with `g_{J(x)} = g_x^{−1}` for every `x ∈ V`. Then `g ↦ (g_1, …, g_d)` is a bijection from `P` onto `Γ`; in particular `|Γ| = |P|`.

**(v) (the count for even `m`)** If moreover `m` is even, then `|Γ| = Q^e_k(m)`.

**(vi) (the upper bound for even `m`)** Let `m ≥ 2` be even. For every field `F`,

`dim_F I_F ≤ Q^e_k(m)`,

with equality if `char F = 0` and `F` contains `m` distinct `m`-th roots of unity; and `rank_ℚ(A) = Q^e_k(m)` for the integer matrix `A = A(m, k)` of `q_col_upper.md`, part (i).

**(vii) (first values)** `Q^e_1(4) = 19`, `Q^e_2(4) = 141`, `Q^e_1(6) = 61`.

## Proof

(i) In the sum defining `Q^e_k(m)` separate the terms by `c ∈ {0, …, k+1}`. For `c = k + 1` all `b_u` are `0` and the term is `N!/N! = 1`. For `c ≤ k`, with `N − 2c = 2(k − c) + 2`,

`N!/((2c)! Π (b_u!)^2) = C(N, 2c) · (N − 2c)!/Π (b_u!)^2`,

and the sum of `(N − 2c)!/Π(b_u!)^2` over the `(b_1, …, b_h)` with `b_1 + ⋯ + b_h = (k − c) + 1` is `Q_{k−c}(m − 1)`, because `(m − 1 − 1)/2 = h`. (If `h = 0`, i.e. `m = 2`, there is no such `b`, the sum is `0`, and `Q_{k−c}(1) = 0`.)

(ii) *If.* Let `J` be a matching with `g_{J(x)} = −g_x` for all `x`. For every `u ∈ T`, `J` maps `{x : g_x = u}` into `{x : g_x = −u}` and, being an involution, maps the second set back into the first; so the two sets have the same number of elements: `cnt_g(u) = cnt_g(−u)`. For `u = o`, `J` restricts to an involution of `{x : g_x = o}` without fixed points, so this set has an even number of elements. *Only if.* Let `g` be closed. For each two-element class `{u, −u}` (`u ≠ o`) the sets `{x : g_x = u}` and `{x : g_x = −u}` have the same number of elements; choose a bijection between them (for instance, the `i`-th element of the first, in increasing order, goes to the `i`-th element of the second). The set `{x : g_x = o}` has an even number of elements; choose a fixed-point-free involution of it (the first with the second, the third with the fourth, and so on). These choices together form a fixed-point-free involution `J` of `V` with `g_{J(x)} = −g_x` for every `x`.

(iii) Let `T' := T ∖ {o}`; with the same map it is a point set with a fixed-point-free involution and `|T'| = 2h`. Sort the closed tuples `g ∈ T^{2k+2}` by the set `S := {x ∈ V : g_x = o}`; its cardinality is even, `|S| = 2c` with `0 ≤ c ≤ k + 1`. For a fixed `S` with `|S| = 2c`, the closed tuples with this `S` correspond to the tuples in `T'` indexed by `V ∖ S` (a set with `2(k − c) + 2` elements if `c ≤ k`, and empty if `c = k + 1`) that satisfy `cnt(u) = cnt(−u)` for every `u ∈ T'`. If `c = k + 1` there is exactly one (the constant tuple `o`). If `c ≤ k` and `h ≥ 1`, their number is the number of closed tuples in `T'^{2(k−c)+2}`, which is `Q_{k−c}(2h + 1)` by Theorem (ii) of `q_theorem_B_lower.md` with `q := 2h + 1`; if `h = 0` there is none, and `Q_{k−c}(1) = 0`. There are `C(2k+2, 2c)` sets `S` with `|S| = 2c`. So the number of closed tuples is `1 + Σ_{c=0}^{k} C(2k+2, 2c) Q_{k−c}(2h + 1)`, which is `Q^e_k(2h + 2)` by (i). (Any other proof is fine.)

(iv) Recall that `μ_m` is the set of roots of `X^m − 1`, so it is closed under products and inverses, and `1 ∈ μ_m`.

*The product is `1`.* Let `g ∈ P` with a matching `J`. `V` is the disjoint union of the pairs `{x, J(x)}`, `x < J(x)`, so `Π_{x ∈ V} g_x = Π_{x < J(x)} g_x g_{J(x)} = 1`. Hence `g_0 = (g_1 ⋯ g_d)^{−1}`. (This replaces the argument of `q_col_upper.md`, which used that `m` is odd.)

*Into `Γ`.* For `g ∈ P` with matching `J` and `a := (g_1, …, g_d)`: for a pair `x < J(x)` we have `J(x) ≠ 0`, so `a_{J(x)} = g_{J(x)} ≠ 1`; for a pair with `0 < x < J(x)`, `a_x a_{J(x)} = g_x g_x^{−1} = 1`. By the criterion, `ev_a(ψ_J) ≠ 0`, so `a ∈ Γ`.

*Injective.* By the first step, `g_0` is determined by `g_1, …, g_d`.

*Surjective.* Let `a ∈ Γ`, with a matching `J` such that `ev_a(ψ_J) ≠ 0`, and let `b := J(0)`. Put `g_x := a_x` for `x ≠ 0` and `g_0 := a_b^{−1}`. By the criterion, `g_x g_{J(x)} = 1` for every pair of `J` avoiding `0`, and `g_0 g_b = 1` by definition; so `g_{J(x)} = g_x^{−1}` for every `x`. Every `g_x` lies in `μ_m`. No `g_x` equals `1`: if `x < J(x)` then `g_{J(x)} = a_{J(x)} ≠ 1` by the criterion, and then `g_x = g_{J(x)}^{−1} ≠ 1`; every `x` is in a pair. So `g ∈ P`, and it maps to `a`.

(v) Let `m` be even. Since `m ≠ 0` in `K` and `m = 2 · (m/2)`, `2 ≠ 0` in `K`, so `−1 ≠ 1`; and `(−1)^m = 1`, so `−1 ∈ μ_m ∖ {1}`. Let `T := μ_m ∖ {1}` with `u ↦ u^{−1}` (it maps `T` to `T`). If `u^{−1} = u` with `u ∈ T`, then `u^2 = 1`, `(u − 1)(u + 1) = 0`, and `u ≠ 1`, so `u = −1`. So `T` is a pointed point set with `o = −1` and `|T| = m − 1 = 2h + 1`, `h = (m − 2)/2`. By (ii) the set `P` of (iv) is the set of closed tuples of `T^{2k+2}`; by (iv) and (iii), `|Γ| = |P| = Q^e_k(2h + 2) = Q^e_k(m)`.

(vi) The complex numbers contain `m` distinct `m`-th roots of unity and `m ≠ 0` in `C`. By parts (i) and (ii) of the Theorem of `q_col_upper.md`, by (v), and by part (ii) of `q_every_field.md`:

`dim_F I_F = rank_F(A) ≤ rank_ℚ(A) = rank_C(A) = dim_C I_C = |Γ| = Q^e_k(m)`.

If `char F = 0` and `F` contains `m` distinct `m`-th roots of unity (then `m ≠ 0` in `F`), part (ii) of `q_col_upper.md` and (v) give equality directly.

(vii) By (i) and `Q_0(3) = 2`, `Q_1(3) = 6`, `Q_2(3) = 20`, `Q_0(5) = 4`, `Q_1(5) = 36`: `Q^e_1(4) = 1 + 6 + 6·2 = 19`, `Q^e_2(4) = 1 + 20 + 15·6 + 15·2 = 141`, `Q^e_1(6) = 1 + 36 + 6·4 = 61`. (Or directly from the definition.) ∎

## Checks

See `chkE2.log`. (A) The explicit sum, the formula of (i) and the table of the paper agree in the 30 cells `m ∈ {4, 6, 8, 10, 12, 16}`, `k ≤ 5`; the direct enumeration of closed tuples of `Z/m ∖ {0}` agrees at 12 cells with `m ≤ 12`. (B) `|Γ|`, by evaluating every `ψ_J` at every point of `μ_m^d` over `F_P` with `P ≡ 1 (mod m)`, equals `Q^e_k(m)` at 11 cells. (C) The exact rank of `I_F` over `F_p` for every prime `p | m` is `≤ Q^e_k(m)`, and over `F_P` it equals `Q^e_k(m)`, at 7 cells. In all 7 the rank over `F_p`, `p | m`, is in fact equal to `Q^e_k(m)`. (D) Controls: with one matching removed from the family, the rank over `F_P` drops at `(m, k) = (4,1), (6,1), (8,1), (10,1)` (`15, 45, 91, 153` instead of `19, 61, 127, 217`) and does not change at `(2,1), (2,2), (4,2)`; the formula for odd degrees read at an even `m` differs from the count in 30 cells of 30. (The control of `q_col_upper.md`, `t_b + 1` in place of `t_b − 1`, cannot fire for even `m`, because `t ↦ −t` is then an automorphism of `K[G]`; it was run, was silent in 7 cells of 7, and was replaced.) 64 checks, 0 failures.
