# Which generators survive on each factor (§6.2 of the paper, Lemma 6.2)

This file uses, unchanged, `q_col_splitting.md`: the Setting (`F` of characteristic `p`, `q = p^v`, `r`, the set `μ` of the `r`-th roots of unity with `X^r − 1 = Π_{ζ∈μ}(X − ζ)`, `m = q·r`), the rings `S = F[t_1, …, t_d]`, `F[G]`, `J_c`, `R_c = S/J_c` and the maps `π_c : F[G] → R_c` of its Lemma 6.1(0).

## Setting

Let `k ≥ 0` and `d := 2k + 1` (in the paper `n = 2k` and `d = n + 1`). A **matching** is a perfect matching of `{0, 1, …, 2k+1}`, encoded as a fixed-point-free involution `J` of `{0, …, 2k+1}`; its **pairs** are the sets `{a, J(a)}`. For an index `a ∈ {1, …, 2k+1}` write `t_a` for the variable of `S` (and its images in `F[G]` and `R_c`). Put

`φ(u) := u^{m−1} + ⋯ + u + 1`,

and, for a matching `J`,

`ψ_J := Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} φ(t_a t_{J(a)})   ∈ F[G]`,

the first product over the `k + 1` pairs (for each pair, the factor of its larger element; for the pair containing `0` this is `t_{J(0)} − 1`), the second over the `k` pairs not containing `0`. For a colouring `c = (c_1, …, c_d) ∈ μ^d` put `c_0 := (c_1 ⋯ c_d)^{−1}` (so `c_0 c_1 ⋯ c_d = 1`).

Elementary facts used freely: `1 ∈ μ`; `μ` is closed under products and inverses (its elements are the roots of `X^r − 1`); every element of `μ` is non-zero, so `c_0` is defined and lies in `μ`. In `R_c`, `(t_i − c_i)^q = 0` for every `i`.

## Lemma 6.2

Fix `c ∈ μ^d`.

**(i)** For `1 ≤ i ≤ d`: if `c_i ≠ 1`, then `t_i − 1` is a unit of `R_c`; if `c_i = 1`, then `(t_i − 1)^q = 0` in `R_c`.

**(ii)** Let `1 ≤ j < l ≤ d` and `u := t_j t_l ∈ R_c`. If `c_j c_l ≠ 1`, then `φ(u) = 0` in `R_c`. If `c_j c_l = 1`, then `φ(u) = w·(u − 1)^{q−1}` for a unit `w` of `R_c`.

**(iii)** Let `J` be a matching. If some pair `{a, J(a)}` with `0 < a < J(a)` has `c_a c_{J(a)} ≠ 1`, then `π_c(ψ_J) = 0`. If `c_a c_{J(a)} = 1` for every pair with `0 < a < J(a)`, then also `c_0 c_{J(0)} = 1`, and

`π_c(ψ_J) = w · Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} (t_a t_{J(a)} − 1)^{q−1}`   (6.2)

for a unit `w` of `R_c`.

## Proof

*Frobenius in `R_c`.* Since `F` has characteristic `p` and `q = p^v`, `(x + y)^q = x^q + y^q` in every commutative `F`-algebra. In `R_c`, `t_i^q − c_i^q = (t_i − c_i)^q = 0`, so `t_i^q = c_i^q`.

*Units.* `R_c` is local (it is `F[s_1, …, s_d]/(s_i^q)` with `s_i = t_i − c_i`): an element `x` is a unit iff it is a non-zero constant plus a nilpotent; every `s_i` is nilpotent, and a sum of nilpotents is nilpotent.

(i) `t_i − 1 = (c_i − 1) + (t_i − c_i)`. If `c_i ≠ 1`, this is a non-zero constant plus a nilpotent, hence a unit. If `c_i = 1`, then `(t_i − 1)^q = (t_i − c_i)^q = 0`.

(ii) In `F[X]`, `(X − 1)·φ(X) = X^m − 1 = Π_{ξ∈μ} (X − ξ)^q` (Lemma 6.1(0)). Since `1 ∈ μ` and `F[X]` is a domain, cancelling `X − 1` gives `φ(X) = (X − 1)^{q−1}·Π_{ξ∈μ, ξ≠1} (X − ξ)^q`. Substitute `X = u`. By Frobenius, `u^q = t_j^q t_l^q = c_j^q c_l^q = ξ_0^q` with `ξ_0 := c_j c_l ∈ μ`, so `(u − ξ_0)^q = u^q − ξ_0^q = 0`. If `ξ_0 ≠ 1`, the factor `(u − ξ_0)^q` occurs in the product, so `φ(u) = 0`. If `ξ_0 = 1`, then `u − 1` is nilpotent (`(u − 1)^q = 0`), and for `ξ ≠ 1` the element `u − ξ = (1 − ξ) + (u − 1)` is a unit; so `w := Π_{ξ≠1} (u − ξ)^q` is a unit and `φ(u) = w·(u − 1)^{q−1}`.

(iii) The first sentence follows from (ii): the factor `φ(t_a t_{J(a)})` of `ψ_J` is `0` in `R_c`. For the second: the pairs of `J` partition `{0, …, d}`, so `1 = c_0 c_1 ⋯ c_d = Π_{a < J(a)} c_a c_{J(a)} = c_0 c_{J(0)}·Π_{0 < a < J(a)} c_a c_{J(a)} = c_0 c_{J(0)}`. Then apply (ii) to each factor `φ(t_a t_{J(a)})`, `0 < a < J(a)`, and let `w` be the product of the units. ∎

## Checks

- Exact computation in `R_c = F_p[s_1, …, s_d]/(s_i^q)` (`t_i = c_i + s_i`) over `F = F_p`, `μ ⊆ F_p^×` the `r`-th roots of unity, for every colouring `c ∈ μ^d`, every `i`, every pair `j < l` and every matching `J`: `(p, q, r, k) ∈ {(3,3,2,1), (3,3,2,2), (5,5,2,1), (7,7,3,1), (7,7,2,1), (5,5,4,1)}`. In (ii) the unit `w = Π_{ξ≠1}(u − ξ)^q` and the identity `φ(u) = w(u−1)^{q−1}` are checked exactly; in (iii), `π_c(ψ_J)` and the product in (6.2) generate the same principal ideal (in the local ring `R_c` this means they differ by a unit), and `c_0 c_{J(0)} = 1`. 1 995 checks, 0 failures.
