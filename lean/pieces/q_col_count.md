# The count factors in the same way (§6.6 of the paper, Lemma 6.8)

This file uses, unchanged:
- `q_col_splitting.md`: the Setting (`F` of characteristic `p`, `q = p^v`, `r`, `μ`, `m = q·r`);
- `q_col_survivors.md`: `k`, `d = 2k + 1`, `V = {0, …, 2k+1}`, matchings, the extended colouring `c_0 := (c_1 ⋯ c_d)^{−1}` and its elementary facts (`μ` is closed under products and inverses, its elements are non-zero, `c_0 ∈ μ`, `c_0 c_1 ⋯ c_d = 1`);
- `q_col_compatible.md`: the classes `𝒞_ζ`, sets `ℛ` of representatives, compatibility, and Lemma 6.3 (i) (for `r` odd the only self-inverse element of `μ` is `1`; the classes `𝒞_1` and `𝒞_ζ ∪ 𝒞_{ζ^{−1}}`, `ζ ∈ ℛ`, partition `V`) and (iv) (a compatible matching exists iff `|𝒞_1|` is even and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`);
- `q_P1_fibres.md`: point sets `T` with a fixed-point-free involution `u ↦ −u` and `|T| = 2h`, and the count `cnt(M, u) = #{i : M_i = u}`;
- `q_theorem_B_lower.md`: the standard point set `T_h = {1, …, h} × {±1}`, closed tuples (`M ∈ T^n` with `cnt(M, u) = cnt(M, −u)` for every `u`), `Q_k(q)`, and its Theorem (ii): for every point set `T` with `|T| = 2h`, `h = (q − 1)/2`, the number of closed tuples in `T^{2k+2}` is `Q_k(q)`;
- `q_bip_setting.md`: the counts `N_{bal}(a, q)` and `N_{ph}(a, q)` (with `Ω` any set of `q` elements), and its Lemma 7.2 (iii): `N_{ph}(a, q) = N_{bal}(a + 1, q)`.

## Setting

In addition, **`p ≠ 2`** (so `q` is odd and `q ≥ 3`) and **`r` is odd**; hence `m = q·r` is odd. Put `h := (q − 1)/2 ≥ 1` and `H := (m − 1)/2`. Fix a set `ℛ` of representatives.

For a colouring `c ∈ μ^d`, extended by `c_0`, write `𝒞_ζ := 𝒞_ζ(c)` for the classes of the extended colouring, and put:

- `comp(c)`: some matching of `V` is compatible with `c`;
- `N_1(c) := #{closed tuples in T_h^{|𝒞_1|}}`;
- for `ζ ∈ ℛ`, with `α := |𝒞_ζ ∖ {0}|` and `β := |𝒞_{ζ^{−1}} ∖ {0}|`:
  `N_ζ(c) := N_{ph}(min(α, β), q)` if `0 ∈ 𝒞_ζ ∪ 𝒞_{ζ^{−1}}`, and `N_ζ(c) := N_{bal}(α, q)` otherwise.

(These are the block counts of Lemmas 6.6 and 6.7: for `0 ∈ 𝒞_1`, `|𝒞_1| = 2j + 2`, `N_1(c) = Q_j(q)` by Theorem (ii) of `q_theorem_B_lower.md`; for `0 ∉ 𝒞_1`, `|𝒞_1| = 2j`, it is the number of closed tuples in `T_h^{2j}`.)

## Lemma 6.8

**(i) (the point set of `μ_m`)** The set

`T_m := (Ω_q × μ) ∖ {(∗, 1)}`,   with `Ω_q := T_h ⊔ {∗}` (a set of `q` elements),

with the involution `(w, ζ) ↦ (w̄, ζ^{−1})`, where `∗̄ := ∗` and `w̄ := −w` for `w ∈ T_h`, is a point set with a fixed-point-free involution and `|T_m| = m − 1 = 2H`.

**(ii) (the count over one colouring)** For every `c ∈ μ^d`, the number of closed tuples `g ∈ T_m^{2k+2}` whose colour tuple `(g_0.2, g_1.2, …, g_{2k+1}.2)` is the extended colouring `(c_0, c_1, …, c_d)` equals `N_1(c)·Π_{ζ∈ℛ} N_ζ(c)` if `comp(c)`, and `0` otherwise.

**(iii) (the sum)**

`Σ_{c ∈ μ^d} [comp(c)]·N_1(c)·Π_{ζ∈ℛ} N_ζ(c) = Q_k(m)`,

where `[comp(c)]·X` means `X` if `comp(c)` and `0` otherwise.

## Proof

(i) The involution is an involution (`∗̄̄ = ∗`, `−(−w) = w`, `(ζ^{−1})^{−1} = ζ`) and maps `T_m` to itself (`(∗, 1)` is its own image). A fixed point `(w, ζ)` has `ζ^{−1} = ζ`, so `ζ = 1` (Lemma 6.3 (i), `r` odd); then `w̄ = w` forces `w = ∗` (the involution of `T_h` has no fixed point), and `(∗, 1) ∉ T_m`. `|T_m| = q·r − 1 = m − 1`.

(ii) Write `κ(g) := (g_0.2, …, g_{2k+1}.2)` for the colour tuple and `ω(g) := (g_0.1, …, g_{2k+1}.1)`.

*Colours of a closed tuple.* If `g` is closed, the colour multiset is closed under inversion: `(w, ζ) ↦ (w̄, ζ^{−1})` is a bijection from the entries of colour `ζ` to those of colour `ζ^{−1}` on the level of counts, `cnt(κ(g), ζ) = Σ_w cnt(g, (w, ζ)) = Σ_w cnt(g, (w̄, ζ^{−1})) = cnt(κ(g), ζ^{−1})`. Hence `Π_i κ(g)_i = 1` (pair each `ζ ≠ 1` with `ζ^{−1} ≠ ζ`), so `κ(g)_0 = (κ(g)_1 ⋯ κ(g)_{2k+1})^{−1}`: `κ(g)` is the extended colouring of `c := (κ(g)_1, …, κ(g)_d)`. Moreover `|𝒞_1|` is even (the entries of colour `1` are `(w, 1)` with `w ∈ T_h`, and their multiset is closed under the fixed-point-free `w ↦ −w`), and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`; so `comp(c)` holds by Lemma 6.3 (iv). This proves the case `¬ comp(c)`.

*The blocks.* Fix `c` with `comp(c)`. A tuple `g` with `κ(g)` = the extended colouring is determined by `ω(g)`, subject to: `ω(g)_i ≠ ∗` for `i ∈ 𝒞_1`. Such a `g` is closed iff, for every colour `ζ`, `cnt(g, (w, ζ)) = cnt(g, (w̄, ζ^{−1}))` for every `w ∈ Ω_q`. By the partition of Lemma 6.3 (i) these conditions split into independent conditions on the blocks:
- on `𝒞_1`: the tuple `(ω(g)_i)_{i∈𝒞_1} ∈ T_h^{𝒞_1}` is closed; after an enumeration of `𝒞_1` this gives `N_1(c)` choices;
- on `𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`): with `ξ := (ω(g)_i)_{i∈𝒞_ζ}` and `η := (ω(g)_l)_{l∈𝒞_{ζ^{−1}}}`, the condition is `cnt(ξ, w) = cnt(η, w̄)` for every `w ∈ Ω_q`, i.e. the multiset of `ξ` equals the multiset of `η̄ := (η_l)^−`. As `η ↦ η̄` is a bijection of `Ω_q^{𝒞_{ζ^{−1}}}`, and `|𝒞_ζ| = |𝒞_{ζ^{−1}}| =: a`, this gives `N_{bal}(a, q)` choices (after enumerations, and a bijection `Ω_q ≅ Ω`).

It remains to see `N_{bal}(|𝒞_ζ|, q) = N_ζ(c)`. If `0 ∉ 𝒞_ζ ∪ 𝒞_{ζ^{−1}}`, `|𝒞_ζ| = α`. If `0 ∈ 𝒞_{ζ^{−1}}`, then `|𝒞_ζ| = α = β + 1` and `min(α, β) = β`, and `N_{bal}(β + 1, q) = N_{ph}(β, q)` (Lemma 7.2 (iii)). If `0 ∈ 𝒞_ζ`, then `|𝒞_ζ| = α + 1 = β`, `min(α, β) = α`, and `N_{bal}(α + 1, q) = N_{ph}(α, q)`. The count is the product of the block counts.

(iii) Every closed tuple of `T_m^{2k+2}` has exactly one colour tuple, which by (ii) is the extended colouring of exactly one `c ∈ μ^d`; so the number of closed tuples is `Σ_c` of the counts of (ii), which is the left side. By (i) and Theorem (ii) of `q_theorem_B_lower.md` (with `q := m`, `h := H`), the number of closed tuples in `T_m^{2k+2}` is `Q_k(m)`. ∎

## Checks

- Exhaustive enumeration with `μ_m` modelled as `Z/m = Z/q × Z/r` (the involution is negation, the colour is the residue mod `r`), at `(m, n) = (15, 2), (21, 2), (45, 2), (15, 4)` and both primes of each `m` (`(q, r) = (3, 5), (5, 3), (3, 7), (7, 3), (9, 5), (5, 9), (3, 5), (5, 3)`): for every colouring `c` the number of closed tuples with colour `c` equals `[comp(c)]·N_1(c)·Π_ζ N_ζ(c)` (0 mismatches in 8 cells), and the sums are `546, 546, 1140, 1140, 5676, 5676, 32900, 32900 = Q_k(m)` (61 and 19 compatible colourings at `m = 15`, `k = 1`, as in Example 6.11 of the paper).
- Negative controls: (a) replacing `N_{ph}` by `N_{bal}(min(α, β), q)` on the blocks containing `0` changes the sum in 8 of 8 cells; (b) counting the block `𝒞_1` with one index fewer when `0 ∈ 𝒞_1` (as if `c_0`'s value were forced) gives per-colouring mismatches in 8 of 8 cells.
