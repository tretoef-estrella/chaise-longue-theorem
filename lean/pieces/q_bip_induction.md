# The bipartite down-set theorem and Theorem C (§7.6 of the paper, Theorem 7.6)

This file uses, unchanged:
- `q_bip_setting.md`: `R_{α,β}` (box exponent `q`), `x_i`, `z_l`, shapes `λ(ξ, η)`, `BPar_q(α, β)`, the product order `≼`, down-sets of `BPar_q(α, β)`, `Z_Λ`, tight patterns and their products, `V_Λ`, the root ideals `I^{bal}_a`, `I^{ph}_a`, the counts `N_{bal}`, `N_{ph}`, Lemma 7.1 (parts (iii) and (iv)) and Lemma 7.2 (parts (i), (ii), (iii));
- `q_bip_options.md`: `F_Λ(μ)`, the layers `Λ_i`, and Lemma 7.3(ii) (`Z_{>i} = Z_{Λ_i}`);
- `q_bip_P2.md`: Proposition 7.4(ii) (every layer `Λ_i` is a down-set of `BPar_q(α − 1, β)`);
- `q_bip_P3.md`: Proposition 7.5 (`V_{Λ_i} ⊆ W_{q−1−i}(V_Λ)`).

## Setting

`F` is a field, `q ≥ 3` is odd, and the binomial coefficients `C(q−1, t)`, `0 ≤ t ≤ q − 1`, are non-zero in `F` (the hypothesis of `q_bip_P3.md`). `Ω` is a finite set with `|Ω| = q`. `dim V` is the `F`-dimension of an ideal `V` of `R_{α,β}`.

**The swap.** For a pair of partitions `λ = (λ_+, λ_−)` put `λ^⊤ := (λ_−, λ_+)`, and for a set `Λ` of pairs put `Λ^⊤ := {λ^⊤ : λ ∈ Λ}`.

## Theorem 7.6 (bipartite down-set theorem)

For all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`:

`dim V_Λ ≥ |Z_Λ|`.

## Theorem C (the bipartite count)

For every `a ≥ 0`: `dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`.

## Lemma S (the symmetry)

For all `α, β ≥ 0`:

**(i)** `λ ∈ BPar_q(α, β)` iff `λ^⊤ ∈ BPar_q(β, α)`; `λ ≼ μ` iff `λ^⊤ ≼ μ^⊤`; hence `Λ` is a down-set of `BPar_q(α, β)` iff `Λ^⊤` is a down-set of `BPar_q(β, α)`.

**(ii)** `λ(η, ξ) = λ(ξ, η)^⊤` for every point `(ξ, η) ∈ Ω^α × Ω^β`; hence `(ξ, η) ↦ (η, ξ)` is a bijection `Z_Λ → Z_{Λ^⊤}` and `|Z_{Λ^⊤}| = |Z_Λ|` (the second set in `Ω^β × Ω^α`).

**(iii)** Let `σ : R_{α,β} → R_{β,α}` be the `F`-algebra isomorphism that renames the variables: `σ(x_i) := z_i` (`i ∈ [α]`) and `σ(z_l) := x_l` (`l ∈ [β]`), where `x_l` (`l ∈ [β]`) and `z_i` (`i ∈ [α]`) are the variables of `R_{β,α}`. Then `σ(V_Λ) = V_{Λ^⊤}`, and so `dim V_{Λ^⊤} = dim V_Λ`.

*Proof.* (i) The three conditions defining `BPar_q(α, β)` are symmetric under exchanging `(λ_+, α)` with `(λ_−, β)`: `|λ_+| − |λ_−| = α − β` iff `|λ_−| − |λ_+| = β − α`; the other two are sums. The product order compares the components separately. (ii) The counts `X(u)` and `Y(u)` are exchanged, so the partitions `λ_+` and `λ_−` are exchanged. (iii) `σ` is well defined and bijective because it is a bijection between the variables and the box relations `x_i^q`, `z_l^q` correspond to box relations. Let `T = (P, (B^+_c), (B^−_c))` be a tight pattern of `λ` on `([α], [β])`. Then `T^⊤ := ({(l, i) : (i, l) ∈ P}, (B^−_c), (B^+_c))` is a tight pattern of `λ^⊤` on `([β], [α])` (the conditions on `T` are those on `T^⊤` with the roles exchanged), and every tight pattern of `λ^⊤` arises in this way from exactly one tight pattern of `λ`. The products correspond: `σ((x_i − z_l)^{q−1}) = (z_i − x_l)^{q−1} = (x_l − z_i)^{q−1}` because `q − 1` is even; and `σ(Δ(x_B)) = Δ(z_B)`, `σ(Δ(z_B)) = Δ(x_B)`, since `σ` keeps the order of the indices inside each block. So `σ` maps the set of generators of `V_Λ` onto the set of generators of `V_{Λ^⊤}`, hence `σ(V_Λ) = V_{Λ^⊤}`, and `σ` is an `F`-linear bijection. ∎

## Proof of Theorem 7.6

Induction on `n := α + β`, for all `α, β` with `α + β = n` and all down-sets `Λ` of `BPar_q(α, β)` at once.

**Base `n = 0`.** `BPar_q(0, 0) = {(∅, ∅)}`, so `Λ = ∅` or `Λ = {(∅, ∅)}`. For `Λ = ∅`, `V_Λ = 0` and `Z_Λ = ∅`. For `Λ = {(∅, ∅)}`, the empty tight pattern has product `1`, so `V_Λ = R_{0,0} = F`, of dimension `1`, and `Z_Λ` is the single point `(∅, ∅)`.

**Step `n ≥ 1`, case `α ≥ 1`.** Peel `w := x_1`. For `i ∈ {0, …, q − 1}`, the layer `Λ_i` is a down-set of `BPar_q(α − 1, β)` (Proposition 7.4(ii)), and `(α − 1) + β = n − 1`, so the induction hypothesis gives `dim V_{Λ_i} ≥ |Z_{Λ_i}|`. By Proposition 7.5, `V_{Λ_i} ⊆ W_{q−1−i}(V_Λ)`, so `dim W_{q−1−i}(V_Λ) ≥ dim V_{Λ_i}`. Hence, by Lemma 7.1(iii) (re-indexing `j = q − 1 − i`), Lemma 7.3(ii) and Lemma 7.1(iv) applied to `Z = Z_Λ`:

`dim V_Λ = Σ_{j=0}^{q−1} dim W_j(V_Λ) = Σ_{i=0}^{q−1} dim W_{q−1−i}(V_Λ) ≥ Σ_{i=0}^{q−1} dim V_{Λ_i} ≥ Σ_{i=0}^{q−1} |Z_{Λ_i}| = Σ_{i=0}^{q−1} |Z_{>i}| = |Z_Λ|`.

**Step `n ≥ 1`, case `α = 0`.** Then `β = n ≥ 1`. By Lemma S(i), `Λ^⊤` is a down-set of `BPar_q(β, 0)`, and `β ≥ 1`, so the previous case (which only used the induction hypothesis for `n − 1`) gives `dim V_{Λ^⊤} ≥ |Z_{Λ^⊤}|`. By Lemma S(ii), (iii), `dim V_Λ = dim V_{Λ^⊤} ≥ |Z_{Λ^⊤}| = |Z_Λ|`. ∎

## Proof of Theorem C

Lemma 7.2(i): `{(∅, ∅)}` is a down-set of `BPar_q(a, a)`, `V_{{(∅,∅)}} = I^{bal}_a` and `|Z_{{(∅,∅)}}| = N_{bal}(a, q)`; Theorem 7.6 gives the first inequality. Lemma 7.2(ii): `{((1), ∅)}` is a down-set of `BPar_q(a + 1, a)`, `V_{{((1),∅)}} = I^{ph}_a` and `|Z_{{((1),∅)}}| = N_{ph}(a, q)`; Theorem 7.6 gives the second inequality, and Lemma 7.2(iii) gives `N_{ph}(a, q) = N_{bal}(a + 1, q)`. ∎

## Checks

- Theorem 7.6, exact linear algebra over `F_p` and enumeration of `Ω^α × Ω^β`, for every down-set `Λ` of `BPar_q(α, β)` (including `Λ = ∅`), cells `(q, α, β, p)` = `(3,0,0,3)`, `(3,1,0,3)`, `(3,0,2,3)`, `(3,1,1,3)`, `(3,2,1,3)`, `(3,1,2,3)`, `(3,2,2,3)`, `(3,3,1,3)`, `(3,0,3,3)`, `(3,3,0,3)`, `(5,1,1,5)`, `(5,2,1,5)`, `(5,1,2,5)`, `(7,1,1,7)`, and over `F_101`: `(3,2,2)`, `(5,1,1)`: 62 down-sets, 0 failures; equality `dim V_Λ = |Z_Λ|` in all 52 down-sets over `F_q` (`q = p`), strict inequality in 6 of the 10 over `F_101`.
- Theorem C: `dim I^{bal}_a = N_{bal}(a, q)` and `dim I^{ph}_a = N_{ph}(a, q)` for `a = 0, 1, 2` over `F_3` (`q = 3`: `1, 3, 15` and `3, 15, 93`) and over `F_5` (`q = 5`: `1, 5, 45` and `5, 45, 545`); over `F_101` at `q = 3`, for `a = 0, 1, 2`: `dim I^{bal}_a = 1, 4, 24` against `N_{bal} = 1, 3, 15`, and `dim I^{ph}_a = 3, 18, 126` against `N_{ph} = 3, 15, 93` — the values printed in §7.7 and §12 of the paper.
