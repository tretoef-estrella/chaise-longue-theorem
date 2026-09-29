# The options of a partition form a chain for weak dominance

## Setting

**Partitions.** A partition is a finite weakly decreasing sequence of positive integers `μ = (μ_1 ≥ μ_2 ≥ ⋯ ≥ μ_ℓ)`, `ℓ = ℓ(μ) ≥ 0` (the empty partition has `ℓ = 0`). Set `μ_i := 0` for `i > ℓ`. (Equivalently: a finite multiset of positive integers, listed in weakly decreasing order.)

**Partial sums.** For `t ≥ 1` let `S_t(μ) := μ_1 + ⋯ + μ_t` (the sum of the `t` largest parts, padded with zeros).

**Weak dominance.** For partitions `λ, μ` (of any sizes and lengths) put `λ ≼ μ` iff `S_t(λ) ≤ S_t(μ)` for every `t ≥ 1`. This is a partial order.

**The options of `μ`.** Let `ℓ = ℓ(μ)` and `1 ≤ j ≤ ℓ`.
- `μ − e_j` is the partition obtained from `μ` by lowering row `j` by one and re-sorting (dropping a part that becomes `0`).
- `μ + e_j` is the partition obtained by raising row `j` by one and re-sorting.
- `μ ⊔ 1` is the partition obtained by adding a new part equal to `1`.

Let `r̄_j := max{i : μ_i = μ_j}` (the last row with the same length as row `j`) and `r̲_j := min{i : μ_i = μ_j}` (the first such row).

**The list of options.** Fix an integer `L ≥ 2ℓ`. Define `opt_p(μ)` for `p = 1, …, L` by:
- `opt_p(μ) := μ − e_p` for `1 ≤ p ≤ ℓ`;
- `opt_p(μ) := μ ⊔ 1` for `ℓ < p ≤ L − ℓ` (there are `L − 2ℓ` such positions);
- `opt_p(μ) := μ + e_{L+1−p}` for `L − ℓ < p ≤ L`.

(In the source, `L = q − 1` for an odd `q`, and the `L` options are the partitions obtained by adding one value to a tuple; nothing below depends on that.)

A set `Λ` of partitions is a **down-set** if `λ ≼ μ` and `μ ∈ Λ` imply `λ ∈ Λ`.

## Lemma (chain)

(a) For every `t ≥ 1` and `1 ≤ j ≤ ℓ`:

`S_t(μ − e_j) = S_t(μ) − [t ≥ r̄_j]`,   `S_t(μ + e_j) = S_t(μ) + [t ≥ r̲_j]`,   `S_t(μ ⊔ 1) = S_t(μ) + [t > ℓ]`,

where `[·]` is `1` if the condition holds and `0` otherwise.

(b) The options are weakly increasing: `opt_1(μ) ≼ opt_2(μ) ≼ ⋯ ≼ opt_L(μ)`.

(c) For every down-set `Λ`, the set `{p ∈ {1, …, L} : opt_p(μ) ∈ Λ}` is an initial segment `{1, …, F}` of `{1, …, L}` (possibly empty), where `F := #{p : opt_p(μ) ∈ Λ}`.

## Proof

(a) Rows `j, …, r̄_j` all have length `μ_j`. Lowering row `j` by one and re-sorting gives the same multiset as lowering row `r̄_j` by one, and lowering row `r̄_j` keeps the sequence weakly decreasing (the next row, if any, has length `< μ_j`, hence `≤ μ_j − 1`). So `μ − e_j` is `μ` with row `r̄_j` lowered by one (a final part `0` is dropped, which does not change any `S_t`). Hence `S_t` drops by one exactly when `t ≥ r̄_j`. Symmetrically, raising row `j` gives the same multiset as raising row `r̲_j`, which keeps the order (the previous row, if any, has length `> μ_j`, hence `≥ μ_j + 1`); so `S_t` rises by one exactly when `t ≥ r̲_j`. Adding a part `1` puts it at position `ℓ + 1` (all parts are `≥ 1`), so `S_t` rises by one exactly when `t ≥ ℓ + 1`.

(b) There are four kinds of consecutive pairs.
- `μ − e_j ≼ μ − e_{j+1}` for `1 ≤ j < ℓ`: since `μ_j ≥ μ_{j+1}`, `r̄_j ≤ r̄_{j+1}`, so `[t ≥ r̄_j] ≥ [t ≥ r̄_{j+1}]` for every `t`; use (a).
- `μ − e_ℓ ≼ μ ⊔ 1` (when `ℓ ≥ 1` and `L > 2ℓ`), and `μ − e_ℓ ≼ μ + e_ℓ` (when `ℓ ≥ 1` and `L = 2ℓ`): by (a), `S_t(μ − e_ℓ) ≤ S_t(μ) ≤ S_t(μ ⊔ 1)` and `S_t(μ) ≤ S_t(μ + e_ℓ)`.
- Copies of `μ ⊔ 1` are equal. And `μ ⊔ 1 ≼ μ + e_ℓ` (when `ℓ ≥ 1`): `r̲_ℓ ≤ ℓ`, so `[t > ℓ] ≤ [t ≥ r̲_ℓ]` for every `t`; use (a).
- `μ + e_{j+1} ≼ μ + e_j` for `1 ≤ j < ℓ`: `r̲_j ≤ r̲_{j+1}`, so `[t ≥ r̲_{j+1}] ≤ [t ≥ r̲_j]`; use (a).

In the list, the positions run through `μ − e_1, …, μ − e_ℓ`, then the copies of `μ ⊔ 1`, then `μ + e_ℓ, …, μ + e_1`, so these four kinds cover every consecutive pair `opt_p ≼ opt_{p+1}`. Transitivity gives (b).

(c) If `opt_p(μ) ∈ Λ` and `p' ≤ p`, then `opt_{p'}(μ) ≼ opt_p(μ)` by (b), so `opt_{p'}(μ) ∈ Λ`. Hence the set is downward closed in `{1, …, L}`, i.e. an initial segment, and its length is its cardinality `F`. ∎

## Checks

- `μ = (2, 2, 1)`, `ℓ = 3`, `L = 6` (so `μ ⊔ 1` does not occur): `r̄_1 = r̄_2 = 2`, `r̄_3 = 3`, `r̲_1 = r̲_2 = 1`, `r̲_3 = 3`. In position order the options are `μ − e_1 = (2,1,1)`, `μ − e_2 = (2,1,1)`, `μ − e_3 = (2,2)`, `μ + e_3 = (2,2,2)`, `μ + e_2 = (3,2,1)`, `μ + e_1 = (3,2,1)`, with `(S_1, S_2, S_3) = (2,3,4), (2,3,4), (2,4,4), (2,4,6), (3,5,6), (3,5,6)`: weakly increasing, as (b) says.
- `μ = (2, 2, 1)`, `L = 8`: the same list with two copies of `μ ⊔ 1 = (2,2,1,1)`, `(S_1, …, S_4) = (2,4,5,6)`, inserted between `(2,2)` and `(2,2,2)`.
- `μ = ∅`, `L = 4`: every option is `(1)`.
