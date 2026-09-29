# The fibres of a point set depend only on the residue partition

This file uses the **Setting** of `q_chain_lemma.md` (partitions, `S_t`, `≼`, the options `μ − e_j`, `μ + e_j`, `μ ⊔ 1`, and the list `opt_p(μ)`, `p = 1, …, L`, for `L ≥ 2ℓ(μ)`) and the tuple notation of `q_peeling_lemma.md`, part (iv).

## Setting

Let `h ≥ 1` and let `T` be a finite set with `|T| = 2h`, together with a fixed-point-free involution `u ↦ −u` (so `−(−u) = u` and `−u ≠ u`). Then `T` splits into `h` **classes** `{u, −u}`. (In the source, `T = F_q^×` with `q = 2h + 1` odd, and `u ↦ −u` is negation; only the involution is used here.)

**Residue partition.** For a tuple `M = (M_1, …, M_m) ∈ T^m` and a class `κ = {u, −u}`, let `a = #{i : M_i = u}` and `ā = #{i : M_i = −u}`. The **residue partition** `λ(M)` is the partition whose parts are the numbers `|a − ā|` over the classes `κ` with `a ≠ ā`, listed in weakly decreasing order. (It does not depend on which element of `κ` is called `u`.)

For `t ∈ T` and a tail `M' = (M_2, …, M_m) ∈ T^{m−1}` write `(t, M') := (t, M_2, …, M_m) ∈ T^m`.

For a set `Λ` of partitions put `F_Λ(μ) := #{p ∈ {1, …, 2h} : opt_p(μ) ∈ Λ}` (with `L = 2h`).

## Proposition

(i) For every `M ∈ T^m`: `ℓ(λ(M)) ≤ h` and `|λ(M)| ≡ m (mod 2)`. (In particular `L = 2h ≥ 2ℓ(λ(M))`, so `opt_p(λ(M))` is defined.)

(ii) For every tail `M' ∈ T^{m−1}` with `μ := λ(M')`, the multiset `{λ((t, M')) : t ∈ T}` (one entry for each of the `2h` elements `t`) equals the multiset `{opt_p(μ) : p = 1, …, 2h}`.

(iii) Consequently, for every set `Λ` of partitions and every tail `M'`: `#{t ∈ T : λ((t, M')) ∈ Λ} = F_Λ(λ(M'))`. In the notation of `q_peeling_lemma.md`, with `Z = Z_Λ := {M ∈ T^m : λ(M) ∈ Λ}`, this says `|F(M')| = F_Λ(λ(M'))`, and hence

`Z_{>i} = {M' ∈ T^{m−1} : F_Λ(λ(M')) > i}` for every `i ≥ 0`.

## Proof

(i) The classes with `a ≠ ā` are among the `h` classes, so there are at most `h` parts. And `|λ(M)| = Σ_κ |a − ā| ≡ Σ_κ (a + ā) = m (mod 2)`.

(ii) Let `ℓ := ℓ(μ)`. Let `κ_1, …, κ_ℓ` be the classes of `M'` with `a ≠ ā`, ordered so that `|a − ā|` on `κ_j` equals `μ_j`, and let `u_j ∈ κ_j` be the majority value (the element with the larger count). The remaining `h − ℓ` classes are **balanced** (`a = ā`, possibly `0 = 0`). Adding one value `t` changes only the counts of the class of `t`, by one:
- `t = −u_j`: the difference on `κ_j` drops from `μ_j` to `μ_j − 1`, and the other classes are unchanged, so `λ((t, M')) = μ − e_j` (a part `0` is dropped).
- `t = u_j`: the difference on `κ_j` rises to `μ_j + 1`, so `λ((t, M')) = μ + e_j`.
- `t` in a balanced class: that class gets difference `1`, so `λ((t, M')) = μ ⊔ 1`. There are `2(h − ℓ)` such `t`.

This lists `ℓ + ℓ + 2(h − ℓ) = 2h = |T|` values of `t`, each once, and the multiset of results is exactly `{μ − e_j}_{j ≤ ℓ} ∪ {μ + e_j}_{j ≤ ℓ} ∪ {μ ⊔ 1}^{×(2h − 2ℓ)}`, which is `{opt_p(μ) : p = 1, …, 2h}` by the definition of the list of options (with `L = 2h`).

(iii) Count the `t` with `λ((t, M')) ∈ Λ` using (ii). The fibre `F(M') = {t : (t, M') ∈ Z_Λ} = {t : λ((t, M')) ∈ Λ}` has `F_Λ(λ(M'))` elements, so `M' ∈ Z_{>i}` iff `F_Λ(λ(M')) > i`. ∎

## Checks

- Verified by exhaustive computer check for `h ≤ 3` and all tails of length `≤ 5`: 10 759 tails, 0 failures in (ii).
- `M'` empty (`m = 1`): `μ = ∅`, and every `t` gives `λ((t)) = (1) = ∅ ⊔ 1`, `2h` times.
