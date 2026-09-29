# The bipartite options, fibres and chain (§7.3 of the paper, Lemma 7.3)

This file uses, unchanged: `q_bip_setting.md` (`R_{α,β}`, shapes `λ(ξ, η) = (λ_+, λ_−)`, `BPar_q(α, β)`, the product order `≼`, down-sets of `BPar_q(α, β)`, `Z_Λ`, Lemma 7.1 with its fibres `F(M')` over the tails `M'`) and `q_chain_lemma.md` (partitions, `S_t`, `≼`, the operations `μ − e_j`, `μ + e_j`, `μ ⊔ 1` — remove a box from row `j`, add a box to row `j`, add a new row of length `1`, each followed by re-sorting — and its parts (a), (b)).

## Setting

`q ≥ 3`, `Ω` a finite set with `|Ω| = q`, `α ≥ 1`, `β ≥ 0`. A **tail** is `M' = (ξ', η) ∈ Ω^{α−1} × Ω^β` (the point with the first coordinate `ξ_1` removed); for `u ∈ Ω`, `(u, M')` is the point `((u, ξ'_1, …, ξ'_{α−1}), η)`.

For `μ = (μ_+, μ_−)` a pair of partitions with `ℓ_+ := ℓ(μ_+)`, `ℓ_− := ℓ(μ_−)` and `ℓ_+ + ℓ_− ≤ q`, the **options** `opt_p(μ)`, `p = 1, …, q`, are:
- `opt_p(μ) := (μ_+, μ_− − e_p)` for `1 ≤ p ≤ ℓ_−` (the **removals**);
- `opt_p(μ) := (μ_+ ⊔ 1, μ_−)` for `ℓ_− < p ≤ q − ℓ_+` (the **middle** positions);
- `opt_p(μ) := (μ_+ + e_{q+1−p}, μ_−)` for `q − ℓ_+ < p ≤ q` (the **additions**).

For a down-set `Λ` of `BPar_q(α, β)` put `F_Λ(μ) := #{p ∈ {1, …, q} : opt_p(μ) ∈ Λ}`.

## Lemma 7.3

Let `μ ∈ BPar_q(α − 1, β)` (so `ℓ_+ + ℓ_− ≤ q`).

**(i) (options stay in `BPar`)** `opt_p(μ) ∈ BPar_q(α, β)` for every `p ∈ {1, …, q}`.

**(ii) (fibres)** For every tail `M'` with shape `μ`, the multiset `{λ(u, M') : u ∈ Ω}` equals the multiset `{opt_p(μ) : p = 1, …, q}`. Consequently, for every down-set `Λ` of `BPar_q(α, β)`, `|F(M')| = F_Λ(μ)`, and `Z_{>i} = Z_{Λ_i}` with `Λ_i := {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` (the sets of Lemma 7.1(iv) and of `q_bip_setting.md`, with `α − 1` in place of `α`).

**(iii) (chain)** `opt_1(μ) ≼ opt_2(μ) ≼ ⋯ ≼ opt_q(μ)` in the product order. (This part only uses `ℓ_+ + ℓ_− ≤ q`.)

**(iv) (initial segment)** For every down-set `Λ` of `BPar_q(α, β)`, `{p : opt_p(μ) ∈ Λ} = {1, …, F_Λ(μ)}`.

**(v) (the three cases)** Let `Λ` be a down-set of `BPar_q(α, β)` and `Φ := F_Λ(μ) ≥ 1`. Then exactly one of the following holds:
- **(α)** `Φ > q − ℓ_+`. With `j_0 := q + 1 − Φ ∈ {1, …, ℓ_+}`: `(μ_+ + e_{j_0}, μ_−) = opt_Φ(μ) ∈ Λ`, and `j_0` is the first row of its length: `j_0 = 1` or `μ_{+, j_0 − 1} > μ_{+, j_0}`.
- **(β)** `ℓ_− < Φ ≤ q − ℓ_+`. Then `Φ = q − ℓ_+` (in particular `ℓ_+ + ℓ_− < q`) and `(μ_+ ⊔ 1, μ_−) = opt_Φ(μ) ∈ Λ`.
- **(γ)** `1 ≤ Φ ≤ ℓ_−`. With `r := Φ`: `(μ_+, μ_− − e_r) = opt_r(μ) ∈ Λ`, and `r` is the last row of its length: `r = ℓ_−` or `μ_{−, r+1} < μ_{−, r}`.

## Proofs

(i) Let `(λ_+, λ_−) := opt_p(μ)`. In every case `|λ_+| − |λ_−| = |μ_+| − |μ_−| + 1 = (α − 1 − β) + 1 = α − β` (a removal lowers `|μ_−|` by one, a middle or an addition raises `|μ_+|` by one), and `|λ_+| + |λ_−| = |μ_+| + |μ_−| ± 1 ≤ (α − 1 + β) + 1`. For lengths: a removal or an addition does not increase `ℓ_+ + ℓ_−`; a middle position exists only when `ℓ_− < q − ℓ_+`, i.e. `ℓ_+ + ℓ_− < q`, and then `ℓ(μ_+ ⊔ 1) + ℓ(μ_−) = ℓ_+ + 1 + ℓ_− ≤ q`.

(ii) Let `X(u)`, `Y(u)` be the counts of the tail. The values `u ∈ Ω` split into three disjoint groups: the `ℓ_−` values with `Y(u) > X(u)` (the rows of `μ_−`, value `v_j` giving the part `μ_{−,j}`), the `ℓ_+` values with `X(u) > Y(u)` (the rows of `μ_+`, value `u_j` giving `μ_{+,j}`), and the `q − ℓ_+ − ℓ_−` values with `X(u) = Y(u)`. Adding `u` as the new first coordinate of `ξ` raises `X(u)` by one and leaves the other counts unchanged. If `u = v_j`, the part `μ_{−,j}` of `λ_−` becomes `μ_{−,j} − 1` (and disappears if it was `1`), so the shape is `(μ_+, μ_− − e_j)`; if `u = u_j`, the part `μ_{+,j}` becomes `μ_{+,j} + 1`: `(μ_+ + e_j, μ_−)`; otherwise a new part `1` appears in `λ_+`: `(μ_+ ⊔ 1, μ_−)`. Matching `v_j ↔ p = j` (`1 ≤ j ≤ ℓ_−`), `u_j ↔ p = q + 1 − j` (`1 ≤ j ≤ ℓ_+`) and the `q − ℓ_+ − ℓ_−` values of the third group with the middle positions gives a bijection `Ω → {1, …, q}` under which `λ(u, M') = opt_p(μ)`. Hence `|F(M')| = #{u : λ(u, M') ∈ Λ} = #{p : opt_p(μ) ∈ Λ} = F_Λ(μ)`, and `Z_{>i} = {M' : F_Λ(λ(M')) > i} = Z_{Λ_i}` (every tail has its shape in `BPar_q(α − 1, β)` by Lemma 7.2(0)).

(iii) By parts (a)/(b) of `q_chain_lemma.md` (identities valid for every partition): `μ_− − e_1 ≼ μ_− − e_2 ≼ ⋯ ≼ μ_− − e_{ℓ_−} ≼ μ_−` and `μ_+ ≼ μ_+ ⊔ 1 ≼ μ_+ + e_{ℓ_+} ≼ ⋯ ≼ μ_+ + e_1`. Along the removals the first component is the constant `μ_+`; along the middle positions and the additions the second component is the constant `μ_−`; and at the step from the last removal (or from `μ` itself if `ℓ_− = 0`) to the first middle or addition option, `(μ_+, μ_− − e_{ℓ_−}) ≼ (μ_+, μ_−) ≼ (μ_+ ⊔ 1, μ_−)` and `(μ_+, μ_−) ≼ (μ_+ + e_{ℓ_+}, μ_−)`. Consecutive options are equal inside the middle block. So each step of the list is `≼`.

(iv) By (iii) and (i), if `opt_p(μ) ∈ Λ` and `p' ≤ p`, then `opt_{p'}(μ) ≼ opt_p(μ)` and `opt_{p'}(μ) ∈ BPar_q(α, β)`, hence `opt_{p'}(μ) ∈ Λ`. So `{p : opt_p(μ) ∈ Λ}` is an initial segment of `{1, …, q}`, of cardinality `F_Λ(μ)`.

(v) By (iv), `opt_Φ(μ) ∈ Λ` and `opt_{Φ+1}(μ) ∉ Λ` if `Φ < q`. The three ranges of `Φ` are disjoint and cover `{1, …, q}`. (α): `opt_Φ(μ) = (μ_+ + e_{j_0}, μ_−)`. If `j_0 ≥ 2`, then `Φ + 1 ≤ q` is also an addition, `opt_{Φ+1}(μ) = (μ_+ + e_{j_0 − 1}, μ_−) ∉ Λ`; if `μ_{+, j_0 − 1} = μ_{+, j_0}`, the two partitions `μ_+ + e_{j_0 − 1}` and `μ_+ + e_{j_0}` coincide after re-sorting, a contradiction. (β): all middle options are equal to `(μ_+ ⊔ 1, μ_−) ∈ Λ`, so by (iv) every middle position lies in the segment, `Φ ≥ q − ℓ_+`, hence `Φ = q − ℓ_+`. (γ): `opt_r(μ) = (μ_+, μ_− − e_r)`. If `r < ℓ_−`, then `opt_{r+1}(μ) = (μ_+, μ_− − e_{r+1}) ∉ Λ`; if `μ_{−, r+1} = μ_{−, r}`, then `μ_− − e_{r+1} = μ_− − e_r` after re-sorting, a contradiction. ∎

## Checks

- (i) and (ii), comparing the two multisets at every tail, `q ∈ {3, 5}`, `1 ≤ α ≤ 3`, `0 ≤ β ≤ 3`: 5 356 tails, 0 failures.
- (iii), every `μ ∈ BPar_q(α, β)`, `q ∈ {3, 5, 7}`, `α, β ≤ 4`: 532 shapes, 0 failures.
- (iv) and (v), every down-set `Λ` of `BPar_q(α, β)` (for the cells with `|BPar_q(α, β)| ≤ 16`, `q ∈ {3, 5, 7}`, `1 ≤ α ≤ 4`, `β ≤ 4`) and every `μ ∈ BPar_q(α − 1, β)`: 3 793 pairs, 0 failures.
