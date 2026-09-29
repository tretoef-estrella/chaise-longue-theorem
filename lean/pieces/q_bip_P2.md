# The layers are down-sets: options of pairs of partitions are monotone (§7.4 of the paper, Proposition 7.4)

This file uses, unchanged: `q_bip_setting.md` (pairs of partitions, `BPar_q(α, β)`, the product order `≼`, down-sets of `BPar_q(α, β)`), `q_bip_options.md` (the options `opt_p(μ)`, `F_Λ(μ)`, the layers `Λ_i`, and parts (i), (iii) of Lemma 7.3), `q_chain_lemma.md` (partitions, `S_t`, `≼`, `μ − e_j`, `μ + e_j`, `μ ⊔ 1`, the rows `r̄_j` (last row of the length of row `j`) and `r̲_j` (first row of that length), and its parts (a), (b)) and `q_P2_monotone_options.md` (the facts (T), (5.2) and the comparisons (a), (b), (c), (e2) of its proof).

## Setting

`q ≥ 3`, `α ≥ 1`, `β ≥ 0`. For a partition `λ`, `ℓ(λ)` is its length and `|λ|` its size.

**Facts from `q_P2_monotone_options.md`, valid for all partitions `λ ≼ λ̃` (no hypothesis on sizes, parities or lengths — its proofs of these facts compare the partial sums term by term and use only `λ ≼ λ̃`):**
- **(T)** If `t ≥ 1` is tight (`S_t(λ) = S_t(λ̃)`), then `λ_t ≥ λ̃_t` and `λ_{t+1} ≤ λ̃_{t+1}`.
- **(5.2)** If `ℓ(λ) ≤ t ≤ ℓ(λ̃)`, then `S_t(λ̃) ≥ |λ| + (t − ℓ(λ))`.
- **(a)** `λ − e_p ≼ λ̃ − e_p` for `1 ≤ p ≤ min(ℓ(λ), ℓ(λ̃))`.
- **(b)** `λ + e_j ≼ λ̃ + e_j` for `1 ≤ j ≤ min(ℓ(λ), ℓ(λ̃))`.
- **(c)** `λ ⊔ 1 ≼ λ̃ ⊔ 1`.
- **(e2)** `λ + e_j ≼ λ̃ ⊔ 1` for `ℓ(λ̃) < j ≤ ℓ(λ)`.

## Proposition 7.4

**(i)** If `μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then `opt_p(μ) ≼ opt_p(μ̃)` for every `p ∈ {1, …, q}`.

**(ii)** Consequently, for every down-set `Λ` of `BPar_q(α, β)`: if `μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then `F_Λ(μ) ≥ F_Λ(μ̃)`; and every layer `Λ_i = {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` is a down-set of `BPar_q(α − 1, β)`.

## Proof

Write `μ = (μ_+, μ_−)`, `μ̃ = (μ̃_+, μ̃_−)`, `ℓ_± := ℓ(μ_±)`, `ℓ̃_± := ℓ(μ̃_±)`. Both lie in `BPar_q(α − 1, β)`, so `|μ_+| − |μ_−| = |μ̃_+| − |μ̃_−|` (**transfer of sizes**: a strict inequality `|μ̃_−| > |μ_−|` gives `|μ̃_+| > |μ_+|`), `ℓ_+ + ℓ_− ≤ q` and `ℓ̃_+ + ℓ̃_− ≤ q`. The hypothesis `μ ≼ μ̃` means `μ_+ ≼ μ̃_+` and `μ_− ≼ μ̃_−`.

For each of `μ` and `μ̃`, a position `p` is a removal (R: `p ≤ ℓ_−`), a middle position (M: `ℓ_− < p ≤ q − ℓ_+`) or an addition (A: `p > q − ℓ_+`), and these three types partition `{1, …, q}`. This gives nine cases (the first letter for `μ`, the second for `μ̃`); for an addition put `j := q + 1 − p`.

- **RR** (`p ≤ min(ℓ_−, ℓ̃_−)`): first components `μ_+ ≼ μ̃_+`; second components `μ_− − e_p ≼ μ̃_− − e_p` by (a).
- **AA** (`j ≤ min(ℓ_+, ℓ̃_+)`): `μ_+ + e_j ≼ μ̃_+ + e_j` by (b); second components `μ_− ≼ μ̃_−`.
- **MM**: `μ_+ ⊔ 1 ≼ μ̃_+ ⊔ 1` by (c); `μ_− ≼ μ̃_−`.
- **RM** and **RA**: by Lemma 7.3(iii) (the chain) for `μ` and for `μ̃`, `opt_p(μ) ≼ μ ≼ μ̃ ≼ opt_p(μ̃)` — a removal of `μ` is `≼ μ` (it lies before the middle/additions in the chain of `μ`, and `(μ_+, μ_− − e_p) ≼ (μ_+, μ_−)` by part (a) of `q_chain_lemma.md`), and a middle or addition option of `μ̃` is `≽ μ̃`.
- **AM** (`j ≤ ℓ_+` and `ℓ̃_+ < j`): `μ_+ + e_j ≼ μ̃_+ ⊔ 1` by (e2); `μ_− ≼ μ̃_−`.
- **MA** (`j > ℓ_+`, `j ≤ ℓ̃_+`): we need `μ_+ ⊔ 1 ≼ μ̃_+ + e_j`. For `t ≤ ℓ_+`: `S_t(μ_+ ⊔ 1) = S_t(μ_+) ≤ S_t(μ̃_+) ≤ S_t(μ̃_+ + e_j)`. For `ℓ_+ < t ≤ ℓ̃_+`: `S_t(μ̃_+) ≥ |μ_+| + 1 = S_t(μ_+ ⊔ 1)` by (5.2). For `t > ℓ̃_+`: `S_t(μ̃_+ + e_j) = |μ̃_+| + 1 ≥ |μ_+| + 1 = S_t(μ_+ ⊔ 1)` (the added box is in row `r̲_j(μ̃_+) ≤ j ≤ ℓ̃_+ < t`, and `|μ̃_+| ≥ |μ_+|` by dominance at large `t`). Second components: `μ_− ≼ μ̃_−`.
- **MR** (`p > ℓ_−`, `p ≤ ℓ̃_−`): by (5.2) at `t = ℓ̃_−`, `|μ̃_−| ≥ |μ_−| + (ℓ̃_− − ℓ_−) ≥ |μ_−| + 1`, hence `|μ̃_+| ≥ |μ_+| + 1` (transfer of sizes). *First components*, `μ_+ ⊔ 1 ≼ μ̃_+`: for `t ≤ ℓ_+` this is dominance; for `t > ℓ_+` we need `S_t(μ̃_+) ≥ |μ_+| + 1`, which holds by (5.2) if `t ≤ ℓ̃_+` and by `|μ̃_+| ≥ |μ_+| + 1` if `t ≥ ℓ̃_+`. *Second components*, `μ_− ≼ μ̃_− − e_p`: for `t < r̄_p(μ̃_−)` this is `S_t(μ_−) ≤ S_t(μ̃_−) = S_t(μ̃_− − e_p)`; for `t ≥ r̄_p(μ̃_−) (≥ p > ℓ_−)`, `S_t(μ_−) = |μ_−|`, while the rows `ℓ_− + 1, …, p` of `μ̃_−` are non-empty, so `S_t(μ̃_−) ≥ S_{ℓ_−}(μ̃_−) + (p − ℓ_−) ≥ |μ_−| + 1`, i.e. `S_t(μ̃_− − e_p) = S_t(μ̃_−) − 1 ≥ |μ_−|`.
- **AR** (`j ≤ ℓ_+`, `p ≤ ℓ̃_−`): since `ℓ_+ + ℓ_− ≤ q` and `ℓ̃_+ + ℓ̃_− ≤ q`, we have `ℓ_− ≤ q − ℓ_+ < p` and `ℓ̃_+ ≤ q − ℓ̃_− ≤ q − p = j − 1`. *Second components:* exactly as in MR (it only used `ℓ_− < p ≤ ℓ̃_−`): `μ_− ≼ μ̃_− − e_p` and `|μ̃_−| ≥ |μ_−| + 1`, hence `|μ̃_+| ≥ |μ_+| + 1`. *First components:* we need `S_t(μ_+) + [t ≥ r̲_j(μ_+)] ≤ S_t(μ̃_+)` for all `t ≥ 1` (part (a) of `q_chain_lemma.md` for `μ_+ + e_j`). This is dominance for `t < r̲_j(μ_+)`, and it follows from `|μ̃_+| ≥ |μ_+| + 1` for `t ≥ ℓ̃_+` (then `S_t(μ̃_+) = |μ̃_+|` and `S_t(μ_+) ≤ |μ_+|`). It remains `S_t(μ_+) < S_t(μ̃_+)` for `r̲_j(μ_+) ≤ t < ℓ̃_+`. Suppose `t` is tight. The rows `r̲_j(μ_+), …, j` of `μ_+` all have length `c := μ_{+,j} ≥ 1`, and `t < t + 1 ≤ ℓ̃_+ ≤ j − 1`, so `μ_{+,t} = μ_{+,t+1} = c`. By (T), `c = μ_{+,t} ≥ μ̃_{+,t} ≥ μ̃_{+,t+1} ≥ μ_{+,t+1} = c`, so every row of `μ̃_+` after the `t`-th has length `≤ c`. As `μ̃_+` has only `ℓ̃_+ ≤ j − 1` rows, `S_j(μ̃_+) ≤ S_t(μ_+) + (j − 1 − t)c < S_t(μ_+) + (j − t)c = S_j(μ_+)`, contradicting `μ_+ ≼ μ̃_+`.

The nine cases cover every position, which proves (i).

(ii) Let `p` with `opt_p(μ̃) ∈ Λ`. By (i), `opt_p(μ) ≼ opt_p(μ̃)`, and `opt_p(μ) ∈ BPar_q(α, β)` by Lemma 7.3(i); since `Λ` is a down-set of `BPar_q(α, β)`, `opt_p(μ) ∈ Λ`. Hence `{p : opt_p(μ̃) ∈ Λ} ⊆ {p : opt_p(μ) ∈ Λ}` and `F_Λ(μ̃) ≤ F_Λ(μ)`. So if `μ̃ ∈ Λ_i` (i.e. `F_Λ(μ̃) > i`), `μ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then `F_Λ(μ) > i`, i.e. `μ ∈ Λ_i`; and `Λ_i ⊆ BPar_q(α − 1, β)` by definition. ∎

## Checks

- (i) for every comparable pair `μ ≼ μ̃` in `BPar_q(α − 1, β)`, `q ∈ {3, 5, 7}`, `1 ≤ α ≤ 5`, `0 ≤ β ≤ 5`, and every `p`: 6 491 pairs, 0 failures.
- Negative control (the transfer of sizes is needed): for comparable pairs of pairs of partitions whose size differences `|μ_+| − |μ_−|` and `|μ̃_+| − |μ̃_−|` differ (taken from `BPar_q(a, b)`, `a, b ≤ 3`, `q ∈ {3, 5}`), the conclusion of (i) fails for 183 of 770 pairs.
