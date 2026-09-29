# Options are monotone in the partition (weak dominance)

This file continues `q_chain_lemma.md` and uses its **Setting** unchanged: partitions `μ = (μ_1 ≥ ⋯ ≥ μ_ℓ)` with `μ_i = 0` for `i > ℓ`, `S_t(μ) = μ_1 + ⋯ + μ_t`, weak dominance `λ ≼ μ` iff `S_t(λ) ≤ S_t(μ)` for all `t ≥ 1`, the options `μ − e_j`, `μ + e_j`, `μ ⊔ 1`, the rows `r̄_j`, `r̲_j`, and the list `opt_p(μ)`, `p = 1, …, L`, defined for `L ≥ 2ℓ(μ)`. Write `|μ| := μ_1 + ⋯ + μ_ℓ`.

## Proposition

Let `h ≥ 1` and `L := 2h`. Let `μ, μ̃` be partitions with `ℓ(μ) ≤ h`, `ℓ(μ̃) ≤ h`, `|μ| ≡ |μ̃| (mod 2)` and `μ ≼ μ̃`. Then `opt_p(μ) ≼ opt_p(μ̃)` for every `p = 1, …, L`.

**Corollary.** For every down-set `Λ` of partitions, `#{p : opt_p(μ̃) ∈ Λ} ≤ #{p : opt_p(μ) ∈ Λ}`. Consequently, for every `i ≥ 0`, the set `{μ : ℓ(μ) ≤ h, |μ| ≡ N (mod 2), #{p : opt_p(μ) ∈ Λ} > i}` is a down-set within the partitions of length `≤ h` and size `≡ N (mod 2)`, for any fixed `N`.

(Both hypotheses matter. `ℓ, ℓ̃ ≤ h` makes `L = 2h ≥ 2ℓ, 2ℓ̃`. Without the parity hypothesis the statement is false, for example for `h = 1`, `μ = ∅`, `μ̃ = (1)`: position 1 gives `(1)` against `∅`.)

## Proof

Write `ℓ = ℓ(μ)`, `ℓ̃ = ℓ(μ̃)`, and mark with a tilde the quantities of `μ̃`. Two facts are used throughout.

- **(T)** If `t ≥ 1` is **tight**, i.e. `S_t(μ) = S_t(μ̃)`, then `μ_t ≥ μ̃_t` (from `S_{t−1}(μ) ≤ S_{t−1}(μ̃)`) and `μ_{t+1} ≤ μ̃_{t+1}` (from `S_{t+1}(μ) ≤ S_{t+1}(μ̃)`).
- **(G)** By part (a) of `q_chain_lemma.md`, each comparison below reads `S_t(μ) + δ ≤ S_t(μ̃) + δ̃` with `δ, δ̃ ∈ {−1, 0, 1}`. Since `S_t(μ) ≤ S_t(μ̃)`, if `δ − δ̃ ≤ 1` it can only fail at a tight `t` with `δ = δ̃ + 1`. The one place where `δ − δ̃ = 2` is possible is (d1).

Also, if `ℓ < t ≤ ℓ̃`, the rows `ℓ + 1, …, t` of `μ̃` are non-empty, so

`S_t(μ̃) ≥ S_ℓ(μ̃) + (t − ℓ) ≥ S_ℓ(μ) + (t − ℓ) = |μ| + (t − ℓ)`.   (5.2)

**Layout.** Positions `p ≤ ℓ` are removals of `μ`, the last `ℓ` positions are additions of `μ`, and the positions in between are `μ ⊔ 1`; likewise for `μ̃`. Since `ℓ + ℓ̃ ≤ 2h = L`, a removal of one partition is never at the same position as an addition of the other. So every position falls in exactly one of the following cases (with `j := L + 1 − p` for the addition positions):

| case | positions | option of `μ` | option of `μ̃` |
|---|---|---|---|
| (a) | `p ≤ min(ℓ, ℓ̃)` | `μ − e_p` | `μ̃ − e_p` |
| (b) | `j ≤ min(ℓ, ℓ̃)` | `μ + e_j` | `μ̃ + e_j` |
| (c) | middle of both | `μ ⊔ 1` | `μ̃ ⊔ 1` |
| (d1) | `ℓ < p ≤ ℓ̃` | `μ ⊔ 1` | `μ̃ − e_p` |
| (d2) | `ℓ < j ≤ ℓ̃` | `μ ⊔ 1` | `μ̃ + e_j` |
| (e1) | `ℓ̃ < p ≤ ℓ` | `μ − e_p` | `μ̃ ⊔ 1` |
| (e2) | `ℓ̃ < j ≤ ℓ` | `μ + e_j` | `μ̃ ⊔ 1` |

*(a)* We need `S_t(μ) − [t ≥ r̄_p] ≤ S_t(μ̃) − [t ≥ r̄̃_p]`. The only danger is a tight `t` with `r̄̃_p ≤ t < r̄_p`. Then `t ≥ p`, and rows `p, …, t+1` of `μ` have length `μ_p`, so `μ_t = μ_{t+1} = μ_p`. Since `t + 1 > r̄̃_p`, `μ̃_{t+1} < μ̃_p`. By (T), `μ̃_{t+1} ≥ μ_{t+1} = μ_t ≥ μ̃_t ≥ μ̃_{t+1}`, so `μ̃_t = μ̃_{t+1} = μ_p` and `μ̃_p > μ_p`. Hence `S_t(μ̃) − S_{p−1}(μ̃) = Σ_{s=p}^{t} μ̃_s ≥ μ̃_p + (t − p)μ_p > (t − p + 1)μ_p = S_t(μ) − S_{p−1}(μ)`. With tightness at `t`, `S_{p−1}(μ̃) < S_{p−1}(μ)`, contradicting `μ ≼ μ̃`.

*(b)* We need `S_t(μ) + [t ≥ r̲_j] ≤ S_t(μ̃) + [t ≥ r̲̃_j]`. The only danger is a tight `t` with `r̲_j ≤ t < r̲̃_j`. Then `t < j`, so `μ_t = μ_{t+1} = μ_j`, and `μ̃_t > μ̃_j`. By (T), `μ̃_{t+1} ≥ μ_{t+1} = μ_j = μ_t ≥ μ̃_t ≥ μ̃_{t+1}`, so `μ̃_t = μ̃_{t+1} = μ_j > μ̃_j`. Every `μ̃_s` with `s > t` is `≤ μ_j`, and `μ̃_j < μ_j`, so `Σ_{s=t+1}^{j} μ̃_s < (j − t)μ_j = Σ_{s=t+1}^{j} μ_s`. With tightness, `S_j(μ̃) < S_j(μ)`, a contradiction.

*(c)* We need `S_t(μ) + [t > ℓ] ≤ S_t(μ̃) + [t > ℓ̃]`. If `ℓ ≥ ℓ̃` this is immediate. If `ℓ < t ≤ ℓ̃`, (5.2) gives `S_t(μ̃) ≥ |μ| + 1 = S_t(μ) + 1`.

*(d1) `ℓ < p ≤ ℓ̃`.* We need `S_t(μ) + [t > ℓ] ≤ S_t(μ̃) − [t ≥ r̄̃_p]`. Check every `t`:
- `t ≤ ℓ`: both brackets are `0` (`r̄̃_p ≥ p > ℓ ≥ t`).
- `t ≥ ℓ̃`: `S_t(μ̃) = |μ̃| ≥ |μ| + 1` by (5.2) at `t = ℓ̃`; by parity `|μ̃| ≥ |μ| + 2`, which suffices.
- `ℓ + 2 ≤ t < ℓ̃`: `S_t(μ̃) ≥ |μ| + 2` by (5.2).
- `t = ℓ + 1 < ℓ̃`: if `t < r̄̃_p`, (5.2) suffices. If `t ≥ r̄̃_p`, then `r̄̃_p = p = ℓ + 1` and we need `S_{ℓ+1}(μ̃) ≥ |μ| + 2`. If `μ̃_{ℓ+1} ≥ 2` this holds, since `S_ℓ(μ̃) ≥ |μ|`. If `μ̃_{ℓ+1} = 1`, then row `ℓ + 2 ≤ ℓ̃` of `μ̃` also has length `1`, so `r̄̃_{ℓ+1} ≥ ℓ + 2 > t`, a contradiction.

*(d2) `ℓ < j ≤ ℓ̃`.* We need `S_t(μ) + [t > ℓ] ≤ S_t(μ̃) + [t ≥ r̲̃_j]`. For `t ≤ ℓ` it is immediate. For `ℓ < t ≤ ℓ̃` it follows from (5.2), and for `t > ℓ̃` from `|μ̃| ≥ |μ| + 1` ((5.2) at `t = ℓ̃`).

*(e1) `ℓ̃ < p ≤ ℓ`.* `μ − e_p ≼ μ ≼ μ̃ ≼ μ̃ ⊔ 1`, by part (a) of `q_chain_lemma.md`.

*(e2) `ℓ̃ < j ≤ ℓ`.* We need `S_t(μ) + [t ≥ r̲_j] ≤ S_t(μ̃) + [t > ℓ̃]`. For `t > ℓ̃` it is immediate. For `t ≤ ℓ̃` with `t ≥ r̲_j`, suppose `t` is tight. Then `r̲_j ≤ t ≤ ℓ̃ < j`, so `μ_t = μ_{t+1} = μ_j ≥ 1`. By (T), `μ̃_t ≤ μ_t = μ_j`, so `μ̃_s ≤ μ_j` for every `s ≥ t`, and `μ̃_j = 0` because `j > ℓ̃`. Hence `Σ_{s=t+1}^{j} μ̃_s < (j − t)μ_j = Σ_{s=t+1}^{j} μ_s`, and with tightness `S_j(μ̃) < S_j(μ)`, a contradiction.

The degenerate cases `ℓ = 0`, `ℓ̃ = 0`, `ℓ = h` and `ℓ̃ = h` are included (some cases are then empty). ∎

*Proof of the Corollary.* If `opt_p(μ̃) ∈ Λ`, then `opt_p(μ) ≼ opt_p(μ̃)` gives `opt_p(μ) ∈ Λ`. So `#{p : opt_p(μ̃) ∈ Λ} ≤ #{p : opt_p(μ) ∈ Λ}`. If `μ ≼ μ̃` (with the length and parity conditions) and `μ̃` lies in the set for `i`, then so does `μ`. ∎

## Checks

- Verified by exhaustive computer check for `h ≤ 4` and parts `≤ 6`: 11 541 pairs `μ ≼ μ̃`, 0 failures. Dropping the parity hypothesis gives failures (24 pairs for `h ≤ 3`, parts `≤ 4`).
