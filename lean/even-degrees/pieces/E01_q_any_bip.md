# The bipartite count for every box `q ≥ 2` (§7 of the paper, version 11: Theorem 7.6 and Theorem C without the parity of `q`)

This file uses, unchanged:
- `q_bip_setting.md`: `R_{α,β}` (box exponent `q`), `x_i`, `z_l`, shapes `λ(ξ, η)`, `BPar_q(α, β)`, the product order `≼`, down-sets of `BPar_q(α, β)`, `Z_Λ`, tight patterns and their products, `V_Λ`, the root ideals `I^{bal}_a`, `I^{ph}_a`, the counts `N_{bal}`, `N_{ph}`, Lemma 7.1 and Lemma 7.2;
- `q_bip_options.md`: the options `opt_p(μ)`, `F_Λ(μ)`, the layers `Λ_i`, Lemma 7.3;
- `q_bip_P2.md`: Proposition 7.4;
- `q_bip_P3.md`: Proposition 7.5;
- `q_bip_induction.md`: Lemma S, Theorem 7.6, Theorem C.

Those files state everything for `q ≥ 3` odd. **The hypothesis «`q` odd» is never used in their proofs, except for one sign in Lemma S(iii), and `q ≥ 3` is used only through `q ≥ 2`.** This file states and proves the same theorems for every integer `q ≥ 2`, odd or even. The even case is needed: the paper (version 11, §9) applies Theorem C with `q = 2^v` over a field of characteristic `2`.

## Setting

`F` is a field and `q ≥ 2` is an integer such that the binomial coefficients `C(q−1, t)`, `0 ≤ t ≤ q − 1`, are non-zero in `F`. `Ω` is a finite set with `|Ω| = q`. All the objects (`R_{α,β}`, `BPar_q(α, β)`, `Z_Λ`, `V_Λ`, `I^{bal}_a`, `I^{ph}_a`, `N_{bal}(a, q)`, `N_{ph}(a, q)`, the slices `W_j`) are those of the files above, with this `q`. `dim V` is the `F`-dimension of an ideal `V`.

## Theorem 7.6′ (bipartite down-set theorem, every `q ≥ 2`)

For all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`:

`dim V_Λ ≥ |Z_Λ|`.

## Theorem C′ (the bipartite count, every `q ≥ 2`)

For every `a ≥ 0`: `dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`.

## Lemma P (the binomial coefficients at a prime power)

Let `p` be a prime (`p = 2` is allowed), `v ≥ 1`, `q = p^v`, and let `F` be a field of characteristic `p`. Then `C(q − 1, t) = (−1)^t` in `F` for `0 ≤ t ≤ q − 1`. In particular these binomial coefficients are non-zero in `F`.

## Corollary P (prime powers, the prime `2` included)

Let `p` be a prime, `v ≥ 1`, `q = p^v`, and let `F` be a field of characteristic `p`. Then for all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`, `dim V_Λ ≥ |Z_Λ|`; and for every `a ≥ 0`, `dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`. In particular this holds for `q = 2^v` and `F` of characteristic `2`, where the box `q` is even.

## Proofs

**Lemma P.** In `F[u]`, `(1 + u)^q = 1 + u^q`, because `q` is a power of the characteristic. So `C(q, s) = 0` in `F` for `0 < s < q`. Pascal's rule `C(q, t + 1) = C(q − 1, t) + C(q − 1, t + 1)` gives `C(q − 1, t + 1) = −C(q − 1, t)` in `F` for `0 ≤ t ≤ q − 2`. Since `C(q − 1, 0) = 1`, induction on `t` gives `C(q − 1, t) = (−1)^t`, which is non-zero in a field.

**What the earlier proofs use.** We go through the five files.

1. *Lemma 7.1 (peeling with the box `q`).* `R_{A,B} = R_{A∖{i_1},B}[w]/(w^q)`. That `W_j(V)` is an ideal, that `dim V = Σ_{j=0}^{q−1} dim W_j(V)` and that `|Z| = Σ_{i=0}^{q−1}|Z_{>i}|` hold for every `q ≥ 1`. The inclusion `W_j(V) ⊆ W_{j+1}(V)` for `0 ≤ j < q − 1` multiplies by `w` and uses `j + 1 ≤ q − 1`; for `q = 2` it is the single inclusion `W_0 ⊆ W_1`.

2. *Lemma 7.2 (the roots) and the counts.* Statements about pairs of tuples in a set `Ω` of `q` elements and about bijections; no condition on `q` beyond `q ≥ 1`.

3. *Lemma 7.3 (options, fibres, chain).* A tail of shape `μ = (μ_+, μ_−)` has `ℓ(μ_+) + ℓ(μ_−) ≤ q`; the `q` values of the new coordinate are the `ℓ_−` removals, the `q − ℓ_+ − ℓ_−` middle values and the `ℓ_+` additions. The chain `opt_1(μ) ≼ ⋯ ≼ opt_q(μ)` and the formula for `F_Λ(μ)` are statements about partitions and the product order. They hold for every `q ≥ 1`.

4. *Proposition 7.4 (the nine cases).* The proof compares partial sums of partitions and uses `ℓ_+ + ℓ_− ≤ q`, `ℓ̃_+ + ℓ̃_− ≤ q` and the equality `|μ_+| − |μ_−| = |μ̃_+| − |μ̃_−|`. Nothing depends on the parity of `q` or on `q ≥ 3`.

5. *Proposition 7.5 (the three lifts).* Cases (α) and (β) produce an element of `w`-degree `j_0 − 1`, respectively `ℓ_+`, which is at most `q − 1`. Case (γ) expands `(w − z_b)^{q−1}` by the binomial theorem and divides by `C(q − 1, r − 1)`, with `1 ≤ r ≤ ℓ_− ≤ q`; this is the hypothesis on `F`. The statement there «`q` is odd» is not used.

6. *Lemma S (the swap).* Parts (i) and (ii) are about pairs of partitions and points. Part (iii) says that the renaming isomorphism `σ : R_{α,β} → R_{β,α}` (`σ(x_i) = z_i`, `σ(z_l) = x_l`) satisfies `σ(V_Λ) = V_{Λ^⊤}`. Let `T` be a tight pattern of `λ = (λ_+, λ_−)` on `([α], [β])`, with pairs `P`, and `T^⊤` the transposed tight pattern of `λ^⊤` on `([β], [α])`. Then

`σ( Π_{(i,l)∈P}(x_i − z_l)^{q−1} · Π_c Δ(x_{B^+_c}) · Π_c Δ(z_{B^−_c}) ) = (−1)^{(q−1)·|P|} · Π_{(l,i)∈P^⊤}(x_l − z_i)^{q−1} · Π_c Δ(z_{B^+_c}) · Π_c Δ(x_{B^−_c})`,

because `(z_i − x_l)^{q−1} = (−1)^{q−1}(x_l − z_i)^{q−1}`. For odd `q` the sign is `+1`, which is how the earlier file argues. For even `q` the sign is `(−1)^{|P|}`. In both cases the image of a generator of `V_Λ` is `±` a generator of `V_{Λ^⊤}`, and `−1` is a unit, so `σ(V_Λ) ⊆ V_{Λ^⊤}`; applying this to `Λ^⊤` and to the inverse renaming gives equality. So `dim V_{Λ^⊤} = dim V_Λ` for every `q`.

**Theorem 7.6′.** Induction on `α + β`, exactly as for Theorem 7.6. *Base* `α = β = 0`: `BPar_q(0, 0) = {(∅, ∅)}`; for `Λ = ∅` both sides are `0`; for `Λ = {(∅, ∅)}`, `V_Λ = F` and `Z_Λ` is one point. *Step*, `α ≥ 1`: by items 1, 3, 4, 5 and the induction hypothesis for the layers `Λ_i`, which are down-sets of `BPar_q(α − 1, β)`,

`dim V_Λ = Σ_{i=0}^{q−1} dim W_{q−1−i}(V_Λ) ≥ Σ_{i=0}^{q−1} dim V_{Λ_i} ≥ Σ_{i=0}^{q−1} |Z_{Λ_i}| = Σ_{i=0}^{q−1} |Z_{>i}| = |Z_Λ|`.

*Step*, `α = 0` and `β ≥ 1`: apply the previous step to `Λ^⊤`, a down-set of `BPar_q(β, 0)`, and use item 6: `dim V_Λ = dim V_{Λ^⊤} ≥ |Z_{Λ^⊤}| = |Z_Λ|`.

**Theorem C′.** By Lemma 7.2, `{(∅, ∅)}` is a down-set of `BPar_q(a, a)` with `V = I^{bal}_a` and `|Z| = N_{bal}(a, q)`, and `{((1), ∅)}` is a down-set of `BPar_q(a + 1, a)` with `V = I^{ph}_a` and `|Z| = N_{ph}(a, q) = N_{bal}(a + 1, q)`. Apply Theorem 7.6′.

**Corollary P.** Lemma P gives the hypothesis on the binomial coefficients; `q = p^v ≥ 2`. Apply Theorems 7.6′ and C′.

## Remarks

1. For `q = 2` the ring is `F[x, z]/(x_i^2, z_l^2)`, `Ω` has two elements, and the generators of `I^{bal}_a` are the products `Π_i (x_i − z_{σ(i)})`. In characteristic `2`, `N_{bal}(a, 2) = C(2a, a)`: `2, 6, 20, 70` for `a = 1, 2, 3, 4`.
2. Checked by exact linear algebra before this file was written (two separate programs): `dim V_Λ = |Z_Λ|` at every down-set of `BPar_q(α, β)` over `F_2` for `q = 2` (nine cells `(α, β)` up to `α + β = 6`), `q = 4` (four cells) and `q = 8` (two cells), `51` down-sets of `51`; and `dim V_Λ ≥ |Z_Λ|` at every down-set for `q = 4` over `F_5` and `q = 6` over `F_7`. Roots: `dim I^{bal}_a = 2, 6, 20, 70` (`q = 2`), `4, 28, 256` (`q = 4`), `8, 120` (`q = 8`). With one bijection only instead of all, the dimension falls below the count (`4 < 6`, `16 < 28`, `64 < 120`).
