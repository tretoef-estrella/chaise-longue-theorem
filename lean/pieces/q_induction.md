# The induction: dim V_Λ ≥ |Z_Λ|

This file assembles, unchanged:
- `q_peeling_lemma.md`: `C_m`, the slices `W_j(V)`, parts (iii) `dim V = Σ_{j=0}^{q−2} dim W_j(V)` and (iv) `|Z| = Σ_{i=0}^{q−2} |Z_{>i}|` (for `|T| = q − 1`), with the fibres `F(M')` and `Z_{>i}` of tails `M' ∈ T^{m−1}`;
- `q_chain_lemma.md` and `q_P2_monotone_options.md`: partitions, `≼`, `opt_p`, `|μ|`, and the Proposition of `q_P2_monotone_options.md`;
- `q_P1_fibres.md`: the finite set `T` with a fixed-point-free involution, `|T| = 2h`, the residue partition `λ(M)`, `F_Λ`, and its parts (i)–(iii);
- `q_P3_identities.md`: tight patterns and the ideals `V_Λ`;
- `q_P3_lifts.md`: `Par_n`, down-sets of `Par_n`, the layers `Λ_i`, and its Proposition `V_{Λ_i} ⊆ W_{q−2−i}(V_Λ)`.

## Setting

Let `F` be a field, `q ≥ 3` odd, `h := (q − 1)/2`, and `T` a finite set with a fixed-point-free involution `u ↦ −u` and `|T| = 2h = q − 1`. For `m ≥ 0` and a down-set `Λ` of `Par_m` put

`Z_Λ := {M ∈ T^m : λ(M) ∈ Λ}`,   `V_Λ ⊆ C_m` as in `q_P3_identities.md` (on all indices `1, …, m`).

## Theorem

For every `m ≥ 0` and every down-set `Λ` of `Par_m`:

`dim_F V_Λ ≥ |Z_Λ|`.

## Proof

Induction on `m`, with `F`, `q`, `T` fixed.

**Base `m = 0`.** `Par_0 = {∅}`, so `Λ = ∅` or `Λ = {∅}`. If `Λ = ∅`, both sides are `0`. If `Λ = {∅}`, the empty tight pattern has product `1`, so `V_Λ = C_0 = F` has dimension `1`, and `Z_Λ = T^0` has one element.

**Step `m ≥ 1`.** Let `Λ` be a down-set of `Par_m` and `Λ_i := {μ ∈ Par_{m−1} : F_Λ(μ) > i}` for `0 ≤ i ≤ q − 2`.

1. *Each `Λ_i` is a down-set of `Par_{m−1}`.* Let `λ ∈ Par_{m−1}`, `μ ∈ Λ_i`, `λ ≼ μ`. Both have length `≤ h`, sizes `≡ m − 1 (mod 2)`, and `L = 2h`. By the Proposition of `q_P2_monotone_options.md`, `opt_p(λ) ≼ opt_p(μ)` for every `p`. All these options lie in `Par_m` (Step 0 of `q_P3_lifts.md`), so if `opt_p(μ) ∈ Λ` then `opt_p(λ) ∈ Λ` (down-set of `Par_m`). Hence `F_Λ(λ) ≥ F_Λ(μ) > i`, i.e. `λ ∈ Λ_i`. (This is the argument of the Corollary of `q_P2_monotone_options.md`, which only compares options; being a down-set *of `Par_m`* is enough.)

2. *The layers of `Z_Λ` are the `Z_{Λ_i}`.* By part (iii) of `q_P1_fibres.md`, `Z_{>i} = {M' ∈ T^{m−1} : F_Λ(λ(M')) > i}`. By part (i) of `q_P1_fibres.md`, `λ(M') ∈ Par_{m−1}` for every `M'`. Hence `Z_{>i} = Z_{Λ_i}`.

3. *Chain of (in)equalities.* By part (iii) of `q_peeling_lemma.md` (reindexing `j = q − 2 − i`), the Proposition of `q_P3_lifts.md`, the induction hypothesis (applicable by 1), step 2, and part (iv) of `q_peeling_lemma.md` (`|T| = q − 1`):

`dim V_Λ = Σ_{i=0}^{q−2} dim W_{q−2−i}(V_Λ) ≥ Σ_{i=0}^{q−2} dim V_{Λ_i} ≥ Σ_{i=0}^{q−2} |Z_{Λ_i}| = Σ_{i=0}^{q−2} |Z_{>i}| = |Z_Λ|`. ∎

(`V_{Λ_i}` lives in `C_{m−1}`, on its variables `y_2, …, y_m`, exactly as in `q_P3_lifts.md`; the induction hypothesis is applied to `C_{m−1}` with its own variables, so no relabelling is needed. The tails `M'` are the coordinates `2, …, m`, matching `consTuple` of `q_peeling_lemma.md`.)

## Checks

- Verified by exact linear algebra over `F_101` and enumeration of `T^m`, for every nonempty down-set `Λ` of `Par_m`, for `(q, m) ∈ {3} × {0..5} ∪ {5} × {0..4} ∪ {7} × {0..3}`: 35 cases, 0 failures of `≥`; in fact equality in all 35 (this is Theorem 5.9 of the paper, not needed here).
