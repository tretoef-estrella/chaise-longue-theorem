# Peeling one variable: a slicing lemma for ideals and point sets

## Setting

Let `F` be a field, `q ≥ 3` an integer, and `m ≥ 1` an integer. Put

`C_m := F[y_1, …, y_m] / (y_1^{q−1}, …, y_m^{q−1})`.

(The source works with odd `q`, but nothing below uses that `q` is odd; only `q ≥ 3` is used, so that `q − 2 ≥ 1`.)

Write `C_m = C_{m−1}[y_1]/(y_1^{q−1})`, where `C_{m−1}` is the analogous ring in the variables `y_2, …, y_m` (for `m = 1`, `C_0 = F`). Every `f ∈ C_m` has a unique expansion `f = Σ_{j=0}^{q−2} f_j y_1^j` with `f_j ∈ C_{m−1}`; write `[y_1^j] f := f_j` and `deg_{y_1} f := max{j : f_j ≠ 0}` (and `deg_{y_1} 0 := −∞`).

For an ideal `V ⊆ C_m` and `0 ≤ j ≤ q−2` put

`V_{≤j} := {f ∈ V : deg_{y_1} f ≤ j}`,   `W_j(V) := {[y_1^j] f : f ∈ V_{≤j}} ⊆ C_{m−1}`.

For the counting part, let `T` be a finite set with `|T| = q − 1`. For `Z ⊆ T^m` (tuples `(t_1, …, t_m)`), and for a tail `M' = (t_2, …, t_m) ∈ T^{m−1}`, put

`F(M') := {t ∈ T : (t, M') ∈ Z}`,   `Z_{>i} := {M' ∈ T^{m−1} : |F(M')| > i}`.

## Lemma (peeling)

(i) `W_j(V)` is an ideal of `C_{m−1}` for every `0 ≤ j ≤ q−2`.

(ii) `W_j(V) ⊆ W_{j+1}(V)` for `0 ≤ j < q−2`.

(iii) `dim_F V = Σ_{j=0}^{q−2} dim_F W_j(V)`. (All rings here are finite-dimensional over `F`.)

(iv) `|Z| = Σ_{i=0}^{q−2} |Z_{>i}|` for every `Z ⊆ T^m`.

## Proof

(i) For `g ∈ C_{m−1}` and `f ∈ V_{≤j}`: `gf ∈ V` (ideal), `deg_{y_1}(gf) ≤ j`, and `[y_1^j](gf) = g·[y_1^j] f`. Also `V_{≤j}` is an `F`-subspace containing `0`, and `f ↦ [y_1^j] f` is additive. So `W_j(V)` is an ideal.

(ii) If `f ∈ V_{≤j}` with `j + 1 ≤ q − 2`, then `y_1 f ∈ V`, `deg_{y_1}(y_1 f) ≤ j+1` (no wrap-around, since `y_1^{j+1} ≠ 0` in `C_m` when `j + 1 ≤ q − 2`), and `[y_1^{j+1}](y_1 f) = [y_1^j] f`. So `W_j(V) ⊆ W_{j+1}(V)`.

(iii) The `F`-linear map `V_{≤j} → W_j(V)`, `f ↦ [y_1^j] f`, is onto by definition, and its kernel is `V_{≤j−1}` (with `V_{≤−1} := 0`). Hence `dim V_{≤j} = dim V_{≤j−1} + dim W_j(V)`. Summing over `j = 0, …, q−2` and using `V = V_{≤q−2}` gives (iii).

(iv) `|Z| = Σ_{M' ∈ T^{m−1}} |F(M')|`. Since `0 ≤ |F(M')| ≤ |T| = q − 1`, the tail `M'` lies in `Z_{>i}` for exactly the `|F(M')|` values `i = 0, 1, …, |F(M')| − 1`, all of which are `≤ q − 2`. So `Σ_{i=0}^{q−2} |Z_{>i}| = Σ_{M'} |F(M')| = |Z|`. ∎

## Checks

- `m = 1`, `V = C_1`: `W_j(V) = F` for every `j`, and `dim V = q − 1`.
- `m = 1`, `V = (y_1^{q−2})`: `W_j(V) = 0` for `j < q−2` and `W_{q−2}(V) = F`, so `dim V = 1`.
- `Z = T^m`: `F(M') = T` for every tail, `Z_{>i} = T^{m−1}` for every `i ≤ q−2`, and `(q−1)·(q−1)^{m−1} = (q−1)^m`.
