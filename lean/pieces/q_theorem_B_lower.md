# Theorem B, lower bound: dim (D_J : J) ≥ Q_k(q)

This file assembles, unchanged: `q_peeling_lemma.md` (`C_m`), `q_chain_lemma.md` (partitions, `≼`), `q_P1_fibres.md` (the involution on `T`, `λ(M)`), `q_P3_identities.md` (`D`, tight patterns, `V_Λ`), `q_P3_lifts.md` (`Par_n`, down-sets of `Par_n`) and `q_induction.md` (the Theorem `dim V_Λ ≥ |Z_Λ|`).

## Setting

Let `F` be a field, `q ≥ 3` odd, `h := (q − 1)/2`, `k ≥ 0`, `n' := 2k + 1`, `N := 2k + 2`, and `C := C_{n'} = F[y_1, …, y_{n'}]/(y_i^{q−1})`.

**Matchings.** `𝒥` is the set of perfect matchings of `{0, 1, …, 2k+1}` (partitions into `k + 1` pairs; equivalently fixed-point-free involutions). For `J ∈ 𝒥`,

`D_J := Π_{{a<b} ∈ J, a ≠ 0} D(y_a, y_b) ∈ C`

(the product over the `k` pairs of `J` that avoid `0`; the empty product is `1`). Let `(D_J : J ∈ 𝒥) ⊆ C` be the ideal they generate.

**The number `Q_k(q)`.** `Q_k(q) := Σ N! / Π_{u=1}^{h} (b_u!)^2`, the sum over all `(b_1, …, b_h) ∈ ℕ^h` with `2(b_1 + ⋯ + b_h) = N`. (Equivalently `Q_k(q) = N!·[x^N] I_0(2x)^h` with `I_0(2x) = Σ_b x^{2b}/(b!)^2`.)

**Point sets.** Let `T` be a finite set with a fixed-point-free involution `u ↦ −u`, `|T| = 2h` (such a `T` exists, e.g. `T = {1, …, h} × {±1}` with `(u, ε) ↦ (u, −ε)`). For a tuple `M` with entries in `T`, and a class `κ = {u, −u}`, let `a_κ(M)`, `ā_κ(M)` be the numbers of entries equal to `u` and to `−u`, and

`ν(M) := Σ_κ min(a_κ(M), ā_κ(M))`   (the largest number of disjoint pairs of indices whose entries are negatives of each other).

A tuple is **closed** if `a_κ = ā_κ` for every class. Put `Γ' := {M ∈ T^{n'} : ν(M) = k}`.

## Theorem

**(i) (the root, Lemma 5.2 of the paper)** In `Par_{n'}`, `Λ := {(1)}` is a down-set; `V_{(1)} = (D_J : J ∈ 𝒥)`; and `Z_{(1)} = Γ'`.

**(ii) (Lemma 2.2)** The number of closed tuples in `T^N` is `Q_k(q)`.

**(iii) (Lemma 3.1)** `|Γ'| = Q_k(q)`.

**(iv) (Theorem B, lower bound)** `dim_F (D_J : J ∈ 𝒥) ≥ Q_k(q)`, for every field `F`, every odd `q ≥ 3` and every `k ≥ 0`.

## Proof

(i) If `λ ≼ (1)` then `S_t(λ) ≤ 1` for all `t`, so `|λ| ≤ 1`; for `λ ∈ Par_{n'}`, `|λ|` is odd, so `λ = (1)`. Hence `{(1)}` is a down-set of `Par_{n'}` (and `(1) ∈ Par_{n'}` since `h ≥ 1`). A tight pattern of `(1)` on `{1, …, n'}` consists of `k` disjoint pairs `P` and one block of size `1` (Vandermonde `= 1`), covering `{1, …, n'} ∖ {c}` and `{c}`; its product is `D_P := Π_{{a<b}∈P} D(y_a, y_b)`. Adding the pair `{0, c}` to `P` gives a matching `J ∈ 𝒥` with `D_J = D_P`, and every `J ∈ 𝒥` arises this way (from its pair through `0`). So the generators of `V_{(1)}` and of `(D_J)` are the same set, and the ideals are equal. Finally, by the definition of `λ(M)` in `q_P1_fibres.md`, `|λ(M)| = Σ_κ |a_κ − ā_κ| = n' − 2ν(M)`, and `λ(M) = (1)` iff exactly one class is unbalanced, by one; for `M ∈ T^{n'}` this is equivalent to `|λ(M)| = 1`, i.e. `ν(M) = k` (since `|λ(M)| ≡ n'` is odd, `|λ(M)| = 1` forces a single part `1`). So `Z_{(1)} = Γ'`.

(ii) A closed `N`-tuple is determined by choosing, for each class `κ`, the number `b_κ` of entries equal to `u` (equal to the number equal to `−u`), with `Σ_κ 2 b_κ = N`, and then the positions: `N! / Π_κ (b_κ!)^2` ways (a multinomial coefficient). Summing gives `Q_k(q)`.

(iii) Bijection `Γ' → {closed tuples in T^N}`: if `ν(M) = k` for `M ∈ T^{n'}`, exactly one class is unbalanced, by exactly one, with majority value `w`; appending `−w` as the last entry gives a closed `N`-tuple. Conversely, deleting the last entry `z` of a closed `N`-tuple leaves a tuple in `T^{n'}` with `ν = k` whose unbalanced value is `−z`. These maps are mutually inverse. By (ii), `|Γ'| = Q_k(q)`.

(iv) By (i), the Theorem of `q_induction.md` with `m = n'` and `Λ = {(1)}`, and (iii): `dim_F (D_J) = dim_F V_{(1)} ≥ |Z_{(1)}| = |Γ'| = Q_k(q)`. ∎

## Checks

- Exact linear algebra over `F_101` and enumeration: `(k, q) ∈ {(0,3), (0,5), (1,3), (1,5), (1,7), (2,3), (2,5), (3,3)}`: `dim (D_J) = Q_k(q) = |Γ'| = #closed N-tuples` = `2, 4, 6, 36, 90, 20, 400, 70`; 0 failures (equality holds; only `≥` is claimed here).
- Table of the paper: `Q_1(9) = 168`, `Q_2(5) = 400`, `Q_k(3) = C(2k+2, k+1)`.
