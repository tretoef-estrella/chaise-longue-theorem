# The odd box: layers and roots

This file uses, unchanged:
- `q_oddbox_shapes.md`: the setting `T` (`OddShapes.OddSetting`: `|T| = r = 2h + 1`, an involution `u ↦ −u` with exactly one fixed point `0`), shapes `(λ, δ)` (`OddShapes.Shape`), the shape of a tuple (`OddSetting.shape`), the sets `Sh_m` (`OddShapes.Sh`), the list `optS_p(μ, δ)`, `p = 1, …, 2h + 1` (`OddShapes.optS`), the components `Λ^0`, `Λ^1` (`OddShapes.comp`), the function `F_Λ(μ, δ) = F_{Λ^δ}(μ) + [μ ∈ Λ^{1−δ}]` (`OddShapes.FS`), the point sets `Z_Λ` (`OddShapes.ZS`), interlaced pairs (`OddShapes.IsInterlaced`, with (D0), (D1), (D2)), and its results (B1)–(B5), (C1)–(C3); the partitions `∅` and `(1)` (`OddShapes.emptyPart`, `OddShapes.onePart`).
- `q_chain_lemma.md`: partitions, `ℓ(μ)`, the rows `μ_i`, `≼`, `μ − e_j`, `μ + e_j`, `μ ⊔ 1`, and its part (a): `μ − e_j` is `μ` with the **last** row of length `μ_j` lowered by one, the other rows in place (a row that becomes `0` is dropped); `μ + e_j` is `μ` with the **first** row of length `μ_j` raised by one, the other rows in place.
- `q_induction.md`, Step 1 (`Induction.FLam_le_FLam`): if `A` is a down-set of `Par_n` (`n ≥ 1`, `h ≥ 1`), and `λ, μ ∈ Par_{n−1}` with `λ ≼ μ`, then `F_A(μ) ≤ F_A(λ)`.
- `q_peeling_lemma.md`, part (iv): `Z_{>i}` (`Peel.Zgt`) and `|Z| = Σ_i |Z_{>i}|` (`Peel.card_eq_sum_Zgt`).
- `q_even_count.md`: the number `Q^e_k(m)` (`EvenCount.QkEven k m`), pointed point sets (`EvenCount.PointedSetting`), closed tuples (`EvenCount.closedPointed`) and Theorem (iii): the number of closed tuples of length `2k + 2` in a pointed point set with `2h + 1` elements is `Q^e_k(2h + 2)` (`EvenCount.card_closedPointed`).

It is the second piece of §8 of the paper (the odd box): Lemma 8.4 (the layers of an interlaced pair are interlaced pairs) and Lemma 8.5 (the roots and their count). Nothing here uses a field.

Throughout, `h ≥ 1`, `r = 2h + 1`, and `T` is as in `q_oddbox_shapes.md`.

## Part L. Layers

### Definition (layers)

For a set `Λ` of shapes, `m ≥ 1` and `i ≥ 0`:

`Λ_i := {σ ∈ Sh_{m−1} : F_Λ(σ) > i}`   (`layerS h m Λ i`).

### Theorem L

Let `m ≥ 1`.

**(L1) (monotone)** Let `Λ` be an interlaced pair of level `m`. If `(μ, δ)` and `(μ̃, δ)` lie in `Sh_{m−1}` (the same mark) and `μ ≼ μ̃`, then `F_Λ(μ̃, δ) ≤ F_Λ(μ, δ)`.

**(E)** Let `Λ` be an interlaced pair of level `m`, `(ν, δ) ∈ Sh_{m−1}`, `1 ≤ j ≤ ℓ(ν)` and `ν' := ν − e_j`. If `1 ≤ p ≤ 2h + 1` and `optS_p(ν, δ) ∈ Λ`, then there is `p'` with `p ≤ p' ≤ 2h + 1` and `optS_{p'}(ν', 1 − δ) ∈ Λ`.

**(L2)** Under the hypotheses of (E): `F_Λ(ν, δ) ≤ F_Λ(ν − e_j, 1 − δ)`.

**(L3) (Lemma 8.4 of the paper, first half)** If `Λ` is an interlaced pair of level `m`, then for every `i ≥ 0` the layer `Λ_i` is an interlaced pair of level `m − 1`. Moreover, for **every** set `Λ` of shapes: `Λ_{i+1} ⊆ Λ_i`, and `Λ_i = ∅` for `i ≥ 2h + 1`.

**(L4) (Lemma 8.4, second half)** For **every** set `Λ` of shapes and every `i ≥ 0`: `(Z_Λ)_{>i} = Z_{Λ_i}`, where `Z_Λ ⊆ T^m` and `Z_{Λ_i} ⊆ T^{m−1}`. (`Peel.Zgt (ZS S m Λ) i = ZS S (m − 1) (layerS h m Λ i)`.)

**(L5)** For every set `Λ` of shapes: `|Z_Λ| = Σ_{i=0}^{2h} |Z_{Λ_i}|`.

### Proofs

Write `A := Λ^δ` and `A' := Λ^{1−δ}`.

(L1) By (8.5), `F_Λ(μ, δ) = F_A(μ) + [μ ∈ A']`; compare the two summands separately.

*`δ = 0`.* Then `μ, μ̃ ∈ Par_{m−1}`, `A = Λ^0` is a down-set of `Par_m` and `A' = Λ^1` is a down-set of `Par_{m−1}` (D1). By Step 1 of `q_induction.md` (with `n = m`), `F_A(μ̃) ≤ F_A(μ)`. If `μ̃ ∈ A'` then `μ ∈ A'`, because `μ ∈ Par_{m−1}` and `μ ≼ μ̃`.

*`δ = 1`.* Then `m − 1 ≥ 1` and `μ, μ̃ ∈ Par_{m−2}`; `A = Λ^1` is a down-set of `Par_{m−1}` and `A' = Λ^0` is a down-set of `Par_m`. By Step 1 of `q_induction.md` (with `n = m − 1 ≥ 1`), `F_A(μ̃) ≤ F_A(μ)`. If `μ̃ ∈ A'` then `μ ∈ A'`, because `Par_{m−2} ⊆ Par_m` (`|μ| ≤ m − 2 ≤ m`, the same parity, `ℓ(μ) ≤ h`) and `μ ≼ μ̃`.

(E) Put `ℓ := ℓ(ν)`, `a := ν_j`, `ℓ' := ℓ(ν')`, `s_p := optS_p(ν, δ)` and `s'_p := optS_p(ν', 1 − δ)`. Let `j*` be the last row of `ν` of length `a`. By part (a) of `q_chain_lemma.md`, `ν'` is `ν` with the row `j*` lowered, the other rows in place: `ν'_i = ν_i` for `i ≠ j*`, and `ν'_{j*} = a − 1`. So `ℓ' = ℓ` if `a ≥ 2`; and if `a = 1`, then `j* = ℓ` and `ℓ' = ℓ − 1`. In both cases `ℓ' ≤ ℓ ≤ h`.

We use (D2) in this form: *if `(κ, ε) ∈ Λ`, then lowering any one row of `κ` (and re-sorting) and switching the mark gives a shape of `Λ`.* We also use that lowering or raising two **different** rows of a partition commutes (the result is the same multiset of parts), and that `μ − e_i` and `μ + e_i` depend only on the length `μ_i` of the row.

*Case 1: `p ≤ ℓ`* (a removal, `s_p = (ν − e_p, δ)`).

- *1a: `ν_p = a`.* Then `ν − e_p = ν − e_j = ν'`, so `(ν', δ) ∈ Λ`. But `(ν', δ) = s'_{ℓ'+1}` (the switch of the mark of `(ν', 1 − δ)`). Take `p' := ℓ' + 1`. If `a ≥ 2`, `p' = ℓ + 1 > p`. If `a = 1`, `p' = ℓ ≥ p`.
- *1b: `ν_p ≠ a`.* Let `p*` be the last row of `ν` of length `ν_p`; so `p ≤ p*`, `p* ≠ j*`, and `ν − e_p` is `ν` with the row `p*` lowered. The row `j*` is untouched, so `ν − e_p` still has a row of length `a`. Lowering it, (D2) gives `(κ', 1 − δ) ∈ Λ`, where `κ'` is `ν` with the two rows `p*` and `j*` lowered. On the other side, `ν'` (which is `ν` with the row `j*` lowered) has the row `p*` of length `ν_p` — note `p* ≤ ℓ'`: if `a = 1` then `j* = ℓ` and `p* < ℓ` — so `ν' − e_{p*} = κ'`, and `s'_{p*} = (κ', 1 − δ) ∈ Λ`. Take `p' := p* ≥ p`.

*Case 2: `p = ℓ + 1`* (`s_p = (ν, 1 − δ)`).

- *2a: `a ≥ 2`.* Raising the row `j*` of `ν'` (of length `a − 1`) gives back `ν`: `ν' + e_{j*} = ν`. So `(ν, 1 − δ) = s'_{p'}` with `p' := 2h + 2 − j*`, an addition position of `ν'` (`j* ≤ ℓ' = ℓ`). And `p' ≥ 2h + 2 − ℓ ≥ ℓ + 2 > p`, because `ℓ ≤ h`.
- *2b: `a = 1`.* Then `ν = ν' ⊔ 1` and `ℓ' = ℓ − 1`. The middle positions of `ν'` are `ℓ' + 1 < p' ≤ 2h + 1 − ℓ'`, that is `ℓ + 1 ≤ p' ≤ 2h + 2 − ℓ`; this range contains `ℓ + 1` because `ℓ ≤ h`. Take `p' := ℓ + 1 = p`: `s'_{p'} = (ν' ⊔ 1, 1 − δ) = (ν, 1 − δ) ∈ Λ`.

*Case 3: `ℓ + 1 < p ≤ 2h + 1 − ℓ`* (a middle position, `s_p = (ν ⊔ 1, δ)`; so `ℓ < h`). The partition `ν ⊔ 1` has a row of length `a`; lowering it gives `ν' ⊔ 1` (if `a = 1`: lowering a row of length `1` of `ν ⊔ 1` gives `ν`, and `ν = ν' ⊔ 1`). By (D2), `(ν' ⊔ 1, 1 − δ) ∈ Λ`. This is `s'_{p'}` for every middle position `p'` of `ν'`, `ℓ' + 1 < p' ≤ 2h + 1 − ℓ'`. Take `p' := 2h + 1 − ℓ'`: it is a middle position because `ℓ' ≤ ℓ < h`, and `p' ≥ 2h + 1 − ℓ ≥ p`.

*Case 4: `p > 2h + 1 − ℓ`* (an addition, `s_p = (ν + e_i, δ)` with `i := 2h + 2 − p`, `1 ≤ i ≤ ℓ`). Let `i_0` be the first row of `ν` of length `ν_i`; so `i_0 ≤ i`, and `ν + e_i` is `ν` with the row `i_0` raised.

- *4a: `ν_i ≠ a`, or `ν_i = a` and `i_0 < j*`* (in the second case there are at least two rows of length `a`). Then `i_0 ≠ j*`, and in `ν + e_i` the row `j*` still has length `a`. Lowering it, (D2) gives `(κ', 1 − δ) ∈ Λ`, where `κ'` is `ν` with the row `i_0` raised and the row `j*` lowered. On the other side `ν'` has the row `i_0` of length `ν_i` — note `i_0 ≤ ℓ'`: if `a = 1` then `j* = ℓ` and `i_0 < ℓ` — so `ν' + e_{i_0} = κ'`. Take `p' := 2h + 2 − i_0`: an addition position of `ν'`, with `s'_{p'} = (κ', 1 − δ) ∈ Λ` and `p' ≥ 2h + 2 − i = p`.
- *4b: `ν_i = a` and `i_0 = j*`* (the row `j*` is the only row of length `a`; so `i = j*`). `ν + e_i` is `ν` with the row `j*` raised to `a + 1`; lowering that row back, (D2) gives `(ν, 1 − δ) ∈ Λ`. If `a ≥ 2`: as in 2a, `(ν, 1 − δ) = s'_{p'}` with `p' := 2h + 2 − j* = p`. If `a = 1`: `j* = ℓ = i`, `ν = ν' ⊔ 1`, and `p' := 2h + 1 − ℓ' = 2h + 2 − ℓ = p` is a middle position of `ν'` (`p' > ℓ' + 1 = ℓ` because `ℓ ≤ h`), with `s'_{p'} = (ν' ⊔ 1, 1 − δ) = (ν, 1 − δ) ∈ Λ`.

(L2) By (C1), `(ν', 1 − δ) ∈ Sh_{m−1}`. Let `F := F_Λ(ν, δ)`. If `F = 0` there is nothing to prove. Otherwise, by (C2) for `(ν, δ)`, `s_F ∈ Λ` (`F ≤ 2h + 1`). By (E) there is `p' ≥ F` with `s'_{p'} ∈ Λ`. By (C2) for `(ν', 1 − δ)`, the positions `p'` with `s'_{p'} ∈ Λ` are `{1, …, F_Λ(ν', 1 − δ)}`; so `F ≤ p' ≤ F_Λ(ν', 1 − δ)`.

(L3) (D0): `Λ_i ⊆ Sh_{m−1}` by definition. (D1): `(Λ_i)^0 = {μ ∈ Par_{m−1} : F_Λ(μ, 0) > i}`, and if `λ ∈ Par_{m−1}`, `λ ≼ μ`, `μ ∈ (Λ_i)^0`, then `F_Λ(λ, 0) ≥ F_Λ(μ, 0) > i` by (L1). `(Λ_i)^1 = {μ : (μ, 1) ∈ Sh_{m−1}, F_Λ(μ, 1) > i}`, and `(μ, 1) ∈ Sh_{m−1}` iff `m − 1 ≥ 1` and `μ ∈ Par_{m−2}`; if `λ ∈ Par_{m−2}`, `λ ≼ μ` and `μ ∈ (Λ_i)^1`, then `m − 1 ≥ 1`, `(λ, 1) ∈ Sh_{m−1}` and `F_Λ(λ, 1) ≥ F_Λ(μ, 1) > i` by (L1). (For `m = 1` the set `(Λ_i)^1` is empty.) (D2): if `(ν, δ) ∈ Λ_i` and `1 ≤ j ≤ ℓ(ν)`, then `(ν − e_j, 1 − δ) ∈ Sh_{m−1}` by (C1) and `F_Λ(ν − e_j, 1 − δ) ≥ F_Λ(ν, δ) > i` by (L2).

`Λ_{i+1} ⊆ Λ_i` is clear. By (B5), `F_Λ(μ, δ) ≤ 2h + 1` whenever `ℓ(μ) ≤ h`; so `Λ_i = ∅` for `i ≥ 2h + 1`.

(L4) By (B4), `(Z_Λ)_{>i} = {M' ∈ T^{m−1} : F_Λ(shape of M') > i}`; and the shape of `M'` lies in `Sh_{m−1}` by (B1). So `M' ∈ (Z_Λ)_{>i}` iff the shape of `M'` lies in `Λ_i`.

(L5) By part (iv) of `q_peeling_lemma.md` for the set `T` with `2h + 1` elements (`Peel.card_eq_sum_Zgt` with `q = 2h + 2`): `|Z_Λ| = Σ_{i=0}^{2h} |(Z_Λ)_{>i}|`; then (L4).

## Part R. The roots

`∅` is the empty partition and `(1)` the partition with one part equal to `1`. Put `Λ^{ev} := {(∅, 0)}` and `Λ^{od} := {((1), 0), (∅, 1)}`. By (C3), `Λ^{ev}` is an interlaced pair at every even level and `Λ^{od}` at every odd level.

### Theorem R (Lemma 8.5 of the paper)

**(R1)** For every `n ≥ 0` and `M ∈ T^n`: the shape of `M` is `(∅, 0)` iff `cnt_M(u) = cnt_M(−u)` for every `u ∈ T` and `cnt_M(0)` is even. (So `Z_{Λ^{ev}}` is the set of the *closed* tuples of the pointed point set `T`.)

**(R2)** For every `k ≥ 0`: `|Z_{Λ^{ev}}| = Q^e_k(2h + 2)` at level `2k + 2`. (`(ZS S (2k+2) {(∅, false)}).card = EvenCount.QkEven k (2h + 2)`.)

**(R3)** For every shape `(μ, δ)` with `ℓ(μ) ≤ h`: `F_{Λ^{ev}}(μ, δ) = 1` if `(μ, δ) ∈ Λ^{od}`, and `= 0` otherwise. Hence, at every level `m = 2k + 2`: the layer `(Λ^{ev})_0` is `Λ^{od}`, and `(Λ^{ev})_i = ∅` for `i ≥ 1`.

**(R4)** For every `k ≥ 0`: `|Z_{Λ^{od}}| = Q^e_k(2h + 2)` at level `2k + 1`. (`(ZS S (2k+1) {((1), false), (∅, true)}).card = EvenCount.QkEven k (2h + 2)`.)

In the paper `Q^e_k(2h + 2)` is written `N_r(2k + 2)`, `r = 2h + 1`: the number of `(2k+2)`-tuples in `T` that split into pairs `{u, −u}` and `{0, 0}`.

### Proofs

(R1) The residue partition of `M` is formed by the positive values of the truncated differences `cnt_M(u) − cnt_M(−u)`, `u ∈ T`. It is `∅` iff all of them are `0`, that is `cnt_M(u) ≤ cnt_M(−u)` for every `u`; applying this to `u` and to `−u` (`−(−u) = u`) gives `cnt_M(u) = cnt_M(−u)` for every `u`. The mark is `0` iff `cnt_M(0)` is even.

(R2) `T` with `u ↦ −u` and `o := 0` is a pointed point set in the sense of `q_even_count.md` with `|T| = 2h + 1` (if `−u = u` then `u = 0`, because `−u ≠ u` for `u ≠ 0`). By (R1), `Z_{Λ^{ev}}` at level `2k + 2` is its set of closed tuples of length `2k + 2`, which has `Q^e_k(2h + 2)` elements by Theorem (iii) of `q_even_count.md`.

(R3) By (B5), `F_{Λ^{ev}}(μ, δ) = #{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) = (∅, 0)}`. An option `(μ ⊔ 1, δ)` or `(μ + e_j, δ)` has a non-empty partition. A removal `(μ − e_p, δ)`, `p ≤ ℓ(μ)`, equals `(∅, 0)` iff `δ = 0` and `μ − e_p = ∅`, that is `μ = (1)` and `p = 1`. The switch `(μ, 1 − δ)`, at the position `ℓ(μ) + 1`, equals `(∅, 0)` iff `μ = ∅` and `δ = 1`; then the position is `1`. So the number is `1` for `(μ, δ) = ((1), 0)` (here `ℓ = 1 ≤ h`), `1` for `(μ, δ) = (∅, 1)`, and `0` otherwise. For the layers at level `m = 2k + 2`: both shapes of `Λ^{od}` lie in `Sh_{2k+1}` (`1 ≤ 2k + 1` and `1` is odd; `ℓ((1)) = 1 ≤ h`), so `(Λ^{ev})_0 = Λ^{od}`; and no shape has `F > 1`, so `(Λ^{ev})_i = ∅` for `i ≥ 1`.

(R4) By (L5) for `Λ^{ev}` at level `m = 2k + 2` and (R3): `|Z_{Λ^{ev}}| = Σ_{i=0}^{2h} |Z_{(Λ^{ev})_i}| = |Z_{Λ^{od}}|`, the last set at level `2k + 1` (the other summands are `|Z_∅| = 0`). Then (R2). (In words: appending to a tuple with exactly one unpaired value, zero or not, the opposite of that value is a bijection onto the closed tuples of length `2k + 2`.)

## Remarks

1. (L3), (L4) and (R4) are what the induction of the paper (Theorem 8.11) needs from the point side: the layers of an interlaced pair are interlaced pairs of the previous level with `|Z_Λ| = Σ_i |Z_{Λ_i}|`, and the point set of the root has `N_r(2k + 2)` elements.
2. The proof of (D2) for the layers given here, through (E) and the chain (C2), is not the one printed in the paper (which compares the three kinds of options by counting, in two cases `ν_j ≥ 2`, `ν_j = 1`); the statement (L2) is the same.
3. Checked by brute force before this file was sent (`chkE7.py`, 120 checks, 0 failures): (L1), (L2), (E) with the explicit position `p'` of the proof, and (L3), for **all** 163 interlaced pairs with `(h, m)` up to `(1, 7)`, `(2, 6)`, `(3, 5)` (3 201, 1 476, 4 856 and 1 008 cases); (L4) and (L5) by points for every interlaced pair of 13 cells; (R1)–(R4) for `h ≤ 3` (`Q^e_k(2h + 2) = 3, 19, 141, 1107` for `h = 1`, `k = 0, …, 3`; `5, 61, 1001` for `h = 2`; `7, 127` for `h = 3`). Controls that fail as they should: layers defined without the zero option (18 of 18 cells); the unmarked half `{((1), 0)}` of the odd root alone has fewer points (7 of 7). Among the pairs of down-sets that do not satisfy (D2), (L2) fails and some layer is not an interlaced pair in 2 of 4, 3 of 6, 9 of 9, 17 of 17 and 11 of 11 (cells `(h, m) = (1,3), (1,4), (2,3), (2,4), (3,3)`): (D2) is needed.
