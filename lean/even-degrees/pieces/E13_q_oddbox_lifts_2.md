# The lifts of the odd box, second part: the three cases in which the marked block changes

Piece E13 of the plan for the even degrees. Source: paper v11, §8.6, proof of Proposition 8.10,
case (Z) with `δ = 1`, case (M) with `δ = 1`, and case (R) with `δ = 1` and `μ_ρ = 1`. The other
cases were done in piece E12 (folder `RequestProject/OddLifts/`). The case analysis of the
Proposition (by the chain) and its assembly are NOT part of this piece.

Everything is stated for a field `F`, an integer `h ≥ 0`, the odd number `r = 2h + 1` and
`q = r + 1 = 2h + 2`. The rings are `C_n = Peel.C F (2*h+2) n` (the box `y_i^r = 0`), with
`y_i = Tight.y F (2*h+2) i`.

**Indices.** As in `q_oddbox_lifts_1.md`: the level is `m = n + 1`; the new variable `y_1` of the
paper is `y_0` of `C_{n+1}`, and the old variables are the images under
`Peel.incl F (2*h+2) n`. For `B ⊆ Fin n`, `B^+ := Lifts.liftSet B`.

**Slices.** For an ideal `V` of `C_{n+1}` and `d ≤ 2h`,
`W_d(V) := Peel.W (m := n+1) _ V d`.

**Partitions.** `ChainLemma.Partition`. For a partition `μ` with `ℓ = μ.len` rows:
`μ ⊔ 1 := μ.addOne` (one more row equal to `1`), and `μ − e_ℓ := μ.subE μ.len` (the last row
lowered by one; when the last row is `1`, the row is dropped).

## What is used unchanged

- Everything listed in `q_oddbox_lifts_1.md`, and the whole folder `RequestProject/OddLifts/`
  (piece E12): `P1`, `P2`, `P3`, `L0a`, `L0b`, `L1`, `cleanMBlocks` and its lemmas,
  `prod_cleanMBlocks`, `mkMPattern`, `prod_mkMPattern`, `exists_mpattern_insert`,
  `exists_mpattern_pair`, `exists_mpattern_zero`, `markedPf_insert_zero`,
  `phi_markedPf_insert_zero`, `prod_eq_Delta_one_mul`, `mPf_expand`, `coeff_mPf_cons`, `map_Pfe`,
  `T1`–`T5`.
- `RequestProject/OddPatterns/` (piece E11): `mPf`, `map_mPf`, `mPf_cast`, `A1`, `A2`,
  `markedPf`, `MarkedPattern`, `MarkedPattern.prod`, `VS`, `VSAll`, `B4_tight`, `B4_marked`,
  and **`D3`** (Lemma 8.7 in the ring: for `1 ≤ h` and `|B| = ℓ + 1 + 2t`,
  `markedPf F h ℓ B ∈ Membership.UB (2h+1) (ℓ+1) y B`).
- `RequestProject/Pfaffian/`: `Pf`, `Pfe`, `ay`, `bpf`, `bmat`, `bpf_expand_var`,
  `bpf_expand_var_zero`, `bpf_expand_last`, `C1`, `C2`, `C3`, `C4`, `C4_eq_zero`, `C5`,
  `bpf_eq_zero_of_border_eq`, `bpf_snoc_add`, `bpf_snoc_sum`.
- `RequestProject/Membership/` (`UB`, `V2`), `RequestProject/Peel/` (`W_isIdeal`),
  `RequestProject/Chain/` (`Partition`, `addOne`, `subE`), `RequestProject/Tight/` (`colLen`).

## Part Q. The marked Pfaffian with one new variable, any block size

For a commutative ring `R`, natural numbers `h`, `l`, `n` and `w : Fin n → R`, put
`z := Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]` (the new variable first, as in
Lemma P of `q_oddbox_lifts_1.md`; there `n = l`).

**Lemma Q** (case (R) of the paper). Let `t` be a natural number, `n = l + 2 + 2t` and `l + 1 ≤ h`.
- **(Q1)** For every `k` with `2h − l < k`: `(OddPatterns.mPf h l z).coeff k = 0`.
- **(Q2)** `(OddPatterns.mPf h l z).coeff (2h − l) = (−1)^l · OddPatterns.mPf h (l + 1) w`.

(Paper: (F4) along the new variable and (F5). With `E = E_l`: the first term of (F4) is
`θ·Pf(w; y^E, D^−(X, ·))`, which by (C1) is `−θ Σ_{u ≤ r−2} (−1)^u X^{r−2−u} Pf(w; y^E, y^u)`; the
terms with `u ∈ E` vanish (`C4_eq_zero`), so its `X`-degree is at most `r − 2 − (l − 1) = 2h − l`
for `l ≥ 1` (the first `u ∉ E` is `u = l − 1`, and `Pf(w; y^{0}, …, y^{l−2}, y^{l−1})` is
`mPf h (l+1) w`), and at most `2h − 1` for `l = 0` (`E_0 = {2h}`). The other terms of (F4) are
`± X^{e} Pf(w; borders without e)` with `e ∈ E`: of degree at most `l − 2 < 2h − l` for `l ≥ 1`, and
for `l = 0` the single term `± X^{2h} Pf(w; no border) = ± X^{2h} mPf h 1 w`. The sign `(−1)^l` was
computed in the convention of this project; it does not depend on `t`.)

**Lemma Q′** (case (M) of the paper). Let `ℓ` and `t` be natural numbers, `n = ℓ + 1 + 2t`, `L = ℓ + 1`,
and let `E^+ : Fin ℓ → ℕ`, `E^+ k = k` (the borders of `mPf h L`, i.e. `0, …, ℓ − 1`). Put
`Φ := X · OddPatterns.mPf h L z + Pfaffian.Pf (2h+1) (fun i => C (w i))
        (Fin.snoc (fun k i => (C (w i)) ^ (E^+ k)) (fun b => ColOne.Dab (2h+2) X (C (w b))))`
(the second term is the bordered Pfaffian of `w` with the borders `y^0, …, y^{ℓ−1}` and the last
border `D(X, ·)`, where `D = ColOne.Dab (2h+2)`; `D^− = ColOne.Dab (2h+1)`). No hypothesis on `h`.
- **(Q′1)** For every `k` with `ℓ < k`: `Φ.coeff k = 0`.
- **(Q′2)** `Φ.coeff ℓ = OddPatterns.mPf h ℓ w`.

(Paper: `θ = (−1)^{0 + n + (L − 1)} = +1` is the sign of `bpf_expand_var` at `x = 0`, or of
`bpf_expand_var_zero` when `L = 1`; by (F4), `X·mPf h L z = θ·X·Pf(w; y^{E^+}, D^−(X, ·)) +
Σ_{e} ± X^{e+1} Pf(w; y^{E^+ ∖ e})`, and by (C3), `Pf(w; y^{E^+}, D(X, ·)) = Pf(w; y^{E^+}, y^{2h})
− X·Pf(w; y^{E^+}, D^−(X, ·))`. The two terms with `D^−(X, ·)` cancel, so
`Φ = Σ_{e ∈ E^+} ± X^{e+1} Pf(w; y^{E^+ ∖ e}) + Pf(w; y^{E^+}, y^{2h})`. For `ℓ ≥ 1` the top term is
`e = ℓ − 1`, with `Pf(w; y^0, …, y^{ℓ−2}) = mPf h ℓ w`; for `ℓ = 0`, `E^+ = ∅` and
`Φ = Pf(w; y^{2h}) = mPf h 0 w`. With the opposite sign in front of the second term the
cancellation fails.)

## Part T. The lifts

In all three, `Λ : Set OddShapes.Shape` is arbitrary, `T : OddPatterns.MarkedPattern μ Finset.univ`
is a marked pattern of `μ` on all the indices of `C_n`, `ℓ = μ.len`, and the conclusion is

`T.prod F h ∈ Peel.W (m := n+1) (by omega) (OddPatterns.VSAll F h (n+1) Λ) d`.

**(T6)** (the zero option of a marked shape; case (Z), `δ = 1`). Hypotheses: `(μ, false) ∈ Λ`,
`1 ≤ h`, `μ.len ≤ h`. Slice `d = 2h − μ.len`.

*Proof (auditor's).* Write `T.prod = Pf_{E_ℓ}(B_0) · G'` with `G' = D_P · Π_{c ≥ 2} Δ(B_c)`
(`prod_cleanMBlocks`). Let `S ⊆ B_0` with `|S| = ℓ + 1` and `Q` a set of pairs that partitions
`B_0 ∖ S`. Then the pairs `P ∪ Q`, the first block `S` and the blocks `B_c` (`c ≥ 2`) form a
**tight** pattern `T'` of `μ ⊔ 1 = μ.addOne` on `Finset.univ`, with product
`Δ(S) · D_Q · G'`. Since `colLen μ c + [c = 1] = colLen (μ.addOne) c` for every `c ≥ 1`,
`1 ≤ colLen (μ.addOne) 1 = ℓ + 1 ≤ 2h + 1`, **(T2)** of E12 applied to `T'`, `lam = μ`, `c0 = 1`
gives `Δ(S)·D_Q·G' ∈ W_{2h+1−(ℓ+1)}(V_Λ) = W_{2h−ℓ}(V_Λ)`. The slice is an ideal of `C_n`
(`Peel.W_isIdeal`, with `q = 2h + 2 ≥ 3` and `2h − ℓ ≤ q − 2`), so it contains
`Membership.UB (2h+1) (ℓ+1) y B_0 · G'` (the generators of `UB` are `vand y S · DPy (2h+1) y Q`,
and `DPy` is the product of the `D` over the pairs of `Q`; check the conventions of `DPy` against
`pairD`); by **`D3`** (with `|B_0| = ℓ + 1 + 2t` from `marked_card`) it contains
`Pf_{E_ℓ}(B_0) · G' = T.prod`. (`μ.len ≤ h` is only used to keep the slice index in range; the
hypothesis `1 ≤ h` is needed by `D3` and `W_isIdeal`.)

**(T7)** (the middle option of a marked shape; case (M), `δ = 1`). Hypotheses:
`(μ.addOne, true) ∈ Λ`, `(μ, false) ∈ Λ`, `μ.len < h`. Slice `d = μ.len`.

*Proof (paper).* Put `B_0' := insert 0 (B_0^+)`, `E^+ = E_{ℓ+1}` and
`f := (y_0 · markedPf F h (ℓ+1) B_0' + Pf(B_0^+; y^{E^+}, D(y_0, ·))) · G'^+`, where `G'^+` is
the image of `G' = D_P · Π_{c≥2} Δ(B_c)` under `incl` (pairs and blocks lifted, `L1`).
*`f ∈ V_Λ`:* `markedPf F h (ℓ+1) B_0' · G'^+` is the product of a marked pattern of
`μ.addOne` (marked block `B_0'` of size `(ℓ + 1) + 1 + 2t`; the columns `c ≥ 2` of `μ.addOne` are
those of `μ`), so it lies in `V_Λ` by `B4_marked`, and so does its multiple by `y_0`. Expanding the
second term along its last border (`bpf_expand_last`): it is a sum of `± D(y_0, y_b) ·
Pf(B_0^+ ∖ b; y^{E^+})` over `b ∈ B_0^+`. If `t ≥ 1`, each `D(y_0, y_b)·Pf_{E^+}(B_0^+ ∖ b)·G'^+`
is the product of a marked pattern of `μ.addOne` (marked block `B_0^+ ∖ b`, of size
`(ℓ + 2) + 2(t − 1)`, pairs `P^+ ∪ {{0, b}}`). If `t = 0`, `|B_0^+ ∖ b| = ℓ = |E^+|` and by `C5`
`Pf_{E^+}(B_0^+ ∖ b) = ± Δ(B_0^+ ∖ b)`, so the summand is `±` the product of a tight pattern of
`μ` (first block `B_0^+ ∖ b`, pairs `P^+ ∪ {{0, b}}`, blocks `B_c^+`), which lies in `V_Λ` by
`B4_tight` and `(μ, false) ∈ Λ`.
*Degree and top coefficient:* under `peelEquiv'`, `f` is the class of `Φ · C(G')` of Lemma Q′ with
`w` the increasing enumeration of `B_0` composed with `y` (as in `phi_markedPf_insert_zero`). By
(Q′1), (Q′2) its `X`-degree is at most `ℓ` and its coefficient of `X^ℓ` is
`mPf h ℓ w · G' = T.prod`. `Lifts.coeff_mem_W` concludes (`ℓ < h` gives `ℓ ≤ 2h`).

**(T8)** (the removal that empties the first column of a marked shape; case (R), `δ = 1`,
`μ_ρ = 1`). Hypotheses: `(μ.subE μ.len, true) ∈ Λ`, `1 ≤ μ.len`, `μ.len ≤ h`,
`μ.row μ.len = 1`. Slice `d = 2h + 1 − μ.len`.

*Proof (paper).* `μ − e_ℓ = μ.subE μ.len` has `ℓ − 1` rows and the same columns `c ≥ 2` as `μ`
(its first column is one shorter). Put `B_0' := insert 0 (B_0^+)`, of size
`((ℓ − 1) + 1) + 2(t + 1)`. Then `markedPf F h (ℓ−1) B_0' · G'^+` is the product of a marked
pattern of `μ.subE μ.len` (marked block `B_0'`, pairs `P^+`, blocks `B_c^+`), so it lies in `V_Λ`
(`B4_marked`). Under `peelEquiv'` it is the class of `mPf h (ℓ−1) z · C(G')` with `w` as above
(`phi_markedPf_insert_zero`); by **Lemma Q** with `l = ℓ − 1` (so `l + 1 = ℓ ≤ h`) its `X`-degree is
at most `2h − (ℓ − 1) = 2h + 1 − ℓ` and its top coefficient is
`(−1)^{ℓ−1} · mPf h ℓ w · G' = (−1)^{ℓ−1} · T.prod`. `Lifts.coeff_mem_W` and
`Lifts.mem_of_neg_one_pow_mul_mem` conclude (`1 ≤ ℓ` gives `2h + 1 − ℓ ≤ 2h`).

## What was checked before sending

`chkE13.py` / `chkE13.log` (exact arithmetic modulo primes; 229 s, 385 MB): **2 269 checks,
0 failures; 6 controls, all fire.**
- **Part Q** (924 checks): Lemma Q and Lemma Q′ as polynomial identities in `R[X]`, with `w`
  evaluated at random points of `F_32003` (so nothing is truncated), for `h = 0, …, 4`, all `l ≤ h`
  (Q1) and `l + 1 ≤ h` (Q2), `ℓ ≤ h + 1` (Q′), `t ≤ 2`, `n ≤ 7`; the Pfaffians computed in the
  convention of this project (`bmat`: variables first, then borders; `pf` expanded along the index
  `0`). Controls: (Q2) with the opposite sign is wrong in 57 of 57 cases with a non-zero top
  coefficient; with the minus sign in front of the second term of `Φ`, the degree exceeds `ℓ` in
  57 of 57 cases.
- **Part T, (I)**: the three lifts on their STATEMENTS, with the slices computed by linear algebra
  from the generators of `V_Λ`, for the smallest `Λ` allowed by the hypotheses
  (`{(μ, 0)}`, `{(μ ⊔ 1, 1), (μ, 0)}`, `{(μ − e_ℓ, 1)}`), every `μ`, in the cells `r = 3`
  (`m ≤ 6`), `r = 5` (`m ≤ 5`), `r = 7` (`m ≤ 4`), primes `101, 2, 3, 5, 7`: 258 (T6), 107 (T7),
  44 (T8) memberships, of which 250, 106, 42 of non-zero products. Since the slices are monotone
  in `Λ` (`L0a`), this is the strongest test of the statements. Controls: one slice lower, some
  product is outside in 36 of 36 (T6), 12 of 12 (T7), 14 of 14 (T8) cases with `d ≥ 1`; (T7)
  without `(μ, 0)` in `Λ` fails in 22 of 22 cases (the patterns with `t = 0` need it).
- **Part T, (II)**: inside every interlaced pair of the same cells, every marked shape whose last
  option in the chain is the zero option, the middle option, or a removal emptying the first
  column satisfies the hypotheses of (T6), (T7), (T8) respectively, and its products lie in the
  slice `r − F_Λ(σ)`: 297, 452, 44 memberships.
- Outside the statement: (T7) also held at `μ.len = h` in the 14 cases met. Not claimed.

## Remarks for the formalization

- The constructions of (T7) and (T8) are those of (T5) of E12 (`exists_mpattern_zero`,
  `phi_markedPf_insert_zero`), with the marked block `insert 0 (B_0^+)` instead of
  `insert 0 (B_1^+)`. The new step in (T7) is the expansion of the border `D(y_0, ·)`
  (`bpf_expand_last`) into patterns with a new pair `{0, b}`.
- The Partition lemmas needed (columns of `μ.addOne` and of `μ.subE μ.len` when the last row is
  `1`, `(μ.addOne).len = μ.len + 1`, `(μ.subE μ.len).len = μ.len − 1`) are elementary; prove them
  as needed.
- If a hypothesis turns out to be needed somewhere (for instance `1 ≤ h` in (T7)), add it and say
  so. Equivalent or more general forms are fine if noted.
