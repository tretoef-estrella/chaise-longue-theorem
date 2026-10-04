# The lifts of the odd box, first part: the cases with a spectator marked block and the zero option of an unmarked shape

Piece E12 of the plan for the even degrees. Source: paper v11, §8.6, proof of Proposition 8.10,
cases (A), (M) with `δ = 0`, (Z) with `δ = 0`, and (R) with an ordinary block. The cases in which
the marked block itself changes ((M) with `δ = 1`, (Z) with `δ = 1`, (R) with `δ = 1` and
`μ_ρ = 1`) and the assembly of the Proposition are NOT part of this piece.

Everything is stated for a field `F`, an integer `h ≥ 0`, the odd number `r = 2h + 1` and
`q = r + 1 = 2h + 2`. The rings are `C_n = Peel.C F (2*h+2) n` (the box `y_i^r = 0`), with
`y_i = Tight.y F (2*h+2) i`.

**Indices.** As in `q_P3_lifts.md`, the level is `m = n + 1`; the new variable `y_1` of the paper
is `y_0` of `C_{n+1}`, and the variables `y_2, …, y_m` of the paper are the images
`y_{i+1} = incl(y_i)` of the variables of `C_n` (`Peel.incl F (2*h+2) n`, `Lifts.incl_y`).
For a set `B` of indices of `C_n`, `B^+ := Lifts.liftSet B` is its image in `Fin (n+1)` under
`Fin.succ`.

**Slices.** For an ideal `V` of `C_{n+1}` and `d ≤ q − 2 = 2h`, `W_d(V) := Peel.W (m := n+1) _ V d`,
the `F`-subspace of `C_n` of the coefficients `[y_0^d] f` of the `f ∈ V` of `y_0`-degree `≤ d`.

## What is used unchanged

- `RequestProject/Peel/` (`C`, `incl`, `peelEquiv'`, `W`, `mem_W`), `RequestProject/Tight/`
  (`y`, `D`, `pairD`, `Delta`, `vand`, `colLen`, `TightPattern`, `TightPattern.prod`, `VLam`,
  `VLamAll`, `sum_eps_Delta`).
- `RequestProject/Lifts/`: `liftSet`, `liftPairs`, `cleanBlocks` and their lemmas, `incl_y`,
  `incl_D`, `incl_Delta`, `incl_pairD`, `phi_y0`, `phi_incl`, `phi_D`, `dpoly`, `coeff_dpoly`,
  `coeff_C_mul_prod`, `coeff_mem_W`, `mem_of_neg_one_pow_mul_mem`, `exists_pattern_insert`,
  `exists_pattern_pair`, and the two lemmas `mem_W_of_insert` and `mem_W_of_pair`.
- `RequestProject/OddShapes/`: `Shape`, `comp`.
- `RequestProject/Pfaffian/`: `bpf_expand_var`, `bpf_expand_var_zero`, `C1`, `C5`,
  `bpf_eq_zero_of_border_eq`, `bpf_laplace` (whichever is convenient).
- `RequestProject/Membership/`: `V2`.
- `RequestProject/OddPatterns/`: `mPf`, `map_mPf`, `mPf_cast`, `A1`, `A7`, `markedPf`,
  `MarkedPattern`, `MarkedPattern.prod`, `VS`, `VSAll`, `B4_tight`, `B4_marked`.

## Part P. The marked Pfaffian with one new variable

Let `R` be a commutative ring, `h ≥ 0`, `ℓ ≥ 1`, `w : Fin ℓ → R`. In the polynomial ring `R[X]`
let `z : Fin (ℓ+1) → R[X]` be `z_0 = X`, `z_{i+1} = C (w_i)` (`Fin.cons X (fun i => C (w i))`), and

`P_ℓ(w) := mPf_ℓ(z) ∈ R[X]`   (`OddPatterns.mPf h ℓ z`).

**Lemma P.**

- (P1) for every `k` with `2h < k + ℓ` and `ℓ < k + 2` (that is, `k > 2h − ℓ` and `k > ℓ − 2`):
  `[X^k] P_ℓ(w) = 0`.
- (P2) if `ℓ ≤ h`: `[X^{2h−ℓ}] P_ℓ(w) = (−1)^{ℓ(ℓ+1)/2} · Π_{i<j} (w_j − w_i)`
  (the product over `i < j` in `Fin ℓ`; it is `Tight.vand w Finset.univ`).
- (P3) in particular, if `ℓ ≤ h`: `[X^k] P_ℓ(w) = 0` for every `k > 2h − ℓ`.
- (P0) for `ℓ = 0` and `z : Fin 1 → R[X]`, `z_0 = X`: `mPf_0(z) = X^{2h}` (this is (A1)).

*Proof.* Write `r = 2h + 1` and `c = (z^0, …, z^{ℓ−2})` for the `ℓ − 1` borders. Expand the
bordered Pfaffian along the variable `0` (`bpf_expand_var` with `x = 0`, `ℓ + 1` variables and
`ℓ − 1` borders; for `ℓ = 1` there is no border and it is `bpf_expand_var_zero`). The sign of the
first term is `(−1)^{0 + (ℓ+1) + (ℓ−1)} = +1`:

`P_ℓ(w) = Pf(w; w^0, …, w^{ℓ−2}, D^−(X, ·)) + Σ_{k=0}^{ℓ−2} ± X^k · Pf(w; the borders without w^k)`,

where the Pfaffians on the right are over `R[X]` in the `ℓ` variables `C(w_i)`, and `D^−(X, ·)` is
the border `b ↦ Dab r X (C w_b)`. The second sum has `X`-degree `≤ ℓ − 2`. By (C1),

`Pf(w; w^0, …, w^{ℓ−2}, D^−(X, ·)) = −Σ_{u=0}^{r−2} (−1)^u X^{r−2−u} · Pf(w; w^0, …, w^{ℓ−2}, w^u)`,

and `Pf(w; w^0, …, w^{ℓ−2}, w^u)` does not contain `X`; it is `0` for `u ≤ ℓ − 2` (two equal
borders, `bpf_eq_zero_of_border_eq`) and for `u = ℓ − 1` it is
`Pf_{(0, …, ℓ−1)}(w) = (−1)^{ℓ(ℓ−1)/2} Π_{i<j}(w_j − w_i)` by (C5). So the first term has
`X`-degree `≤ r − 2 − (ℓ − 1) = 2h − ℓ`, and its coefficient of `X^{2h−ℓ}` is
`−(−1)^{ℓ−1}(−1)^{ℓ(ℓ−1)/2} Π(w_j − w_i) = (−1)^{ℓ(ℓ+1)/2} Π(w_j − w_i)`. This gives (P1). If
`ℓ ≤ h` then `ℓ − 2 < 2h − ℓ`, so the second sum does not reach the degree `2h − ℓ`: (P2), (P3). ∎

(For `ℓ = h + 1` the statement (P2) is false in general: the second sum reaches the degree
`2h − ℓ = ℓ − 2`.)

## Part L. Auxiliary facts

- (L0a) `W_d` is monotone in the ideal: if `V ≤ V'` are ideals of `C_m` (`m ≥ 1`), then
  `Peel.W hm V d ≤ Peel.W hm V' d` for every `d`.
- (L0b) `Tight.VLamAll F (2h+2) m (comp Λ false) ≤ VSAll F h m Λ` for every set `Λ` of shapes.
- (L1) for `B ⊆ Fin n` and `ℓ ≥ 0`: `incl(Pf_{E_ℓ}(B)) = Pf_{E_ℓ}(B^+)`, that is
  `Peel.incl F (2h+2) n (markedPf F h ℓ B) = markedPf F h ℓ (Lifts.liftSet B)`.
  (`map_mPf`, `incl_y`, and the increasing enumeration of `B^+` is `Fin.succ` composed with the
  increasing enumeration of `B`.)
- (L2) (clean blocks of a marked pattern) as for `Lifts.cleanBlocks`: for a marked pattern `T`
  of `μ` on `I`, the blocks `B_c` for `c ∉ [2, μ_1]` may be taken empty without changing the
  product; with this convention `Π_{c=2}^{N} Δ(B_c) = Π_{c=2}^{μ_1} Δ(B_c)` for every `N ≥ μ_1`.
  (State and prove whatever form of this is convenient.)

## Part T. The lifts

In all the statements `Λ` is an arbitrary set of shapes (no hypothesis on `Λ` besides the
membership stated), `n ≥ 0`, `V_Λ := VSAll F h (n+1) Λ ⊆ C_{n+1}`, and the patterns `T` are on all
the indices of `C_n` (`Finset.univ : Finset (Fin n)`). `λ'_c = Tight.colLen λ c`.

**(T1) Insertion into a column, unmarked** (cases (A) and (M) of the paper with `δ = 0`).
Let `(λ, 0) ∈ Λ`, `T` a tight pattern of `μ`, `c^* ≥ 1`, and suppose
`λ'_c = μ'_c + [c = c^*]` for every `c ≥ 1`, and `μ'_{c^*} ≤ 2h`. Then

`T.prod ∈ W_{μ'_{c^*}}(V_Λ)`.

(From `Lifts.mem_W_of_insert` with the set `comp Λ false` and `q = 2h + 2`, (L0a), (L0b).)

**(T2) Removal from a column, unmarked** (case (R) with `δ = 0`).
Let `(λ, 0) ∈ Λ`, `T` a tight pattern of `μ`, `c_0 ≥ 1`, and suppose
`λ'_c + [c = c_0] = μ'_c` for every `c ≥ 1`, and `1 ≤ μ'_{c_0} ≤ 2h + 1`. Then

`T.prod ∈ W_{2h+1−μ'_{c_0}}(V_Λ)`.

(From `Lifts.mem_W_of_pair`, (L0a), (L0b).)

**(T3) Insertion into a column `c^* ≥ 2`, marked** (case (A) with `δ = 1`).
Let `(λ, 1) ∈ Λ`, `T` a marked pattern of `μ`, `c^* ≥ 2`, and suppose
`λ'_c = μ'_c + [c = c^*]` for every `c ≥ 1` (so `ℓ(λ) = ℓ(μ)`), and `μ'_{c^*} ≤ 2h`. Then

`T.prod ∈ W_{μ'_{c^*}}(V_Λ)`.

*Proof.* Put the index `0` into the block of the column `c^*`: the marked pattern `T'` of `λ` on
`Fin (n+1)` has the pairs `liftPairs T.pairs`, the marked block `T.marked^+` (of the same size, and
`ℓ(λ) = ℓ(μ)`), and the blocks `B_c^+` for `c ≠ c^*`, `B_{c^*}^+ ∪ {0}` (`B_{c^*} = ∅` if
`c^* > μ_1`). By (L1), `incl_pairD`, `incl_Delta` and the factorisation of the Vandermonde
product used in `Lifts.exists_pattern_insert`,

`T'.prod = Π_{x ∈ B_{c^*}} (y_{x+1} − y_0) · incl(T.prod)`.

Then exactly as in `Lifts.mem_W_of_insert` (`coeff_C_mul_prod`, `coeff_mem_W`): the `y_0`-degree
is `|B_{c^*}| = μ'_{c^*} ≤ 2h` and the top coefficient is `(−1)^{|B_{c^*}|} T.prod`. ∎

**(T4) Removal from a column `c_0 ≥ 2`, marked** (case (R) with `δ = 1` and `μ_ρ ≥ 2`).
Let `(λ, 1) ∈ Λ`, `T` a marked pattern of `μ`, `c_0 ≥ 2`, and suppose
`λ'_c + [c = c_0] = μ'_c` for every `c ≥ 1`, and `1 ≤ μ'_{c_0} ≤ 2h + 1`. Then

`T.prod ∈ W_{2h+1−μ'_{c_0}}(V_Λ)`.

*Proof.* As `Lifts.mem_W_of_pair`: with `S = B_{c_0}` and `T.prod = Δ(S)·G'`
(`G' = D_P · Pf_{E_ℓ}(B_0) · Π_{c ≥ 2, c ≠ c_0} Δ(B_c)`), for `b ∈ S` the pairs
`liftPairs T.pairs ∪ {{0, b+1}}`, the marked block `T.marked^+` and the blocks `B_c^+`
(`c ≠ c_0`), `(S ∖ b)^+` form a marked pattern of `λ` on `Fin (n+1)` with product
`D(y_0, y_{b+1}) · incl(Δ(S ∖ b) · G')`; `f := Σ_{b ∈ S} ε_b · (that product)` lies in `V_Λ`, and
by `phi_D`, `coeff_dpoly` and `Tight.sum_eps_Delta` its coefficients `[y_0^k]` vanish for
`k > 2h + 1 − |S|` and `[y_0^{2h+1−|S|}] f = ± T.prod`. ∎

**(T5) The zero option of an unmarked shape** (case (Z) with `δ = 0`).
Let `(μ, 1) ∈ Λ`, `T` a tight pattern of `μ`, and `ℓ(μ) ≤ h`. Then

`T.prod ∈ W_{2h−ℓ(μ)}(V_Λ)`.

*Proof.* Let `ℓ = ℓ(μ)`, `B_1` the first block of `T` (`|B_1| = μ'_1 = ℓ`; `B_1 = ∅` if `μ = ∅`),
and `T.prod = Δ(B_1)·G'` with `G' = D_P · Π_{c ≥ 2} Δ(B_c)`.

The marked pattern `T'` of `μ` on `Fin (n+1)`: pairs `liftPairs T.pairs`, blocks `B_c^+`
(`c ≥ 2`), marked block `B_1^+ ∪ {0}`, of size `ℓ + 1` (`t = 0`). Its product is

`f := T'.prod = Pf_{E_ℓ}(B_1^+ ∪ {0}) · incl(G') ∈ V_Λ`   (by (B4)).

The increasing enumeration of `B_1^+ ∪ {0}` is `0` followed by the increasing enumeration of
`B_1^+`. So, under `φ = peelEquiv'` (`φ(y_0) = root`, `φ(incl g) = of g`) and `map_mPf`,

`φ(Pf_{E_ℓ}(B_1^+ ∪ {0})) = mk( P_ℓ(w) )`,  `w_i := y_{b_i}` (`b_1 < ⋯ < b_ℓ` the elements of `B_1`),

for `ℓ ≥ 1`, and `= mk(X^{2h})` for `ℓ = 0` (P0). Hence `φ(f) = mk( C(G') · P_ℓ(w) )`. By (P3)
its coefficients vanish above `2h − ℓ`, and by (P2) and `Membership.V2` the coefficient of
`X^{2h−ℓ}` is `(−1)^{ℓ(ℓ+1)/2} Δ(B_1)·G' = ± T.prod` (for `ℓ = 0`: the coefficient of `X^{2h}` is
`G' = T.prod`). As `2h − ℓ ≤ 2h = q − 2`, `coeff_mem_W` gives `± T.prod ∈ W_{2h−ℓ}(V_Λ)`, and
`W_{2h−ℓ}(V_Λ)` is an `F`-subspace. ∎

## What was checked before sending

In exact arithmetic modulo primes (101, and the characteristics 2, 3, 5, 7), in the rings `C_m`
with `r = 3` (`m ≤ 6`), `r = 5` (`m ≤ 5`), `r = 7` (`m ≤ 4`); 8 261 checks, 0 failures:

- Lemma P: (P0), (P1), (P2), (P3) for `1 ≤ ℓ ≤ h` with the sign as stated, the Pfaffian computed
  in the convention of this project (`bmat`, `pf` along the index `0`). (P2) fails with the
  opposite sign, and it fails at `ℓ = h + 1`.
- (L1) on every set `B`.
- (T1)–(T5), tested on the statements: for every single shape `Λ = {(λ, δ)}` of those levels,
  every `μ` in the stated relation with `λ` and every pattern `T` of `μ`, the membership of
  `T.prod` in the slice, the slices being computed by linear algebra from the generators of
  `V_Λ` (the constructions of the proofs above are not used). 3 402 memberships of non-zero
  products. In every case with `d ≥ 1` some product lies outside the slice `d − 1`. (T5) fails
  for `ℓ(μ) = h + 1`.
- The same memberships inside all the interlaced pairs `Λ` of those levels, with the slice
  `r − F_Λ(σ)` and the case read off from the chain: 3 824 memberships of non-zero products
  (cases (A) `δ = 0, 1`, (M) `δ = 0`, (Z) `δ = 0`, (R) ordinary `δ = 0, 1`); in every case with
  `d ≥ 1` some product lies outside the next lower slice.

## Remarks for the formalization

- If a statement is easier in a slightly different but equivalent form, use it and say so.
- (T1)–(T5) are stated for an arbitrary set `Λ`; nothing about interlaced pairs is needed here.
- Signs: only the top coefficients up to sign matter for (T3)–(T5), because the slices are
  `F`-subspaces (`Lifts.mem_of_neg_one_pow_mul_mem`).
- More general statements are fine if noted.
