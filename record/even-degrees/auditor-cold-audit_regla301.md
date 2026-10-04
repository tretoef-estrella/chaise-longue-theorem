# Cold audit of «Grepy is in the Sky», Mission 1 — the odd box and the even degrees (2 October 2026)

Auditor and scribe: Grepy Chats. Created empty, with its sections, before any reading or computing (disk rule). Every item is rewritten in my own words and marked **CORRECT**, **GAP** or **ERROR**. Nothing here is registered as proved until this file is complete and a second reader has attacked the same documents.

Documents under audit (md5): `PROOF_ODD_BOX.md` `fbe75a684758c43f8b466dd5f8ba8323`, `REPORT.md` `993bfbbd95fb47ff9e2487fbfcead165`, in `VIVOS/ATAQUES_Y_REPORTES/GREPY_IS_IN_THE_SKY_1/`. Paper: `PAPER_OFICIAL_v10.md` `76082a9e85a693c2aee8c8d4e2710744`. Original of [DS]: arXiv:1405.4683v3 (text in `~/Desktop/GREPY_IS_IN_THE_SKY/material/sources/`).

Notation of the audit. `r = 2h + 1` odd, `C_m = F[y_1..y_m]/(y_i^r)`, `D = D_r`, `B = D_{r−1}`. «Sufficiency» means the direction needed for Theorem E (the lower bounds); «necessity» means the converse directions of the «if and only if» statements of B3, B4, B5, which Theorem E does not use.

## 0. First line (the verdict; filled in last)

**On my reading the proof HOLDS: every item of §1–§7 is marked CORRECT, with no GAP and no ERROR, and every gate of my own (§8) passes, with controls that fire.** This is the auditor's cold reading, item by item, in my own words; it is not yet a second independent reading. By Rafa's rule the result is **not registered as proved** until the cold reader «Grepy Skies 2» has delivered its report and I have graded it.

What the reading rests on, apart from the two documents: [DS, Theorem 1.1(a) and Claim 4.3] (for every `m > 2`); the paper's §6 (Lemmas 6.1–6.5, 6.7, 6.8), §7 (Theorem C / Theorem 7.6, **read here at an even box in characteristic 2, which the paper does not state and the Lean files do not cover**), Lemma 5.1, Lemma 5.5, Proposition 5.6, Lemma 5.7(ii), Theorem 5.3, Lemma 2.3. Theorem E uses only lower bounds on blocks and the global count; it does not use the upper bound of the odd box, nor Theorem A, nor Lemma B.0.

Presentation notes for a later write-up (none changes a verdict): (1) Corollary 6.2(i) quotes the upper bound of Remark 8.7(3), which is stated in `2k + 2` variables; the passage to `2k + 1` variables (the map `θ`) should be written there. (2) In Lemma 2.4 (D2) the rows must be read as labelled (vectors of row lengths). (3) Definition 4.1 should state the number of pairs of a marked pattern, `(m − 1 − |λ|)/2 − t`. (4) The hypothesis «`q ≥ 3` odd» at the head of §7 of the paper should become «`q ≥ 1`» with the binomial condition, and the Lean statements `Bip.thm76`, `Bip.theoremC` carry `Odd q`.

## 1. The reduction for even `m` (`REPORT.md` §3)

### 1.0 The translation, from the original — CORRECT
[DS] work with degree `m > 2` and `n = 2d` even, with no condition on the parity of `m` (original, p. 1; Theorem 1.1, Definition 1.3, Theorem 1.4, Corollary 1.5, Claim 4.3 are stated for every such `m`). Proposition 2.1 of the paper uses only: `R` is free of rank `m^{n+1}`; Claim 4.3 at `p = 0`; Theorem 1.1(a); Corollary 1.5. None of these needs `m` odd. So for even `m`: Conjecture 1.2 at `(k, m)` holds iff `dim_{F_p}(ψ̄_J : J)F_p[G] = |Γ|` for every prime `p | m`, and `≤` always holds. This is the statement the pilot works with. (The restriction «`m` odd» in the paper starts after Proposition 2.1.)

### 1.1 B1 — the count — CORRECT
For `a ∈ Γ` with matching `J`: the pairs with `i ≥ 1` cover `{1..n+1} ∖ {k_0}` and multiply to `1`, so `a_1⋯a_{n+1} = a_{k_0}`; with `a_0 := (a_1⋯a_{n+1})^{−1}` the pair `{0, k_0}` also multiplies to `1` and `a_0 ≠ 1`. Conversely an `N`-tuple in `μ_m ∖ 1` split into inverse pairs by a perfect matching has product `1` and restricts to an element of `Γ`. The tuple splits iff each class `{c, c^{−1}}`, `c ≠ ±1`, is balanced and `−1` is used an even number of times: exponential generating function `I_0(2x)^{(m−2)/2}·cosh x`, and `(m−2)/2 = (r−1)/2` for `r = m − 1`. **External check (mine, from the original):** [DS, Remark 4.4] gives the constant term of `(x_1 + ⋯ + x_{h−1} + 1 + x_{h−1}^{−1} + ⋯ + x_1^{−1})^{n+2}` for `m = 2h`, which is the same count (for even `n + 2` the parity of the fixed value is automatic); and their polynomial for `n = 4` gives `141` at `m = 4` and `1001` at `m = 6`, the values of `N_3(6)` and `N_5(6)`.

### 1.2 B2 — the chain at `m = q = 2^v` — CORRECT
In characteristic `2`: `F_2[G] = B := F_2[s]/(s_i^q)`, `s = t − 1`; `φ(u) = (u − 1)^{q−1}` (from `(u−1)φ(u) = (u−1)^q` in a domain); `t_jt_k − 1 = s_j + s_k + s_js_k`. (1) `dim I ≤ |Γ|`: Proposition 2.1. (2) `dim I = dim in(I)`: the filtration `I ∩ B_{≥d}`, whose graded pieces are the spaces of lowest forms of degree `d`; `in(I)` is an ideal. (3) the lowest form of `ψ̄_J` is `L_J` whenever `L_J ≠ 0` in `B`, because `(s_i^q)` is homogeneous. (4) `(a+b)^{q−1} = Σ_{u=0}^{q−1} a^u b^{q−1−u}` in `F_2[a,b]`; times `b`, modulo `b^q`: `ab·Σ_{w=0}^{q−2} a^w b^{q−2−w}`. The monomial factors use each of `s_1..s_{2k+1}` once, so `L_J = Y·D^{(2)}_J`; multiplication by `Y` has kernel `(s_i^{q−1})`, so `(L_J)B ≅ (D^{(2)}_J)C_r` with `r = q − 1`, and over `F_2` `D^{(2)} = D_r`. Hence (O)≥ at `(k, 2^v − 1, F_2)` gives `dim I ≥ N_r(2k+2) = |Γ|` (B1). The only prime dividing `2^v` is `2`.

### 1.3 Lemma B.0 — the bound colouring by colouring — CORRECT
`G = G_q × G_{r'}`. Over the ring `W` of integers of the unramified extension of `Q_p` containing `μ_{r'}`, `|G_{r'}|` is a unit, so `W[G] = ⊕_c W[G_q]e_c` and `I_W = ⊕_c e_cI_W`. For a `W`-submodule `M` of a free module `L`, the image of `M` in `L/pL` is a quotient of `M/pM`, of dimension `rank M`; and the image of `e_cI_W` in `F'[G]e_c` is `e_c·(ψ̄_J)F'[G]`, the component `π_c(I)` (on `e_c` the element `t_i` has the single eigenvalue «reduction of the `μ_{r'}`-part», which identifies the character `c` with the colouring). The rank of `e_cI_W` is the number of characters `g` of `G` with `μ_{r'}`-part `c` at which some `ψ_J` does not vanish, i.e. `g ∈ Γ` ([DS, Claim 4.3], whose proof I read in the original). The inequality goes in the stated direction. Used only for necessity and for the equalities over `F̄_p`.

### 1.4 B3 — the prime `2` at `m = 2^v r'`, `r' > 1` odd — CORRECT (sufficiency and necessity)
Read again, by me, with `p = 2`, `q = 2^v`:
- **Lemma 6.1:** needs `(t^{r'} − 1)^q = t^m − 1` (true, `q = 2^v`) and `t^{r'} − 1` separable (`r'` odd). Holds.
- **Lemma 6.2:** `φ(u) = (u−1)^{q−1}Π_{ξ≠1}(u−ξ)^q`; in `R_c`, `(u − c_jc_l)^q = 0` by Frobenius. No use of `p` odd. Holds.
- **Lemma 6.3, 6.4, Proposition 6.5:** need only `ζ ≠ ζ^{−1}` for `ζ ≠ 1` in `μ_{r'}` (`r'` odd). A unit of `R_c` in front of a pure tensor does not change the ideal. Hold.
- **Lemma 6.7:** `t_it_l − 1 = (x_i − z_l)(1 + z_l)^{−1}`; the sign in `(x − z)^{q−1}` is irrelevant in characteristic `2`. Holds.
- **Theorem C and Theorem 7.6 at `q = 2^v`, characteristic `2`.** I went through §7 of the paper line by line. §7.1 (peeling with box `q`): uses `w^{j+1} ≠ 0` for `j + 1 ≤ q − 1` and `|F(M')| ≤ q`. §7.2–§7.4: statements about pairs of partitions with `ℓ(λ_+) + ℓ(λ_−) ≤ q` and about the `q` options; Lemma 7.2′ borrows from §5.6 only (T), (5.2), (a), (b), (c), (e2), none of which uses the parity of `q` or the cap `ℓ ≤ h` (I re-read those four cases of §5.6: they compare partial sums only). Proposition 7.5: (α), (β) need a `w`-degree `≤ q − 1`; (γ) needs `C(q−1, r−1) ≠ 0` in `F`, and `C(2^v − 1, t)` is odd for all `t` (Lucas). Theorem 7.6: the symmetry step needs `(x − z)^{q−1} = ±(z − x)^{q−1}`. The hypothesis «`q ≥ 3` odd» of §7 is not used anywhere in the proofs; `q = 2` is allowed (`C(1, 0) = C(1, 1) = 1`). **So Theorem C holds at every `q = 2^v`, `v ≥ 1`, in characteristic `2`, given the proofs of §7.** Note for the record: the Lean theorems `Bip.thm76` and `Bip.theoremC` are stated with `Odd q` and `3 ≤ q`; the machine check does not cover the even box. Own gate at down-sets that are not roots: §8, run G3.
- **Block of colour `1`, `0 ∈ 𝒞_1`.** `R_{c,1} = F[H]`, `H = (Z/q)^{𝒞_1 ∖ 0}`, and `(u−1)^{q−1} = φ_q(u)` for `u^q = 1`. From (6.2), `g_P = (unit)(t_{k_0} − 1)Π(t_l − 1)φ_q(t_it_l)`: after an order-preserving relabelling these are the `ψ̄_J` of degree `2^v` and dimension `2(k' − 1)`, `|𝒞_1| = 2k'`. Correct.
- **Block of colour `1`, `0 ∉ 𝒞_1` (the map `θ`).** `uφ_q(u) = φ_q(u)`, so `g := Π_{i∈𝒞_1} t_i` fixes every `g_P`. Writing `f = Σ_{j<q} t_{i_1}^j f_j`, `gf = f` gives `f_{j+1} = g'f_j` (indices modulo `q`), so `f ↦ f_0` is injective on the ideal and `F[H']`-linear. For `{i_1, l} ∈ P` the coefficient of `t_{i_1}^0` in `φ_q(t_{i_1}t_l) = Σ_j t_{i_1}^j t_l^j` is `1`, so `θ(g_P)` is the generator of the previous case with `i_1` in the role of `0`; and `t_{i_1}g_P = t_l^{−1}g_P` gives `ℳ = Σ_P g_PF[H']`. Same dimension. Correct.
- **The count** (Lemma 6.8 for even `m`, `p = 2`): the colours `≠ 1` are not self-inverse; in the block `𝒞_1` the `w_i` lie in `μ_q ∖ 1`, where inversion has the fixed point `−1`: `N_{q−1}(|𝒞_1|)`; in a pair block all `w_i ∈ μ_q` are allowed (`g_i ≠ 1` because `c_i ≠ 1`): `N_{bal}`, `N_{ph}` with `|Ω| = q`. The coupling through `w_0` is as in the paper: a block without `0` that satisfies its condition has product `1`. Correct.
- **Sufficiency:** `dim I = Σ_c dim I_{c,1}·Π dim I_{c,ζ} ≥ Σ_c N_1(c)ΠN_ζ(c) = |Γ|`, given Theorem C (lower bounds) and the lower bound for the block of colour `1`, which is the statement at `(k' − 1, 2^v)`, `k' − 1 ≤ k`; `k' − 1 = 0` is `dim (t − 1)F[t]/(t^q − 1) = q − 1 = N_{q−1}(2)`.
- **Necessity:** equality for the pair blocks over `F̄_2` by Lemma B.0 applied to the colouring «`a` indices `ζ`, `a` indices `ζ^{−1}`, one index `1`» (take `r' = 3`); then `dim I = |Γ|` forces `dim I_{c,1} = N_1(c)` for every compatible `c`, and every size `2k' ≤ 2k + 2` occurs. Correct.

### 1.5 B3′ — `q = 2` — CORRECT
`s_i^2 = 0`, so `s_l(s_i + s_l + s_is_l) = s_is_l` and `g_P = Π_{i ∈ 𝒞_1 ∖ 0} s_i` (or the product over all of `𝒞_1` when `0 ∉ 𝒞_1`): the socle, dimension `1`; the count is `1` (all entries `−1`, an even number of them). With Theorem C at `q = 2` (`dim(Π(x_i + z_{σ(i)}) : σ) ≥ C(2a, a)` in `F[x, z]/(x_i^2, z_l^2)`) there is no `2`-torsion for `m ≡ 2 (mod 4)`. This rests on §7 of the paper at `q = 2` (§1.4 above) and on nothing of Theorem O.

### 1.6 B4 — the odd primes of an even `m` — CORRECT (sufficiency and necessity)
`m = q r'`, `q = p^v`, `p` odd, `r'` even. Lemmas 6.1, 6.2 as written. The self-inverse colours are `1` and `−1` (`−1 ≠ 1` in `F`), so a compatible matching is a perfect matching of `𝒞_1`, one of `𝒞_{−1}`, and bijections `𝒞_ζ → 𝒞_{ζ^{−1}}`, chosen independently; Proposition 6.5 with one more factor. Blocks `1` and `ζ`: §6.4, §6.5 of the paper as they stand (`p` odd).
- **Block `−1`.** `u := −t` satisfies `(u − 1)^q = 0`; Lemma 2.3 of the paper needs only that and `2 ∈ F^×` (the paper says so after Lemma 2.2). So the factor is `F[y]/(y^q)` with the **full box `q`**, `t_it_l − 1 = u_iu_l − 1 = (unit)(y_i + y_l)`, and `t_i − 1 = −(2 + (u_i − 1))` is a unit. In (6.2) a pair inside `𝒞_{−1} ∖ 0` gives `(unit)(y_i + y_l)^{q−1} = (unit)·D_q(y_i, y_l)` (the identity `(a+b)^{q−1} = Σ(−1)^u a^u b^{q−1−u}` in characteristic `p`, proof of Lemma 2.4(i)), and the pair of `0` gives a unit. So for `0 ∈ 𝒞_{−1}`, `|𝒞_{−1}| = 2a`: the ideal of (O) at `(a − 1, q, F)`. For `0 ∉ 𝒞_{−1}`: `Σ_P D_{q,P}C_q` over the perfect matchings of `2a` variables; its lower bound is Theorem 6.1 of the proof for `Λ = {(∅, 0)}` at level `2a` (Corollary 6.2(ii)), so the `θ` of Corollary 8.6(i) is not needed for sufficiency. (I checked that `θ` anyway: `e_1·D_{r,J} = 0` for every `r ≥ 2`, `f_{u−1} = −σf_u`, the coefficient of `x_0^{r−1}` in `D_r(x_0, y)` is `(−1)^{r−1}`. It works for every `r`.)
- **Count.** On `𝒞_{−1}`, `g_i = −w_i ≠ 1` for every `w_i ∈ μ_q` (`−1 ∉ μ_q`), and `g_ig_l = w_iw_l`; inversion on `μ_q` has the single fixed point `1`: `N_q(2a)`.
- **Sufficiency** needs (O)≥ at `(a − 1, p^v, F)` for `a − 1 ≤ k`, over `F̄_p` (Theorem O is over every field). **Necessity** by Lemma B.0, Theorem 5.9′ and Corollary 7.8 of the paper.

### 1.7 B5 — CORRECT
Proposition 2.1 splits the conjecture at `(k, m)` over the primes `p | m`. Odd `p`: B4 with `r' = m/p^{v_p}` (even). `p = 2`: `m = 2^v` is B2 (`v ≥ 2`); `m = 2^v r'` is B3, then B2 for `v ≥ 2`, and B3′ for `v = 1`. The indices `k' ≤ k`, `k'' ≤ k` are those of the block sizes.

## 2. `PROOF_ODD_BOX.md` §1–§2: identities, shapes, interlaced pairs, layers — CORRECT

- **(1.1)–(1.4)**: checked by reindexing `w = r − 1 − u`, `w = r − 2 − u` (`r − 1` even, `r − 2` odd), and by telescoping. The peeling lemma (Lemma 5.1 of the paper) uses only `y_1^{j+1} ≠ 0` for `j + 1 ≤` (box) `− 1` and `|F(M')| ≤ |T|`; with box `r` and `|T| = r` it gives `dim V = Σ_{j=0}^{r−1} dim W_j` and `|Z| = Σ_{i=0}^{r−1}|Z_{>i}|`.
- **Lemma 2.1.** A new entry `−u_j` closes a pair in the class of `u_j`; `u_j` lengthens the row; a non-zero value of an absent class starts a row of length `1` (`2(h − ℓ)` values); `0` changes only the parity of the zeros. The resulting shapes lie in `Sh_m` (sizes and parities checked for both marks). `ℓ + ℓ + 2(h − ℓ) + 1 = r`.
- **Lemma 2.3.** Removals: Lemma 5.5 of the paper and (D1). Zero option in `Λ` ⟹ every removal in `Λ`: (D2) applied to `(μ, 1 − ε)`. Middle in `Λ` ⟹ zero option in `Λ`: (D2) on the new row. Addition in `Λ` ⟹ middle in `Λ` (if `ℓ < h`: `μ ⊔ 1 ≼ μ + e_j`, Lemma 5.5, (D1)) and zero option in `Λ` ((D2), removing the added box); additions `μ + e_{j+1} ≼ μ + e_j`. So the options in `Λ` are an initial segment.
- **Lemma 2.4, (D1).** `F_Λ(μ, 0) = F^*_{Λ^0}(μ) + [μ ∈ Λ^1]` for `μ ∈ 𝒫_{m−1}`: the first term is non-increasing by Proposition 5.6 of the paper with `q := r` (its `Par^{(h)}`, its `L = r − 1` positions; the proof uses `ℓ + ℓ̃ ≤ 2h` and the common parity of `|μ|, |μ̃|`, both true here), the second because `Λ^1` is a down-set of `𝒫_{m−1}`. `F_Λ(μ, 1) = F^*_{Λ^1}(μ) + [μ ∈ Λ^0]` for `μ ∈ 𝒫_{m−2}`: Proposition 5.6 one level lower, and `𝒫_{m−2} ⊆ 𝒫_m` with `Λ^0` a down-set of `𝒫_m`.
- **Lemma 2.4, (D2).** With rows labelled (vectors of row lengths up to order). `ν_j ≥ 2`: each option of `ν` in `A` gives, by (D2) on row `j` (which is still non-empty, also when the option is the removal in row `j` itself), the corresponding option of `ν' = ν − e_j` in `A'`; `ν ∈ A' ⟹ ν' ∈ A`. `ν_j = 1`: the options of rows `i ≠ j` transfer as before; the removal of row `j` is `[ν' ∈ A]` on both sides; and `(r − 1 − 2ℓ)[ν ⊔ 1 ∈ A] + [ν + e_j ∈ A] + [ν ∈ A'] ≤ (r + 1 − 2ℓ)[ν ∈ A']`, because each of the first two brackets implies `ν ∈ A'` by (D2). So `F_Λ(ν', 1 − ε) ≥ F_Λ(ν, ε)`.
- **The root.** `{(1)}` and `{∅}` are the minima of `𝒫_{2k+1}` and `𝒫_{2k}`; (D2) holds; appending the opposite of the unpaired value is a bijection onto the closed `(2k+2)`-tuples.

## 3. §3: bordered Pfaffians, (F1)–(F7) — CORRECT

(i)–(iii) are standard (for (ii): `Pf^2 = det` over the generic ring, a domain). (F2), (F3): the matrix `[[*, C], [−C^t, 0]]` has Pfaffian `± det C` when `C` is square and `0` when the zero block is larger than half. (F4): move `x` to the last position; the terms of the row expansion with partner in `N ∖ x` are the expansion (F2) of the matrix in which `x` is a border with column `b ↦ B(y_x, y_b)` (same minors `A^{x,z}`, same positions, one global sign), the terms with partner a border `k` give `± c_k(x)·Pf(N ∖ x; c` without `c_k)`. (F5): from (1.4), the column `B(y_x, ·)` is `−Σ_u (−1)^u y_x^{r−2−u}·y^u` and `D(y_x, ·) = Σ_u (−1)^u y_x^{r−1−u}·y^u = y^{r−1} − y_x·B(y_x, ·)`; then linearity. (F6) is the expansion of a Vandermonde determinant with a repeated row. (F7) is the Laplace expansion along the borders.

## 4. §4–§5: patterns and the membership lemma — CORRECT

- **Definition 4.1.** The bordered matrix of `Pf_{E_ℓ}(M)` has even size: `(ℓ + 1 + 2t) + (ℓ − 1)` for `ℓ ≥ 1`, `(1 + 2t) + 1` for `ℓ = 0`. For a marked shape the number of pairs is `(m − 1 − |λ|)/2 − t`. The four examples are right (I expanded the `4 × 4` Pfaffians). `V_Λ` is stable under relabelling.
- **5.1** Over `Z` an alternating polynomial has no monomial with a repeated exponent, so the alternants with increasing exponents `≤ r − 1` are a basis of `𝒜_n`; `∧` is the Laplace expansion.
- **5.2** `k!γ_k(φ) = φ^{∧k}` (terms square to zero), and torsion-freeness gives the rules. `φ^{∧k} ↔ k!·Pf`, because permuting blocks of size `2` is an even permutation.
- **5.3** Each of the elements is a signed sum of images, under permutations of the variables, of the one polynomial; the hypothesis is on its image in the box ring.
- **5.4** `ω_s` is antisymmetric (`s` odd) and is the image of `Ω_s`; `ω_{r−2} = B`; in `b^iD(a, b)` the terms with `u < i` die in the box and the rest are the terms of `ω_{r−1+i}`; so every `ω_s`, `s ≥ r` odd, is a multiple of `D` in the box. `(−1)^u v_u ∧ v_{u'}` is (even) `∧` (odd) in both cases of the parity of `u`. So `Ω_{2σ+1} = J_σ`, `B ↔ J_{h−1}`, and the high forms are `σ ≥ h`.
- **5.5** `E(ζ) ∧ O(ζ) = Σ_σ ζ^σ J_σ`. Lemma 5.2 by induction from `0 = γ_n(L + ζ^hU)`. Corollary 5.3: the top coefficients of `γ_{t+1}(L)` and of `E ∧ γ_t(L)`; the term `ζ^{h(t+1)}A'` starts above the degree `(t+1)(h−1)`; `E ∧ L = −ζ^hE ∧ U`.
- **5.6** `Pf_{E_ℓ}(M) ↔ ± v_0 ∧ ⋯ ∧ v_{ℓ−2} ∧ γ_{t+1}(J_{h−1})` (`ℓ ≥ 1`), `± e_h ∧ γ_t(J_{h−1})` (`ℓ = 0`), sizes `(ℓ − 1) + 2(t + 1)` and `1 + 2t`. `𝔘_ℓ(M) ⊇ Λ^{ℓ+1}(V) ∧ 𝔥_t` because an alternating polynomial is divisible by the Vandermonde determinant over `Z`. Conclusion by Corollary 5.3. The statement is over `Z`, hence over every field.

## 5. §6: Proposition 6.1, the seven cases — CORRECT

For each case I checked: the shape used lies in `Λ` (by the chain); every summand is the product of a pattern of that shape at level `m` (sizes of the marked block, number of pairs); the `y_1`-degree; the top coefficient; and `r − Φ`.

| case | `Φ` | `f` | shape of the summands | `deg_{y_1}`, top |
|---|---|---|---|---|
| (A) | `r − j_0 + 1` | index `1` into the block of column `μ_{j_0} + 1 ≥ 2` | `(μ + e_{j_0}, ε)`; marked block unchanged | `j_0 − 1`, `±G` |
| (M), `ε = 0` | `r − ℓ` | index `1` into `B_1` | `(μ ⊔ 1, 0)` | `ℓ`, `±G` |
| (M), `ε = 1` | `r − ℓ` | `(y_1 Pf_{E^+}(M ∪ 1) + θ Pf(M; y^{E^+}, D(y_1,·)))D_PR` | `(μ ⊔ 1, 1)` with marked block `M ∪ 1` (`t`) or `M ∖ b` and the pair `(1, b)` (`t − 1`); for `t = 0`, `(μ, 0)` with first block `M ∖ b` | the `B(y_1,·)` terms cancel by (F4), (F5); `ℓ`, `±Pf_{E_ℓ}(M)`; for `ℓ = 0`, degree `0` |
| (Z), `ε = 0` | `ℓ + 1` | `y_1^{r−1}G` (`ℓ = 0`); `Pf_{E_ℓ}(B_1 ∪ 1)D_PR` (`ℓ ≥ 1`) | `(μ, 1)`, marked block `{1}` or `B_1 ∪ 1`, `t = 0` | `r − 1 − ℓ` (the term `u = ℓ − 1`; the other sum has degree `≤ ℓ − 2 < r − 1 − ℓ`), `±Δ(B_1)` |
| (Z), `ε = 1` | `ℓ + 1` | `f_{S,Q} = Σ_{b∈S} ε_bΔ(S∖b)D(y_1,y_b)D_QD_PR` | `(μ, 0)`, first block `S ∖ b`, pairs `P ∪ Q ∪ (1,b)` | `r − 1 − ℓ`, `±Δ(S)D_QD_PR`; then Lemma 5.1 |
| (R), ordinary column | `ρ` | `Σ_{b∈S} ε_bΔ(S∖b)D(y_1,y_b)G'` | `(μ − e_ρ, ε)` | `r − ρ`, `±G` |
| (R), `ε = 1`, `μ_ρ = 1` | `ρ = ℓ` | `Pf_{E_{ℓ−1}}(M ∪ 1)D_PR` | `(μ − e_ℓ, 1)`, marked block `M ∪ 1` with `t + 1` absorbed pairs | `r − ℓ` (`u = ℓ − 2` for `ℓ ≥ 2`; the border `y^{r−1}` for `ℓ = 1`), `±Pf_{E_ℓ}(M)` |

The cases cover every tail: the last option in `Λ` is an addition, the middle, the zero or a removal, and `Φ ≥ 1`. In (M, `ε = 1`) the sign `θ` is that of (F4) for `N = M ∪ 1`, `x = 1`, and depends on positions only, so the cancellation is exact.

## 6. §7: the induction, the root, Theorem O — CORRECT

`Sh_0 = {(∅, 0)}`. The step is the peeling lemma, Proposition 6.1, the induction hypothesis for the interlaced pairs `Λ_i` (Lemma 2.4), and Lemma 2.4 again. At the root: the patterns of `((1), 0)` give the `D_J`; a pattern of `(∅, 1)` gives `Pf_{{r−1}}(M)D_{P'}`, which lies in `(D_J)` by Lemma 5.1 with `ℓ = 0`. So `V_{root} = (D_J : J ∈ 𝒥)`. Corollary 6.2(ii): `{(∅, 0)}` at level `2k + 2` is an interlaced pair whose patterns are the perfect matchings. The upper bound quoted in Corollary 6.2(i) (paper, Remark 8.7(3): Proposition 8.5(iii) with Theorem A in characteristic `≠ 2`; integer vectors in characteristic `2`) is for the form in `2k + 2` variables; the passage to `2k + 1` variables is the map `θ` of §1.6. **The upper bound is not used by Theorem E.**

## 7. §8–§9: Theorem T3 and Theorem E — CORRECT

T3: checked by hand in the first pass (every case, including the two identities of case II, `J = 1`) and by own code, 40 ideals of 40 (`corpus4/regla298_sky/auditoria_T3.py`). Theorem E: §1.7 and Theorem O; for `m = 4` only T3 over `F_2` and B2.

## 8. Own gates (estimates written before each run)

Own code, nothing imported from the pilot: `corpus4/regla298_sky/fria_engine.py` (box rings, graded elimination, shapes, interlaced pairs, patterns of Definition 4.1, bordered Pfaffians, slices), `fria_gate1.py`, `fria_gate3.py`, `fria_gate4.py` (this one through Singular). Estimates: `fria_gate1.estimate`, `fria_gate3.estimate`, `fria_gate4.estimate`, written before the runs. Every run inside `vigia.sh`. **A gate is not a proof: it would have shown an error; it does not replace §1–§7.**

**G1 — Theorem 6.1 from the definitions.** For **every** interlaced pair `Λ ⊆ Sh_m`, with `V_Λ` built from the patterns exactly as in Definition 4.1 and `Z_Λ` counted point by point: `dim V_Λ ≥ |Z_Λ|`, with equality, in **163 interlaced pairs of 163**, in the 26 cells `(r, m, p)`: `r = 3`, `m = 2..6`, `p = 2, 3` (and `101` for `m = 4, 5`); `r = 5`, `m = 2..4`, `p = 2, 5` (and `101` for `m = 3, 4`); `r = 7`, `m = 2, 3` (`p = 2, 7`) and `m = 4` (`p = 2`); `r = 9`, `m = 3`, `p = 2`. Control that can fail: without the absorbed pairs (`t = 0` only) the dimension falls below `|Z_Λ|` in 15 of the 163.

**G2 — Lemma 2.4 and Proposition 6.1, as stated.** In the same cells: the number of completions of a tail is one number per shape and equals (2.1); every layer `Λ_i` is an interlaced pair; `Σ_i |Z_{Λ_i}| = |Z_Λ|` (0 failures in 163). And **Proposition 6.1 as ideal memberships**: the slices `W_j(V_Λ)` computed from the ideal itself (elimination ordered by the degree in `y_1`), and every pattern product of every shape of every layer `Λ_i` tested for membership in `W_{r−1−i}(V_Λ)`: **12 530 memberships, 0 failures**; `Σ_j dim W_j = dim V_Λ` in all.

**G3 — Theorem 7.6 of the paper at an even box, characteristic `2`, at every down-set** (the pilot measured the roots only). `q = 2`: `(α, β) = (1,1), (2,1), (2,2), (3,1), (3,2), (3,3), (4,1), (4,2), (5,1)`; `q = 4`: `(1,1), (2,1), (2,2), (3,1)`; `q = 8`: `(1,1), (2,1)`: `dim V_Λ = |Z_Λ|` in **51 down-sets of 51**. Calibration with an odd box (`q = 3`, characteristic `3`, `(2,2)`, `(3,2)`): 13 of 13. Control (generators of the maximal shapes only): below `|Z_Λ|` in 15 of the 64.

**G4 — the colour reduction for even `m`, from the literal generators `ψ_J` of [DS], colouring by colouring** (Groebner bases in Singular over a finite field containing `μ_{r'}`; the colourings are grouped by type, which is legitimate because the ideal is invariant under permutations of `t_1..t_{n+1}`: `(t_j − 1)φ(t_jt_k) = −t_k^{−1}(t_k − 1)φ(t_jt_k)`). For each colouring the measured `dim π_c(I)` is compared with `N^{(1)}(|𝒞_1|)·N^{(−1)}(|𝒞_{−1}|)·Π_ζ N_{bal}(|𝒞_ζ|, q)`, and the sum with `|Γ|`.
- Calibration on odd `m`: `(k, m, p) = (1, 15, 3)`, `(1, 15, 5)`: 0 mismatches, sums `546`, `546` (paper, Example 6.11).
- B3 (`p = 2`): `(1,12,2)`, `(2,12,2)`, `(1,24,2)`, `(1,20,2)` (`v ≥ 2`, never gated colouring by colouring by the pilot), `(1,14,2)`, `(2,6,2)`, `(2,14,2)`: 0 mismatches; sums `331, 15101, 1519, 1027, 469, 1001, 26041 = |Γ|`.
- B4 (`p` odd, `r'` even): `(1,12,3)`, `(2,12,3)`, `(1,18,3)` (box `9`), `(1,30,5)`: 0 mismatches; sums `331, 15101, 817, 2437 = |Γ|`.
- **A cell that is in neither [DS, §5] nor the pilot's runs, in the literal ring: `(n, m) = (4, 20)`.** Prime `2`: 126 colouring types, 0 mismatches, sum `87661`. Prime `5`: 56 types, 0 mismatches, sum `87661`. And `|Γ| = N_19(6) = 87661`, which is also the value of the polynomial of [DS, Remark 4.4] at `m = 20` (`120000 − 36000 + 3500 − 100 + 261`). So Conjecture 1.2 holds at `(n, m) = (4, 20)` by direct computation, independently of Theorem O.
- **More cells outside [DS, §5], in the literal ring** (0 mismatches and sum `= |Γ|` in each): `(n, m) = (4, 14)` at the primes `2` and `7` (`26041`); `(4, 30)` at the primes `2`, `3`, `5` (`329561`); and, at one prime only, `(4, 18)` prime `2` (`61601`), `(6, 10)` prime `2` (`345465`), `(6, 12)` prime `3` (`876331`). So Conjecture 1.2 is verified directly at `(4, 14)`, `(4, 20)` and `(4, 30)`; none of these uses Theorem O.
- Eight more cells were launched last (run E of `fria_gate4.estimate`); their outcome is in the addendum at the end of this file.

Totals of peak memory and time are in the logs (`fria_gate*.log`); the largest finished run used 99 MB.

## 9. Literature read in the original

- **[DS], arXiv:1405.4683v3** (text on disk): the setting is `m > 2`, any parity; Theorem 1.1, Definition 1.3, Theorem 1.4, Corollary 1.5, Claim 4.3 and its proof, Remark 4.4 (the count for even `m`), §5 (the cells computed: `(4, m)` for `3 ≤ m ≤ 12`, `(6,3)`, `(6,4)`, `(6,5)`, `(8,3)`). Read by me in this audit.
- **Degtyarev, arXiv:1512.06199** (`FUENTES_ORIGINALES_HODGE_2026-09-25/`): Conjecture 4.4, «for the full set `K = 𝒥`, `T_𝒥 = 0`», with «we failed to prove the conjecture in full generality»; no restriction on the parity of `m`. Read in the original (grep and the surrounding lines).
- **Aoki 1983, Theorem A** (same folder, OCR of the original): the Hodge classes of the Fermat variety of degree `m` and dimension `n` are all standard iff `m` is prime or `4`, or every prime divisor of `m` is greater than `n + 2`. So `m = 4` is covered for every `n`. **Reading; the corollary «integral Hodge conjecture for Fermat quartics in every even dimension» is not written and not checked here.**
- **Searches (result pages only, not readings):** three web searches on the conjecture and on even degrees, and the arXiv list of A. Degtyarev (2015–2026): no later paper on this conjecture appears; the only related items are [DS], Degtyarev 2015, and Aljovin–Movasati–Villaflor (arXiv:1711.02628), who verify by computer the integral Hodge conjecture for quartic and quintic Fermat fourfolds. **I did not search for the odd-box statement under other names (orthogonal group, regular nilpotent, Pfaffian identities).** I cannot say the result is new; I can say I did not find it.

## 10. Errors of the auditor in this audit

1. **A wrong memory estimate.** Run C of G1: I estimated `< 600 MB` for the cell `(r, m, p) = (5, 5, 2)`; the watchdog killed it at `1.28 GB` after 77 s (the list of pattern products is kept in memory). The four cells before it in the same run had finished and are counted; `(5, 5, 2)` is **not done** and was not repeated.
2. **A wrong line in my own gate script.** `fria_gate4.py` prints the comparison of the sum with `|Γ|` using the formula for even `m`; in the two calibration cells with `m = 15` it printed «equal False» although the sums (`546`) are the right ones for odd `m` (paper, Example 6.11). The mismatch counts are not affected.
3. **Theorem T3 was not derived again in this audit**: §7 relies on the first pass of this morning (by hand, and 40 ideals by own code).
4. **All my sealed predictions were «it holds», and all held.** After the first pass I expected the proof to survive; a pre-registration in which nothing can fail is weak, and I say so. The parts with real risk were the gates G2 (memberships computed from the ideal, not from the constructions) and G4 (literal generators, another program), and the new literal cells.
5. I did not search the literature for the odd-box statement under other names.
6. I am the same kind of reader as the pilot. This audit does not replace the second reader.
7. **An invalid control in gate G5** (first version): I compared with the ideal generated by `|S| = ℓ + 3`; for `t = 1` that ideal is `(Δ(M))`, and an alternating polynomial is always a multiple of the Vandermonde determinant, so the control could not fail (it «held» 17 times of 17). Replaced by a control that can fail (one fixed `S` only), which fires 17 times of 17. Log of the invalid version kept: `fria_gate5_A_invalid_control.log`.
8. **Two cells killed by the watchdog in run E** (memory): `(k, m, p) = (2, 16, 2)` after 29 s and `(4, 4, 2)` after 3 s, both pure powers of `2` with no colour splitting. **Not done.** So step B2 has no literal check of mine beyond the cells of [DS, §5].

## Addendum (same day, after the background runs ended)

**Run E of G4 (literal ring, one watchdog per cell).** Finished, each with 0 mismatches and sum `= |Γ|`: `(2,30,2)`, `(2,30,3)` → `329561`; `(3,12,2)` → `876331` (186 s); `(2,28,2)`, `(2,28,7)` → `263901`; `(2,18,3)` → `61601` (516 s, 727 MB). Killed by memory: `(2,16,2)`, `(4,4,2)` (error 8).

**Cells of Conjecture 1.2 verified by me in the literal ring of [DS], at every prime dividing `m`, none of them in [DS, §5]:** `(n, m) = (4, 14)`: `26041`; `(4, 18)`: `61601`; `(4, 20)`: `87661`; `(4, 28)`: `263901`; `(4, 30)`: `329561`; **`(6, 12)`: `876331`**. (One prime only: `(6, 10)` at the prime `2`, `345465`.) They rest on [DS, Theorem 1.1(a)], on the splitting of Lemma 6.1 of the paper (the Chinese remainder theorem) and on Groebner bases; not on Theorem O, nor on the block theory. The pilot had checked `(6, 6)`.

**G5 — Lemma 5.1 as stated.** `Pf_{E_ℓ}(M) ∈ (Δ(S)·D_Q : |S| = ℓ + 1)` in 17 non-trivial instances of 17: `r = 3`: `(ℓ, t) = (0,1)`; `r = 5`: `(0,1), (1,1), (0,2)`; `r = 7`: `(0,1), (1,1)`; `r = 9`: `(0,1), (1,1)`; characteristics `2`, `3`, `5`, `7`, `101` as listed in `fria_gate5_B.log`. In four more instances with `ℓ + t > h` the Pfaffian is zero, as Remark (2) of §5 of the proof says. Control (one fixed `S` only): fails 17 times of 17.

The verdict of §0 does not change.

— Grepy Chats
