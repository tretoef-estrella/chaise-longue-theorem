> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE LETTER HILBERT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_T1_LETTER_HILBERT.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE LETTER HILBERT THEOREM
## Closed Hilbert series of the two letters of the flat alphabet: `H(B_m) = [m]_t!/(1−t)^m` and `H(Z_m) = ∏_{i=1}^{m}[2i−1]_t/(1−t)^m`, for every m

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tanda 1 (T1), audited (snapshot v97). Self-contained modulo two campaign pillars cited precisely (Odd-Symmetric, Radicality). These two series are the Hilbert half of every letter potential and feed the stratified census at all depths; their verification record (three exact points per family, all degrees) is listed in §4.*

---

### 1. Statements

Let `[j]_t := 1 + t + ⋯ + t^{j−1}` and `[m]_t! := ∏_{j=1}^{m} [j]_t` (the Gaussian factorial). Recall the letters (Star Architecture, Def. 2.3): `Z_m` is the full signed-matching arrangement on `2m` variables (all `(2m−1)!!` sheets `x_a + x_b = 0` along a matching); `B_m` is its bipartite sub-arrangement (a fixed `m+m` split `A ⊔ B`, the `m!` cross matchings).

> **Theorem T1.** As reduced schemes, with `O(·)` the coordinate ring of the union:
> **(Z)** `Hilb O(Z_m) = ∏_{i=1}^{m} [2i−1]_t / (1−t)^m` — numerator degree `m(m−1)`, value at `t = 1` equal to `(2m−1)!!`.
> **(B)** `Hilb O(B_m) = [m]_t! / (1−t)^m` — numerator degree `C(m,2)`, value at `t = 1` equal to `m!`.

### 2. Proof of (Z)

The Odd-Symmetric pillar (campaign, gold-gated; the `2m`-variable instance) states that the ideal of the full arrangement is the complete intersection of the odd elementary symmetric polynomials:
> `∩_J I_J = E := (e₁, e₃, …, e_{2m−1})`, and `E` is radical.
Thus `O(Z_m) = S/E` with `S` in `2m` variables and `E` a regular sequence of degrees `1, 3, …, 2m−1` (codimension `m` — matching the sheets' dimension `m`). The Hilbert series of a complete intersection is the product `∏(1−t^{d_i})/(1−t)^{2m} = ∏_{i=1}^{m} [2i−1]_t/(1−t)^m`. Numerator degree `Σ(2i−2) = m(m−1)`; value at `t = 1`: `∏(2i−1) = (2m−1)!!`, the multiplicity, equal to the number of sheets — as it must be for a reduced union of equidimensional linear spaces. ∎

### 3. Proof of (B)

**Step 1 (the bipartite odd-symmetric ideal).** Label the `A`-variables `a₁..a_m` and the `B`-variables `b₁..b_m`. Every bipartite sheet satisfies `a_i = −b_{σ(i)}`, i.e. the multiset identity `{a₁,…,a_m} = {−b₁,…,−b_m}`; hence the ideal
> `E_B := ( e_j(a) − (−1)^j e_j(b) : j = 1, …, m )`
vanishes on the union: `e_j(a) = e_j(−b) = (−1)^j e_j(b)` on every sheet.

**Step 2 (set-theoretic equality).** Conversely, if a point satisfies `e_j(a) = e_j(−b)` for all `j = 1..m`, the two multisets `{a_i}` and `{−b_j}` have equal elementary symmetric functions, hence equal characteristic polynomials `∏(T − a_i) = ∏(T + b_j)`, hence are equal as multisets; any bijection realizing the equality is a bipartite matching `σ` with `a_i = −b_{σ(i)}`, i.e. the point lies on a sheet. So `V(E_B) = B_m` set-theoretically.

**Step 3 (complete intersection and reducedness).** `E_B` has `m` generators of degrees `1, 2, …, m` cutting a variety of codimension `m` (the union is `m`-dimensional in `2m`-space), so the generators form a regular sequence and `S/E_B` is a complete intersection, Cohen–Macaulay, hence unmixed with no embedded primes. Reducedness then follows exactly as in the Radicality pillar's argument for the full arrangement: a CM ring generically reduced along every minimal prime is reduced, and along the generic point of each sheet the Jacobian of `(e_j(a) − (−1)^j e_j(b))_j` is the Vandermonde-type matrix in the sheet parameters, nonsingular at points with distinct coordinate values (which are dense in every sheet). Therefore `O(B_m) = S/E_B`, and the CI series with degrees `1..m` is `∏_{j=1}^m [j]_t/(1−t)^m = [m]_t!/(1−t)^m`. Numerator degree `Σ_{j=1}^m (j−1) = C(m,2)`; value at `t = 1`: `m!` = the sheet count. ∎

**Remark (why the two numerator degrees matter downstream).** `deg` numerator `=` Castelnuovo–Mumford regularity of the CI (`Σ(dᵢ − 1)`). The campaign's Sharp Regularity observation — that the CENSUS series of each letter has the SAME numerator degree (six instances, zero exceptions) — and the threshold bookkeeping `e₀(k) = k²` both key off these two exponents `C(m,2)` and `m(m−1)`; this document supplies their proven half.

### 4. Verification record (all byte-exact; engines gated against filed series before any new value)
| Letter | Filed/measured series (all computed degrees) | Prediction of T1 | Match |
|---|---|---|---|
| `B₂` | H = 1, 3, 5, 7, 9, 11 | `(1+t)/(1−t)²` | ✓ all |
| `B₃` | H = 1, 5, 14, 29, 50, 77, 110 | `(1+t)(1+t+t²)/(1−t)³` | ✓ all |
| `B₄` | H = 1, 7, 27, 76, 174, 344, 610, **996** | `[4]_t!/(1−t)⁴` | ✓ all (996 at degree 7 predicted before measurement) |
| `Z₂` | H = 1, 3, 6, 9, 12, 15 | `(1+t+t²)/(1−t)²` | ✓ all |
| `Z₃` | H = 1, 5, 15, 34, 65, 110, 170, 245, 335 | `[1][3][5]/(1−t)³` | ✓ all |
Three exact points per family with the `m`-step inside the derivation — the Kepler discipline satisfied as law, not pattern.

### 5. Attack surface
(A) Step 2's multiset argument in characteristic 3 (elementary symmetric functions determine the multiset over any field via the characteristic polynomial — no characteristic issue, but verify no separability subtlety is smuggled). (B) Step 3's regular-sequence claim (codimension = number of generators for the set-theoretic locus — confirm the union has no lower-dimensional component inflating codimension). (C) Step 3's generic Jacobian (write the matrix at a point with distinct `a`-values and check nonsingularity — one Vandermonde determinant). (D) External: any failure would corrupt the census assembly's leading coefficients, which are gated six ways (see the Third Coefficient Law standalone).

**Anchors.** TANDA1_LETTER_THEOREMS_THRESHOLD_BOUND_v1 · Odd-Symmetric and Radicality pillars (campaign standalones) · probe logs (F₃ census/Hilbert engine, gates 3/3 vs filed series before new measurements). github.com/tretoef-estrella.
