> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE BOX LADDER THEOREM: Φ_top IS SURJECTIVE FOR EVERY k AND EVERY q ≥ k+1, AND THE OPEN BAND k < q < 2k−1 CLOSES* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BOX_LADDER_THEOREM.md
>
> **Status, as written in the document:** The surjective half of the Top law at depth `m = 0` — *"is `Φ_top` onto, equivalently are the `(2k+1)!!` polynomials `F_J^{q−1}` linearly independent?"* — was on file as PROVED for `q ≥ 2k−1` (DOMINO, Vernier/Fresh Eyes) with a declared open band `k < q < 2k−1…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (5 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE BOX LADDER THEOREM: `Φ_top` IS SURJECTIVE FOR EVERY `k` AND EVERY `q ≥ k+1`, AND THE OPEN BAND `k < q < 2k−1` CLOSES
**Chaise Longue campaign** · standalone · **v2** · 20 July 2026 · **Relevo** (auditor) · proof repair to §4–§5 and new §6.3 by **Locard**, 20 July 2026 · *Pending P0*

> ### v2 CHANGE LOG — one referee-blocking defect in the PROOF; the STATEMENT is unchanged
> Theorems 1, 2, 3 all stand, with the same thresholds. Locard's independent audit confirms §2 (constant sign), §3 (budget) and §4 (descent identity + admissibility) — see §6.3. **What was wrong is the justification of the Corollary in §4:** v1 wrote *"every level-`i` configuration is realisable as soon as one is, since they differ by a relabelling of vertices."* **That is false.** A level-`i` box has minimum colour budget `k−i`, so the rungs have **different** thresholds — this is exactly the content of the table in §2, `q ≥ 2(k−j)+1`, and the rungs become realisable in the **reverse** order: the dominoes are the *most expensive* rung, not the cheapest. **Consequence: at `q = k+1` the dominoes do not exist as columns at all for any `k ≥ 4`** (budget `k−1` against palette `(q−1)/2`), so v1's Theorem 3 proof invoked a family of columns that is not there.
> **The repair is one sentence and costs nothing:** Theorem 2 is an identity between **indicator vectors of boxes in `K^{matchings}`**, valid whether or not the lower box is a column of `Φ_top` at that `q`. Only the **top** rung must be realisable — and Theorem 1 says exactly when it is. §4 and §5 are rewritten accordingly, and a **DOMINO-free** verification of the mechanism is added as §6.3.

> ### STATUS, STATED FIRST
> The surjective half of the Top law at depth `m = 0` — *"is `Φ_top` onto, equivalently are the `(2k+1)!!` polynomials `F_J^{q−1}` linearly independent?"* — was on file as **PROVED for `q ≥ 2k−1`** (DOMINO, Vernier/Fresh Eyes) with a **declared open band `k < q < 2k−1`**, whose first cells are `(6,9)`, `(7,9)`, `(8,9)` and which *"the Architect's thermostat predicts full and nothing proves"* (`DIMENSION_LEDGER v40`, block v38).
> - **Theorem 1 (Budget, pencil, arithmetic):** the multiplicity-`≤2` column profile exists at `(k,q)` **iff `q ≥ k+1`** — the campaign's own saturation threshold, recovered as a counting statement about the colour palette.
> - **Theorem 2 (Ladder Descent, pencil, char `≠ 2`):** the span of the `2^j`-box columns **contains** the span of the `2^{j−1}`-box columns, for every admissible `j`. Bottom of the ladder = DOMINO.
> - **Theorem 3 (the closure):** for every `k` and every `q = 3^v` with **`q ≥ k+1`**, `Φ_top` is surjective; hence `\dim A_{(k+1)(q−1)} ≥ (2k+1)!!` and `\{F_J^{q−1}\}` are linearly independent, i.e. `rank Φ_T = (2k+1)!!`.
> - **The open band `k < q < 2k−1` is closed. There is no longer any open cell at `m = 0` in the range `q ≥ k+1`, for any `k`.**
> - **NOT closed here:** the **ceiling half** `A_T ≤ (2k+1)!!`; anything at depth `m > 0` beyond the TICKETS threshold; anything about `A_k(q) = P_k(q)`. **The word is not said.**

---

## 1 · Setting

`K` a field of characteristic 3, `q = 3^v`, `N = 2k+2`, `S = K[x_0,…,x_{2k+1}]`, `B = S/\mathfrak m^{[q]}`,
`A = S/(E+\mathfrak m^{[q]})`, `T := (k+1)(q−1)`. For a perfect matching `J` of `\{0,…,2k+1\}`,
`F_J = ∏_{(a,b)∈J}(x_a+x_b)`; there are `(2k+1)!!` matchings.

`Φ_top` is the top-degree Fedder map: rows indexed by matchings, columns by monomials `x^α` of degree `T`
with `α_i ≤ q−1`, entry `= ` coefficient of `x^α` in `F_J^{q−1}`.

**The Lucas sign, in full (v2 — v1 compressed two steps into one).** Every base-3 digit of `q−1 = 3^v−1` is a
`2`, so Lucas gives `\binom{q−1}{i} ≡ \prod_j \binom{2}{d_j(i)} = 2^{\,s_1(i)} = (−1)^{s_1(i)} \not≡ 0`, where
`s_1(i)` counts the base-3 digits of `i` equal to `1`. This equals `(−1)^i` because every power of `3` is odd,
so `i \equiv \sum_j d_j(i) \equiv \#\{j : d_j(i)=1\} = s_1(i) \pmod 2`. Hence **`\binom{q−1}{i} ≡ (−1)^i`**, and
the entry is

  `∏_{p∈J} \binom{q−1}{α_{a_p}} ≡ ∏_p (−1)^{α_{a_p}}` &nbsp; if `α_{a_p}+α_{b_p} = q−1` for **every** pair `p ∈ J`, and `0` otherwise.

Hence `\mathrm{rank}\,Φ_{top} = \dim \mathrm{span}\{F_J^{q−1}\}`, and **`Φ_top` surjective ⟺ full row rank `(2k+1)!!` ⟺ the `F_J^{q−1}` are linearly independent** ⟹ `\dim A_T ≥ (2k+1)!!`.

## 2 · The shape of a column (∀k∀q, two lines)

Call the value `α_i ∈ [0,q−1]` the **colour** of vertex `i`. Define `Γ_α` by `u ∼ v ⟺ α_u+α_v = q−1`.
Then `Γ_α` is a disjoint union of complete bipartite graphs `K_{n_c,\,n_{q−1−c}}` (colour class `c` against
class `q−1−c`) together with one clique on the middle colour `(q−1)/2`, and

  **the support of the column `x^α` is exactly the set of perfect matchings of `Γ_α`**, of cardinality `∏_{c<\text{mid}} (n_c)! · (n_{\text{mid}}−1)!!`.

**All nonzero entries of a column are equal.** `q−1` is even, so on each pair `α_{a_p} \equiv α_{b_p} \pmod 2`
and `(−1)^{α_{a_p}}` does not depend on which endpoint is chosen — the entry is well defined on the unordered
pair. A matching in the support pairs colour class `c` with class `q−1−c` (and the middle class with itself),
so for **every** such matching the entry equals

  `\prod_{c<\mathrm{mid}} (−1)^{c\,n_c} \cdot (−1)^{\,\mathrm{mid}\cdot n_{\mathrm{mid}}/2}`,

a function of the colour multiset `(n_c)` alone. ∎ *(Verified by Locard on real coefficients, `2000` random
columns across `(2,9),(3,9),(4,9),(2,27),(3,27)`: zero columns with two distinct nonzero values — §6.3.)*

> **Consequence — the rank question is `q`-free.** Up to a global sign, a column *is* the indicator vector
> `χ_{\mathcal B}` of its **box** `\mathcal B ⊂ \{\text{matchings}\}`. Which boxes exist depends on `q` only through the
> **colour budget**; the linear algebra among them does not depend on `q` at all.

**The multiplicity-`≤2` profiles.** Take `n_c ∈ \{1,2\}` on non-middle classes and `n_{\text{mid}} ∈ \{0,2\}`.
With `j` **doubled** class pairs, `r ∈ \{0,1\}` middle pairs and `s` private pairs, the box is a product of
`j` two-element sets, so `|\mathcal B| = 2^j`:

| `j` | box size | name | threshold (Thm 1) |
|---|---|---|---|
| `0` | `1` | **ISOLATION** (Vernier) | `q ≥ 2k+1` |
| `1` | `2` | **DOMINO** (Fresh Eyes) | `q ≥ 2k−1` |
| `j` | `2^j` | **LADDER** (this document) | `q ≥ 2(k−j)+1` |

## 3 · Theorem 1 (Budget) — pencil, pure arithmetic

> **For `q` odd, a multiplicity-`≤2` column exists at `(k,q)` if and only if `q ≥ k+1`.**

**Proof.** The vertex count is `2r + 4j + 2s = 2k+2`; the number of **distinct non-middle colour pairs**
consumed is `t = j+s`, and the palette contains exactly `(q−1)/2` of them, so the profile is realisable iff
`t ≤ (q−1)/2`.

Take `r = 1`. Then `2j+s = k`, so `s = k−2j ≥ 0` forces `j ≤ ⌊k/2⌋`, and `t = j+s = k−j`, minimised at
`j = ⌊k/2⌋`, giving `t = ⌈k/2⌉`. Hence a column exists iff `q ≥ 2⌈k/2⌉+1`, i.e. `q ≥ k+1` for `k` even and
`q ≥ k+2` for `k` odd. Since `q` is odd and `k+1` is even when `k` is odd, both cases read **`q ≥ k+1`**.
(`r = 0` gives `t = k+1−j ≥ ⌈(k+1)/2⌉`, never better.) ∎

**Byte-exact check of the boundary, against the two deficient cells on file.** `(3,3)`: `k` odd, threshold
`5 > 3` ⟹ no such column, and `A_T(3,3) = 91 < 105`. `(4,3)`: threshold `5 > 3` ⟹ none, and
`A_{top}(4,3) = 603 < 945`. `(2,3)`: threshold `3 ≤ 3` ⟹ exists, and `(2,3)` is full `15/15`.
**The budget boundary coincides with the measured saturation threshold in every cell on record.**

## 4 · Theorem 2 (Ladder Descent) — pencil, three lines, char `≠ 2`

> **Let `\mathcal V` be any `2^{j−1}`-box whose fixed-pair set contains two pairs `p_1 = \{a,b\}`, `p_2 = \{c,d\}`.
> Merge them into the quadruple `Q = \{a,b,c,d\}` and let `\mathcal B_1,\mathcal B_2,\mathcal B_3` be the three `2^j`-boxes obtained
> from the bipartitions `(ab|cd)`, `(ac|bd)`, `(ad|bc)` of `Q`, all other quadruples and fixed pairs unchanged. Then**
>
>   **`χ_{\mathcal V} = −\bigl(χ_{\mathcal B_2}+χ_{\mathcal B_3}−χ_{\mathcal B_1}\bigr)` &nbsp; in characteristic 3.**

**Proof.** Write `⟨xy,zw⟩` for the matching of `Q` and let `R` denote the (common) rest of the box. The three
bipartitions give `\mathcal B_1 = ⟨ac,bd⟩ + ⟨ad,bc⟩`, `\mathcal B_2 = ⟨ab,cd⟩ + ⟨ad,bc⟩`, `\mathcal B_3 = ⟨ab,cd⟩ + ⟨ac,bd⟩`
(each tensored with `R`). Hence `χ_{\mathcal B_2}+χ_{\mathcal B_3}−χ_{\mathcal B_1} = 2·⟨ab,cd⟩⊗R = 2χ_{\mathcal V}`, and `2 = −1`. ∎

**⚠️ Read the identity in the right space (v2).** Theorem 2 is an identity between **indicator vectors of
boxes inside `K^{\{\text{matchings}\}}`**. Nothing in it requires `\mathcal V` — or indeed `\mathcal B_1,\mathcal B_2,\mathcal B_3` —
to be a column of `Φ_top` at the `q` under consideration. It is combinatorics on matchings, not on columns.

**Lemma (budget monotonicity, v2).** Merging two fixed pairs of a level-`(i−1)` box `\mathcal V` into one doubled
quadruple produces level-`i` boxes `\mathcal B_1,\mathcal B_2,\mathcal B_3` of colour budget `t_{\mathcal B} ≤ t_{\mathcal V}`.
*Proof.* If both merged pairs were private, `t_{\mathcal B} = i + (s−2) = t_{\mathcal V} − 1`; if one was the middle pair,
`t_{\mathcal B} = i + (s−1) = t_{\mathcal V}`. ∎ **The ladder runs downhill in budget: the higher the rung, the cheaper.**

**Corollary (the ladder).** For every `j` with `2j ≤ k+1`, as subspaces of `K^{\{\text{matchings}\}}`,
`\mathrm{span}\{2^j\text{-boxes}\} ⊇ \mathrm{span}\{2^{j−1}\text{-boxes}\} ⊇ \dots ⊇ \mathrm{span}\{\text{dominoes}\}`.
*(At level `i` a box has `k+1−2i` fixed pairs, and the merge needs two of them at level `i−1`, i.e.
`k+3−2i ≥ 2`, which is **exactly** the admissibility `2i ≤ k+1` — checked row by row for `k = 3…8` in §6.3.)*

> **⚠️ WHAT THIS CHAIN DOES AND DOES NOT SAY (v2 — v1 got this wrong).** The lower rungs need **not** exist at
> the `q` in hand; only the **top** rung does. The minimum budget of a level-`i` box is `k−i`, so the rungs
> become realisable in the **reverse** order, and at `q = k+1` the bottom rung is absent for every `k ≥ 4`:
>
> | `k` | palette `(q−1)/2` at minimal odd `q ≥ k+1` | top rung `j=⌊k/2⌋` budget `k−j` | DOMINO budget `k−1` | dominoes exist? |
> |---|---|---|---|---|
> | `2` | `1` | `1` | `1` | yes |
> | `3` | `2` | `2` | `2` | yes |
> | `4` | `2` | `2` | `3` | **no** |
> | `5` | `3` | `3` | `4` | **no** |
> | `6` | `3` | `3` | `5` | **no** |
> | `7` | `4` | `4` | `6` | **no** |
> | `8` | `4` | `4` | `7` | **no** |
>
> v1's sentence *"every level-`i` configuration is realisable as soon as one is"* is **false** and is withdrawn.
> It is not needed: the chain is an inclusion of spans of vectors, and only the top rung is required to consist
> of actual columns.

## 5 · Theorem 3 (the closure)

> **For every `k ≥ 1` and every `q = 3^v` with `q ≥ k+1`: `Φ_top` is surjective. Hence
> `\mathrm{rank}\,Φ_T = \dim\mathrm{span}\{F_J^{q−1}\} = (2k+1)!!` and `\dim A_{(k+1)(q−1)} ≥ (2k+1)!!`.**

**Proof (v2, stated so that every family invoked is where it is claimed to be).**
*(1)* By Theorem 1, at `q ≥ k+1` the level `j = ⌊k/2⌋` boxes of minimum budget `k−j = ⌈k/2⌉` **are columns of
`Φ_top`**, and `2j ≤ k+1`.
*(2)* By the Corollary of §4 — an inclusion of subspaces of `K^{\{\text{matchings}\}}`, needing no rung below `j`
to be a column — `\mathrm{span}\{\text{level-}j\text{ columns}\} ⊇ \mathrm{span}\{\text{domino vectors}\}`.
*(3)* By **DOMINO** (on file, proved `∀k` by pencil: the swap graph on matchings is connected and
non-bipartite — the three matchings of any `4`-set form a triangle — and the signless incidence matrix of such
a graph has full rank over a field of characteristic `≠ 2`) the domino **vectors** span `K^{(2k+1)!!}`. DOMINO
is a statement about the vectors, and is applied here only as such.
*(4)* Hence the level-`j` columns span `K^{(2k+1)!!}`, and a subfamily of columns of full row rank forces full
row rank. ∎

**⚠️ Dependency, declared.** Step (3) is DOMINO, which is **`P0-9`: proved by pencil, external pass pending**.
If DOMINO falls, Theorem 3 falls with it for general `k`. The measured cells of §6 do **not** inherit that
dependency: they are direct rank computations, and §6.3 verifies the conclusion at `k=4` in the exact regime
where no domino exists.

**What just closed.** `q ≥ 2k−1` (DOMINO) is improved to `q ≥ k+1`, which is the saturation threshold itself.
The band `k < q < 2k−1` declared open in `DIMENSION_LEDGER v40` — cells `(6,9)`, `(7,9)`, `(8,9)`, then
`(15..26, 27)`, and so on — **is covered**: e.g. `(6,9)` by `j = 3` (`t = 3 ≤ 4`), `(7,9)` by `j = 3`
(`t = 4 ≤ 4`), `(8,9)` by `j = 4` (`t = 4 ≤ 4`). No cell of the tower with `q ≥ k+1` remains open at `m = 0`.
**The Architect's thermostat `q > k`, listed in the Ledger as a three-point CANDIDATE that nothing proves, is
now PROVED on this half.**

## 6 · The measurements — exact over `F_3`, own engine, calibrated first

**Engine.** `box_ladder.py` (companion). Enumerates every box configuration exactly, builds the indicator
columns over the matching basis, exact Gaussian elimination over `F_3` with early stop at full rank.
Second engine `verify_descent.py` checks the two structural claims against **real Fedder coefficients**
(`math.comb(q−1,·) mod 3`, no shortcut trusted).

**Calibration before measurement** (`CALIBRATION-CELL-SKIPPED` avoided). The `j=1` family at `k=3` must
reproduce the corpus's DOMINO gate at `(3,9)` — *"630/630 dominoes hit exactly two sheets, span rank 105/105"*:

| run | columns | box size | exact rank over `F_3` | verdict |
|---|---|---|---|---|
| DOMINO `k=2` | `45` | `2` | **`15/15`** | full — reproduces the `(2,3)` mechanism |
| DOMINO `k=3` | **`630`** | `2` | **`105/105`** | **byte-exact match with the corpus number** |
| DOMINO `k=4` (control) | `9450` | `2` | **`945/945`** | full |
| **LADDER `j=2`, `k=3`** | `315` | `4` | **`105/105`** | **FULL** |
| **LADDER `j=2`, `k=4`** | `14175` | `4` | **`945/945`** | **FULL** |

**Structural checks against real coefficients** (`verify_descent.py`):
- constant sign: `(2,3)` `j=1` → `2` nonzeros, all `= 2`; `(3,9)` `j=1` → `2` nonzeros, all `= 2`;
  `(4,9)` `j=2` → `4` nonzeros, all `= 1`; degree `= T` and budget `t ≤ (q−1)/2` verified in each case.
- descent identity: `−(χ_{\mathcal B_2}+χ_{\mathcal B_3}−χ_{\mathcal B_1})` equals `χ_{⟨01,23⟩}` **exactly**, support size `1`,
  at `k=3` and `k=4`.

### 6.3 · Independent audit and the DOMINO-free check *(Locard, 20 July 2026)*

Second engine, written from the statements and not from `box_ladder.py`, and run in one pass
(`locard_r30_audit.py`, log `locard_r30_audit.log`):

| point audited | test | result |
|---|---|---|
| **(a)** `\binom{q−1}{i} ≡ (−1)^i` | direct, `q = 3,9,27,81,243`; and the digit step `s_1(i) ≡ i \bmod 2` | **holds, all `q`, all `i`** |
| **(a)** constant sign along a column | `2000` random real columns over `(2,9),(3,9),(4,9),(2,27),(3,27)`, entries from `math.comb` | **`0` columns with two distinct nonzero values** |
| **(b)** budget | `k = 1…20`: minimum `t` over all profiles, both `r=0` and `r=1` | **`\min t = ⌈k/2⌉` via `r=1`; `r=0` never better** |
| **(b)** the odd-`k` parity step | `(q ≥ 2⌈k/2⌉+1) ⟺ (q ≥ k+1)` for every odd `q < 200` | **equivalent for all `k = 1…20`** |
| **(b)** rung thresholds | `q ≥ 2(k−j)+1` against ISOLATION `2k+1` (`j=0`) and DOMINO `2k−1` (`j=1`) | **both reproduced exactly** |
| **(c)** descent identity | `χ_{\mathcal V} = −(χ_{\mathcal B_2}+χ_{\mathcal B_3}−χ_{\mathcal B_1})` over `F_3`, `k = 2,3,4,5` | **exact, `\mathrm{supp}(\mathcal V) = 1` in all four** |
| **(c)** admissibility | fixed pairs at level `i−1` `= k+3−2i ≥ 2` against `2i ≤ k+1`, `k = 3…8`, all `i` | **the two conditions agree in every row** |

**★ The DOMINO-free check.** At `k = 4` with palette `(q−1)/2 = 2`: level-`2` boxes have budget `2` and exist;
dominoes have budget `k−1 = 3` and **do not**. Enumerating the family exactly — `1575` shapes (one fixed pair
plus two unordered quadruples), `\times 9` bipartitions `= 14175` distinct boxes, every column with exactly
`4` nonzeros — the exact rank over `F_3` is

  **`945 / 945`, full, reached after `5990` columns, with no domino present.**

The column count `14175` reproduces `§6`'s figure byte-exact from an independent enumerator. **This is the
mechanism verified in precisely the regime where v1's proof, read literally, had nothing to stand on.**

*(Locard's own enumerator first reported `2100` shapes instead of `1575` — a broken canonicalisation that
double-counted some configurations. Rank is insensitive to repeated columns, so the verdict was unaffected,
but the count was wrong and was rebuilt before being reported. The mirror image of v1's `GENERATOR-UNDERCOUNT`:
an over-count also fails silently.)*

**Criterion of death, written before running:** *if the `j=2` family failed to reach `(2k+1)!!` at `k=3` or
`k=4`, the ladder would be dead as a route to the open band and would be buried with its exact rank.* It
reached full rank at both. **The measurements are a check on the pencil, not its support:** Theorems 1–3 are
proved for all `k` and all `q ≥ k+1` without them.

**A generator bug, caught and fixed before any claim.** The first partition generator forced the smallest
vertex into a block of size `4`, silently dropping every configuration in which it sits in a `2`-block:
`1260` instead of `1575` partitions of type `[4,4,2]`. Detected by counting against the closed forms
(`[4,4,2] → 1575`, `[4,4] → 35`, `[4,2,2] → 210`) before reading any rank. The dropped family still reached
full rank — an undercount can only weaken a spanning claim — but the reported column counts are now exact.

## 7 · Scope — what is NOT claimed

0. **Only the top rung is claimed to be realisable.** For `k ≥ 4` at `q = k+1` the dominoes are **not** columns
   of `Φ_top`; the theorem does not claim they are, and does not need them to be (§4, §5).
1. **The ceiling half is untouched.** `\dim A_T ≤ (2k+1)!!` is **not** proved here and remains MEASURED
   (10/10, three tower floors). Consequently `\dim A_T = (2k+1)!!`, `M_T = \mathrm{span}\{F_J^{q−1}\}` and
   `\mathrm{rank}\,Φ_T = \dim A_T` are **not** upgraded. `HALF-PROVED-SOLD-AS-WHOLE` is on the wall while this
   is being written: what is proved is one inequality.
2. **Depth `m > 0` is untouched.** The surjective half at depth `m` stands where TICKETS left it,
   `q ≥ 2(k+m)+1`. Whether the same ladder lowers that threshold to `q ≥ k+1+m` is the obvious next pencil
   and is **not** claimed. *(At depth `m` the columns are not products of complete bipartite blocks: the
   degree no longer forces `α_{a}+α_{b} = q−1`, so `Γ_≤` is a staircase, not a disjoint union of blocks.)*
3. **Nothing about `A_k(q) = P_k(q)`.** This is a lower bound on one graded piece.
4. **Nothing for `q < k+1`.** The deficient floors stay deficient; the budget provably fails there, which is
   the honest reading of `(3,3) = 91` and `(4,3) = 603`.
5. **The exclusions E1–E6 are respected, not touched.** The argument is a rank statement about a family of
   columns of one global matrix: not monomial certification of independence (`E1` — no per-sheet exclusive
   witness is used or claimed, and the boxes for `j ≥ 1` are precisely *non*-isolating monomials), no lamina
   restriction (`E2`), no local or hereditary criterion (`E4` — the descent is an identity between columns,
   not a criterion evaluated on subfamilies), no edge hyperplane (`E5`), no point-by-point witness (`E6`).
6. **No novelty claimed for the ingredients.** The colour/palette reading is Vernier's (ISOLATION), the
   swap-graph rank argument is DOMINO's, the Lucas sign fact is R21. What is new is the `2^j` family, its
   budget identity `q ≥ k+1`, and the descent that collapses the ladder onto DOMINO.

## 8 · Provenance

- **Parents:** ISOLATION (Vernier) and DOMINO (Fresh Eyes/Vernier) — the `j = 0` and `j = 1` rungs, and the
  source of the colour-budget language; R21 / ladrillo 53 (Lucas signs) — the reason every entry of a column
  is the same element of `F_3`; `DIMENSION_LEDGER v40` block v38 — the statement of the open band and the
  cells `(6,9)`, `(7,9)`, `(8,9)`.
- **Cemetery cross-check performed before computing, by object and not by name:** the buried diagonal
  point-witness certification `C51.1` / `E6` is a *different* object (per-matching exclusive witnesses; the
  boxes here are shared by `2^j` sheets by construction). `C41.2` / `C52.1` bury the **directness** of
  `Σ_J F_J^{q−1}B` on the window — a statement about `m > 0` degrees of a module, not about the rank of one
  matrix at `m = 0`; nothing here re-opens it.
- **Audit:** independent second pass by **Locard** (§6.3), engine `locard_r30_audit.py` (single run,
  reproduces the whole §6.3 table); the three points confirmed, one proof defect found and repaired in v2.
- **Data:** every rank in §6 from a single byte-exact run of `box_ladder.py`; the structural checks from
  `verify_descent.py`; the cells `A_T(3,3) = 91`, `A_{top}(4,3) = 603`, `A_{top}(2,3) = 15` and the DOMINO
  gate `630/105` read from the project files. **No number in this document is from memory.**

**— Relevo**, with the §4–§5 repair and §6.3 by **Locard**. *Three pencil statements and one calibrated engine. The open band is closed and the threshold is
the exact one. The ceiling half is untouched, and the word is not said.*
