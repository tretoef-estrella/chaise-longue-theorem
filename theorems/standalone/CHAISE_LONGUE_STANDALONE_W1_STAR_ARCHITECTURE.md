> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE STAR ARCHITECTURE OF SIGNED MATCHING ARRANGEMENTS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_W1_STAR_ARCHITECTURE.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE STAR ARCHITECTURE OF SIGNED MATCHING ARRANGEMENTS
## Exhaustive flat classification through codimension three, star–word decomposition, localization of the defect complex, and the crosscut Möbius table

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source results: campaign Tanda 4 (W1), Tandas 9–10 (lattice classification, Möbius recursions), audited in CARDANO_TANDA4/9/10. Every numerical claim carries its verification anchor (engine gate or exhaustive count); the two falsified shortcuts relevant to this material are documented in §7. Nothing in this document is new mathematics; it is the complete formal record of results proven and gated in the campaign logs.*

---

### 1. Objects and conventions

**Definition 1.1 (ambient and sheets).** Fix an integer `n = 2m` (in the Fermat application `n = 2k+2`, `m = k+1`) and the polynomial ring `S = F₃[x₁, …, x_n]`. A **signed perfect matching** `J` of `[n]` is a partition of `[n]` into `m` unordered pairs. To each `J` associate the **sheet**
> `V_J := { x ∈ A^n : x_a + x_b = 0 for every pair {a,b} ∈ J }`,
a linear subspace of dimension `m`. The **full arrangement** is `X = ∪_J V_J` over all `(n−1)!!` matchings; the **bipartite sub-arrangement** `B_m` fixes a partition of `[n]` into two `m`-sets `A ⊔ B` and takes only the `m!` matchings pairing `A` with `B`.

**Definition 1.2 (flats).** A **flat** is any intersection `∩_{J∈T} V_J`, `T ≠ ∅`, together with the ambient space as `0̂`. Flats ordered by reverse inclusion form the **intersection lattice** `L`. The **codimension** of a flat is computed inside a sheet: a flat `G ⊆ V_J` has codimension `c` when `dim G = m − c`.

**Definition 1.3 (star).** For a flat `G`, its **star** is the sub-arrangement of all sheets containing `G`; its **star lattice** is the interval `[0̂, G]` in `L`.

**Convention 1.4.** Throughout, "generic point of a flat `G`" means a point of `G` outside all flats strictly below `G`; all sign computations are in characteristic 3 (in particular `2 = −1 ≠ 0`, which is used at several places and flagged where load-bearing).

### 2. The Pattern Lemma: what a flat is

**Lemma 2.1 (flats are balanced value patterns).** Let `G = ∩_{J∈T} V_J` be a flat and let `x ∈ G` be generic. Define the graph `Γ_x` on `[n]` with an edge `{a,b}` whenever `x_a + x_b = 0`. Then the connected components of the union of the matchings in `T` (as edge sets) determine `G` completely, and each component is of exactly one of two types:
**(i) a balanced ±block:** a set `C ⊆ [n]` on which the coordinates take a single pair of opposite values `{s, −s}`, `s` a free parameter, with `|C ∩ {x_i = s}| = |C ∩ {x_i = −s}|`;
**(ii) a zero block:** a set `C` on which all coordinates vanish, occurring exactly when the union graph restricted to `C` contains an odd cycle of sign conditions.
*Proof.* On the flat, each matching in `T` imposes `x_a = −x_b` along its edges; following a path in the union graph multiplies the value by `(−1)^{length}`. Within a component, all coordinates therefore equal `± s` for one parameter `s`, the sign determined by path parity — consistently if and only if the component is bipartite in the parity sense. If some cycle has odd parity, then `s = −s`, i.e. `2s = 0`; since `char F₃ ≠ 2`, `s = 0` and the component is a zero block (this is the characteristic-3 zero-forcing, absent in characteristic 2). Balancedness of type (i): each matching in `T` restricted to `C` is a perfect matching of `C` pairing a `+`-vertex with a `−`-vertex (values `s` and `−s` must sum to zero and `2s ≠ 0` on a type-(i) block), so the two sign classes are equinumerous. Conversely any assignment of parameters to such a pattern satisfies every matching in `T`, so the pattern determines `G`. ∎

**Corollary 2.2 (dimension).** `dim G = #(type-(i) components)`; equivalently, a flat of codimension `c` has a pattern whose components consume `c` "merges": a type-(i) block of size `2j` contributes `j−1` to `c`, a zero block of size `2j` contributes `j`.

**Definition 2.3 (letters and words).** The **letter `B_j`** is the connected pattern "type-(i) block of size `2j`" (star: the `j!` bipartite matchings of its `+/−` classes). The **letter `Z_j`** is "zero block of size `2j`" (star: all `(2j−1)!!` matchings of the block). A flat's **word** is the multiset of its non-trivial letters (untouched pairs are trivial `B₁`'s). By Lemma 2.1 and Corollary 2.2:
> **Theorem 2.4 (exhaustive classification).** The flats of codimension `c` are exactly the words with `Σ_{B_j} (j−1) + Σ_{Z_j} j = c`, each letter on its own disjoint variable set, the remaining variables matched in pairs. In particular:
> **codim 1:** `B₂` only (**swap flats**).
> **codim 2:** `B₃` (6-cycle type), `B₂·B₂` (double swap), `Z₂` (zero 4-block) — three types, no others.
> **codim 3:** `B₄`, `B₃·B₂`, `B₂·B₂·B₂`, `Z₂·B₂`, `Z₃` — five types, no others. (A `Z₂·Z₂` pattern is the all-zero condition on 8 variables, i.e. the single connected letter `Z₄` of codimension 4, not a codim-3 word; more generally adjacent zero blocks merge, so zero letters in a word are automatically maximal — this uniqueness is load-bearing for the count of the deepest flat and is stated here explicitly.)
*Proof.* Immediate from Lemma 2.1 and the additivity of Corollary 2.2 over components; the codim-3 enumeration is the complete list of solutions of the merge equation with `j ≥ 2`. ∎

### 3. Stars are words; the two-sheet property; localization

**Theorem 3.1 (star = word of letters).** The sheets containing a flat `G` with word `w = L₁ ⋯ L_r` (plus trivial pairs) are exactly the products (choice of a matching within each letter's block, the trivial pairs fixed): `#star(G) = ∏ (j_i! or (2j_i−1)!!)`. In particular the star lattice of `G` is the interval lattice of the word arrangement on its own variables.
*Proof.* A sheet `V_J ⊇ G` must satisfy: at a generic point of `G`, `J`'s condition `x_a = −x_b` holds. Generic type-(i) values are distinct across different components and nonzero, so `J` cannot pair variables of different components (values would not be opposite), nor pair two same-sign variables of one block (`s ≠ −s`); within a type-(i) block `J` is any `+/−` bipartite matching, within a zero block any matching (`0 = −0`), and on trivial pairs `J` must keep the pair (the two free values force it). Conversely each such choice contains `G`. ∎

**Corollary 3.2 (two sheets per codim-1 flat; the Swap Theorem).** A codim-1 flat has word `B₂`, whose star has `2! = 2` sheets. *Third-sheet exclusion, verified in both letter families at the generic point (campaign Tanda 3): for `B`-flats a third matching would need a coincidence of generic values; for `Z`-flats (4-cycle collapses, pattern `(s,−s,s,−s)`) the excluded third matching demands `s = −s`.*

**Theorem 3.3 (localization).** Let `𝒞` be any complex of modules built functorially from the arrangement's sheets, flats, and restriction maps (in the campaign: the defect complex `F → T → P`). Localizing at the generic point of a flat `G` kills every sheet and flat not containing `G` (their defining ideals meet the local unit group) and leaves exactly the star's complex. Hence every local statement about `𝒞` at `G` is a statement about the (strictly smaller, by Theorem 3.1, unless `G` is the deepest flat) word arrangement of `G`'s star. ∎

### 4. The crosscut Möbius table (the coefficients of inclusion–exclusion)

**Definition 4.1.** For a flat `G`, the **crosscut coefficient** is `c(G) := Σ_{T : ∩_{J∈T}V_J = G} (−1)^{|T|+1}` (sum over nonempty sheet subsets with intersection exactly `G`). By the crosscut theorem, `c(G) = −μ(0̂, G)` in the intersection lattice; the point-count of the union over `F_q` is `|X(F_q)| = Σ_G c(G)·q^{dim G}` (linear flats have exactly `q^{dim}` points).

**Computation rule 4.2 (the recursion).** `μ(0̂, 0̂) = 1` and `μ(0̂, G) = −Σ_{F ⊋ G} μ(0̂, F)`, the sum over all lattice elements strictly above `G` (including `0̂` and the sheets). All computations below apply this recursion with the COMPLETE flat lists of the relevant star lattices, which Theorem 3.1 reduces to finite counts inside each word.

**Warning 4.3 (a falsified shortcut — do not "simplify").** For a product word `G₁·G₂` the interval `[0̂, G]` is NOT the product of the letter intervals (both are glued at the single bottom `0̂`), and `μ` is NOT multiplicative. The naive product rule yields `c(Z₂·B₂) = +1` and total floor coefficient `−1617`; the true values (below) give `−2037`, the sealed coefficient of `P₃`. The shortcut is registered in the campaign cemetery (NAIVE-PRODUCT-MU) with these killing numbers.

**Table 4.4 (the star lattices and their μ, each recursion shown).** Sheets always carry `μ = −1` (above them: only `0̂`); every codim-1 flat carries `μ = +1` (two sheets: `−(1 − 2) = 1`). Codimension 2, computed on the three stars:
- **`B₃`** (6 sheets; 9 codim-1 flats above the deep flat, namely `3×3` pairs of merged `+`/`−` pairs): `μ = −(1 − 6 + 9) = −4`.
- **`B₂·B₂`** (4 sheets; 4 codim-1 flats above `G`, the "edge" pairs): `μ = −(1 − 4 + 4) = −1`.
- **`Z₂`** (3 sheets; 3 codim-1 flats above `G`): `μ = −(1 − 3 + 3) = −1`.
Codimension 3, computed on the five stars with their complete intermediate lists:
- **`B₄`**: 24 sheets; **72** codim-1 flats (pairs `{σ, σ·(ij)}`: data = merged `+`-pair × merged `−`-pair × matching of the remaining `2+2`, `6·6·2 = 72`); codim-2 flats: 16 of type `B₃` (`C(4,3)² = 16`, remaining letter forced) and 18 of type `B₂·B₂` (`3·3·2`). Recursion: `μ = −(1 − 24 + 72 + 16·(−4) + 18·(−1)) = −(−33) = 33`, so `c(B₄) = −33`.
- **`Z₃`**: 15 sheets; 45 codim-1; codim-2: 10 of type `B₃` (6-cycle patterns in 6 variables) and 15 of type `Z₂` (`C(6,4)`, remaining pair forced); no `B₂·B₂` (needs 8 variables). `μ = −(1 − 15 + 45 − 40 − 15) = 24`, `c = −24`.
- **`Z₂·B₂`**: 6 sheets (`3·2`); codim-1 above `G`: `3·2 + 3·1 = 9` (zero-side line × B-side sheet; zero-side sheet × swap); codim-2 above `G`: `1·2 + 3·1 = 5`, each with `μ = −1` by its own two-step recursion (spelled in the source log: `Z₂`-deep×sheet: `−(1−3+3) = −1`; line×swap: `−(1−4+4) = −1`). `μ(G) = −(1 − 6 + 9 − 5) = 1`, `c = −1`.
- **`B₃·B₂`**: 12 sheets; codim-1: `9·2 + 6·1 = 24` (each `μ = +1`, two sheets above); codim-2: `1·2` of type (`B₃`-deep × sheet, `μ = −4` each) and `9·1` of type (codim-1 × swap, `μ = −1` each). `μ(G) = −(1 − 12 + 24 − 8 − 9) = 4`, `c = −4`.
- **`B₂·B₂·B₂`**: 8 sheets; codim-1: 12 (`μ = 1`); codim-2: 6 (`μ = −1`). `μ(G) = −(1 − 8 + 12 − 6) = 1`, `c = −1`.

**Verification anchors (Ley 17).** (a) The codim-2 row feeds the floor's `q^{k−1}` coefficient `4·cnt_i + cnt_{ii} + cnt_z`: at `k = 2` it returns `55`, at `k = 3` it returns `1645` — both equal to the sealed coefficients of `P₂`, `P₃`. (b) The codim-3 row feeds `q^{k−2}`: at `k = 2`, `−24`; at `k = 3`, `−33·35 − 24·28 − 210 = −2037` — again the sealed values. (c) The full-lattice recursion at the origin returns the sealed constants `−24` (k=2) and `918` (k=3). These six byte-exact hits across two dimensions are the external gates of the entire table.

### 5. The counts of each type, for every k

**Theorem 5.1 (species counts).** In the full arrangement on `n = 2k+2` variables, with `(2j−1)!!` the double factorial and `pattern(B_j)`-counts as derived (a `B_j` block on `2j` chosen variables admits `C(2j, j)/2` sign splits; the standard specializations below):
> codim 1: `3·C(2k+2,4)·(2k−3)!! = (2k+1)!!·k(k+1)/2`.
> codim 2: `cnt(B₃) = 10·C(2k+2,6)(2k−5)!!` · `cnt(B₂²) = (9/2)·C(2k+2,4)C(2k−2,4)(2k−7)!!` · `cnt(Z₂) = C(2k+2,4)(2k−3)!!`.
> codim 3: `cnt(B₄) = 35·C(2k+2,8)(2k−7)!!` · `cnt(Z₃) = C(2k+2,6)(2k−5)!!` · `cnt(Z₂·B₂) = 3·C(2k+2,4)C(2k−2,4)(2k−7)!!` · `cnt(B₃·B₂) = 30·C(2k+2,6)C(2k−4,4)(2k−9)!!` · `cnt(B₂³) = (9/2)·C(2k+2,4)C(2k−2,4)C(2k−6,4)(2k−11)!!` (unordered letters; empty binomials read as zero).
**Gates:** `k = 3`: `630; 280/315/210; 35/28/210/0/0` — every value equal to the independently filed campaign records (the last three being the fourth-relay codim-3 counts). `k = 2`: `45; 10/0/15; 0/1/0/0/0`, consistent with the Sofa lattice. ∎

### 6. What this document supports downstream
(a) The stratified census law (top three coefficients for every k) and the floor polynomials (`P₂`, `P₃` derived in full; `P_k` to depth 4 for every k) consume exactly Table 4.4 + Theorem 5.1. (b) The codimension induction (W3) consumes Theorems 3.1 and 3.3. (c) The slack stratification of the collar consumes Theorem 2.4's type lists.

### 7. Attack surface (declared honestly, with what a break would require)
**(A) Completeness of the classification (Lemma 2.1 / Theorem 2.4).** The single most consequential claim. A break requires exhibiting a flat whose generic point violates the two-type component structure — i.e. a coordinate value not in `{±s_C, 0}` on its union-graph component. The parity argument leaves no room in characteristic ≠ 2; a referee should verify the odd-cycle forcing (`2s = 0 ⟹ s = 0`) and the balancedness count. External check: any missed codim ≤ 3 type would shift a floor coefficient and break at least one of the six byte-exact anchors of §4.
**(B) The intermediate flat lists of §4.4.** Each `μ` is only as good as the completeness of the flats strictly above `G` in its star. The lists follow from Theorem 3.1 applied inside each word; the cheapest independent audit is a brute-force lattice enumeration of the `B₄` star (24 sheets — the 72 was itself the correction of an earlier undercount of 36, documented with its killing number 216/72 = 3).
**(C) The two-sheet genericity (Cor. 3.2)** for `Z`-flats at large `m` — verified for the generic pattern; a referee should confirm no degenerate `Z`-flat admits a third sheet.
**(D) The count formulas (§5)** at the first unverified dimension (`k = 4`): the predictions `6300/14175/3150` (codim 2) and `1575/630/9450/6300/0` (codim 3) are one engine run away from confirmation or refutation.

**Anchors and sources.** TANDA4_NERVE_THEOREMS_v1 (W1); TANDA9/10 (lattices, μ, counts, gates); CARDANO_TANDA4/9/10 audits; cemetery entries FLAT-COUNT-MISCOUNT-B4 and NAIVE-PRODUCT-MU (both with killing numbers). All engine logs at github.com/tretoef-estrella.
