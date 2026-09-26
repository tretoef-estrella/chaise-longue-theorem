> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE FLOOR CROSSCUT THEOREMS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_F_FLOOR_CROSSCUT.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE FLOOR CROSSCUT THEOREMS
## The Degtyarev–Shimada floor polynomials from the flat lattice: top coefficients for every dimension, `P₂` and `P₃` derived in full, and the staircase machine — with a constitutional candidate falsified en route

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tandas 9–10 (F1, F2, F3), audited in CARDANO_TANDA9/10. Inputs: the crosscut theorem (classical), the Star Architecture standalone (flat classification, Möbius table 4.4, species counts 5.1). The floor polynomial `P_k(q)` is the characteristic-0 point count `|X(F_q)|` of the arrangement — the quantity Conjecture 1.2 of [DS] asserts is preserved in characteristic 3; deriving its coefficients turns the target of the conjecture from a certified number into a theorem.*

---

### 1. The mechanism

For linear flats, `|G(F_q)| = q^{dim G}` exactly, so inclusion–exclusion over sheet subsets grouped by their intersection gives
> **`P_k(q) = |X(F_q)| = Σ_{G ∈ L} c(G)·q^{dim G}`,  `c(G) = Σ_{T: ∩T = G}(−1)^{|T|+1} = −μ(0̂, G)`** (the crosscut theorem).
By the Star Architecture's dimension count, a codim-`c` flat contributes at `q^{k+1−c}`: the coefficient of `q^{k+1−c}` in `P_k` is the sum of `c(G)` over the codim-`c` flats — closed the moment the type list, the Möbius table, and the counts are (all three are: Star Architecture §§2, 4, 5).

### 2. Theorem F1 (depth 3: the top three coefficients, every k)

> `P_k(q) = N·q^{k+1} − [N·k(k+1)/2]·q^k + [4·cnt_i(k) + cnt_{ii}(k) + cnt_z(k)]·q^{k−1} + O(q^{k−2})`, `N = (2k+1)!!`.
*Proof.* Sheets contribute `+1` each; each swap flat, lying on exactly two sheets (Swap Theorem), contributes `(−1)^{2+1} = −1`; the three codim-2 coefficients are the alternating sums over each star computed in the Möbius table: 6-cycle `+4` (the sum `Σ_{|T|≥2}(−1)^{|T|+1} = −5` over the 6-sheet star, corrected by the 9 pairs landing on codim-1 flats: `−5 + 9 = 4`), double-swap `−3 + 4 = +1`, zero-flat `−2 + 3 = +1`. Counts by species (Star Architecture Thm 5.1). ∎
**Gates:** `k = 2`: `(15, −45, 55)` with `55 = 4·10 + 0 + 15` — the sealed `P₂` coefficients; `k = 3`: `(105, −630, 1645)` with `1645 = 4·280 + 315 + 210` — the sealed `P₃` coefficients. **Predictions:** `k = 4`: `(945, −9450, 42525)`; `k = 5`: `(10395, −155925, 1074150)`.

**A constitutional candidate falsified (Kepler's discipline, exhibited).** The campaign constitution carried, as its living example of a two-point candidate, the pattern "`P_k`'s second coefficient `= −2k·N`" (from `−45 = −3·15` at `k=2`... in fact `−45 = −3·15` and `−630 = −6·105`). F1 proves the law is `−N·k(k+1)/2`, which equals `−2k·N` **iff `k(k+1)/2 = 2k` iff `k = 3`** — and at `k = 2`: `−45 = −15·3 = −N·k(k+1)/2` ✓ while `−2k·N = −60` ✗. The two-point pattern was a coincidence *centered at the very dimensions measured*; the discipline of refusing to promote it (Ley 48) is here vindicated by the derived law. (Cemetery record: the candidate, with its killing comparison.)

### 3. Theorem F2 (depth 4: the `q^{k−2}` coefficient, every k)

> `[q^{k−2}]P_k = −33·cnt_{B₄} − 24·cnt_{Z₃} − 1·cnt_{Z₂·B₂} − 4·cnt_{B₃·B₂} − 1·cnt_{B₂³}`,
with the five codim-3 crosscut coefficients from the Möbius table (each recursion written there) and the species counts (`35·C(2k+2,8)(2k−7)!!`, `C(2k+2,6)(2k−5)!!`, `3·C(2k+2,4)C(2k−2,4)(2k−7)!!`, `30·C(2k+2,6)C(2k−4,4)(2k−9)!!`, `(9/2)·C(2k+2,4)C(2k−2,4)C(2k−6,4)(2k−11)!!`).
**Gates:** `k = 2`: counts `(0,1,0,0,0)` give `−24` — the sealed constant of `P₂` (at `k = 2` this coefficient IS the constant). `k = 3`: counts `(35, 28, 210, 0, 0)` — equal to the independently filed campaign records — give `−33·35 − 24·28 − 210 = −2037`, the sealed `q`-coefficient of `P₃`. **Predictions:** `k = 4`: `−101745`; `k = 5`: `−4178790`.
**The falsified shortcut (bench record).** The multiplicative guess `μ(word) = ∏ μ(letters)` yields `c(Z₂·B₂) = +1` and total `−1617 ≠ −2037`; it was executed by the gate before any proof used it (cemetery: NAIVE-PRODUCT-MU). The surviving values are per-lattice recursions with complete flat lists.

### 4. Theorem F3 (the ground floor: `P₂` and `P₃` complete)

The constant of `P_k` is the crosscut coefficient of the origin (the unique dimension-0 flat: the single connected letter `Z_{k+1}` — uniqueness by the zero-block maximality of the Star Architecture), computed by the μ-recursion over the ENTIRE lattice, all of whose higher strata are now themselves theorem values:
> `k = 2`: `c(origin) = −(1 − 15 + 45 + 10·(−4) + 15·(−1)) = −24` ✓ the sealed constant.
> `k = 3`: `c(origin) = −(1 − 105 + 630 + 280·(−4) + 315·(−1) + 210·(−1) + 35·33 + 28·24 + 210·1) = 918` ✓ the sealed constant.
> **Therefore `P₂(q) = 15q³ − 45q² + 55q − 24` and `P₃(q) = 105q⁴ − 630q³ + 1645q² − 2037q + 918` are derived in full — every coefficient a lattice computation.** ∎
**The staircase machine.** Each further depth of `P_k` for higher `k` is: (next codimension's word list — finite, from the merge equation) + (species counts — mechanical) + (per-word μ-recursion — finite). The floor of every dimension is a terminating algorithm whose every step has been executed and gated through `k = 3` and predicted at `k = 4, 5`.

### 5. Consequences
(a) The floor jaw of the sandwich (`A_k ≥ P_k`) now rests on a DERIVED target (previously: the [DS] identification plus point-count verification). (b) With X1's census top-3, the collar budget `B_k = P_k − ZA_k − W_k − Top_k` becomes unconditional at its top block (the Collar Budget standalone). (c) The identical lattice, read with census residuals instead of `q^{dim}`-weights, produces the census law — floor and census are the two readings of one combinatorial object, which is the structural heart of the Chaise Longue.

### 6. Attack surface
(A) The crosscut theorem's application (linear flats: exact point counts `q^{dim}` — verify no flat is non-reduced or non-linear). (B) The `B₄` star's 72 (not 36) codim-1 flats — the count that killed an earlier candidate; recount it (`6·6·2`). (C) The origin's uniqueness as a word (`Z₂·Z₂` = the same all-zero flat as `Z₄` — the maximality argument; a double count would shift F3's constants, which hit both seals). (D) The five codim-3 counts at `k = 3` against the fourth-relay records (35/28/210, with `B₃·B₂` and `B₂³` structurally zero at eight variables — check `C(2,4) = 0` does the killing). (E) The `k = 4` predictions: one point count of `|X(F_p)|` over a few primes decides depth 4.

**Anchors.** TANDA9_FLOOR_CROSSCUT_BUDGET_LAW_v1 (F1) · TANDA10_FLOOR_STAIRCASE_COMPLETE_v1 (F2, F3) · CARDANO_TANDA9/10 audits · Star Architecture standalone (table 4.4, counts 5.1, tombstones) · Sofa Theorem (the sealed `P₂`) · Hammock Theorem (the sealed `P₃`) · session sympy logs. github.com/tretoef-estrella.
