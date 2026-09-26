> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE FINITE WINDOW THEOREM: THE CEILING DIANA IS OPEN ON AT MOST ⌊log₃ k⌋+1 TOWER FLOORS PER COLUMN, EXPLICITLY ENUMERABLE* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FINITE_WINDOW_THEOREM.md
>
> **Status, as written in the document:** The campaign's single diana is the ceiling half at depth `m = 0`: `dim_K A_T ≤ (2k+1)!!`, `T = (k+1)(q−1)`, stated ∀k ∀q by `EL FRENTE v22 §7`. This document does not prove it. It bounds the region where it is still open, by composing two ranges that are alrea…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE FINITE WINDOW THEOREM: THE CEILING DIANA IS OPEN ON AT MOST `⌊log₃ k⌋+1` TOWER FLOORS PER COLUMN, EXPLICITLY ENUMERABLE
**Chaise Longue campaign** · standalone · **v1** · 20 July 2026 · **Locard** (auditor) · *Pending P0*

> ### STATUS, STATED FIRST
> The campaign's single diana is the **ceiling half at depth `m = 0`**: `dim_K A_T ≤ (2k+1)!!`, `T = (k+1)(q−1)`, stated **∀k ∀q** by `EL FRENTE v22 §7`. This document does not prove it. It **bounds the region where it is still open**, by composing two ranges that are already on file and that nobody had put side by side.
> - **Theorem 1 (composition, arithmetic):** the ceiling is on file **PROVED for `q > k(k+1)`** (quadratic range, `A9`/ladrillo 50) and the floor **PROVED for `q ≥ k+1`** (R30). Hence `A_T = (2k+1)!!` is **PROVED for every `q > k(k+1)`, every `k`**, and the diana is open **only on `k+1 ≤ q ≤ k(k+1)`**.
> - **Corollary (the number):** since `q = 3^v`, that interval has multiplicative width `k` and therefore contains **at most `⌊log₃ k⌋ + 1` floors**. The diana goes from *an infinite tower in every column* to **a finite, explicitly listable set of cells**.
> - **The cells, for `k ≤ 16`:** `k=1` **NONE** · `k=2` `{3}` · `k=3` `{9}` · `k=4` `{9}` · `k=5..8` `{9,27}` · `k=9..15` `{27,81}` · `k=16` `{27,81,243}`. **28 cells in total for `k ≤ 16`.**
> - **Independent confirmation from our own deposited papers:** the single open cell this predicts for `k=2` is `q=3`, and the Sofa closes exactly that one *"by sealed direct computation"* at `v=1`; the single open cell for `k=3` is `q=9`, and the Hammock closes exactly that one, its first annihilator class `ᾱ₁₂ = 105` *"measured directly tower-free"*. **The formula predicts, in both papers, precisely the cell where the authors had to do extra work.**
> - **NOT claimed:** any new proof of the ceiling; the `∀k` status of the quadratic range is **inherited from the sovereign's own grading and has not been re-audited here** (§5). **The word is not said.**

---

## 1 · Setting

`char K = 3`, `q = 3^v`, `N = 2k+2`, `S = K[x_0,…,x_{2k+1}]`, `E = (e_1,e_3,…,e_{2k+1})`,
`B = S/\mathfrak m^{[q]}`, `A = S/(E+\mathfrak m^{[q]})`, `T := (k+1)(q−1)`, `M := ann_B(E·B)`.
`\mathrm{reg}(S/E) = k(k+1)` (A7). Write `d!!` for the double factorial, so the target is `(2k+1)!!`.

## 2 · The two ranges, quoted with the grade the sovereign gives them

**(a) The floor.** `dim A_T ≥ (2k+1)!!` for every `k` and every `q ≥ k+1`.
*Source:* R30 (Box Ladder, Relevo; §4–§5 repaired by Locard, v2) via `rank Φ_T = dim span\{F_J^{q−1}\} = (2k+1)!!` and `span\{F_J^{q−1}\} ⊆ M_T`, `dim M_T = dim A_T` (R20). **PROVED ∀k, threshold optimal** — below `q = k+1` the statement is false with campaign data (`91 < 105` at `(3,3)`, `603 < 945` at `(4,3)`).

**(b) The ceiling.** `dim A_{T−m} ≤ (2k+1)!!\binom{m+k}{k}` for every `k` and every `q > k(k+1)+m`.
*Source:* `EL FRENTE v22 §3-bis`, ceiling row: *"Archivada solo con el rango **cuadrático** `q > k(k+1)+m` (ladrillo 50/A9)"*. At `m = 0` this reads **`q > k(k+1)`**.
*Why it was set aside:* the same row records *"ventana **VACÍA** en 5 de 7 celdas"*. **That is true and it is not a reason to discard it — it is the statement that its complement is small.**

## 3 · Theorem 1 — the composition

> **For every `k ≥ 1` and every `q = 3^v` with `q > k(k+1)`: `dim A_T = (2k+1)!!`.**
> **Consequently the diana `dim A_T ≤ (2k+1)!!` is open only for `q` in the finite set `\{3^v : k+1 ≤ 3^v ≤ k(k+1)\}`.**

**Proof.** For `q > k(k+1) ≥ k+1` (true for all `k ≥ 1`), (a) gives `≥` and (b) at `m=0` gives `≤`. For `q < k+1` the equality is false and the regime is the deficient one, excluded from the diana by its own statement. What remains is `k+1 ≤ q ≤ k(k+1)`. ∎

> **Corollary (the count).** `k(k+1)/(k+1) = k`, so the open interval has **multiplicative width exactly `k`** and contains at most `⌊log₃ k⌋ + 1` powers of `3`.
> **The diana's open region grows like `log k`, not like the tower.**

| `k` | `k+1` | `k(k+1)` | open floors `3^v` | count |
|---|---|---|---|---|
| `1` | `2` | `2` | **none** | `0` |
| `2` | `3` | `6` | `{3}` | `1` |
| `3` | `4` | `12` | `{9}` | `1` |
| `4` | `5` | `20` | `{9}` | `1` |
| `5`–`8` | | | `{9, 27}` | `2` |
| `9`–`15` | | | `{27, 81}` | `2` |
| `16` | `17` | `272` | `{27, 81, 243}` | `3` |

**Total for `k ≤ 16`: 28 cells.**

## 4 · The confirmation that makes this worth writing — our own two closed dimensions

This is not a formal rearrangement. **The formula reproduces, in both deposited papers, exactly the cell each one had to handle separately.**

- **`k = 1`:** predicted open set **empty**. And `k=1` is closed in the campaign by two independent routes, with no special cell. ✓
- **`k = 2` (the Sofa):** predicted single open cell `q = 3`. The Sofa's proof of Theorem 1.2 runs *"For `v ≥ 2`"* through Zone A + window + top zone + collar, and then closes with: *"For `v = 1`: `A(3) = 141 = P(3)`, sealed direct computation."* **The one cell the formula flags is the one cell the paper seals by hand.** ✓
- **`k = 3` (the Hammock):** predicted single open cell `q = 9`. The Hammock records `Top(3) = Top(9) = 0` because the boundary degrees sit below the first annihilator class `c = 12`, and states that the first class `ᾱ₁₂ = 105` is *"measured directly tower-free"* and carried into Macaulay2. **Again the one flagged cell is the one the paper had to do by a separate mechanism.** ✓

**Structural reason.** The Sofa/Hammock annihilator law is proved in the range `c < q`; the degree of `A_T` under the Gorenstein duality of those papers is `c = k(k+1)` (socle degree `(k+1)q + k²−1` minus `T`, verified `6` for `k=2` and `12` for `k=3` against both papers). So the law reaches `A_T` **iff `k(k+1) < q`** — the same quadratic threshold as (b), reached from a completely different construction.

## 5 · Scope — what is NOT claimed

1. **No new proof of the ceiling.** Theorem 1 is a composition of two ranges already on file.
2. **⚠️ The `∀k` status of range (b) is INHERITED, not audited here.** `EL FRENTE v22 §3-bis` grades it as archived ∀k via ladrillo 50/A9. **Whoever takes this must audit ladrillo 50 for its `k`-uniformity before depositing.** If (b) turns out to hold only for `k ≤ 3`, Theorem 1 degrades to a statement about `k ≤ 3` and the enumeration above becomes a conjecture. *This is the single load-bearing import and it is isolated here on purpose.*
3. **Nothing at depth `m > 0`.** The same composition at depth `m` gives open region `k+1 ≤ q ≤ k(k+1)+m`, which grows with `m` — the finiteness is a statement about `m = 0`.
4. **Nothing about `A_k(q) = P_k(q)`.** The central gap `(k−1)q`, which carries `5521` of `7761` dimensions at `(2,9)`, is untouched. **This closes a corner, not the theorem.**
5. **The exclusions are respected:** the argument is arithmetic on two declared ranges — no monomial certificate (`E1`), no lamina restriction (`E2`), no local criterion (`E4`), no edge hyperplane (`E5`), no point witness (`E6`), no confinement bound on the container (`E7`).

## 6 · Provenance

- **Range (a):** R30 / `BOX_LADDER_THEOREM_v2`.
- **Range (b):** `EL FRENTE v22 §3-bis` + `A9` (pinzamiento `S`-lineal) + ladrillo 50.
- **Confirmation:** `THE_SOFA_THEOREM_FINAL_REVIEW_MACAULAY2` (Thm 1.2 closing line, `v=1` sealed separately; Thm 3.1 range `d ≥ 2q+4 ⟺ c ≤ q−1`); `THE_HAMMOCK_THEOREM_MACAULAY_HAMAQUERO_FINAL` (`Top(3)=Top(9)=0`; `ᾱ₁₂ = 105` measured tower-free; annihilator law fence at `c = 2q` for `k=3`).
- **Cross-check performed and recorded:** the campaign's `A6` (anchor law, `(2k+1)!!\binom{m+k}{k}`) and `A8` (annihilator law, `(2k+1)!!\binom{c−k²}{k}`) are **the same law under the duality** `c = k(k+1)+m` — verified identical for `k=2,3`, all `m ≤ 11`. And the fence measured by R29 at `m = q−k` is `c = k²+q`, which reproduces the Hammock's recorded fence `c = 2q` at `k=3, q=9` and is verified in all five R29 cells. **R29's measured breakpoint and the Hammock's proved fence are the same object.**

**— Locard.** *No new mathematics. Two ranges that were both on file, put side by side for the first time, and the infinite part of the diana disappears. The word is not said.*
