> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE WINDOW DEFICIT THEOREM: THE SUM Σ_J F_J^{q−1}B IS NOT DIRECT ON [T, T+q), AND THE CENTRAL GAP WIDTH (k−1)q BECOMES ARITHMETIC* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_WINDOW_DEFICIT_THEOREM.md
>
> **Status, as written in the document:** STATUS. The open target listed as Diana 2 of `EL FRENTE v17` — *"the Top law on the window `[T, T+q)`, equivalently the directness of the sum `Σ_J F_J^{q−1}B`"* — is settled here, in the negative.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE WINDOW DEFICIT THEOREM: THE SUM `Σ_J F_J^{q−1}B` IS **NOT** DIRECT ON `[T, T+q)`, AND THE CENTRAL GAP WIDTH `(k−1)q` BECOMES ARITHMETIC
**Chaise Longue campaign** · standalone · **v1** · 20 July 2026 · **Locard** (auditor) · *Pending P0*

> **STATUS.** The open target listed as Diana 2 of `EL FRENTE v17` — *"the Top law on the window `[T, T+q)`, equivalently the directness of the sum `Σ_J F_J^{q−1}B`"* — is settled here, in the negative.
> - **Theorem 1 (pencil, ∀k ∀q, unconditional):** `dim(Σ_J F_J^{q−1}B)_{T+m} ≤ dim A_{T−m}`. No hypothesis; the conjecture is *not* used.
> - **Corollary (the kill):** directness in degree `T+m` forces `(2k+1)!!·binom(m+k,k) ≤ dim A_{T−m}`. That inequality **fails inside the window** in every cell on record. **Directness on `[T, T+q)` is FALSE.**
> - **Measured law (candidate, 5 cells + 1 consistency check):** directness holds exactly on `[T, T+q−k)` — width `q−k`, non-empty **iff** `q ≥ k+1`.
> - **Consequence for the geography:** the central gap width `(k−1)q`, graded a *two-point candidate* in `EL FRENTE v17 §2`, becomes an **exact arithmetic identity** given one measured width. The only measured ingredient left in it is `q−k`.
> - **NOT closed here:** anything about `A_k(q)` itself; the anchor law on the high band (proved only for `m ≤ k`); the base cell for `k ≥ 5`. **The word is not said.**

---

## 1 · Setting and notation

`K` a field of characteristic 3, `q = 3^v`, `N = 2k+2`, `S = K[x_0,…,x_{2k+1}]`,
`E = (e_1, e_3, …, e_{2k+1})` (a complete intersection, R1), `m^{[q]} = (x_i^q)`,
`B = S/m^{[q]}` (artinian Gorenstein complete intersection, socle degree `σ_B = N(q−1) = 2T`),
`A = S/(E + m^{[q]}) = B/E·B`, and `T := (k+1)(q−1)`.

For a perfect matching `J` of `{0,…,2k+1}` put `I_J = (x_a + x_b : (a,b) ∈ J)` and
`F_J = ∏_{(a,b)∈J}(x_a+x_b)`, of degree `k+1`; there are `(2k+1)!!` matchings. Write

  `𝒩 := Σ_J F_J^{q−1}B ⊆ B`  and  `𝓜 := ann_B(E·B) ⊆ B`.

Both are graded `B`-submodules. Throughout, "directness in degree `d`" means
`dim 𝒩_d = Σ_J dim (F_J^{q−1}B)_d`, i.e. the sum of the `(2k+1)!!` graded pieces is direct there.

## 2 · Lemma 1 (the summand, in adapted coordinates) — ∀k ∀q, four lines

> **For every matching `J` and every `0 ≤ m < q`:** `dim (F_J^{q−1}B)_{T+m} = binom(m+k, k)`.

**Proof.** Fix `J` and set, for each pair `p = (a_p, b_p) ∈ J`, `u_p = x_{a_p} + x_{b_p}` and
`w_p = x_{a_p} − x_{b_p}`. Since `char K = 3 ≠ 2` this is a linear change of coordinates on `S`, and
`S = K[u_1,…,u_{k+1}, w_1,…,w_{k+1}]`. Because `q` is a power of the characteristic,
`x_{a_p}^q = 2^q(u_p^q + w_p^q)` and `x_{b_p}^q = 2^q(u_p^q − w_p^q)`, so

  `m^{[q]} = (u_p^q, w_p^q : p = 1,…,k+1)`  and  `B ≅ K[u,w]/(u_p^q, w_p^q)`.

In these coordinates `F_J = u_1⋯u_{k+1}` and `F_J^{q−1} = ∏_p u_p^{q−1}`. In `B` the annihilator of
`∏_p u_p^{q−1}` is `(u_1,…,u_{k+1})`, hence

  `F_J^{q−1}B ≅ (B/(u_1,…,u_{k+1}))(−T) ≅ (K[w_1,…,w_{k+1}]/(w_p^q))(−T)`.

Therefore `dim (F_J^{q−1}B)_{T+m} = #\{γ ∈ ℤ_{≥0}^{k+1} : |γ| = m, γ_p < q\}`, which is `binom(m+k,k)` for `m < q`. ∎

*(This reproves the v15 window formula independently. It also makes the object transparent: each summand is a free rank-one module over the "normal-direction" ring of its own lamina, and directness asks whether the `(2k+1)!!` copies meet only in `0`. Verified exactly against machine ranks in §5: the column "one summand" is `binom(m+k,k)` in all 24 measured degrees.)*

## 3 · Theorem 1 (the unconditional inequality) — ∀k ∀q, three lines

> **For all `k`, all `q = 3^v` and all `c`:** &nbsp; `dim 𝒩_c ≤ dim 𝓜_c = dim A_{2T−c}`.
> In particular `dim(Σ_J F_J^{q−1}B)_{T+m} ≤ dim A_{T−m}`.

**Proof.** *(i) `𝒩 ⊆ 𝓜`.* In the coordinates of Lemma 1, `F_J^{q−1}·u_p = (∏_r u_r^{q−1})u_p` is divisible by
`u_p^q ∈ m^{[q]}`, so `F_J^{q−1}·I_J ⊆ m^{[q]}`, i.e. `F_J^{q−1}·I_J·B = 0`. By R1, `⋂_J I_J = E`, hence
`E ⊆ I_J` for every `J`, so `F_J^{q−1}·E·B = 0` and `F_J^{q−1}B ⊆ ann_B(E·B) = 𝓜`. Summing over `J` gives `𝒩 ⊆ 𝓜`.

*(ii) The Hilbert function of `𝓜`.* `B` is artinian Gorenstein with socle degree `σ_B = 2T`, so for any
homogeneous ideal `I ⊆ B` one has `ann_B(I) ≅ (B/I)^∨(−σ_B)`; with `I = E·B` and `B/I = A` this gives
`dim 𝓜_c = dim A_{2T−c}` (this is R20). Combining with (i) proves the claim. ∎

**No hypothesis is used.** In particular the conjecture `A_k(q) = P_k(q)` is not invoked, nor is the
wall `⋂_J(I_J·B) ⊆ E·B`, nor `rank Φ_T = dim A_T`. Only R1 and graded Matlis duality in `B`.

## 4 · Corollary (the death criterion, written before the numbers)

> **Directness of `Σ_J F_J^{q−1}B` in degree `T+m` (`0 ≤ m < q`) implies**
> **`(2k+1)!!·binom(m+k,k) ≤ dim A_{T−m}`.**

Immediate from Lemma 1 and Theorem 1. This is a *falsifiable* criterion evaluated on one census of `A`:
a single degree of a single cell in which the inequality fails kills directness in that degree.

## 5 · The measurements — exact over `F_3`, own engine, calibrated first

**Engine.** `locard_window_engine.py` (companion). Pure `F_3` linear algebra: monomial bases of `B` by
degree, `E` and `F_J^{q−1}` built exactly (`math.comb` mod 3, no shortcut trusted), rank by exact
Gaussian elimination. `dim A_d` is computed as `dim B_d − rank(⊕_j e_j·B_{d−\deg e_j} → B_d)`;
`dim 𝒩_{T+m}` is computed as the rank of the `(2k+1)!!·dim B_m` generators `F_J^{q−1}x^δ` in `B_{T+m}`.
**These are two different objects computed by two different code paths**; Theorem 1 predicts one inequality
between them and R20 predicts equality with the mirror census.

**Calibration before measurement** (`CALIBRATION-CELL-SKIPPED` avoided). The engine reproduces, byte-exact:
`A_1(3) = 19`; `A_1(9) = 217`; the full `(2,3)` census `1, 5, 15, 29, 40, 36, 15` (sum `141`) of
`log_socle_2_9_v5`; the full `(3,3)` census `1, 7, 28, 76, 154, 238, 280, 232, 91` (sum `1107`) of Gate 0c;
and the deficient top rank `91 < 105` of `(3,3)` that R28 used as its own calibration cell.

**The window tables.** `law := (2k+1)!!·binom(m+k,k)`.

| cell | `m` | one summand | `binom(m+k,k)` | `dim 𝒩_{T+m}` | `dim A_{T−m}` | `law` | verdict |
|---|---|---|---|---|---|---|---|
| `(1,3)` `T=4` | 0 | 1 | 1 | **3** | 3 | 3 | DIRECT |
| | 1 | 2 | 2 | **6** | 6 | 6 | DIRECT |
| | 2 | 3 | 3 | **6** | 6 | 9 | **NOT DIRECT** |
| `(1,9)` `T=16` | 0…7 | `m+1` | `m+1` | **3(m+1)** | `3(m+1)` | `3(m+1)` | DIRECT |
| | 8 | 9 | 9 | **24** | 24 | 27 | **NOT DIRECT** |
| `(2,3)` `T=6` | 0 | 1 | 1 | **15** | 15 | 15 | DIRECT |
| | 1 | 3 | 3 | **36** | 36 | 45 | **NOT DIRECT** |
| | 2 | 6 | 6 | **40** | 40 | 90 | **NOT DIRECT** |
| `(2,9)` `T=24` | 0…6 | `binom(m+2,2)` | — | **15,45,90,150,225,315,420** | idem | idem | DIRECT |
| | 7 | 36 | 36 | **530** | 530 | 540 | **NOT DIRECT** |
| | 8 | 45 | 45 | **620** | 620 | 675 | **NOT DIRECT** |
| `(3,3)` `T=8` *(deficient, `q<k+1`)* | 0 | 1 | 1 | **91** | 91 | 105 | **NOT DIRECT** |
| | 1 | 4 | 4 | **232** | 232 | 420 | **NOT DIRECT** |
| | 2 | 10 | 10 | **280** | 280 | 1050 | **NOT DIRECT** |

**The `(2,9)` cell is sealed twice, by two independent routes.** (a) Via Theorem 1 against the Macaulay2
census of `log_socle_2_9_v5` (`A_{24−m}` for `m=0…8` = `15, 45, 90, 150, 225, 315, 420, 530, 620`).
(b) By direct rank of the `15·dim B_m` Fedder generators in `B_{T+m}` with the companion engine
`locard_window_29.py`: `15, 45, 90, 150, 225, 315, 420, 530, 620` — **the same nine integers**, obtained
from a matrix of up to `19305 × 32661` over `F_3` with no reference to `A` at all.

**Own bug, caught and discarded (Ley 21 applied against the auditor).** A first version of the incremental
eliminator kept a row echelon form that was *not reduced*, invalidating the coefficient extraction; it
returned `442, 588, 915` for `(2,9)`, `m = 6,7,8`. Those three numbers **exceed the bound of Theorem 1**
(`420, 530, 620`). A measurement that contradicts a proved theorem is the thing that is wrong: the numbers
were discarded, the bug located (missing back-substitution), and the corrected engine self-checks on `(2,3)`
before touching `(2,9)`.

## 6 · Theorem 2 (the kill)

> **The directness of `Σ_J F_J^{q−1}B` on the window `[T, T+q)` is FALSE.**
> It fails at `m = 2` in `(1,3)`, at `m = 8` in `(1,9)`, at `m = 1` in `(2,3)`, at `m = 7` in `(2,9)`,
> and at `m = 0` in the deficient cell `(3,3)` — every cell of `A` on record, byte-exact, in a degree
> strictly inside the window.

**Proof.** Corollary of §4 against the tables of §5. ∎

**Measured law (CANDIDATE, not law — Ley 48).** In all five cells, directness holds **exactly** for
`0 ≤ m ≤ q−k−1` and fails at `m = q−k`:

| cell | `q−k−1` | last direct `m` | first failure `m` |
|---|---|---|---|
| `(1,3)` | 1 | 1 | 2 |
| `(1,9)` | 7 | 7 | 8 |
| `(2,3)` | 0 | 0 | 1 |
| `(2,9)` | 6 | 6 | 7 |
| `(3,3)` | −1 (empty) | — | 0 |
> 🟢 **NOTA `2026-09-17` (Grepy, MISIÓN 6 tras el barrido) — la ley medida queda PROBADA en `0 ≤ m ≤ q−2k`, `∀k`, y ENTERA para `k = 1`** (`q−2 = q−k−1`): la sobreyectividad de la restricción a hojas en `T−m` (dual de la directez en `T+m`) sale de `X_J·h` (Covering Lemma) y de `indeg((u^{[q]}):Π) = q−2k+1` (`FR_PUREZA_1` R3). Quedan `k−1` grados, `q−2k < m ≤ q−k−1`, sólo medidos. `corpus4/regla154_apendice_b_y_banda.md` §3.

> 🟢 **NOTA `2026-09-17` (Grepy, MISIÓN 7 tras el barrido) — los `k−1` grados NO están «sólo medidos»:** con `(*CK*)` (`FR_CAMBIOS_2`) y `GLUED_PURITY` Thm 2 la directez vale hasta `m = q−k−1`, y con `WALL_GLUING` Thm 3 falla en `m = q−k` con defecto `½C(2k+2,k+1)` ⟹ **la ley medida de `WINDOW_DEFICIT` es TEOREMA para `q > k²`, en sus dos mitades** (`pending P0`). Gate 21/21 contra el `H_1` del collar (`530 = 540−10`, `620 = 675−55`). El Teorema S (`m ≤ q−2k`) es su sombra por hoja. `corpus4/regla155_empujar_desde_arriba.md` §2–§3.


The window `[T, T+q−k)` has width `q−k` and is **non-empty iff `q ≥ k+1`** — the campaign's own saturation
threshold recovered as the degenerate case, and confirmed by the deficient cell `(3,3)`, where the predicted
width is `≤ 0` and directness indeed fails already at `m = 0`.

**Consistency at `k=3`, `q=9` (not a measurement of the breakpoint).** `DIMENSION_LEDGER v40`, Peinado v26,
records the two-band probe at `(3,9)`: the anchor law `105·binom(35−d,3)` holds with deviation `0`, `6/6`,
on `d = 27…32`, i.e. exactly `m = 0…5 = 0…q−k−1`, and the collar is recorded as splitting **exactly at
`d = 26/27`**, i.e. at `m = 5/6 = (q−k−1)/(q−k)`. This is consistent with the candidate law and independent
of it; **the failure at `m = 6` in `(3,9)` is not measured here and is not claimed.** `(3,9)` is out of
reach of this engine (`9^8` box).

## 7 · Corollary (the central gap width becomes arithmetic)

`EL FRENTE v17 §2` grades the central-gap width `(k−1)q` as a **two-point candidate**. It is an exact
identity given the two band widths:

- **Low band, width `q`, PROVED ∀k∀q:** `m^{[q]}` starts in degree `q`, so `dim A_d = dim (S/E)_d` for
  `0 ≤ d ≤ q−1`, a `q`-free expression. *(Cross-checked here: for `(2,9)` the complete-intersection Hilbert
  series `(1−t^3)(1−t^5)/(1−t)^5` gives `1, 5, 15, 34, 65, 110, 170, 245, 335` in degrees `0…8`, byte-exact
  against the sealed census.)*
- **High band, width `q−k`, MEASURED (5 cells, §6):** the degrees `T−m` with `m ≤ q−k−1`, where the anchor
  law `(2k+1)!!binom(m+k,k)` holds. *(Proved only for `m ≤ k`; see §8.)*
- **Total number of degrees:** `T+1 = (k+1)(q−1)+1 = kq + q − k`.

Hence the gap between the two bands has width exactly

  `(kq + q − k) − q − (q−k) = (k−1)q`.

**The only measured ingredient is the high-band width `q−k`.** Checked against the recount already on file:
`k=1, q=9` gives gap `0` (the two bands touch — the reason column `k=1` closes) and `k=2, q=9` gives gap `9`,
both matching the cemetery's two-band table. This does **not** make `(k−1)q` proved; it reduces it from a
free-standing two-point pattern to a consequence of a single measured width, which is where the next pencil
should be aimed.

## 8 · Scope — what is NOT claimed

1. **Nothing is proved about `A_k(q)`.** Theorem 1 is an inequality between `𝒩` and the Matlis mirror of `A`;
   the conjecture `A = P` is untouched.
2. **The converse is not proved.** `dim A_{T−m} = (2k+1)!!binom(m+k,k)` does **not** imply directness: that
   would require `𝒩_{T+m} = 𝓜_{T+m}`, which is the annihilator **face of the conjecture**, not a theorem.
   Measured `27/27` in the degrees of §5, and nothing more is claimed (`ONE-DIRECTION-CANONISED`).
   Consequently the phrase *"directness holds for `m ≤ q−k−1`"* is **measured**, never proved, even where the
   anchor law is proved.
3. **The anchor law on the high band is open.** It is proved only for `m ≤ k` (corpus, ladrillo 50) and
   measured to `m = q−k−1`. Closing the range `k < m ≤ q−k−1` is the diana handed forward.
4. **`k = 3` at `q = 9` is a consistency check, not a measurement** of the breakpoint (§6).
5. **The six method exclusions are respected, not touched.** Theorem 1 is global (Matlis duality on the whole
   ring, not a criterion on subfamilies — outside `E4`), non-monomial (`E1`), uses no lamina restriction
   (`E2`), no edge hyperplane (`E5`), and no point-by-point witness (`E6`). Lemma 1 is a linear change of
   coordinates, not a restriction to a lamina.
6. **No claim of novelty for the ingredients.** R1, R20 and the v15 window formula are on file; what is new
   is their composition into a falsifiable inequality, and the five censuses run against it.

## 9 · Provenance

- **Parents:** R1 (radicality, `⋂_J I_J = E`); R20 (`dim 𝓜_c = dim A_{2T−c}`, graded Matlis in `B`);
  the v15 window formula (reproved as Lemma 1); R23 (`𝒩 = ann_B(⋂_J I_J·B)`, not needed for the kill but
  the reason `𝒩` is the natural object); the Anchor Law A6, whose recorded failure `530` vs `540` at
  `(2,9)`, `m=7` is the number that made this criterion worth writing.
- **Cemetery cross-check performed before computing (by object, not by name):** `C41.2` buried
  *"`ann` as a FREE module outside its window"* with exactly `530` vs `540`. The present object is the same
  mathematical content under a different name — *directness of `Σ_J F_J^{q−1}B`* is the free-module reading
  of `𝒩` on the window — and `EL FRENTE v17` had re-opened it as Diana 2. **`C41.2`'s consolation clause
  ("the Hilbert-function identity holds inside the range") is corrected here: the failure is INSIDE the
  window `[T,T+q)` that `EL FRENTE` names, not outside it.**
- **Data:** all ranks and censuses from single byte-exact runs of `locard_window_engine.py` and
  `locard_window_29.py`; the `(2,9)` census also from `log_socle_2_9_v5`; the `(3,9)` band probe from
  `DIMENSION_LEDGER v40`, Peinado v26. **No number in this document is from memory.**

**— Locard.** *One inequality, five censuses, one street buried, one candidate width turned into arithmetic,
and one of my own engines discarded for contradicting a proved bound. The word is not said.*
