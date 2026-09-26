> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-28
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE DEGREE LAW IS FALSE* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEGREE_LAW_REFUTED_AT_2_5.md
>
> **Status, as written in the document:** Don Mister Grep (auditor) · 2026-08-28 · Pending P0 · `char K = 3`
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (4 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE DEGREE LAW IS FALSE
### Refuted at the cell `(k,q) = (2,5)` with five explicit minimal generators above the bound
### Don Mister Grep (auditor) · 2026-08-28 · Pending P0 · `char K = 3`
### Engine delivered with this file: `CHAISE_LONGUE_CELL_2_5_ENGINE_v1.py` — pure `numpy`, single thread, three cells in minutes.

**Certificado Ley 41.** Object: the minimal generation degrees of `H_1(x^{[q]}; S/E)`, i.e. the **Degree Law** *(`E∩m^{[q]}` generated in degrees `≤ q+2k`)*. Cemetery grep by object and by number: the Degree Law is recorded as **MEASURED at `k=1,2,3` and `q=3,5`, PROVED at `k=1`, OPEN in general** (`ASSEMBLY §97.3`, `§98.1`; `CATÁLOGO v249.b`). **The cell `(2,5)` had never been computed** — it is named as the first honest test in `ANSWER_SOCLE_HK` §5. No tomb shares the object.

---

## 0 · THE RESULT

> # **THE DEGREE LAW IS FALSE.** At `(k,q) = (2,5)`, `H_1(x^{[q]}; S/E)` has **five minimal generators in degree `11`**, while `q+2k = 9`.

Consequently the hypothesis of `THE_Q_FREE_WINDOW_THEOREM_standalone_v3` (Theorems 3.1 and 3.2, both stated *"conditional on the Degree Law"*) is **false**, and **bands II, III and IV do not close by that route.**

---

## 1 · THE MEASUREMENT, WITH ITS TWO POSITIVE CONTROLS

Notation as in `ANSWER_SOCLE_HK`: `n' = 2k+1`, `S' = K[x_1,…,x_{n'}] = S/(e_1)`, `\bar e_j := e_j|_{e_1=0}`, `B' := S'/(x_1^q,…,x_{n'}^q)`, `H'_1 := H_1(\bar e_3,…,\bar e_{2k+1}; B')`. By **R1** of that report (`p_q = 0` in `R`, PROVED `∀k∀q`), `H_1 = H'_1 \oplus \bar A(-q)\,[p_q]`, so the generation degrees of `H_1` are those of `H'_1` together with `q`.

**Same code, three cells:**

| cell | `\dim \bar A` | gate | minimal generators of `H'_1` | `q+2k` | verdict |
|---|---|---|---|---|---|
| `(2,3)` | **141** | `= A_2(3)`, sealed ✓ | `\{5:1,\; 7:15\}` | `7` | top `= 7` ✅ |
| `(1,5)` | **61** | `= P_1(5)` ✓ | `\{7:3\}` | `7` | top `= 7` ✅ |
| **`(2,5)`** | **1001** | `= P_2(5)` ✓ | `\{7:1,\; 9:10,\; \mathbf{11:5}\}` | `9` | ### top `= 11 > 9` ⛔ |

**The two controls are the point.** `(2,3)` reproduces the campaign's sealed row `HF(\bar A) = 1,5,15,29,40,36,15` and the sealed generator pattern `\{5:1, 7:15\}` — **measured independently elsewhere in the corpus**. `(1,5)` reproduces `P_1(5) = 61` and gives `3 = (2k+1)!!` generators at exactly `q+2k`, as the proved `k=1` case requires. **The same code then fails at `(2,5)`.**

### 1.1 · Gates on the decisive cell

| gate | value | verdict |
|---|---|---|
| `\dim \bar A` | `1001` | `= P_2(5) = 15\cdot125-45\cdot25+55\cdot5-24` ✅ |
| Euler | `\dim H'_0 - \dim H'_1 + \dim H'_2 = 1001 - 2002 + 1001 = 0` | ✅ |
| duality (R2) | `\dim H'_2 = 1001 = \dim \bar A` | ✅ |
| duality, graded | `HF(H'_2) = 15,45,90,140,170,171,145,105,65,34,15,5,1` on `[16,28]` `=` `HF(\bar A)` reversed | ✅ |
| self-duality of `H'_1` | `HF(H'_1) = 1,5,25,70,150,245,325,\mathbf{360},325,245,150,70,25,5,1` on `[7,21]`, symmetric about `14 = (a+n'q)/2` | ✅ |

`HF(\bar A) = 1,5,15,34,65,105,145,171,170,140,90,45,15` on `[0,12]`, `T = (k+1)(q-1) = 12`, `\bar A_T = 15 = (2k+1)!!`.

---

## 2 · ★ THE TWIST: LEVELNESS HOLDS AND THE DEGREE LAW FAILS — IN THE SAME CELL

> ### **`\operatorname{soc}(\bar A) = \{12 : 15\}` at `(2,5)`. `\bar A` IS LEVEL.**

Measured directly (kernel of `\bar A_d \to \bigoplus_i \bar A_{d+1}`, all `d`). This is consistent with `k=2` being a deposited dimension and with the six proved-equivalent faces of `GAP 3`.

> # **So at `(2,5)`: `\bar A` level = TRUE, Degree Law = FALSE.** The two statements are **not** equivalent, and the cell that separates them is the first one ever computed outside `q = 3`.

This is exactly the separation predicted in `ANSWER_SOCLE_HK` **R3**: at `q = 3` Newton's identities in characteristic `3` make `\bar e_5,\bar e_7` multiples of `\bar e_3` inside `B'`, the Koszul complex collapses, and *the Degree Law degenerates into levelness of `\bar A`*. **Every previously measured cell of the Degree Law sits at `q = 3`.** The report's conclusion — *"they contain no evidence about the Degree Law beyond levelness of `\bar A`"* — is confirmed, and the first honest cell refutes the law.

**The "second law" also dies here.** `ASSEMBLY §98.2` recorded, `4/4`, that the top-degree multiplicity of `H_1` equals `\dim\operatorname{soc}(\bar A)`. At `(2,5)`: `\dim\operatorname{soc}(\bar A) = 15`, and the top multiplicity is `5`, in degree `11`. *(The four measured points were `(1,3), (1,5), (2,3), (3,3)` — three of them at `q=3`, and `(1,5)` at `k=1` where the collapse is trivial.)* **It was a `q=3` artefact.**

---

## 3 · THE SOCLE FORM, DISPROVED WITH ITS WITNESS

The dual statement — *`\operatorname{soc}(H_k)` lives in degrees `\ge k^2-2k-1+(2k+1)q`* — falls with an explicit witness.

By **R2**, for `k=2`, `H'_1` is self-dual with shift `a + n'q = (k^2-1) + (2k+1)q = 3 + 25 = 28`, and generators of `H'_1` correspond to socle elements under `d \mapsto 28-d`. Hence:

- a minimal generator in degree `11` gives a **socle element of `H'_1` in degree `17`**;
- the threshold for `\operatorname{soc}(H'_{k-1}) = \operatorname{soc}(H'_1)` is `k^2-2k-1+2kq = 4-4-1+20 = \mathbf{19}`;
- and `H_k = H_2 = H'_2 \oplus H'_1(-q)` gives a **socle element of `H_2` in degree `22`** against the threshold `k^2-2k-1+(2k+1)q = \mathbf{24}`.

> ### `17 < 19` and `22 < 24`. **Two below the threshold, five times over.**

---

## 4 · WHAT THIS KILLS, AND WHAT SURVIVES — stated exactly

**KILLED:**
1. **The Degree Law**, in both its forms (module `H_1` and ideal `E\cap\mathfrak m^{[q]}`; minimal generators of the ideal surject onto those of the module).
2. **The route `Degree Law ⟹ bands II+III+IV`.** Theorems 3.1 and 3.2 of `THE_Q_FREE_WINDOW_THEOREM_v3` remain **correct as implications** and become **vacuous**: their hypothesis is false.
3. **The "second law"** (top multiplicity `= \dim\operatorname{soc}(\bar A)`), as a law.
4. **The reading that the measured cells were evidence for the Degree Law.** They were evidence for levelness of `\bar A`, which is `GAP 3`.

**SURVIVES, untouched:**
- **R1, R2 and R3** of `ANSWER_SOCLE_HK` (splitting, primed duality, `q=3` collapse) — all PROVED, and R1/R2 are what make this refutation computable and its witness explicit.
- **Band IV** (`q \ge (k+1)^2`, the gear) — unconditional, never depended on the Degree Law.
- The **`q=3` layer `∀k`** (Steinberg) and the deposited `k \le 3`.
- **Levelness of `\bar A`**, now measured at a fourth cell `(2,5)` and **still holding**.
- The Koszul–Poincaré duality, the Euler identity, the generators↔socle dictionary.

**RE-OPENED:** bands **II** and **III**. Band I was never closed.

---

## 5 · THE NUMBER THAT DECIDES THE NEXT TURN

Generation degree of `H_1`, measured:

| `k` | `q` | gen-deg | `q+2k` | excess |
|---|---|---|---|---|
| 1 | 3 | `5` | `5` | `0` |
| 1 | 5 | `7` | `7` | `0` |
| 2 | 3 | `7` | `7` | `0` |
| **2** | **5** | **`11`** | `9` | **`+2`** |

At `k=1` the law holds (proved). At `k=2` the excess is `0` at `q=3` and `2` at `q=5`.

> ### **The fork, pre-registered.** Two readings fit the two points at `k=2`, and they have opposite consequences:
> - **`\text{gen-deg} = q+2k+2`** *(excess constant in `q`)* ⟹ images under `\lambda` land in degrees `\le 2k+3`: **the `q`-free window SURVIVES, merely wider**, and the whole programme is repairable.
> - **`\text{gen-deg} = 2q+1`** *(fits `7` at `q=3` and `11` at `q=5`)* ⟹ images land in degrees `\le q+2`: **the `q`-free window is DEAD**, because the range grows with `q`.
>
> ### **The cell that separates them is `(2,9)`: `q+2k+2 = 15` against `2q+1 = 19`.** `\dim B' = 9^5 = 59\,049`. Beyond this sandbox; within reach of the machine that ran `BISEL_DEGREE_LAW_K3_ENGINE_v1`. ⚠️ **Ley 12: two points are not a law. Neither reading is claimed.**

> ### 🔴 **NOTA `2026-09-16` (Grepy, turno 12, informe 140) — la bifurcación está RESUELTA en el corpus, en la rama mala (`2q+1`):** la Ley del Grado **TAMBIÉN está refutada DENTRO de la torre, en `(2,9)`**: generadores de `H'_1` `{11:1, 13:10, 19:5}` con `q+2k = 13` (`corpus/EL_CAMINO_DE_DON_GREP_v18.md:210`, retirado por seis erratas que NO tocan esta tabla — `MASTER_ASSEMBLY §103.5`) y recuento `1+10+5 = 16` confirmado por la fuente de registro (`corpus/LA_MOCHILA_DE_LA_VICTORIA_v121.md:1940`, medido en `(2,5)`, `(2,7)`, `(2,9)`); ley de los altos `2q+2k−3` (`MASTER_ASSEMBLY §103.2`). Grepy reprodujo hoy las dos calibraciones `(2,3) → {5:1,7:15}` y `(2,5) → {7:1,9:10,11:5}` con motor propio (`corpus4/regla140_leydelgrado.log`); `(2,9)` NO se re-corrió (estimada en horas, LEY 13). **Cierre enterrado en otros ficheros; marcado aquí, en el suyo.**

> 🔴 **NOTA `2026-09-16` (Grepy, turno 18, informe 146) — cita de línea errónea (mía, turno 12):** el recuento `1+10+5 = 16` está en `corpus/LA_MOCHILA_DE_LA_VICTORIA_v121.md:1967`, no en `:1940` (que es el encabezado de §0.5). Vale para las dos apariciones de este bloque.



---

## 6 · SCOPE, HONESTLY

The refutation is a **computation in one cell**, gated five ways and flanked by two positive controls that reproduce sealed corpus values with the same code. It proves the Degree Law **false**; it proves nothing about `A_k(q) = P_k(q)`, which at `(2,5)` is **true** (`k=2` is deposited, and `\dim\bar A = 1001 = P_2(5)` is itself one of this note's gates). Nothing here is claimed in `char K = 2`.

**Engine:** `CHAISE_LONGUE_CELL_2_5_ENGINE_v1.py`. Single thread, `numpy` only, no external libraries. Reproduces all three cells; `(2,3)` and `(1,5)` are its built-in positive controls and must pass before `(2,5)` is read.

— Don Mister Grep, Chaise Longue campaign
