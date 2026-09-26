> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-27
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · THE s=0 BLOCK LAW — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_S0_BLOCK_LAW.md
>
> **Status, as written in the document:** MEASURED, set equality monomial by monomial, `k = 1,2,3,4` (Singular, char 3, `dp`;
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · THE `s=0` BLOCK LAW — v1
### Standalone · Tardieu (auditor), 27 Jul 2026 · **the first block of the staircase written in closed form in `k`**

`n = 2k+2`, `S = F_3[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`, `>` = degrevlex with
`x_0 > x_1 > ⋯ > x_{n−1}`.

The staircase `in_>(E + m^{[q]})` splits by growth exponent `s` (the number of coordinates whose
generator exponent grows with `q`). The block `s = 0` — the part that does not depend on `q` — is
`in_>(E)`, measured at `k = 1,2,3` as a set of monomials, not merely as a count.

---

## THE LAW

> ### Index set
> Ballot sequences `1 ≤ a_1 < a_2 < ⋯ < a_{k−1} ≤ 2k−2` subject to `a_i ≥ 2i−1`. Set `a_k := 2k−1`.
> ### Generator
> ## `g(a) = ∏_{i=1}^{k} x_{a_i}^{\,a_i − 2i + 3} · x_{2k}`
> ### The block
> `minbase(in_>(E))` at level `k` is `{x_0} ∪ \{ g(a) : a` a ballot sequence at level `j`, `j ≤ k \}`,
> the lower levels embedded by the variable prefix.
> ### Counts
> new at level `k`: `C_k` · total: `Σ_{i=0}^{k} C_i` (OEIS A014137).

`x_0` is the leading monomial of `e_1`; it is the seed, and it corresponds to `C_0 = 1`.

---

## EVIDENCE, WITH ITS GRADE

**MEASURED, set equality monomial by monomial, `k = 1,2,3,4`** (Singular, char 3, `dp`;
`tardieu_s0_block_law_v1.py`): predicted set `=` measured `minbase(in_>(E))` exactly — `2, 4, 9, 23`
monomials, **no monomial predicted and missing, none measured and unpredicted.**

**MEASURED by count, `k = 5`:** `65`, on the Architect's Mac (Singular, `1907.6 s`), against the
**pre-registered** prediction `Σ_{i=0}^{5} C_i = 65`. The three positive controls (`2, 4, 9`) passed
before the number was read. A second engine (Macaulay2) was launched as a cross-check.

**PROVED: in no dimension.** This is a measured law with an explicit closed form. It is not a theorem.

> ### 🟢 **NOTA `2026-09-16` (Grepy, turno 11, informe 139) — reproducido y ampliado.** (i) La igualdad de CONJUNTOS en `k = 1..4` sale 4/4 con motor independiente (M2, `corpus4/regla139_s0.log`). (ii) `k = 5 → 65` lo re-obtuvo el informe 92 por otra vía (decisor por serie de Hilbert). (iii) **La pieza (2) de la ley, `HS(S/J) = HS(S/E)`, está PROBADA `∀k`** (`corpus/CHAISE_LONGUE_KEY_LEMMA_FULL_v1.md`, consolidado en `corpus/CHAISE_LONGUE_S0_CLOSED_FORM_v15.md`) y además medida por Grepy hasta `k = 7` con control negativo que dispara (`corpus4/regla139_pieza2.log`, `…_control.log`). **Lo que sigue abierto es `in(E) ⊆ J`** (pieza (1)), no la ley entera. ⚠️ **Y una precisión de coste:** la etiqueta «NO CABE at `k=5`» de `CHAISE_LONGUE_S0_CATALAN_GATE` era del entorno del auditor (Singular muerto pasados 28 min); en el Mac del Arquitecto terminó en `1907.6 s`.


The generators, printed:

| `k` | new generators (`C_k` of them) |
|---|---|
| 1 | `x_1²x_2` |
| 2 | `x_1²x_3²x_4` · `x_2³x_3²x_4` |
| 3 | `x_1²x_3²x_5²x_6` · `x_1²x_4³x_5²x_6` · `x_2³x_3²x_5²x_6` · `x_2³x_4³x_5²x_6` · `x_3⁴x_4³x_5²x_6` |
| 4 | 14 generators, degrees `{9:1, 10:3, 11:3, 12:3, 13:2, 14:1, 15:1}` |

---

## WHY THIS MATTERS, STATED WITHOUT INFLATION

1. **It is the first `k`-uniform description of any part of the staircase.** The campaign has been
   trying to read a law off the totals `6, 20, 111`; the totals are the wrong object. The staircase is
   **nested in `k`** (measured: `6/6`, `20/20`), so the right object is *what is added*, and for the
   `s=0` block what is added is `C_k` generators with an explicit formula.
2. **It hands the Witness Ceiling Principle a complete sub-target.** By that principle the ceiling
   `A_k(q) ≤ N(n,q)` follows from a full list of leading monomials plus one explicit witness each.
   For the `s=0` block the list is now written for every `k`; only the witnesses remain, and each is
   an element of `E` — no `q` in sight.
3. **Catalan is an index, not a coincidence.** `C_k` counts non-crossing structures, and the sheets
   `L_J` are indexed by *all* perfect matchings, `(2k+1)!!` of them. The `s=0` block picking out a
   Catalan-sized family is a structural signal and is the first place in this campaign where a
   matching-flavoured count has survived a fifth dimension. *(Lacassagne's earlier attempt to index
   the whole staircase by all matchings, `C(2k+2,k+1)`, died at `k=3`: `70 ≠ 111`.)*

---

## WHAT THIS STANDALONE DOES **NOT** CLAIM

1. **It proves nothing.** `PROVED` in no dimension; `MEASURED` monomial-exact to `k=4` and by count
   at `k=5`.
2. **It says nothing about `s ≥ 1`.** The `q`-growing blocks — `53 + 44 + 5` of the `111` at `k=3` —
   have no law here. They are the bulk.
3. **It is order-dependent and characteristic-tagged.** Degrevlex with the stated variable order,
   characteristic 3. The `q`-staircase was separately measured identical in char 0 and char 3 at
   `k=2`; **that measurement has not been repeated for `in(E)` alone at higher `k`.**
4. **The nesting it relies on is MEASURED**, in three dimensions (`6/6`, `20/20`, `6/6`), not proved.
5. **It does not touch `GAP 3`.** `G = 3`, the target has not moved.

---

## PROVENANCE

The count law `Σ_{i≤k} C_i` is **Lacassagne**'s (turn 8), measured to `k=4` and pre-registered at
`k=5`. The `k=5` run is the **Architect**'s (Mac, Singular, `1907.6 s`, `65` MATCH). The ballot-sequence
index, the closed form `g(a)`, and the monomial-exact gate at `k = 1,2,3,4` are **Tardieu**'s
(auditor), 27 Jul 2026. Motors: `tardieu_s0_block_law_v1.py`, `CHAISE_LONGUE_S0_CATALAN_GATE.py`,
`tardieu_nesting_v1.py`. Consumed by: `EL FRENTE v109`.
