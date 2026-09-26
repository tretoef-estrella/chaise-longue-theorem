> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — EL ENLACE 5 (standalone), v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ENLACE_5.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — EL ENLACE 5 (standalone), v1
*Grepy Toloco, 2026-09-18, misión 161 de Bisel. Sacado del informe 66 §2, donde vivía sin fichero propio.*

> ⚠️ **NO ES UN ASCENSOR DE TORRE.** Su hipótesis y su conclusión viven en el MISMO `q = 3^v`. Lo que sube la torre en el Sofá es el tramo `bone(3) ⟹ bone(v)` (`THE_SOFA_THEOREM_V63_GRANITO.md:56`), no este enlace.

## Objeto
- `S = F_3[x_0..x_{n−1}]`, `n = 2k+2`, `E = ⋂_J I_J = (e_1, e_3, …, e_{2k+1})`, `q = 3^v`.
- Hojas `L_J`, `J` un emparejamiento perfecto de `{0..n−1}`.
- `Z = ⋃_J L_J(F_q)` y `P_k(q) = |Z|`.
- `A_k(q) = dim S/(E + m^{[q]})`.
- `Δ_v`: su matriz sobre `ℤ` en el mundo tensorial (`nv` variables). Filas = evaluaciones de los monomios reducidos en los puntos de `X_v(F_3)` (`V63:33`).

## Enunciado (`∀k`, `∀v`)
**(E5)** `drop(v) := rank_ℚ(Δ_v) − rank_{F_3}(Δ_v) = dim Tors_3(coker Δ_v)`, y

**`drop(v) = 0` ⟺ `Tors(coker Δ_v) = 0` (saturación) ⟺ DS 1.2 en `q = 3^v` ⟺ `A_k(q) = P_k(q)`.**

Con la hipótesis de la campaña: **hueso en `q` ⟹ `drop(v) = 0`**.

## Eslabones, grado y fuente
| eslabón | grado | fuente |
|---|---|---|
| `rank_ℚ(Δ_v) = P_k(3^v)` | 🟢 PROBADO, por ranura, verbatim en `n` | la matriz de evaluación completa es el tensor `nv`-ádico de la Vandermonde `3×3` sobre `{−1,0,1}`, **`det = 2`** (tensor `m`-ádico: `2^{m·3^{m−1}}`, gate `corpus4/regla161_ascensor_candidato2.md` §0) |
| `rank_{F_3}(Δ_v) ≥ dim T(v)` | 🟢 PROBADO, por ranura (`2 ≠ 0` en `F_3`) | `V63:33` |
| `drop = #\{divisores elementales divisibles por 3\}` ⟹ `drop = 0 ⟺ Tors_3 = 0` | 🟢 álgebra lineal sobre `ℤ` | — |
| `Tors = Tors_3` (la torsión es `m`-primaria, `m = 3^v`) | 🟨 cita de la FUENTE | DS vía `corpus/THE_NAIL_THEOREM_v3.md §8.5` (**no** `teoremas de fermat/THE_NAIL_THEOREM.md`: colisión de nombre, informe 66) |
| `saturado ⟺ DS 1.2`, dimensión `2s` general, cualquier número de parejas | 🟨 cita de la FUENTE | DS [2, §4.6] y [2, Lemma 4.1], vía `THE_NAIL_THEOREM_v3.md §8.5`; original sin leer |
| hueso ⟹ `A = P` (la dirección que se usa) | 🟢 PROBADO de lápiz, **sin torsión** | informe 66, Ruta 1: `A ≥ P ≥ B` y hueso `A = B` (= `L2`) |

**Grado global:** 🟢 en todo eslabón propio; 🟨 en los dos puentes a la fuente. El único paso del Sofá que dependía de `n = 6` (el menor `141×141` con `det = 3`) es redundante (informe 66).

## Lo que NO es
1. **No es un ascensor.** Ver arriba.
2. **Como vía hacia DS 1.2 es un re-enunciado** (test `FR20:151`): `drop = 0` ES DS 1.2 en el nivel `v` (`THE_SOFA_THEOREM_V84_GRANITO.md:16`, *«drop(v)=0 ⟺ DS 1.2 at v»*).
3. **Su determinante no contiene la conjetura.** El `2` de la Vandermonde da el suelo. La parte impar que decide la conjetura es la de un conúcleo RESTRINGIDO a la unión de hojas (`3 ∉ Smith(Δ_v)`, `V84:2`).
4. **No es local.** `V84:73` declara muerta la localización por tripletes: la torsión es global.

## Dependencias
`L1` (`E` radical) → `L2` (hueso ⟹ `A = P`) ⟸ este enlace (segunda prueba de `L2`, con torsión). Ningún lema de la campaña depende SÓLO de él.
