> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_VERTEX_LADDER_THEOREM_v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_VERTEX_LADDER_THEOREM.md
>
> **Status, as written in the document:** What this file contains. Three statements PROVED `∀k ∀q` (A, B, D), one decomposition that is an
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_VERTEX_LADDER_THEOREM_v2
### Standalone · Auditor GETTLER 4 · Campaign Chaise Longue · Degtyarev–Shimada Conjecture 1.2 · THE CEILING (Law 32)
### Engines delivered with this file: `CHAISE_LONGUE_VERTEX_LADDER_ENGINE_v2.py` (7.5× faster: ONE elimination per degree, all rungs read off it), `CHAISE_LONGUE_GEOMETRIC_LADDER_v1.py`, logs `LOG_VERTEX_LADDER_k3_q3.log`, `LOG_VERTEX_LADDER_k2_q5.log`
### **v2 changes:** cell `(2,5)` added — pre-registered death criterion, could fire, **did not**; `(3,3)` independently reproduced by auditor 2 on his own machine; the rung table now separates THEOREM rungs from TEST rungs.

> **What this file contains.** Three statements PROVED `∀k ∀q` (A, B, D), one decomposition that is an
> EQUIVALENT REFORMULATION and is labelled as such so that nobody pays a turn for it, and **three kills with
> their numbers**, one of which killed this author's own 17/17 pattern in the first cell of the third
> dimension. **Nothing here closes a gap. The reserved phrase is not spoken.**

---

## 0 · Setting (everything printed; no external reference is load-bearing)

`K` a field, `char K ≠ 2`; `q ≥ 3` odd (the conjecture's case is `q = 3^v`, `char K = 3`).
`n = 2k+2`, `S = K[x_0,…,x_{n−1}]`, `e_j` = elementary symmetric of degree `j`.
`E = (e_1, e_3, …, e_{2k+1})` · `m^{[q]} = (x_0^q,…,x_{n−1}^q)` · **`A = A_k(q) := S/(E + m^{[q]})`.**
`V := V(E) ∩ F_q^n = {p : the multiset {p_0,…,p_{n−1}} is closed under negation}`, and `|V| = P_k(q)`
(the deposited floor: `P_k(q)` is exactly this point count for `q` odd).

**Vertex forms.** `ℓ_a := x_a + x_{n−1}` for `a = 0,…,2k` — **`2k+1` forms**, one per possible partner of the
last coordinate.
**Ladder elements.** `L_0 := 1`, `L_a := ℓ_0ℓ_1⋯ℓ_{a−1}` (`a = 1,…,2k+1`), `deg L_a = a`.
**Ladder ideals.** `𝔏_a := L_a·A`. Chain `A = 𝔏_0 ⊇ 𝔏_1 ⊇ ⋯ ⊇ 𝔏_{2k+1}`.
**Geometric strata.** `V_a := {p ∈ V : p_a = −p_{n−1} and p_c ≠ −p_{n−1} for all c < a}`, `a = 0,…,2k`.
**Cumulative targets.** `𝒱_{≥a} := #{p ∈ V : p_c ≠ −p_{n−1} for all c < a} = Σ_{c ≥ a} |V_c|`;
`𝒱_{≥0} = P_k(q)`, `𝒱_{≥2k+1} = 0`.

**Two deposited `∀k` inputs, quoted, both by Lacassagne:**
- **(D1)** `∏_{a=0}^{2k} ℓ_a ∈ E` (gated `k = 1,2,3`).
- **(D2)** `A_k/ℓ_bA_k ≅ A_{k−1} ⊗ K[z]/(z^q)` via `x_b ↦ −z`, `z = x_{n−1}`, using
  `e_j|_{x_b=−z} = a_j − z²a_{j−2}`, which untriangulates to the level-`(k−1)` odd ideal
  `(a_1,a_3,…,a_{2k−1})`. Gated `dim = 9, 25, 57, 305 = q·A_{k−1}(q)`.
  **The substitution is linear, hence the isomorphism is GRADED** — used below and not previously used.

---

## 1 · THEOREM A — the ladder is exhaustive on both sides. **PROVED ∀k ∀q odd, char ≠ 2.**

> **(i)** `𝔏_{2k+1} = 0`.  **(ii)** `V = ⨆_{a=0}^{2k} V_a` (disjoint).

*Proof.* (i) is (D1): `L_{2k+1} = ∏_a ℓ_a ∈ E`, so it is `0` in `A`.
(ii) Disjointness is by construction (`a` is the least index with `p_a = −p_{n−1}`); what must be shown is
that such an index `≤ 2k` always exists. Write `z := p_{n−1}`, `w := −z`.
 · If `z ≠ 0`: the multiset is negation-closed, so `mult(w) = mult(z) ≥ 1`; the index realising `w` is not
 `n−1` because `p_{n−1} = z ≠ w`; hence it is some `c ≤ 2k`.
 · If `z = 0`: the nonzero values occur in pairs `{v,−v}` with equal multiplicities, so the number of nonzero
 coordinates is **even**; `n` is even, hence `mult(0)` is **even**, hence `mult(0) ≥ 2`, hence some `c ≠ n−1`
 has `p_c = 0 = w`. ∎

## 2 · THEOREM B — the bottom rung is exactly the level-`(k−1)` ceiling. **PROVED ∀k ∀q odd.**

> `dim_K 𝔏_0/𝔏_1 = dim_K A/ℓ_0A = q·A_{k−1}(q)` and `|V_0| = q·P_{k−1}(q)`.
> **Hence `dim 𝔏_0/𝔏_1 ≤ |V_0| ⟺ A_{k−1}(q) ≤ P_{k−1}(q)`.**

*Proof.* Algebraic half is (D2) at `b = 0`. Geometric half: choose `z = p_{n−1}` freely (`q` ways); `p_0 = −z`
is then forced; deleting a `{v,−v}` pair from a negation-closed multiset leaves a negation-closed multiset and
conversely, so the remaining `2k` coordinates range over exactly the `P_{k−1}(q)` negation-closed `2k`-tuples. ∎

> **This is the real content of the file: the algebraic ladder and the geometric ladder have the SAME first
> step, `∀k ∀q`, and that step is precisely the induction on `k`.**

## 3 · THEOREM D — frame-free crude ceiling. **PROVED ∀k ∀q odd, char ≠ 2. SECOND ROUTE (see grade).**

> `HF(A_k)(t) ≼ [2k+1]_t · [q]_t · HF(A_{k−1})(t)` coefficientwise, hence
> `HF(A_k)(t) ≼ ∏_{i=1}^{k}[2i+1]_t · [q]_t^{k+1}` and **`A_k(q) ≤ (2k+1)!!·q^{k+1}`.**

*Proof.* `L_a` is homogeneous of degree `a` and `·L_a : A(−a) ↠ 𝔏_a` carries `ℓ_aA` into `ℓ_a𝔏_a`, so it
induces a surjection `(A/ℓ_aA)(−a) ↠ 𝔏_a/𝔏_{a+1}`; therefore
`HF(𝔏_a/𝔏_{a+1}) ≼ t^a·HF(A/ℓ_aA) = t^a·[q]_t·HF(A_{k−1})` by (D2) graded. Sum over `a = 0..2k`; the sum of the
graded pieces of the chain is `HF(A_k)` by Theorem A(i). Iterate, with `A_0 = K[x]/(x^q)`, `HF = [q]_t`. ∎

> ### **GRADE — read this before banking it.** The **bound** is not new: it is the deposited `s21`
> "Sandwich" / Two-Column Law (`A_k(q) ≤ (2k+1)!!q^{k+1}`, verified `k=2,3,4`), and
> `∏_{i=1}^{k}[2i+1]_t·[q]_t^{k+1}` is byte-identical to the filed `Hilb(Λ)`.
> **`SECOND-ROUTE-TO-CLOSED-AS-NEW` is declared here, against this author.**
> **What IS new is only the proof:** it uses no s.o.p., no frame, no genericity, no field extension. It runs
> over the prime field `F_3`, where the corpus records that random linear forms are **not** an s.o.p.
> (`SOP-NOT-CHECKED`; no transversal SEP frame exists over `F_3` at `k=3`). Filed as **method**, not as a bound.

---

## 4 · THE DECOMPOSITION, AND ITS HONEST GRADE

Theorems A + B give the two partitions
`A_k(q) = Σ_{a=0}^{2k} dim 𝔏_a/𝔏_{a+1}` and `P_k(q) = Σ_{a=0}^{2k} |V_a|`, indexed by the same set,
with the `a=0` terms equal to one another whenever the level-`(k−1)` ceiling holds.

> **Consequently, with `A_{k−1}(q) = P_{k−1}(q)` as inductive hypothesis (base `A_0(q)=q=P_0(q)`):**
> ### `A_k(q) ≤ P_k(q) ⟺ dim_K (ℓ_0·A_k(q)) ≤ 𝒱_{≥1}(k,q)`.

> ### ⚠️ **GRADE: EQUIVALENT REFORMULATION, NOT A REDUCTION.** The `a=1` rung is the conjecture at level `k`
> written differently. **It must not be commissioned as if it were a smaller statement**
> (`reducción-que-es-rename`). It is filed because the object on the left is a *principal* ideal generated by
> one linear form in an Artinian ring and the object on the right is a bare point count — a better-shaped
> statement of the same thing, and that is all.

---

## 5 · THE GATE — 30 cumulative rungs, six cells, three dimensions, four values of `q`

> ### 🔵 **NOTA `2026-09-16` (Grepy, turno 9, informe 137) — errata de arrastre de la `v1`:** en la `v2` son **36 peldaños, 7 celdas y 22 pruebas genuinas** (tabla y línea siguientes); el «30 rungs, six cells» de este título y del `§7` es de la `v1`. **Motores y logs:** `CHAISE_LONGUE_VERTEX_LADDER_ENGINE_v1/v2.py` y `CHAISE_LONGUE_GEOMETRIC_LADDER_v1.py` están en `mix downloads/Downloads/` (el CATÁLOGO decía que no estaban en el proyecto); los dos logs, rescatados por copia en `RESCATE_LOGS_VERTEX_LADDER_2026-09-16/`. `HF(A_2(5))` reproducido exacto (`corpus4/regla137_hf25.log`).


Algebraic side: graded `GF(3)` linear algebra in `S/(E+m^{[q]})`, degree by degree (engine delivered).
Geometric side: direct point count over `F_q^n` (engine delivered). **The two are computationally disjoint.**

**Rung bookkeeping, stated honestly (auditor-2 correction absorbed).** In every cell the rungs `a = 0` and
`a = 2k+1` are **THEOREMS, not tests**: `a = 2k+1` is `0 ≤ 0` (Theorem A) and `a = 0` is
`A_k(q) ≤ P_k(q)`, already deposited in each of these cells. **They cannot fire.** Only the `2k` middle
rungs of each cell are genuine tests — a larger algebraic number there kills the route on the spot.

| cell | `dim 𝔏_a`, `a=0..2k+1` | `𝒱_{≥a}` | test rungs | verdict |
|---|---|---|---|---|
| `(1,3)` | `19, 10, 4, 0` | `19, 10, 4, 0` | 2 | equalities |
| `(1,5)` | `61, 36, 16, 0` | `61, 36, 16, 0` | 2 | equalities |
| `(1,7)` | `127, 78, 36, 0` | `127, 78, 36, 0` | 2 | equalities |
| `(1,9)` | `217, 136, 64, 0` | `217, 136, 64, 0` | 2 | equalities |
| `(2,3)` | `141, 84, 46, 22, 8, 0` | `141, 84, 46, 22, 8, 0` | 4 | equalities |
| **`(2,5)`** | **`1001, 696, 452, 260, 112, 0`** | **`1001, 696, 452, 260, 112, 0`** | **4** | **equalities — pre-registered, could fire, did not** |
| **`(3,3)`** | **`1107, 684, 402, 222, 112, 49, 17, 0`** | **`1107, 684, 402, 222, 114, 54, 22, 0`** | **6** | **`≤`, STRICT at `a = 4,5,6`** |

> **`dim 𝔏_a ≤ 𝒱_{≥a}` holds in 36/36 rungs, of which 22 are genuine tests** (19 satisfied with **zero
> margin**, 3 with slack `2, 5, 5`). Grade: **MEASURED**, seven cells, three dimensions, four values of `q`.
> **The three slack rungs are the only evidence that the inequality is not an identity — and they are all in
> one cell.** That is stated as a weakness, not hidden.
> Anchors re-hit: `dim A = 19, 61, 127, 217, 141, 1001, 1107` and `P_k(q)` identical — the filed values.
> `(3,3)` reproduced byte-exact by auditor 2 on an independent machine (`8/8` plus the strata).

**New free data banked from the `(2,5)` run — the graded Hilbert function of `A_2(5)`, which the corpus did
not have (grepped by literal number, absent):**
> ### `HF(A_2(5)) = 1, 5, 15, 34, 65, 105, 145, 171, 170, 140, 90, 45, 15`  (sum `1001`)
It agrees with the complete intersection `h_2 = 1,5,15,34,65,110,…` exactly up to degree `q−1 = 4` and departs
at degree `q = 5` (`105` vs `110`), and its top degree is `T = (k+1)(q−1) = 12` with
**`dim A_T = 15 = (2k+1)!!`** — an independent re-hit of the freezing criterion `dim A_T = (2k+1)!! ⟺ q ≥ k+1`
in a cell where only the total was on file.

**Geometric ladder, free and computed here for twelve cells (totals re-hit the sealed `P_k(q)` 12/12):**

| `(k,q)` | `|V_a|` | `P_k(q)` |
|---|---|---|
| `(1,3)`,`(1,5)`,`(1,7)`,`(1,9)`,`(1,11)` | `q², q(q−1), (q−1)²` | `19, 61, 127, 217, 331` |
| `(2,3)` | `57, 38, 24, 14, 8` | `141` |
| `(2,5)` | `305, 244, 192, 148, 112` | `1001` |
| `(2,7)` | `889, 762, 648, 546, 456` | `3301` |
| `(2,9)` | `1953, 1736, 1536, 1352, 1184` | `7761` |
| `(3,3)` | `423, 282, 180, 108, 60, 32, 22` | `1107` |
| `(3,5)` | `5005, 4004, 3152, 2432, 1832, 1344, 964` | `18733` |
| `(4,3)` | `3321, 2214, 1428, 882, 516, 284, 150, 86, 72` | `8953` |

Closed forms read off and **verified on their whole printed domain** (not fitted beyond it):
`|V_0| = q·P_{k−1}(q)` (Theorem B) · at `k=2`: `|V_1| = (q−1)P_1(q)`, `|V_2| = 3(q−1)³`,
`|V_3| = (q−1)P_1(q−1)`, `|V_4| = 4(q−1)P_1((q−1)/2)`, all `4/4` on `q = 3,5,7,9`.
**No `∀k` law is claimed for `|V_a|`, `a ≥ 1`.** Deriving it is the first action of `FR24`.

---

## 6 · ☠️ THREE KILLS, EACH WITH ITS NUMBER

**KILL 1 — the stratum-wise inequality `dim 𝔏_a/𝔏_{a+1} ≤ |V_a|` is FALSE.**
Killing numbers, cell `(k,q) = (3,3)`: at `a = 3`, **`110 > 108`**; at `a = 4`, **`63 > 60`**.
Algebraic strata `423, 282, 180, 110, 63, 32, 17` against geometric `423, 282, 180, 108, 60, 32, 22`.
⟹ **the clean sufficient condition "Ceiling(k) ⟸ Ceiling(k−1) + 2k stratum bounds" is DEAD.** What survives
is only the cumulative ladder, which has to *carry slack down* (`(3,3)` slacks: `0,0,0,0,2,5,5,0`).
**And the kill is order-independent:** `S_{2k+1}` permutes `x_0,…,x_{2k}` preserving `E` and `m^{[q]}`, hence
permutes the `ℓ_a` and fixes both ladders setwise ⟹ **every ordering of the vertex forms gives the same
numbers. No reordering rescues it.**

**KILL 2 — this author's own 17/17 pattern.** "`dim 𝔏_a/𝔏_{a+1} = |V_a|` for every rung" was exact in
`17/17` rungs across `(1,3),(1,5),(1,7),(1,9),(2,3)` — two dimensions, four values of `q`. **It dies in the
first cell of the third dimension**, `(3,3)`, at `21/24`. Textbook `Kepler-como-cierre`, caught by a
pre-registered gate before it entered any live document. *Two dimensions were never a law (Law 12).*

**KILL 3 — the covering route in the TOP degree is a gate that cannot fire.**
For any family of linear forms `{ℓ}` such that every leaf `L_M` is annihilated by at least one of them,
`(⋂_ℓ ℓA)_T ⊆ ker Φ_T` (on a leaf killed by `ℓ`, everything in `ℓA` restricts to `0`; every matching pairs
`n−1` with some `a ≤ 2k`). The resulting bound therefore reads `rank Φ_T ≤ Σ_ℓ dim(A/ℓA)_T`. For the vertex
family, `dim(A/ℓ_aA)_T = dim A_T(k−1,q) = (2k−1)!!` in the frozen band, so the right-hand side is
**`(2k+1)·(2k−1)!! = (2k+1)!!` exactly: margin ZERO.** `3·1 = 3`, `5·3 = 15`, `7·15 = 105`.
⟹ **`fit-gate-that-cannot-fire`.** This kills, in the socle degree, the "next probe" proposed by the FR23
turn report (§6: a pair/two-form covering argument): **the ladder must be run in the whole ring, never in the
top degree alone.**

**KILL 4 (minor, Kepler again) — `|V_{2k}| = (q−1)^{k+1}`.** Exact `3/3` (`4, 16, 8`); at `(2,5)` it predicts
**`64`** against the true **`112`**. Killed before it was written anywhere.

**NOT A KILL, AND SAID SO — `(2,5)`.** The `(2,5)` cell was pre-registered as a death criterion in the sense
of Law 6 (target `1001, 696, 452, 260, 112, 0`, any excess kills the route) and **it did not fire**. That is a
gate passed, not a theorem, and **a third measured cell of the same shape would be `MEASUREMENT-TREADMILL`.**
The next turn on this object must be pencil.

---

## 7 · SCOPE — said twice, in both directions

**What this file buys.** A frame-free `∀k∀q` proof of the crude ceiling (method only, bound already deposited);
an exhaustive two-sided ladder with its bottom rung proved to be exactly the induction on `k`; a
better-shaped equivalent form of the ceiling; and four routes closed with numbers, three of them mine.

**What it does NOT buy.** **No gap falls. The ceiling `A_k(q) ≤ P_k(q)` is not proved in any new cell.** The
cumulative ladder inequality is MEASURED in 30 rungs and PROVED in none for `a` between `1` and `2k`. The
`a=1` rung is *equivalent* to the conjecture and must never be sold as a reduction. **The reserved closing
phrase is not spoken.**

---

`CHAISE_LONGUE | LEY 1 STATUS: [ceiling surface re-described with data — 3 theorems ∀k∀q (A, B, D-as-method), 36 rungs / 22 genuine tests / 22 passes across 7 cells and 3 dimensions, 4 candidates killed with numbers (110>108, 21/24, (2k+1)!! margin 0, 112≠64). NO GAP FELL. 99.1 % unchanged.]`
