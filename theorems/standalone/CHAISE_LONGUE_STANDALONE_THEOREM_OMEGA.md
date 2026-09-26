> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-01
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *AN UPPER BOUND ON THE ORBIT HARMONICS IDEAL, AND AN INDUCTION STEP* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_THEOREM_OMEGA.md
>
> **Status, as written in the document:** 🟢 Self-contained. Every object defined here. `THEOREM F`, `THEOREM D` and `THEOREM OMEGA` are `PROVED for all k and all odd q`.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (6 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **AN UPPER BOUND ON THE ORBIT HARMONICS IDEAL, AND AN INDUCTION STEP**
### Standalone · `THEOREM OMEGA` · Chaise Longue Campaign · 2026-09-01
### ### 🟢 **Self-contained. Every object defined here. `THEOREM F`, `THEOREM D` and `THEOREM OMEGA` are `PROVED for all k and all odd q`.**

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «`THEOREM OMEGA` … `PROVED for all k and all odd q`»: INFLADO EN LA CABECERA.** Sólo `THEOREM OMEGA (i)` es incondicional; `(ii)` y el `COROLLARY` son **condicionales a la Conjetura 1.2 en nivel `k−1`**, como dice la propia tabla del `§7`. Lo que está bien: `THEOREM F`, `THEOREM D` y `(i)`, re-derivados por Grepy en el turno 8; gate `N_k(3)` cruzado con el informe 127.


---

# 1 · SETUP

`K = F_3`, `n = 2k+2`, `q = 3^v` odd, `S = K[x_0,…,x_{n−1}]`, `S' = K[x_0,…,x_{2k}]`, `m^{[q]} = (x_i^q)`.
> ### `E_k := (e_1, e_3, …, e_{2k+1})` — the **odd** elementary symmetric polynomials in `n = 2k+2` variables.

`E_k` is radical in characteristic `≠ 2` and `E_k = ⋂_J I_J` over the `(2k+1)!!` perfect matchings `J` of `{0,…,n−1}`, with `I_J = (x_a + x_b : \{a,b\} ∈ J)`.

**Two loci.**
> ### **The cone** `X_k := V(E_k)(F_q) ⊆ A^{n}`, of cardinality `P_k(q)`.
> ### **The slice** `V_1^{(k)} := V(E_k)(F_q) ∩ \{x_n = 1\} ⊆ A^{2k+1}`, of cardinality `N_k(q)`.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 8, informe 136) — `x_n` no existe:** las variables son `x_0,…,x_{n−1}`; léase `x_{n−1}` aquí y en `:17`, `:25`, `:84`. Errata `E47`, ya registrada en `corpus/LA_MOCHILA_DE_LA_VICTORIA_v121.md` `§0.217` y nunca llevada a este fichero.


For a finite locus `Z`, `I(Z)` is its vanishing ideal, `gr I(Z)` the ideal of top forms, and `R(Z) = K[x]/gr I(Z)` the **orbit harmonics ring** (Li–Liu–Rhoades, arXiv:2607.28157, Def. 1.2).

**Conjecture 1.2 at level `k`** (Degtyarev–Shimada, arXiv:1405.4683) states `A_k(q) = P_k(q)`, where `A_k(q) = dim_K S/(E_k + m^{[q]})`. It is **equivalent** to
> ### `gr I(X_k) = E_k + m^{[q]}`,
since `gr I(X_k) ⊇ E_k + m^{[q]}` always, and the two quotients have dimensions `P_k(q)` and `A_k(q)` respectively.

**The anchor.** A point of `V(E_k)(F_q)` has coordinate multiset closed under negation. On the slice `x_n = 1`, this forces
> ### `#\{i ≤ 2k : x_i = −1\} = #\{i ≤ 2k : x_i = 1\} + 1 ≥ 1`,
so **every point of the slice has at least one coordinate equal to `−1`**. Set
> ### `Y_a := \{x_a = −1\} × X_{k−1}(x_i : i ≠ a)`, i.e. the points of `V_1^{(k)}` with `x_a = −1`.

Then `V_1^{(k)} = ⋃_{a=0}^{2k} Y_a`. ⭐ **This is the anchor, and it is what makes everything below valid.**

---

# 2 · `THEOREM F` — THE ANCHOR FIBRATION *(`PROVED`, all `k`, all odd `q`)*

For `j ≥ 0`, `r ≥ 0` put
> ### `Z(j,r) := \{y ∈ F_q^j :` the multiset of `y` together with `r` copies of `1` is closed under negation`\}`.

So `V_1^{(k)} = Z(2k+1, 1)` and `X_k = Z(2k+2, 0)`.

> ### **(i)** `#Z(j,r) = j! · [t^j] \, e^t · I_0(2t)^{(q−3)/2} · I_r(2t)`, with `I_r` the modified Bessel functions `I_r(2t) = Σ_m t^{2m+r}/(m!\,(m+r)!)`.
> ### **(ii)** For `r ≥ 1`: `#Z(j,r) = Σ_{m ≥ 1} (−1)^{m−1} \binom{j}{m} \, #Z(j−m, |r−m|)`.

**Proof.** A multiset is closed under negation iff `mult(c) = mult(−c)` for every `c ≠ 0`, with `mult(0)` unconstrained; with `r` extra copies of `1` the condition reads `mult_y(−1) = mult_y(1) + r`. Build the exponential generating function value by value: `e^t` for the value `0`; `Σ_m t^{2m}/(m!)^2 = I_0(2t)` for each of the `(q−3)/2` pairs `\{c,−c\}` with `c ≠ 0, ±1`; and `Σ_m t^{2m+r}/(m!(m+r)!) = I_r(2t)` for the pair `\{1,−1\}`. Multiply. For (ii), `r ≥ 1` forces some coordinate to equal `−1`; fixing the set `A` of coordinates equal to `−1` with `|A| = m` and deleting them, the remainder satisfies `mult(−1) − mult(1) = r − m`, i.e. lies in `Z(j−m, r−m)` for `m ≤ r` and, by `y ↦ −y`, in `Z(j−m, m−r)` for `m > r`. Inclusion–exclusion over `A` gives the formula. ∎

✅ **Gate `8/8`:** `N_k(3) = 6, 45, 357, 2907` and `N_k(9) = 24, 855, 37947, 1930329` for `k = 1,…,4`, by the EGF **and** by inclusion–exclusion, both agreeing with `P_k = P'_k + (q−1)N_k`.

⚠️ **Note.** `I_0(2t)` as the EGF of balanced pairs is classical. `I_r(2t)` with `r` interpreted as the **anchor imbalance** in a count of `F_q`-rational points appears to be new; combinatorially, `I_r(2t)` is the EGF of lattice paths ending at height `r`.

---

# 3 · `THEOREM D` — THE DETECTORS NEST *(`PROVED`, all `k`, all odd `q`)*

For disjoint `A, B ⊆ \{0,…,2k\}` with `T = A ∪ B`, the **parity detector** is
> ### `G_{A,B} := (∏_{l ∈ T^c} x_l)·[ (−1)^{|A|}∏_{a∈A}(1+x_a^{q−1}) − (−1)^{|B|}∏_{b∈B}(1+x_b^{q−1}) ] ∈ I(V_1^{(k)})`.

> ### **Restricted to `\{x_a = −1\}`, a level-`k` detector becomes a level-`(k−1)` CONE detector:**
> ### if `a ∈ T^c` then `G_{A,B}|_{x_a=−1} = −G^{cone}_{A,B}`; if `a ∈ A` then `G_{A,B}|_{x_a=−1} = G^{cone}_{A∖a,\,B}`; symmetrically for `a ∈ B`.

**Proof.** On `x_a = −1` one has `x_a^{q−1} = 1`, so `1 + x_a^{q−1} = 2 = −1`, and the factor `(−1)^{|A|}∏_A` becomes `(−1)^{|A|−1}∏_{A∖a}`; the prefactor loses the factor `x_a = −1` when `a ∈ T^c`. The remaining `2k` coordinates carry the cone condition (`Theorem F` with `r = 0`), and the same parity argument shows the restricted polynomial vanishes there: zeros pair up in a negation-closed multiset. ∎

---

# 4 · `THEOREM OMEGA` — THE UPPER BOUND *(`PROVED`, all `k`, all odd `q`)*

> ### **(i) Unconditionally:** `\; gr\,I(V_1^{(k)}) \;⊆\; ⋂_{a=0}^{2k} \big( (x_a) + gr\,I(X_{k−1})^{(a)} \big)`,
> ### where `gr I(X_{k−1})^{(a)}` denotes the level-`(k−1)` cone ideal in the variables `x_i`, `i ≠ a`.
> ### **(ii) If Conjecture 1.2 holds at level `k−1`**, so that `gr I(X_{k−1}) = E_{k−1} + m^{[q]}`, then
> # `gr\,I(V_1^{(k)}) \;⊆\; Ω_k := ⋂_{a=0}^{2k} \Big( (x_a) + E_{k−1}(x_i : i ≠ a) + m'^{[q]} \Big)`.
> ### Equivalently, there is a surjection `R(V_1^{(k)}) ↠ S'/Ω_k`, and `HF(R(V_1)) ≥ HF(S'/Ω_k)` degreewise.

**Proof.**
**(a)** Since `V_1^{(k)} = ⋃_a Y_a` *(the anchor)*, `I(V_1^{(k)}) = ⋂_a I(Y_a)`. For any family of ideals, `gr(⋂_a J_a) ⊆ ⋂_a gr(J_a)`: the top form of an element of the intersection is a top form of an element of each `J_a`. ⭐ **This is the free direction; no hypothesis is used.**

**(b)** For an ideal `J` in the variables other than `x_a`, one has `gr\big(J + (x_a+1)\big) = gr\,J + (x_a)`. Indeed `⊇` holds because `x_a` is the top form of `x_a + 1` and top forms of `J` are top forms of `J + (x_a+1)`; and both quotients have the same Hilbert function, since `S'/(gr J + (x_a)) ≅ S_{2k}/gr J` and the translated point set `Y_a = \{−1\} × X` has the same degree-filtered function space as `X`. Hence equality.

**(c)** Take `J = I(X_{k−1}) = E_{k−1} + (x_i^q − x_i)`. Then `gr J ⊇ E_{k−1} + m^{[q]}` always, `dim S_{2k}/gr J = #X_{k−1} = P_{k−1}(q)` and `dim S_{2k}/(E_{k−1}+m^{[q]}) = A_{k−1}(q)`; so `gr J = E_{k−1} + m^{[q]}` **iff** `A_{k−1} = P_{k−1}`, i.e. iff Conjecture 1.2 holds at level `k−1`. Substituting into (a)–(b) gives (i) and (ii). ∎

---

# 5 · THE INDUCTION STEP

> # **COROLLARY.** `\;\big[\text{Conjecture 1.2 at level } k−1\big] \;+\; \big[\,Ω_k ⊆ J_1\,\big] \;\Longrightarrow\; \big[\text{Conjecture 1.2 at level } k\big]`,
> ### where `J_1 := \big((E_k + m^{[q]}) : x_n + (x_n)\big)/(x_n)`.

**Proof.** Conjecture 1.2 at level `k` is equivalent to the single containment `gr I(V_1^{(k)}) ⊆ J_1` *(the reverse containment `J_1 ⊆ gr I(V_1)` is known)*. Under the first hypothesis, `Theorem Omega (ii)` gives `gr I(V_1^{(k)}) ⊆ Ω_k`, and the second hypothesis then gives `gr I(V_1^{(k)}) ⊆ J_1`. ∎

> ### ⭐ **Both hypotheses are inclusions between EXPLICIT IDEALS: no point set appears. `Ω_k` is built from level `k−1`; `J_1` from level `k`. And the base of the induction is deposited: Conjecture 1.2 is proved for `k ≤ 3` (Degtyarev–Shimada; the campaign's `SOFÁ` and `HAMACA`, DOI 10.5281/zenodo.21382543).**

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «Conjecture 1.2 is proved for `k ≤ 3` (Degtyarev–Shimada; SOFÁ and HAMACA)»: HAY QUE PRECISARLO.** `k=1` `∀q` de lápiz; `k=2` Sofá y `k=3` Hamaca, depositados y **pendientes de revisión humana**. La Hamaca tiene además que corregir la frontera de su Top (`c = q, q+1, q+2`; `MISION_CORRECCION_HAMACA_v3.md`, retenida). Degtyarev–Shimada sólo calculan celdas sueltas.


⚠️ **The equality `gr I(V_1) = Ω_k` is NOT needed** for the corollary and is NOT claimed here: only the inclusion `Ω_k ⊆ J_1` is missing.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «only the inclusion `Ω_k ⊆ J_1` is missing»: LA INCLUSIÓN QUE FALTA ES ESTRICTAMENTE MÁS FUERTE QUE LA CONJETURA EN NIVEL `k`.** Como `J_1 ⊆ gr I(V_1) ⊆ Ω_k` (`E45`), `Ω_k ⊆ J_1` obliga a `Ω_k = gr I(V_1) = J_1`, o sea a la Conjetura 1.2 en nivel `k` **y además** a `OMEGA-EQ`. Es la misma especie que `E48` (`MOCHILA §0.221`). **Y `Ω_k` quedó ELIMINADO como diana** (`VIVOS/CHAISE_LONGUE_CEMENTERIO_LIVE_v363.md:906`), aunque el teorema sigue probado y citable.


---

# 6 · MEASURED EVIDENCE *(gates, not part of the proofs)*

`HF(S'/Ω_k) = h_{V_1}` **in every degree, in six cells including new terrain:**

| cell | `h_{V_1}` | sum |
|---|---|---|
| `(1,3)` | `(1,2,3)` | `6` |
| `(1,9)` | `(1,2,3^7)` | `24` |
| `(2,3)` | `(1,4,10,15,15)` | `45` |
| `(2,9)` | 17-term vector | `855` |
| `(3,3)` | `(1,6,21,49,84,105,91)` | `357` |
| **`(4,3)`** *(new terrain)* | `(1,8,36,111,258,468,672,750,603)` | **`2907`** |

**Independently recomputed base case.** At `k = 1`, `q = 3`: `Ω_1 = ⋂_{a=0}^{2}\big((x_a) + (x_i + x_j) + m'^{[3]}\big)`, where `\{i,j\} = \{0,1,2\}∖\{a\}` and `E_0 = (e_1)` in the two remaining letters. Direct linear algebra over `F_3` gives `HF(S'/Ω_1) = (1,2,3)`, sum `6 = N_1(3)`. ✅

Support ends at `k(q−1)` in all six cells. The `LDL` drop at degree `q` equals `2k` in all cells with `k ≥ 2`.

---

# 7 · GRADES, SCOPE, AND WHAT IS NOT CLAIMED

| statement | grade |
|---|---|
| `THEOREM F` (anchor fibration, Bessel EGF, inclusion–exclusion) | **PROVED, all `k`, all odd `q`** |
| `THEOREM D` (detectors nest onto the level-`(k−1)` cone) | **PROVED, all `k`, all odd `q`** |
| `THEOREM OMEGA (i)` | **PROVED unconditionally** |
| `THEOREM OMEGA (ii)` and the `COROLLARY` | **PROVED, conditional on Conjecture 1.2 at level `k−1`** |
| `HF(S'/Ω_k) = h_{V_1}` | **MEASURED 6/6**, new terrain included |
| `gr I(V_1) = Ω_k` (`OMEGA-EQ`) | **CONJECTURE — not needed for the corollary** |
| `Ω_k ⊆ J_1` | **OPEN. This is the whole of what remains.** |

⚠️ **`OMEGA-EQ` is a distributivity of `gr` over an intersection, the same species as the campaign's wall, and is flagged as such.** ⚠️ Nothing is claimed in characteristic `2`, nor for even `q`. **The obstruction to `OMEGA-EQ`, when it is wanted, is the classical gluing defect, whose public vocabulary is CAYLEY–BACHARACH and SEPARATORS** *(Eisenbud–Green–Harris, Bull. AMS 33 (3) (1996) 295–324; Geramita–Kreuzer–Robbiano, Trans. AMS 339 (1) (1993) 163–189; Caviglia–De Stefani, Bull. LMS 53 (4) (2021) 1185–1195)*.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «`OMEGA-EQ` … the same species as the campaign's wall»: RETIRADO POR `E43`** (`VIVOS/EL_CATALOGO_MAESTRO_v385.md` entrada `v264.a`; `CEMENTERIO_LIVE v363:917`). `OMEGA-EQ` se decide contando dimensiones, sin distributividad. La retirada nunca llegó a este fichero.


---
*Standalone `THEOREM OMEGA v1` · Chaise Longue Campaign. Companion to `LDL-SHARP v1` and `CONJECTURE R v1`.*
