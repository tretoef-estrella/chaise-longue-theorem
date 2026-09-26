> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-02
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SNAP THEOREMS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_SNAP_THEOREMS.md
>
> **Status, as written in the document:** 🟢 Self-contained. Every object defined. Every statement carries its grade and its scope. Nothing is graded `PROVED` without a proof written out here.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (7 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# **THE SNAP THEOREMS**
### Standalone · `v2` · Chaise Longue Campaign · 2026-09-02
### ### 🟢 **Self-contained. Every object defined. Every statement carries its grade and its scope. Nothing is graded `PROVED` without a proof written out here.**

---

# 1 · SETUP

Let `K = F_3`, `q = 3^v` odd, `k ≥ 1`, and `n = 2k+2`.

`S' = K[x_0,…,x_{2k}]` with the standard grading; `e_j(·)` denotes the elementary symmetric polynomial of degree `j` in the indicated letters; and
> ### `E'_k := (e_1, e_3, …, e_{2k+1})` — the **odd** elementary symmetric polynomials — and `m'^{[q]} := (x_0^q,…,x_{2k}^q)`, the **Frobenius box**.

Put `J_0 := E'_k + m'^{[q]}` and `B := S'/J_0`.

**The linear form.** Let `z := x_{2k}` and `U := \{x_0,…,x_{2k−1}\}` (the other `2k` letters), and write `ℓ := e_1(U)`. Since `e_1(x_0,…,x_{2k}) = 0` in `B`, we have `z = −ℓ` in `B`; and since `q = 3^v` in characteristic `3`, Frobenius gives `ℓ^q = Σ_{u∈U}u^q ∈ m^{[q]}`, so `z^q = 0`. Thus `B` is a module over
> ### `Λ := K[z]/(z^q)`, with `z` acting nilpotently. Write `E := ∏_{u∈U} x_u = e_{2k}(U)`.

**The generators.** For a pair `a < b` in `U` put `C' := U∖\{a,b\}`, `W := ∏_{c∈C'}x_c`, `Φ_u := u^{q−1}`, and
> ### `h_{ab} := Σ_{i=0}^{q−2} a^i(−b)^{q−2−i}`, so that `(a+b)·h_{ab} = Φ_a − Φ_b`;
> ### `s_{ab} := h_{ab}·W + (Φ_a − Φ_b)·e_{2k−3}(C')`,  and  `I_s := (s_{ab} : a<b ∈ U)·B`.

**Banked input (proved elsewhere in the campaign, gated 4/4):**
> ### `(H3')` `\quad z·s_{ab} = −T'_{ab}` in `B`, where `T'_{ab} := (Φ_a − Φ_b)·W`.

---

# 2 · `LEMMA 0` — THE TOP RELATION *(`PROVED`, all `k`, all `q = 3^v`)*

> ### **`z·E = 0` in `B`.**

**Proof.** Among the generators of `J_0` is `r_{2k+1} := e_{2k+1}(x_0,…,x_{2k})`. Written in terms of `U` and `z`, and using `e_1(x_0,…,x_{2k}) = 0`, this generator reduces to `e_{2k+1}(U) − ℓ·e_{2k}(U)`. But `U` has only `2k` letters, so `e_{2k+1}(U) = 0`; hence `ℓ·e_{2k}(U) = 0` in `B`, i.e. `z·E = 0`. ∎

---

# 3 · `T-SNAP` — THE PAIR DIRECTION *(`PROVED`, all `k`, all `q = 3^v`)*

> ### **(i)** `z·(x_a s_{ab}) = x_b^{q−2}·E`.
> ### **(ii)** `z^2·(m·s_{ab}) = 0` for every monomial `m` divisible by `x_a` or by `x_b`.

**Proof.** By `(H3')`, `z(x_a s_{ab}) = −x_a T'_{ab} = −x_aΦ_a W + x_aΦ_b W`.
The first term is `x_a·x_a^{q−1}·W = x_a^q W = 0`, since `x_a^q ∈ m'^{[q]}`.
The second is `x_a x_b^{q−1} W = x_b^{q−2}·(x_a x_b W) = x_b^{q−2}·E`, because `x_a x_b W = ∏_{u∈U}x_u = E`.
This proves (i). Applying `z` once more and using `LEMMA 0`, `z^2(x_a s_{ab}) = x_b^{q−2}·(z E) = 0`. The statement is symmetric in `a,b`; and since `z^2` is `B`-linear, for `m` divisible by `x_a` we get `z^2(m s_{ab}) = (m/x_a)·z^2(x_a s_{ab}) = 0`. ∎

> ### **Scope.** All `k ≥ 1`, all `q = 3^v`. The proof consumes `x_a^q = 0` (the box) and `LEMMA 0` (the top odd elementary). **It has no characteristic-zero content:** without the box there is no `x_a^q = 0`, and without `q = 3^v` there is no `z^q = 0`.

---

# 4 · `C-SNAP` — THE PAIR DIRECTION IS INVISIBLE *(`PROVED`, all `k`, all `q = 3^v`)*

> ### `z^2·I_s = z^2·Σ_{a<b} K[C']·s_{ab}`.

**Proof.** `B` is spanned by monomials in `U`. Split them into those divisible by `x_a` or `x_b` — killed by `z^2` on `s_{ab}`, by `T-SNAP (ii)` — and those lying in `K[C']`. ∎

> ### **Consequence.** The generating set for `z^2 I_s` drops from `\binom{2k}{2}·q^{2k}` multiples to `\binom{2k}{2}·q^{2k−2}`: **a factor of `q^2`** (`81` at `q = 9`, `729` at `q = 27`).

---

# 5 · THE SLICE RING, AND `J^2 = 0`

**The slice ring.** Fix `a ∈ U` and put `Y := (U∖\{a\}) ∪ \{w\}` with `w := −ℓ_a`, `ℓ_a := e_1(U∖\{a\})`; so `|Y| = 2k`. Write `E_Y := ∏_{y∈Y} y`. The relevant quotient is
> ### `Q_{k−1} := K[Y]\big/\big(e_1(Y),\,e_3(Y),\,…,\,e_{2k−1}(Y),\;e_{2k}(Y),\;\text{box}\big)`,
i.e. **the even cone of level `k−1`, with its top elementary killed.** In `Q_{k−1}`, all *odd* elementaries vanish, and also `E_Y = e_{2k}(Y) = 0`.

## 5.1 · `LEMMA C` — the cross products *(`PROVED`, exact identity over `Z`)*

> ### For all `u ≠ v` in `Y`: `\;(E_Y/y_u)(E_Y/y_v) \;=\; E_Y\cdot\big(E_Y/(y_uy_v)\big)`.

**Proof.** Pure letter count. In the product `(E_Y/y_u)(E_Y/y_v)`, every letter `y_w` with `w ∉ \{u,v\}` occurs once in each factor, hence twice; `y_u` occurs only in `E_Y/y_v`, hence once; and `y_v` occurs only in `E_Y/y_u`, hence once. Therefore
> ### `(E_Y/y_u)(E_Y/y_v) = y_uy_v·∏_{w∉\{u,v\}}y_w^{\,2} = \Big(∏_{w∈Y}y_w\Big)·∏_{w∉\{u,v\}}y_w = E_Y·\big(E_Y/(y_uy_v)\big)`. ∎

**This identity holds over `Z`, in any characteristic, and uses nothing else.** ✅ *Verified symbolically for all pairs at `|Y| = 4` and `|Y| = 6`.*

> ### **COROLLARY C.** In `Q_{k−1}`, where `E_Y = e_{2k}(Y) = 0`: `\;(E_Y/y_u)(E_Y/y_v) = 0` for all `u ≠ v`.

## 5.2 · `LEMMA S` — the squares *(`PROVED`, exact identity over `Z`)*

> ### For every `v ∈ Y`: `\;(E_Y/y_v)^2 = (E_Y/y_v)·e_{2k−1}(Y) − E_Y·e_{2k−2}(Y∖v)`.

**Proof.** Since `|Y| = 2k`, the elementary symmetric polynomial of degree `2k−1` is the sum of the products omitting one letter: `e_{2k−1}(Y) = Σ_{u∈Y} E_Y/y_u`. Multiplying by `E_Y/y_v`,
> ### `(E_Y/y_v)·e_{2k−1}(Y) = (E_Y/y_v)^2 \;+\; Σ_{u≠v}(E_Y/y_u)(E_Y/y_v)`,
where the term `u = v` has been separated. By **`LEMMA C`** the sum over `u ≠ v` equals `E_Y·Σ_{u≠v}E_Y/(y_uy_v)`, and
> ### `Σ_{u≠v} E_Y/(y_uy_v) = e_{2k−2}(Y∖v)`,
since `E_Y/(y_uy_v)` is the product of the `2k−1` letters of `Y∖v` with `y_u` omitted, and letting `u` run over `Y∖v` gives exactly the degree-`(2k−2)` elementary symmetric polynomial in those letters. Rearranging yields the identity. ∎

**It holds over `Z`, in any characteristic.** ✅ *Verified symbolically for every `v` at `|Y| = 2, 4, 6, 8` — 20 cases, all exact.*

> ### **COROLLARY S.** In `Q_{k−1}`, where `e_{2k−1}(Y) = 0` (odd elementary) and `E_Y = 0`: `\;(E_Y/y_v)^2 = 0` for every `v ∈ Y`.

⚠️ **Note on dependency.** `LEMMA C` is proved by letter count alone and does **not** invoke `LEMMA S`; `LEMMA S` cites `LEMMA C`. The order of the two is strict and there is no forward reference.

## 5.2bis · `THEOREM J` — the square-zero ideal *(`PROVED`, all `k`, all `q`)*

> ### Let `J := \big(E_Y/y_u \;:\; u ∈ Y\big) ⊆ Q_{k−1}`. Then `\;J^2 = 0`.

**Proof.** `J` is generated by the `2k` elements `E_Y/y_u`, so it suffices that every product of two generators vanishes. The cross products `u ≠ v` vanish by **`COROLLARY C`**; the squares `u = v` vanish by **`COROLLARY S`**. ∎

> ### **Why the two cases genuinely differ.** For `u ≠ v` the product is divisible by `E_Y` — every letter appears — and dies immediately. For `u = v` it is **not**: `(E_Y/y_u)^2` omits `y_u` altogether, so no argument by divisibility is available, and the vanishing has to be extracted from `LEMMA S`.
> ### **Structure.** `J` has `2k` generators subject to the single linear relation `Σ_{u∈Y}E_Y/y_u = e_{2k−1}(Y) = 0`, and `J^2 = 0`: in the public vocabulary, `J` is a **square-zero (trivial-multiplication) ideal**, hence a module over `Q_{k−1}/J` and nothing more.

## 5.3 · `COROLLARY W` — the `W`-direction *(`PROVED`, all `k`, all `q = 3^v`)*

With `Y = (U∖\{a\}) ∪ \{w\}` and `U∖\{a\} = \{b\} ∪ C'`, one has `E_Y/y_b = w·W`. Applying `COROLLARY S` with `v = b` gives `w^2W^2 = 0`, i.e. `ℓ_a^2W^2 = 0`, whence
> ### `z^3(W·s_{ab}) = 0` for every pair `a<b`, all `k`, all `q = 3^v`.

⚠️ **Scope note.** `COROLLARY W` transfers a statement from `Q_{k−1}` to `B` through the slice `Φ_a·B`. That transfer is exact up to relations of `B` not present in `Q_{k−1}`; at `(k,q) = (2,9)` those extra relations were measured and are exactly two, `Φ_aΦ_b·cd` and `Φ_aΦ_b·c^2`, both in degree `q+1`, i.e. **above** the degree where the statement is used. **One cell only.**

> ### 🟢 **NOTA `2026-09-16` (Grepy, turno 8, informe 136) — LA TRANSFERENCIA NO NECESITA MEDIDA: `COROLLARY W` ESTÁ PROBADO `∀k∀q=3^v` MÓDULO `(H3')`.** La aplicación `f ↦ x_a^{q−1}f` está bien definida `Q_{k−1} → B`. Cada generador del ideal de `Q_{k−1}` muere al multiplicarlo por `x_a^{q−1}`: las elementales impares de `Y` por `e_j(todas) ∈ E'_k` y `x_a^q = 0`; `e_{2k}(Y)` por `LEMMA 0`; `w^q ∈` caja. Además `z − w = −x_a` hace que `x_a^{q−1}f(z) = x_a^{q−1}f(w)`. **Luego toda relación de `Q_{k−1}` pasa a `B`**, que es la única dirección que usa el corolario; las relaciones de `B` que no están en `Q_{k−1}` no intervienen. Con la rebanada de `b` para el término `Φ_b`, `z^3(W s_{ab}) = −z^2W^2(Φ_a−Φ_b) = 0`. **Gate: `corpus4/regla136_corolarioW.log`, 9 celdas, entre ellas `(3,9)` y `(2,27)`, con 0 fallos y los controles negativos disparando.** Vale también para la fila `:138`.


---

# 6 · THE FREENESS CRITERION *(`PROVED`, general)*

Let `M` be a finitely generated `Λ`-module, `f ∈ M`. Write `ann(f)` for the least `t` with `z^tf = 0`, and let `h_{free}(f)` be the height of `f` measured in `M/(zM + Ann_M(z))`.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 8, informe 136) — la definición de `h_free` escrita aquí no mide nada:** en `M/(zM + Ann_M(z))` todo elemento tiene altura `0`, porque ya se ha cocientado por `zM`. La lectura que el corpus usa de verdad es **«altura MÓDULO EL ZÓCALO»** (`VIVOS/EL_CATALOGO_MAESTRO_v385.md`, entrada `v267.f`). El criterio, su prueba y el gate `114/114` no cambian; lo que cambia es la frase.


> ### **`h_{free}(f) + ann(f) = q` ⟺ `f` lies inside a free summand and contributes no elementary divisor of its own.**

**Proof.** (⟹) If `f = z^hu` with `u` free, then `ann(f) = q−h` and `h_{free}(f) = h`.
(⟸) Write `f = z^hg` with `g` of height `0`. Then `ann(f) = q−h` gives `z^{q−h−1}f ≠ 0`, i.e. `z^{q−1}g ≠ 0`, so `ann(g) = q` and `g` is free.
Finally, if `f` generates its own summand of size `r < q`, then `h_{free}(f) = 0` and `ann(f) = r`, so the sum is `r < q`. **The criterion separates the two cases.** ∎

⚠️ **The height must be measured modulo the socle.** `B` is not free — at `(2,9)` it is `Λ^{88} ⊕ K^{129}` — and an element `z^hu + w` with `w` in the `K`-part has height `0` in `B` because `zK = 0`, while its annihilator is still `q−h`; the naive height gives a false negative.

> ### **`MEASURED`, `(2,9)`, `114/114`:** for `f = x_c^{\,j}s_{ab}` with `x_c ∈ C'`, the sum `h_{free} + ann` equals `q` in every case, including `j = q−2` where `h_{free} = 7`.
> ### ⟹ **the pure powers lie inside free summands and contribute no new elementary divisor.** *(Grade: the criterion is `PROVED`; its application to the `x_c^{\,j}s_{ab}` is `MEASURED` at one cell.)*

---

# 7 · GRADES AND SCOPE

| statement | grade |
|---|---|
| `LEMMA 0` (`z·E = 0`) | **PROVED**, all `k`, all `q = 3^v` |
| `T-SNAP` (i) and (ii) | **PROVED**, all `k`, all `q = 3^v` |
| `C-SNAP` | **PROVED**, all `k`, all `q = 3^v` |
| **`LEMMA C`** (the cross identity) | **PROVED**, exact over `Z`, any characteristic — *verified symbolically, `|Y| = 4, 6`* |
| **`LEMMA S`** (the square identity) | **PROVED**, exact over `Z`, any characteristic — *verified symbolically, `|Y| = 2,4,6,8`, 20 cases* |
| **`THEOREM J`** (`J^2 = 0`) | **PROVED**, all `k`, all `q` — *cross terms by `LEMMA C`, squares by `LEMMA S`* |
| `COROLLARY W` (`z^3(W s_{ab}) = 0`) | **PROVED**, all `k`, all `q = 3^v` — ⚠️ modulo the slice transfer, measured at one cell |
| The freeness criterion (§6) | **PROVED**, general |
| Its application to `x_c^{\,j}s_{ab}` | **MEASURED**, `(2,9)`, `114/114` |
| The Jordan theorem for `I_s`, all `k` | **OPEN** |

**Nothing is claimed in characteristic `2`, nor for even `q`.** The identity of `LEMMA S` is the only statement here that is characteristic-free; everything else consumes the Frobenius box `x^q = 0` with `q = 3^v`.

---

# 8 · WHAT REMAINS

By `C-SNAP` the pair direction is invisible; by `COROLLARY W` the multiples of `W` die at `z^3`; and by §6 the pure powers of a single `C'`-letter sit inside free summands. **What is open is the behaviour of `m·s_{ab}` for `m ∈ K[C']` not divisible by `W`** — monomials of `C'` missing at least one letter. The measured Jordan type of `I_s` at `(2,9)` is `\{1{:}99,\;3{:}38,\;9{:}4\}`, and the `38` blocks of size `3` are exactly `b_{q−1}`, the multiplicity that the campaign must explain.

⚠️ **A caution recorded with the data:** the split of the generators into three directions (pair, `W`-multiples, rest) is a decomposition **of generators, not of modules** — at `(2,9)` the pieces have `39+3` blocks of size `2` that do not appear in `I_s` at all.

---
*Standalone `SNAP THEOREMS v2` · Chaise Longue Campaign. Companion to `LDL-SHARP v1`, `CONJECTURE R v1`, `THEOREM OMEGA v1` and `JORDAN REDUCTION v2`.*
