> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-30
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · COLON LADDER STRUCTURE THEOREM — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_COLON_LADDER_STRUCTURE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · COLON LADDER STRUCTURE THEOREM — v1
**Standalone. Locard, 30 August 2026. Target: the full ladder `(L_j)`, `j = 2..2k`, of the vertex route (`VERTEX_REDUCTION_THEOREM_v1` Thm 2.1 + Lemma P).**

---

## 0. Setting and what this closes

`K = F_3`, `n = 2k+2`, `Ā = Ā_k(q) = S/(E + m^[q])`, `q = 3^v`, `ℓ_a = x_a + x_{n−1}`.
`Q_0 := Ā/ℓ_0Ā ≅ R[z]/(z^q)`, `R := Ā_{k−1}(q)` on the variables `x_1..x_{2k}`, `z = x_{n−1}` (P5+X5, banked).
After the Frobenius shift `y := z + x_1` (an automorphism since `x_1^q = 0`), the vertex forms read
`ℓ̄_1 = y`, `ℓ̄_b = y + c_b`, `c_b := x_b − x_1 ∈ R`, `c_b^q = 0`.

**Banked reduction (Mochila §0.62, proved):** given `(L_{j−1})`,
`(L_j) ⟺ (0:_Ā ℓ_1⋯ℓ_j) ↠ (0:_{Q_0} ℓ̄_1⋯ℓ̄_j)`.

**This document computes the target of that surjection completely, for every `j`, every `k`, every `q = 3^v`** (in fact every `q ≥ 2` and any commutative ring `R` with `c_b` satisfying no hypothesis at all; `c_b^q = 0` is used only where flagged). The `2k−1` rungs of the ladder are shown to be governed by ONE explicit matrix over `Ā_{k−1}` whose entries are complete homogeneous polynomials in the differences `c_b`.

Everything happens inside `T := R[y]/(y^{q−1})`, because
> **(0:_{Q_0} ℓ̄_1⋯ℓ̄_j) = y^{q−1}R ⊕ N_j,  N_j := (0:_T ∏_{b=2}^j (y+c_b)).**
*(Proof: `h ∈ (0:_{Q_0} y·g)` ⟺ `g·h ∈ (0:_{Q_0} y) = y^{q−1}R` ⟺ the `y^0..y^{q−2}` coefficients of `g·h` vanish; the `y^{q−1}` coefficient of `h` is unconstrained and contributes the free summand `y^{q−1}R ⊆ ℓ̄_1^{q−1}Q_0`.)*

---

## 1. The two elementary bricks

**Definition.** `Φ_c := Σ_{i=0}^{q−2} (−c)^{q−2−i} y^i ∈ R[y]` (degree `q−2`).
For nodes `c_{b'},…,c_b` let `Φ_{[c_{b'}..c_b]}` be the divided difference of order `b−b'` of `c ↦ Φ_c`. Divided differences of a polynomial are polynomials in the nodes (no denominators): explicitly
`Φ_{[c_{b'}..c_b]} = Σ_i (−1)^{q−2−i}\,h_{q−2−i−(b−b')}(c_{b'},…,c_b)\,y^i`,
where `h_m` is the complete homogeneous polynomial of degree `m` (`h_m := 0` for `m<0`, `h_0 = 1`).

**Lemma 1 (one factor, exact).** `(y+c)\,Φ_c = y^{q−1} − c^{q−1}` in `R[y]`; hence in `T`:
`(y+c)Φ_c = −c^{q−1}` and `(0:_T (y+c)) = Φ_c·(0:_R c^{q−1})`.
*Proof.* The product telescopes (Lucas is not even needed; it is a binomial-free telescope). For the colon: `(y+c)h = 0` with `h = Σ_{i≤q−2}h_iy^i` forces `h_{i} = (−c)^{q−2−i}h_{q−2}` downward and the bottom coefficient gives `c^{q−1}h_{q−2} = 0`. ∎

**Lemma 2 (the workhorse identity, exact in `R[y]`).** For any nodes `c_{b'},…,c_b` (`b > b'`):
> `(y + c_b)\,Φ_{[c_{b'}..c_b]} = −Φ_{[c_{b'}..c_{b−1}]} − h_{q−1−(b−b')}(c_{b'},…,c_b).`
*Proof.* Apply the divided difference `[c_{b'}..c_b]` to the identity of Lemma 1, `ψ_c := (y+c)Φ_c = y^{q−1} − c^{q−1}`, using the Leibniz rule `[u_0..u_m](fg) = Σ_i [u_0..u_i]f·[u_i..u_m]g` with `f = y+c` (degree 1, so only the first two terms survive) and the symmetry of divided differences in their nodes (so the surviving factor may be taken at the LAST node `c_b`):
`(y+c_b)[c_{b'}..c_b]Φ + [c_{b'}..c_{b−1}]Φ = [c_{b'}..c_b](y^{q−1} − c^{q−1}) = −h_{q−1−(b−b')}(c_{b'}..c_b)`,
by the standard evaluation `[u_0..u_m]\,t^N = h_{N−m}(u_0..u_m)`. ∎

*(Char-free; no Frobenius used so far.)*

---

## 2. The matrix and the main theorem

**Definition (the ladder matrix).** For `j ≥ 2`, `M_j ∈ Mat_{(j−1)×(j−1)}(R)`, rows and columns indexed by `b, b' ∈ {2,…,j}`:

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 9, informe 137) — ERROR DE SIGNO: con esta `M_j` literal, `α(ker M_j) ⊄ N_j` desde `j = 3`.** A mano en `j=3`, `q=3`: con `c_3²r_3 = −(c_2+c_3)r_2` (fila literal) sale `(c_2+c_3)h_0 + c_2c_3h_1 = −(c_2+c_3)r_2 ≠ 0`. **La matriz que produce la propia inducción del Teorema A es `M'_2 = (c_2^{q−1})`, `M'_j = [[M'_{j−1}·D, 0], [h_{q−1−(j−b')}(c_{b'}..c_j)\ (b'<j),\ −c_j^{q−1}]]` con `D = diag(−1,…,−1,+1)`** (el parámetro heredado `s_b = −u_b` para `b < j−1`). **Gate `corpus4/regla137_colon_signo.log` (M2), celdas `(2,3)`, `(3,3)` y `(2,9)`, `j = 2..4`:** con la matriz literal, generadores fuera de `N_j`: `5, 7 · 32, 79 · 6, 12`; **con `M'_j`: 0 en las nueve, y el ideal generado es igual a `N_j` en las nueve.** Las dimensiones no cambian, porque `M'_j = D_1 M_j D_2` con diagonales `±1`; **por eso el gate `8/8` de `§4`, que compara sólo `dim ker`, no podía ver el error.**

> `(M_j)_{b,b'} := h_{q−1−(b−b')}(c_{b'}, c_{b'+1}, …, c_b)` for `b' ≤ b`;  `0` above the diagonal.
Diagonal: `h_{q−1}(c_b) = c_b^{q−1}`. First subdiagonal: `h_{q−2}(c_{b−1},c_b)`. Entries vanish once `b−b' > q−1`; the entry at `b−b' = q−1` is `h_0 = 1`.

**Theorem A (structure of every rung; PROVED, all `j`, all `k`, all `q`).** Define
`α: R^{j−1} → T`, `α(r) = −Σ_{b=2}^{j−1} Φ_{[c_b..c_j]}\,r_b + Φ_{[c_j]}\,r_j.`
Then
> ### `N_j = α(\ker M_j)`.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 9, informe 137) —** este enunciado vale con `M'_j` (ver la marca de `:47`), no con la `M_j` impresa. Afecta a la copia literal del CATÁLOGO (`VIVOS/EL_CATALOGO_MAESTRO`, línea que empieza por «En `T=R[y]/(y^{q-1})`»).

Consequently `(0:_{Q_0} ℓ̄_1⋯ℓ̄_j) = y^{q−1}R + α(ker M_j)`, and the lifting problem of EVERY rung `(L_j)` is the problem of lifting the finitely many classes `α(r)`, `r ∈ ker M_j`, from `(0:_Ā ℓ_1⋯ℓ_j)`.

*Proof by induction on `j`.*
`j = 2`: Lemma 1 (`M_2 = (c_2^{q−1})`, `α(r) = Φ_{c_2}r`).
Step `j−1 → j`: `h ∈ N_j ⟺ (y+c_j)h ∈ N_{j−1}`, where `N_{j−1}` is taken at the nodes `c_2..c_{j−1}`. By the inductive hypothesis `(y+c_j)h = α_{j−1}(s)` for some `s ∈ ker M_{j−1}`.
(i) *Particular solutions.* By Lemma 2 with appended node `c_j`,
`(y+c_j)\,Φ_{[c_b..c_j]} = −Φ_{[c_b..c_{j−1}]} − h_{q−1−(j−b)}(c_b..c_j)`,
so `h_b := −Φ_{[c_b..c_j]}s_b` satisfies `(y+c_j)h_b = Φ_{[c_b..c_{j−1}]}s_b + h_{q−1−(j−b)}(c_b..c_j)\,s_b`: it solves the `b`-th summand up to a CONSTANT (`y`-degree 0) error.
(ii) *Absorbing the constants.* Summing, `(y+c_j)(h − Σ_b h_b) = −κ(s)` with `κ(s) := Σ_{b=2}^{j−1} h_{q−1−(j−b)}(c_b..c_j)\,s_b ∈ R`. By Lemma 1 the general solution of `(y+c_j)h_0 = −κ` is `h_0 = Φ_{[c_j]}t` with `c_j^{q−1}t = κ(s)`, existing iff `κ(s) ∈ c_j^{q−1}R`, and unique up to `Φ_{[c_j]}(0:_R c_j^{q−1})`.
(iii) *Collecting.* `h = −Σ_{b<j}Φ_{[c_b..c_j]}s_b + Φ_{[c_j]}t` with `M_{j−1}s = 0` and the new row `c_j^{q−1}t = Σ_b h_{q−1−(j−b)}(c_b..c_j)s_b` — i.e. exactly `M_j(s,t)^T = 0` after a uniform sign flip of the inherited rows (which does not change the kernel). Conversely every `α(r)`, `r ∈ ker M_j`, lands in `N_j` by the same identities read forward. ∎

**Remark (parametrisation vs. dimension).** `α` restricted to `ker M_j` is bijective onto `N_j` for `j ≤ q−1` (the generators `Φ_{[c_b..c_j]}` have `y`-degrees `q−1−(j−b+1)`, strictly decreasing, with unit leading coefficients: triangular). For `j > q−1` some generators degenerate to constants or `0` and `α` may have kernel; the identity `N_j = α(ker M_j)` (both inclusions) holds regardless — it is what the induction proves. **MEASURED moreover: `dim ker M_j = dim N_j` in all 8 available cells, including the degenerate regime** (see §4). The campaign only needs the surjection.

**Theorem B (the free part, PROVED, all `j`, all `k`, `q = 3^v`).** Here Frobenius enters: `ℓ̄_b^{q} = y^q + c_b^q = 0`, so `ℓ̄_b^{q−1}` are the free annihilators. Then, exactly:
> `Σ_{b=1}^{j} ℓ̄_b^{q−1}Q_0 = y^{q−1}R \;⊕\; Σ_{b=2}^{j} c_b\,Φ_{c_b}R.`
*Proof.* `ℓ̄_1^{q−1}Q_0 = y^{q−1}R`. By Lucas `ℓ̄_b^{q−1} = (y+c_b)^{q−1} = y^{q−1} − c_bΦ_{c_b}`. And `c_bΦ_{c_b}Q_0 = c_bΦ_{c_b}R` because `Φ_{c_b}·y = −c_b^{q−1} − c_bΦ_{c_b}` (Lemma 1), so multiplying by `y` reproduces `c_bΦ_{c_b}R` modulo `c_b^qR = 0` and `y^{q−1}R`-terms with coefficient `c_b^{q−1}·c_b = 0`. ∎

**Corollary (the invariant, now exact).**
> `Θ_j = \dim\big[\,α(\ker M_j)\;/\;(α(\ker M_j) ∩ (y^{q−1}R + Σ_b c_bΦ_{c_b}R))\,\big]` — the mass every rung still needs, and it is computed by ONE matrix over `Ā_{k−1}`.

---

## 3. What died in this turn (pre-registered gate fired)

**The greenlit candidate** `(0:_{Q_0}ℓ̄_1⋯ℓ̄_j) = Σ_bℓ̄_b^{q−1}Q_0 + Φ_j·(0:_R γ_j)`, `γ_j = ∏_{b≥2}c_b`, **is DEAD with its number**: already at `j = 2` the true residual parameter module is `(0:_R c_2^{q−1})` (Lemma 1), not `(0:_R γ_2) = (0:_R c_2)`, and the two differ byte-exact:
`dim(0:_R c_2) = 7 ≠ 14 = dim(0:_R c_2^{q−1})` at `k=2, q=3`; `51 ≠ 102` at `k=3, q=3`.
Moreover no single-annihilator form can be correct for `j ≥ 3`: the proved matrix `M_j` couples the nodes through the OFF-diagonal entries `h_{q−1−(b−b')}(c_{b'}..c_b)` (e.g. `h_1 = c_2+c_3` at `q=3`), which no colon `(0:_R x)` of one element reproduces. Registered as `SINGLE-ATOM-LADDER` in the cemetery. The matrix law replaces it and is strictly stronger.

---

## 4. Gates (all executed this turn, engines attached)

Engine `CHAISE_LONGUE_MJ_KERNEL_GATE_v1.py` (builds `R = Ā_{k−1}(q)`, the commuting multiplication matrices `c_b = X_b − X_1`, the blocks `h_m(c_{b'}..c_b)` by the recursion `h_m(C∪{c}) = h_m(C) + c·h_{m−1}(C∪{c})`, and `ker M_j`); engine `CHAISE_LONGUE_THETA_LADDER_ENGINE_v1.py` (measures the colons independently).

| cell | `j` | `dim ker M_j` (law) | `dim N_j` (measured colon − dR) | |
|---|---|---|---|---|
| `k=2, q=3` | 2,3,4 | `14, 24, 30` | `14, 24, 30` | ✅ 3/3 |
| `k=3, q=3` | 2,3,4,5,6 | `102, 174, 222, 250, 265` | `102, 174, 222, 250, 265` | ✅ 5/5 |

| cell | `j` | free part `dR + dim Σc_bΦ_bR` (Thm B) | measured `Σℓ̄_b^{q−1}Q_0` | |
|---|---|---|---|---|
| `k=2, q=3` | 2,3,4 | `31, 39, 43` | `31, 39, 43` | ✅ 3/3 |
| `k=3, q=3` | 2..6 | `231, 289, 327, 352, 363` | `231, 289, 327, 352, 363` | ✅ 5/5 |

Positive/negative controls inside the engines: `dim R = 3, 19, 141` and `dim Q_0 = 9, 57, 423` reproduce the corpus; `Θ_2 = m_{q−1}(Ā_{k−1}) = 2, 12` (the broken tiles) reproduced by an engine independent of the one that produced the corpus figures.
Death criterion pre-registered in the mission (`Θ_j` must come out `0,2,4,6` and `0,12,26,36,39,43`): **satisfied by the matrix law, fired against the naive candidate.**

---

## 5. Scope, grades, consequences

- **Theorem A:** `PROVED`, all `j ≥ 2`, all `k ≥ 1`, all `q ≥ 2`, any coefficients (divided-difference calculus only; nothing about `Ā` is used beyond `Q_0 = R[y]/(y^q)`).
- **Theorem B:** `PROVED`, all `j`, all `k`, `q = 3^v` (uses `c_b^q = 0`, i.e. Frobenius linearity in char 3).
- **`α` bijective on `ker M_j`:** `PROVED` for `j ≤ q−1`; `MEASURED 8/8` beyond (not needed by the campaign).
- **Consequence for the wall:** the vertex route `(I)_k ⟺ (I')_k` + Lemma P + Prop. `∏ℓ_a ∈ E` (N15) reduce the conjecture to: *for each `j`, every class `α(r)`, `r ∈ ker M_j`, lifts to `(0:_Ā ℓ_1⋯ℓ_j)`*. The free lifts `ℓ_b^{q−1}` cover exactly `y^{q−1}R ⊕ Σc_bΦ_{c_b}R` (Thm B). **What remains — MISSION 2 — is one uniform lifting statement, and its target is now an explicit matrix kernel over `Ā_{k−1}`, not `2k−1` separate problems.**
- **Named next machine (banked path, not yet executed):** the `W`-rule of the ∀k annihilator (`ℓ_0ℓ_2(ℓ_aW)=0`, Mochila §0.58) generalises by taking `F = {x_1,…,x_j, x_{n−1}, …}` and a matching `W` on the complement: `W·E(t) ≡ W·E_F(t)∏(1+q_it²)` kills every seam by Frobenius and delivers `W·σ_{odd}(F) ∈ E+m^[q]` — a supply of annihilators of long products of `ℓ`'s, with a parity structure (`|F|` and the complement must admit a matching) to be worked out. Gate for Mission 2 pre-registered: the lifted family must cover masses `Θ_j = 0,12,26,36,39,43` at `k=3` and `0,2,4,6` at `k=2`.

*Locard · 2026-08-30 · Campaña Chaise Longue.*
