> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-05
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SHEET COLON ONSET THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHEET_COLON_ONSET_THEOREM.md
>
> **Status, as written in the document:** GRADE: PROBADO. `N = 1` — one formula, `k` and `q` as letters. Characteristic-free. Pencil; no measurement enters the proof. The only numbers appearing anywhere below are the coefficients of one hand expansion at `(k,q) = (2,9)`, done on paper.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SHEET COLON ONSET THEOREM
## `indeg((u_1^q,…,u_{k+1}^q) : Δ) = q − 2k + 1` — for every `k ≥ 1`, every odd `q ≥ 2k+1`, over **any** field

**Standalone theorem document · v1 · 2026-09-05** · Prefix CHAISE_LONGUE · Pending P0 (cold gate).
**Constructor:** Fable (mission `FR-PUREZA-1`, one turn). **Audit:** MacGyver. **Scribe copy:** Ulen 3.
*Nothing in this file is new relative to `FR_PUREZA_1_REPORT.md`. The proofs of §2 are Fable's, reproduced verbatim in substance; §3 is the auditor's check; §4–§6 are placement, scope and the three equivalent languages, all with their sources.*

> ### **WHY THIS IS A SEPARATE STANDALONE, AND NOT A SECTION OF `GLUED_PURITY`.**
> Theorem 1 of `CHAISE_LONGUE_GLUED_PURITY_THEOREM_v1` is this theorem, and that file is the right home for the glued statement. **This one exists because the hypotheses are strictly weaker and a referee should be able to audit it without accepting any of the others: no characteristic assumption, no Frobenius, no frame condition, no `q = p^v`.** It needs only: a field, a polynomial ring, `q` odd, `q ≥ 2k+1`. **Whatever happens to the glued half, this statement stands.**

---

## §1 · Setting and statement

**Setting.** Let `K` be **any** field. Let `k ≥ 1`, let `q` be **odd**, and let
```
P     = K[u_1, …, u_{k+1}]          (one sheet's coordinate ring)
x_i  := u_i^2 ,      m := (q−1)/2
Δ    := ∏_{i<j} (u_i^2 − u_j^2)  =  V(x_1, …, x_{k+1})     the Vandermonde in the SQUARES,   deg_u Δ = k(k+1)
𝔟    := (u_1^q, …, u_{k+1}^q)        the Frobenius power of the maximal ideal on the sheet
```
`(𝔟 : Δ) = { h ∈ P : Δ·h ∈ 𝔟 }` is the colon ideal, and `indeg` is the least degree in which it is nonzero.
*(In the campaign `Δ = Δ_J = Π_J` is the leaf generator of the conductor `c_ = ann_R(R̃/R)` on the sheet `V_J`; `SINGULAR_LOCUS_LEMMA:53`, `FR_CAMBIOS_2 §3`. The identification `Π_J = Δ_J` is by definition: `(w_p+w_{p'})(w_p−w_{p'}) = w_p²−w_{p'}²`, same degree `k(k+1)`, same object.)*

---

> # **THEOREM (sheet colon onset).**
> **For every `k ≥ 1`, every odd `q ≥ 2k+1` and every field `K`:**
> # **`indeg(𝔟 : Δ) = q − 2k + 1`**
> **and the onset is realised by the explicit witness**
> # **`h* = h_{(q+1)/2 − k}(u_1², …, u_{k+1}²)`**
> **where `h_r` is the complete homogeneous symmetric polynomial of degree `r`.**
>
> **Degenerate regime, for completeness:** for odd `q ≤ 2k−1` one has `Δ ∈ 𝔟` and `indeg(𝔟:Δ) = 0`.

**GRADE: PROBADO.** `N = 1` — one formula, `k` and `q` as letters. Characteristic-free. Pencil; **no measurement enters the proof.** The only numbers appearing anywhere below are the coefficients of one hand expansion at `(k,q) = (2,9)`, done on paper.

**Corollary A (the degree at the wall).** `deg(Δ·h*) = k(k+1) + (q − 2k + 1) = q + k² − k + 1`. **This equals `q + k²` if and only if `k = 1`.**

**Corollary B (Schur basis of the symmetric part).** `Δ · s_λ(u²) = a_{λ+δ}(u²) ∈ 𝔟 ⟺ λ_1 + k ≥ (q+1)/2`, hence
```
(𝔟 : Δ) ∩ Sym  =  span_K { s_λ(u²)  :  λ_1 ≥ (q+1)/2 − k }
```
closed, parametrised by `q`, with `k` symbolic.

---

## §2 · Proof

The band to decide has width `k`. Below it nothing can happen; at its bottom degree nothing happens; at the next degree the witness fires.

### §2.0 · The trivial band (banked as B1): `(𝔟:Δ)_e = 0` for `e ≤ q − 2k − 1`.
Every exponent appearing in `Δ` is at most `2k`. So if `deg h < q − 2k`, every exponent of every monomial of `Δ·h` is `≤ deg h + 2k < q`. Since `𝔟` is a monomial ideal generated in the pure powers `u_i^q`, no monomial of `Δ·h` lies in `𝔟`, hence `Δ·h ∈ 𝔟` forces `Δ·h = 0`, hence `h = 0` (`P` is a domain).
**⟹ the undecided band is `e ∈ [q−2k, q−k−1]`, of width `k`.**

### §2.1 · Upper bound (R1): the witness. `Δ·h* ∈ 𝔟` with `deg_u h* = q + 1 − 2k`.
**Jacobi's bialternant identity** (classical, valid over `Z` and therefore over any field): for the staircase `δ = (k, k−1, …, 1, 0)` and `λ = (r, 0, …, 0)`, so that `s_λ = h_r`,
```
V(x) · h_r(x)  =  det [ x_i^{r+k} | x_i^{k−1} | … | x_i | 1 ]_{i = 1..k+1}
```
Substitute `x_i = u_i²` and take **`r = m + 1 − k = (q+1)/2 − k`** (this needs `r ≥ 0`, i.e. `q ≥ 2k−1`). The top column becomes
```
x_i^{r+k} = x_i^{m+1} = u_i^{q+1}
```
so
```
Δ · h*  =  det [ u_i^{q+1} | u_i^{2k−2} | … | u_i^2 | 1 ] .
```
Every term of the Laplace expansion along the first column carries a factor `u_i^{q+1}` for some `i`, and `u_i^{q+1} ∈ 𝔟`. **Hence `Δ·h* ∈ 𝔟`.**
`h*` is nonzero: the coefficient of `x_1^{m+1−k}` in `h_{m+1−k}` is `1`, in every characteristic.
Its degree is `deg_u h* = 2(m+1−k) = q + 1 − 2k`, and
```
q + 1 − 2k  ≤  q − k − 1   ⟺   k ≥ 2 .
```
**⟹ For every `k ≥ 2` there is a nonzero element of `(𝔟:Δ)` of degree `≤ q−k−1`, and `indeg(𝔟:Δ) ≤ q−2k+1`.** ∎

### §2.2 · Lower bound (R2): `(𝔟 : Δ)_{q−2k} = 0`, for all `k ≥ 1`, all odd `q ≥ 2k+1`, any field.
Suppose `h ≠ 0` is homogeneous of degree `q − 2k` with `Δ·h ∈ 𝔟`.

*Parity splitting.* `Δ` is **even in every `u_i`** and `𝔟` is a **monomial** ideal, so multiplication by `Δ` preserves the parity class `ε ∈ {0,1}^{k+1}` of a monomial `u^a` (`a ≡ ε mod 2`), and `𝔟`-membership is checked monomial by monomial. Therefore we may assume `h` is supported in a **single** parity class `ε`.

*The leading-monomial argument.* Fix `j ∈ {1,…,k+1}` and take the lex order with `u_j` largest. Writing `Δ = ± ∏_{i≠j}(x_j − x_i) · V(x_{≠j})`,
```
LM(Δ) = u_j^{2k} · (a monomial in the other variables, every exponent ≤ 2k−2).
```
`P` is a domain, so `LM(Δ·h) = LM(Δ)·LM(h) = LM(Δ)·u^a` with `|a| = q − 2k`. Since `Δ·h ∈ 𝔟` and `𝔟` is monomial, **every** monomial of `Δ·h` lies in `𝔟`, in particular `LM(Δ·h)`: some exponent of it is `≥ q`. For `i ≠ j` that exponent is at most
```
(2k − 2) + a_i  ≤  (2k − 2) + (q − 2k)  =  q − 2  <  q ,
```
so the exponent that reaches `q` must be the `j`-th: `2k + a_j ≥ q`, and since `|a| = q − 2k` this forces
```
a = (q − 2k)·e_j .
```
Hence `u_j^{q−2k}` occurs in `h` with nonzero coefficient. **`q − 2k` is odd** (`q` odd), so the parity class of `h` is `ε = e_j`.

*The contradiction.* This holds for **every** `j`, so `e_1 = ε = e_2`. Since `k+1 ≥ 2` these are distinct vectors — contradiction. Therefore `h = 0`. ∎

**Ingredients used, and nothing else:** `P` a domain; `𝔟` a monomial ideal; `q` odd; `q − 2k ≥ 0`. **No assumption on `char K`.**

### §2.3 · The theorem.
§2.0 gives vanishing below `q−2k`; §2.2 gives vanishing at `q−2k`; §2.1 gives a nonzero element at `q−2k+1`. Hence `indeg(𝔟:Δ) = q−2k+1`. For odd `q ≤ 2k−1`, every monomial of `Δ` already has an exponent `≥ q` (the top exponent of `Δ` is `2k ≥ q+1`), so `Δ ∈ 𝔟` and `indeg = 0`. ∎

### §2.4 · Corollary B (the Schur basis).
The same bialternant identity with general `λ` reads `Δ · s_λ(u²) = a_{λ+δ}(u²)`, whose top column is `x_i^{λ_1+k} = u_i^{2(λ_1+k)}`. That column lies in `𝔟` — and hence, by Laplace, so does the whole determinant — precisely when `2(λ_1+k) ≥ q`, i.e. (as `q` is odd) `λ_1 + k ≥ (q+1)/2`. The `s_λ(u²)` with `λ` running over partitions with at most `k+1` parts are a `K`-basis of the symmetric part of `P` in the squares, so the stated span is exactly `(𝔟:Δ) ∩ Sym`. ∎

---

## §3 · Verification

### §3.1 · Hand expansion at `(k,q) = (2,9)` (Fable, on paper; re-checked by the auditor).
Here `h* = h_3(x_1,x_2,x_3)`, `deg_u h* = 6 = q − k − 1`, and
`V = x_1²x_2 − x_1²x_3 − x_1x_2² + x_1x_3² + x_2²x_3 − x_2x_3²`. Coefficients of `V·h_3`:
```
x1^3 x2^2 x3 :  +1 −1 −1 +1 = 0        x1^4 x2^2   :  +1 −1 = 0
x1^4 x2 x3   :  +1 −1     = 0          x1^3 x2^3   :  +1 −1 = 0
x1^3 x3^3    :  −1 +1     = 0          x1^2x2^2x3^2:  +1 −1 −1 +1 +1 −1 = 0
x1^5 x2      :  +1                     (= u_1^{10} u_2^2 ∈ 𝔟)
```
**Only the six monomials `x^{σ(5,1,0)}` survive, and every one of them carries a `u_i^{10}`, hence lies in `𝔟`.** ✓

### §3.2 · Control cell `k = 1` — the criterion passes a cell where the OLD claim is true.
At `k = 1`, `deg h* = q − 1 = q − k`, which is **outside** the forbidden band `[q−2k, q−k−1]`. So the refutation of §2.1 does **not** fire at `k=1`, and the old per-sheet claim (`indeg = q−k`) survives there — as it must, since `q−2k+1 = q−1 = q−k` when `k=1`. **A death criterion that killed the cell where the target holds would be a false criterion (Ley 5); this one does not.** ✓

### §3.3 · Auditor's line-by-line check (MacGyver).
Bialternant with `λ = (r,0,…,0)`, `s_{(r)} = h_r`, `δ = (k,…,1,0)` ✓ (verified independently at `n=2`, any `r`: `(x_1−x_2)h_r = x_1^{r+1} − x_2^{r+1}`, and at `(n,r) = (3,3)` above). Top column `x_i^{(q+1)/2} = u_i^{q+1} ∈ 𝔟` ✓. Every Laplace term carries one such factor ✓. `deg_u h* = q+1−2k ≤ q−k−1 ⟺ k ≥ 2` ✓. Requirement `r ≥ 0 ⟺ q ≥ 2k−1` ✓.
Parity splitting legitimate (`Δ` even in each `u_i`, `𝔟` monomial) ✓. `LM(Δ) = u_j^{2k}·LM(V(x_{≠j}))`, other exponents `≤ 2k−2` ✓. Domain used only for `LM(Δh) = LM(Δ)LM(h)` ✓. `q` odd used only to make `q−2k` odd ✓. **Sound, characteristic-free.**

---

## §4 · The same theorem in three languages

| # | language | statement | source |
|---|---|---|---|
| `(i)` | **colon** | `indeg(𝔟:Δ) = q−2k+1`. The old "Lemma A" (`Δh ∈ 𝔟`, `deg h < q−k` ⟹ `h = 0`) holds on exactly **one** degree, `[q−2k, q−2k]`, not on the band of width `k` | §2 |
| `(ii)` | **apolar** | with `P* = Δ ∘ (u_1⋯u_{k+1})^{q−1}`: `HF_{A(P*)}(e) = C(e+k, k)` **exactly** for `e ≤ q−2k`, and `HF_{A(P*)}(q−2k+1) ≤ C(q−k+1, k) − 1` — the first drop is at `e = q−2k+1` | `APOLAR_COUPLING` (B3): `(0 :_Q Δ) = ann_{apolar}(P*)` |
| `(iii)` | **Gorenstein dual** | `P/𝔟` is Gorenstein artinian with socle degree `(k+1)(q−1)`; `(0:_{P/𝔟} Δ)_e` is dual to `(P/(𝔟,Δ))_{(k+1)(q−1)−e}`, so **top degree of `P/(𝔟,Δ)` = `kq + k − 2`** | Lemma A would have required `kq − 1` |

**All three are exact, and all three are the same computation.** *(Arithmetic checked by the scribe: `(k+1)(q−1) − (q−2k+1) = kq+k−2`, and `(k+1)(q−1) − (q−k) = kq−1`.)*

---

## §5 · Placement, and what this does **not** say

**What it closes.** The per-sheet face of the collar ceiling, for all `k`, over any field. **Nothing in the campaign had the per-sheet colon exactly**; the corpus had only the trivial band `deg h < q−2k` (`MOORE:45`).

**What it refutes.** The previous per-sheet "face A", `indeg(𝔟:Δ) = q−k`, is **FALSE for every `k ≥ 2`** — it was true at `k=1` and had been extended to all `k`. `MOORE_WALL_ONSET_v1 §4`'s "sign-coherence lemma" is false as a **per-sheet** statement for `k ≥ 2` and must be restated glued.

**What it identifies.** `MOORE §5`'s per-sheet "death families" (the raised staircases `a_{λ+δ}`) **are Schur functions in the squares** (Corollary B). The Schur combinatorics the corpus had been naming is now literal.

> ### ⛔ **WHAT IT DOES NOT SAY, AND THE DISTINCTION IS THE EXPENSIVE ONE.**
> **This is a PER-SHEET statement.** The object the conjecture needs is **GLUED**: a global annihilator class of degree `c` dies only if its restrictions `x|_J = Δ_J h_J` die on **every** sheet **with global witnesses** (`SLAP3 §0` — leaf-wise solvability does not glue). **Per-sheet death is necessary, not sufficient, so `indeg(𝔟:Δ)` is a LOWER BOUND on the glued death degree, never the glued onset.**
> **Registered failure mode: `PER-SHEET-OBJECT-BANKED-AS-GLOBAL`** (`CEMENTERIO v251`). **Binding antidote: every statement banked on a sheet carries the word "per-sheet" in its label, and every mission declares which of the two its target is.**
> **The glued statement is a different theorem with strictly stronger hypotheses** (`char ≠ 2`, Frobenius over `F_p`, all sheet matrices `B_J` invertible) and it is proved separately: **`CHAISE_LONGUE_GLUED_PURITY_THEOREM_v1`, Theorem 2** — `H_1(ℓ^{[q]};Q)_{q+e} = 0` for `0 ≤ e ≤ k²−1` with `e < q`. **Do not cite this file for that.**

**The delay, and its exact domain.** Where both apply, per-sheet death sits at `c = q+k²−k+1` and the glued onset at `c = q+k²`, a delay of `k−1` degrees; the mechanism is the triangle holonomy `−1` of `GLUED_PURITY` Theorem 3, which exists for every `k ≥ 2` and is absent at `k = 1`.
⚠️ **DOMAIN WARNING, and it is the one that has already caused an error in the live documents: this theorem requires `q ≥ 2k+1`. The cell `(3,3)` is OUTSIDE that domain (`q = 3 < 7`): there `Δ ∈ 𝔟`, the per-sheet onset is `deg Δ = k(k+1) = 12`, the delay is `0` and not `k−1 = 2`, and the coincidence `k(k+1) = q+k²` at that cell holds only because `q = k = 3`.** `(3,3)` supports neither the delay nor the `k²` law independently (`GLUED_PURITY` R7).

---

## §6 · Dependencies and honest scope

| used | status |
|---|---|
| Jacobi bialternant `a_{λ+δ} = s_λ·a_δ` | classical, over `Z`; not re-proved here (independently checked at `n=2` any `r`, and at `(n,r) = (3,3)`) |
| Laplace expansion; `K[u]` a domain and a UFD | standard |
| `q` odd | **used**, only to make `q−2k` odd in §2.2 |
| `q ≥ 2k+1` | **used**; `q ≥ 2k−1` for the witness to exist, `q ≥ 2k` for §2.2 |
| `char K` | **NOT used anywhere** |
| Frobenius, frames, `B_J` invertible, `q = p^v`, `p = 3` | **NOT used anywhere** |

**Not claimed:** any glued statement; any value of `dim H_1(ℓ^{[q]};Q)`; anything about the regime `q < 2k+1`; anything about `A_k(q) ≤ P_k(q)`.

```
§0(b)-CIERRE: the product carries k inside — ONE formula with k and q as letters. N = 1.
It does not close the theorem. It closes the per-sheet face of one of the five, exactly, and over any field.
Numbers written from memory: NONE. The only numbers in this file are the (2,9) hand expansion and
the arithmetic identities re-derived by the scribe in §4.
```

**MARCADOR: [teorema `∀k` libre de característica · testigo explícito de Jacobi · base de Schur de la parte simétrica · la vieja cara A refutada `∀k≥2` con contraejemplo a mano · celda de control `k=1` superada · dominio `q ≥ 2k+1` declarado y con su celda degenerada nombrada]. — Fable (constructor) · MacGyver (auditor) · Ulen 3 (escribano)**
