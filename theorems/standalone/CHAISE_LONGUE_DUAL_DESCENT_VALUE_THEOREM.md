> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_DUAL_DESCENT_VALUE_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DUAL_DESCENT_VALUE_THEOREM.md
>
> **Status, as written in the document:** Grade: PROVED ∀k (closes the descent VALUE `r_2 = A_{k−1}(q)`; with iteration, `r_{2j}=A_{k−j}(q)`). Char ≠ 2; over `F_3`, `q` odd (free exponent). Gated `(1,3),(1,5),(2,3),(2,5)`.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_DUAL_DESCENT_VALUE_THEOREM_v1
### Standalone theorem · Constructor: Lacassagne · campaign Chaise Longue · GAP 3 (Matlis-dual descent, STEP 1b)
### Grade: **PROVED ∀k** (closes the descent VALUE `r_2 = A_{k−1}(q)`; with iteration, `r_{2j}=A_{k−j}(q)`). Char ≠ 2; over `F_3`, `q` odd (free exponent). Gated `(1,3),(1,5),(2,3),(2,5)`.

> 🔴 **NOTA `2026-09-16` (Grepy, turno 16, informe 144) — `r_{2j} = A_{k−j}` es FALSO desde `r_4`** (`21≠19`, `153≠141`, `1179≠1107`; informe 119; `CATÁLOGO v393:4368`). Sólo `r_2 = A_{k−1}` está probado.

### ⚠️ Does NOT close GAP 3: STEP 2 (the sum `M=Σ_a ann_M(ℓ_a)`) stays open, and its naive mechanism fails (§5). `G` stays 3.

---

## 0. What this closes

STEP 1a (`DUAL_PAIR_COLLAPSE_LEMMA_v1`, PROVED ∀k) reduced the pair-annihilator to a box-ring dimension:
`dim(M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b)) = dim(B''/Ê·B'')`, with the `(1−zτ)²`-twisted generators
`Ê_j = e_j + z e_{j−1} + z² e_{j−2}`, `z = x_{n−1}` the smallest variable. STEP 1b is: **prove
`dim(B''/Ê·B'') = A_{k−1}(q)` ∀k.** This theorem does it — the twist is undone by the sign-flip `z ↦ −z`.

Notation: `B'' = S''/m^{[q]}`, `S'' = F_3[w_0,…,w_{2k−2}, z]` (the `2k = 2(k−1)+2` box-ring variables,
`z` smallest in grevlex). `a_m` = elementary symmetric of degree `m` in the `2k−1` variables `≠ z`.
`e_m` = elementary symmetric of degree `m` in all `2k` variables. `E_{k−1} = (e_1,e_3,…,e_{2k−1})`.

---

## 1. Lemma A — the generators are `z`-linear (∀k)

`e_j = a_j + z·a_{j−1}`. **Proof:** every variable occurs to degree `≤ 1` in an elementary symmetric,
so `z` occurs to degree `≤ 1`; splitting `e_j` by whether the `z`-slot is used gives the `z`-free part
`a_j` and the coefficient of `z`, which is the elementary symmetric of degree `j−1` in the other `2k−1`
variables, `= a_{j−1}`. ∎

## 2. Lemma B — the twist is the sign-flip, up to a unitriangular tail (∀k, `F_3`)

Let `σ` be the linear automorphism `z ↦ −z`, `w_i ↦ w_i`. Write `ẽ_j := σ(e_j) = a_j − z a_{j−1}`
(Lemma A). Then **over `F_3`**
### `Ê_j = ẽ_j − z²·ẽ_{j−2}` ###
for every odd `j` (with `ẽ_m := 0` for `m ≤ 0`). **Proof:** by Lemma A,
`Ê_j = (a_j+z a_{j−1}) + z(a_{j−1}+z a_{j−2}) + z²(a_{j−2}+z a_{j−3})
     = a_j + 2z a_{j−1} + 2z² a_{j−2} + z³ a_{j−3}
     = a_j − z a_{j−1} − z² a_{j−2} + z³ a_{j−3}` (using `2 = −1` in `F_3`);
and `ẽ_j − z² ẽ_{j−2} = (a_j − z a_{j−1}) − z²(a_{j−2} − z a_{j−3})` gives the same. ∎
*(This is the only place char 3 is used — the `2 = −1` that turns the truck's tilt into a clean sign.)*

## 3. Corollary — `(Ê) = σ(E_{k−1})` as ideals (∀k)

From Lemma B, `Ê_j = ẽ_j − z² ẽ_{j−2} ∈ (ẽ_1,…,ẽ_{2k−1}) = σ(E_{k−1})` (the top `j = 2k+1` has
`ẽ_{2k+1}=0`, so `Ê_{2k+1} = −z² ẽ_{2k−1}`, still inside). Conversely, telescoping,
`ẽ_j = Ê_j + z² ẽ_{j−2} = Σ_{i≥0} z^{2i} Ê_{j−2i} ∈ (Ê)`. Hence **`(Ê) = σ(E_{k−1})`.** ∎

## 4. Theorem — STEP 1b, `dim(B''/Ê·B'') = A_{k−1}(q)` (∀k)

`σ` preserves the box: `q` is odd, so `σ(z^q) = −z^q` generates the same ideal, and `σ(w_i^q)=w_i^q`;
thus `σ(m^{[q]}) = m^{[q]}`. With §3, `Ê + m^{[q]} = σ(E_{k−1}) + m^{[q]} = σ(E_{k−1} + m^{[q]})`. Therefore
`σ` induces a ring isomorphism
### `S''/(E_{k−1}+m^{[q]}) ≅ S''/(Ê+m^{[q]})`, so `dim(B''/Ê·B'') = A_{k−1}(q)` ∀k. ###
Moreover `σ` scales the single variable `z` by `−1`, fixing every monomial up to sign, so it fixes every
monomial ideal; hence **`in(Ê+m^{[q]}) = in(E_{k−1}+m^{[q]})`** — the equal Gröbner staircase measured last
turn is not a coincidence but this `σ`-conjugacy. ∎

**Corollary (the descent value).** With STEP 1a, `r_2 := dim(M ∩ ann_M(ℓ_a) ∩ ann_M(ℓ_b)) = A_{k−1}(q)`
∀k. One pair-collapse sends `M_k` to `ann_{B''}(Ê·B'') = σ(M_{k−1}) ≅ M_{k−1}`, a genuine level-`(k−1)`
module; iterating `j` collapses gives **`r_{2j} = A_{k−j}(q)` ∀k**, matching the measured intersection

> 🔴 **NOTA `2026-09-16` (Grepy, turno 16, informe 144) — `r_{2j} = A_{k−j}` es FALSO desde `r_4`** (`21≠19`, `153≠141`, `1179≠1107`; informe 119; `CATÁLOGO v393:4368`). Sólo `r_2 = A_{k−1}` está probado.

profile (`k=2,q=3`: `141,57,19,7,3,1`, even sub-sequence `141,19,3 = A_2,A_1,A_0`).

---

## 5. Scope — honest (`G` stays 3)

- **Reconciliation.** The "`≅ M_{k−1}`" candidate killed last turn as a **subspace equality**
  (`ann_{B''}(Ê) ≠ M_{k−1}`, union-rank `5/9/31`) is correct as stated; this theorem shows the two are
  **isomorphic via `σ`** (`ann_{B''}(Ê) = σ(M_{k−1})`), which is all the *dimension* needs. Both stand.
- **Does NOT close STEP 2**, hence not GAP 3. STEP 2 asks `M = Σ_a ann_M(ℓ_a)` (dim of the SUM). Its
  proposed mechanism — distributive arrangement ⟹ Boolean inclusion–exclusion `Σ_s(−1)^{s+1}C(2k+1,s)r_s
  = dim M` — **FAILS at `k=2`:** it gives `151`, but `dim M = 141` (matches at `k=1`: `19`, `61`). So the
  `{ann_M(ℓ_a)}` arrangement is **not distributive**; STEP 2 needs a different argument.
- `A ≤ P`: never used (this is a value computation, not a bound). `Q`: never (F_3). `ρ`/restriction of `M`:
  never (all maps dual/annihilator side). New `k` as product: none (`q`-controls only).

**Gate (control):** `(Ê)+m^{[q]} = σ(E_{k−1})+m^{[q]}` byte-exact at `(1,3),(1,5),(2,3),(2,5)`
(dims `3,5,19,61 = A_{k−1}(q)`); identity of §2 verified symbolically mod 3 at `k=1,2,3`.
**Engines:** `step1b_signflip_lacassagne.py`, `step1b_initial_ideal_lacassagne.py`.
**Depends on:** `DUAL_PAIR_COLLAPSE_LEMMA_v1`, `TWIST_LEADING_TERM_LEMMA_v1` (superseded as the closure —
its residual, the completion-matching, is now explained by `σ`-conjugacy), `ODD_ELEMENTARY_CI_THEOREM`.
**Feeds:** GAP 3 STEP 2 (the only remaining piece of the Matlis-dual route).

— Lacassagne
