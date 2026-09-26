> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CEILING-CI STRUCTURE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CEILING_CI_STRUCTURE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CEILING-CI STRUCTURE THEOREM
## The graded structure of the ceiling complete intersection `Λ`, the exact residual count, and the unconditional relocation of the top-degree target — for every `k` and every `q`

**Chaise Longue campaign** · standalone · **v1** · 21 July 2026 · **Bertillon** (auditor, ceiling front)
*Companion to `THE_SOFA_THEOREM` (dim 4, `k=2`) and `THE_HAMMOCK_THEOREM` (dim 6, `k=3`). This is a brick, not the theorem. The Chaise Longue Conjecture remains open; the name `THE CHAISE LONGUE THEOREM` is reserved and is not used here.*

---

### Abstract

Let `K = \bar{F}_3`, `S = K[x_0,…,x_{2k+1}]`, `N = 2k+2`, `E = (e_1,e_3,…,e_{2k+1})`, `R = S/E`, `q = 3^v`, and `A = R/m^{[q]}R` with `T := (k+1)(q-1)`. We determine the complete graded structure of the *ceiling complete intersection* `Λ := R/(ℓ_1^q,…,ℓ_{k+1}^q)R` for **every `k` and every `q`, with no frame hypothesis, no separation hypothesis and no threshold in `q`**: its Hilbert series is `∏_{j=1}^{k+1}[2j-1]_z · [q]_z^{k+1}`, it is Artinian Gorenstein of socle degree `σ = (k+1)(q+k-1)`, and `dim_K Λ = (2k+1)!!\,q^{k+1}`. We then prove that the residual Frobenius generators number **exactly `k`**, not `k+1`, for every `k` and every `q` — a step recorded as used but unproven on both closed shelves — and deduce, again unconditionally, that

> **`dim_K A_T = dim_K \operatorname{ann}_Λ(g_1^q,…,g_k^q)_{k(k+1)}`,**

i.e. the top-degree target sits **exactly** at degree `k(k+1) = \operatorname{reg}(S/E)` of the annihilator, for all `k` and all `q` simultaneously. Finally we prove that the ceiling obtained from the free-module structure alone — that is, from `Λ` with the `k` residual generators discarded — is `dim_K A_T ≤ Γ_k := dim_K R_{k(k+1)}`, and that this can **never** reach `(2k+1)!!` for any `k ≥ 1`, with the exact overshoot tabulated. The `k` residual generators are not an accounting detail; they carry the entire remaining content.

---

## 1 · Setting

`K = \bar F_3` algebraically closed of characteristic `3`. `S = K[x_0,…,x_{N-1}]`, `N = 2k+2`, standard graded. `e_j` the elementary symmetric polynomials, `E = (e_1,e_3,e_5,…,e_{2k+1})` — the `k+1` odd ones. `R = S/E`. `q = 3^v`, `m^{[q]} = (x_0^q,…,x_{N-1}^q)`, `A = S/(E + m^{[q]}) = R/m^{[q]}R`, `A_k(q) = dim_K A`. `T := (k+1)(q-1)`. `[m]_z := 1 + z + ⋯ + z^{m-1}`.

Two facts are imported, both proved for all `k` elsewhere in the campaign and both used only as stated:

- **(I1) `E` is a regular sequence** of degrees `1,3,5,…,2k+1`; hence `S/E` is a complete intersection, `\operatorname{reg}(S/E) = Σ_{j=1}^{k+1}(2j-2) = k(k+1)`, `dim R = k+1`, `deg R = (2k+1)!!`. *(Odd Symmetric / Radicality; `reg` in `SLAP2`.)*
- **(I2) Recognition, degree-zero case.** For `λ ∈ K^N`, `Σ_i λ_i x_i^q ∈ E` iff all `λ_i` are equal. *(Recognition Theorem, the case `\deg λ = 0 < q`.)*

**Convention on the ground field.** Every statement below is over `K = \bar F_3`. This is not a weakening: `A_k(q) = dim_K S/(E+m^{[q]})` is a dimension, invariant under base change to the algebraic closure.

---

## 2 · The ceiling complete intersection

**Lemma 2.1 (linear system of parameters).** `R` admits a homogeneous system of parameters `ℓ_1,…,ℓ_{k+1}` consisting of **linear** forms, and `R` is then free over `C := K[ℓ_1,…,ℓ_{k+1}]` of rank `(2k+1)!!`, with free-basis degree profile
```
      g(z) := Σ_s z^{d_s} = Hilb(R)(z)·(1-z)^{k+1} = ∏_{j=1}^{k+1} [2j-1]_z ,
      g(1) = 1·3·5⋯(2k+1) = (2k+1)!! ,      deg g = k(k+1) = reg(S/E).
```

*Proof.* `R` is a complete intersection by (I1), hence Cohen–Macaulay of dimension `k+1`; `K` is infinite, so a linear homogeneous s.o.p. exists, and Cohen–Macaulayness makes `R` a free `C`-module. Its rank equals `deg R = (2k+1)!!`. The profile is forced: `Hilb(R)(z) = ∏_{j=1}^{k+1}(1-z^{2j-1})/(1-z)^{2k+2}`, so `Hilb(R)(z)(1-z)^{k+1} = ∏_{j=1}^{k+1}(1-z^{2j-1})/(1-z)^{k+1} = ∏_{j=1}^{k+1}[2j-1]_z`. Evaluating at `z=1` gives `(2k+1)!!`; the top degree is `Σ_{j=1}^{k+1}(2j-2) = k(k+1)`. ∎

**Lemma 2.2 (Frobenius absorption — no rationality hypothesis).** For **every** linear form `ℓ = Σ_j a_j x_j` with `a_j ∈ K`, `ℓ^q ∈ m^{[q]}`.

*Proof.* `q` is a power of `\operatorname{char} K = 3`, so `ℓ^q = Σ_j a_j^q x_j^q`, a `K`-linear combination of the generators `x_j^q` of `m^{[q]}`. ∎

> **Remark 2.3.** Lemma 2.2 is where a rationality hypothesis is commonly and unnecessarily imposed. One does *not* need `a_j ∈ F_q`: the `q`-th power of the coefficient stays in `K`, and `m^{[q]}` is a `K`-ideal. Consequently **no `F_q`-frame is required for anything in §2–§4**, and in particular the obstruction "no `F_3` frame exists at `k=3`" recorded on the Hammock shelf does not touch these statements.

**Definition 2.4.** Fix a linear s.o.p. `ℓ_1,…,ℓ_{k+1}` as in Lemma 2.1 and set
```
      Λ := R/(ℓ_1^q,…,ℓ_{k+1}^q)R = S/(e_1,e_3,…,e_{2k+1}, ℓ_1^q,…,ℓ_{k+1}^q).
```

**Theorem 2.5 (Ceiling-CI structure; `∀k ∀q`, unconditional).**
`Λ` is a graded Artinian complete intersection of degrees `1,3,5,…,2k+1,q,q,…,q` (`k+1` copies of `q`), hence Gorenstein, and
```
   (a)  Hilb(Λ)(z) = ∏_{j=1}^{k+1}[2j-1]_z · [q]_z^{k+1} ;
   (b)  socle degree  σ = k(k+1) + (k+1)(q-1) = (k+1)(q+k-1) ;
   (c)  dim_K Λ      = (2k+1)!! · q^{k+1} ;
   (d)  Λ is free over Λ_0 := K[ℓ_1,…,ℓ_{k+1}]/(ℓ_i^q) of rank (2k+1)!!,
        with the same degree profile g(z); Λ_0 is Gorenstein with socle degree exactly T.
```

*Proof.* By Lemma 2.1 the `ℓ_i` are a regular sequence on `R`, hence so are the `ℓ_i^q`; together with (I1) this exhibits `Λ` as a complete intersection of the stated degrees, so `Λ` is Artinian Gorenstein. (a): `Hilb(Λ) = Hilb(R)·(1-z^q)^{k+1} = ∏_j(1-z^{2j-1})(1-z^q)^{k+1}/(1-z)^{2k+2} = ∏_j[2j-1]_z·[q]_z^{k+1}`. (b): the socle degree of a graded Artinian complete intersection is `Σ(\deg - 1) = Σ_{j=1}^{k+1}(2j-2) + (k+1)(q-1)`. (c): evaluate (a) at `z=1`. (d): base-change the free `C`-module of Lemma 2.1 along `C ↠ Λ_0 = C/(ℓ_i^q)`; `Λ_0` is a tensor product of `k+1` copies of `K[t]/(t^q)`, Gorenstein with socle degree `(k+1)(q-1) = T`. ∎

**Verification 2.6 (against both closed shelves).** Specialising Theorem 2.5:
`k=2`: `σ = 3(q+1) = 3q+3`, `dim_K Λ = 15q^3` (`v=1`: `405`) — matching the sealed `k=2` statement verbatim.
`k=3`: `σ = 4(q+2) = 4q+8` — matching the `k=3` statement verbatim.
Checked at `(k,q) = (2,3), (2,9), (3,3), (3,9), (3,27)`: **5/5 byte-exact**; closed forms (b),(c) re-verified at 8 cells `k∈{1,2,3,4}, q∈{3,9}`: **8/8**.

---

## 3 · The residual count: exactly `k`

**Theorem 3.1 (Residual Frobenius generators; `∀k ∀q`, unconditional).**
Let `V := S_1` and let `V^{[q]} := \operatorname{span}_K\{x_0^q,…,x_{N-1}^q\}`. Then:
```
   (i)   dim_K (V^{[q]} + E)/E = N - 1 = 2k+1 ;
   (ii)  the k+1 elements ℓ_1^q,…,ℓ_{k+1}^q are K-independent modulo E ;
   (iii) there exist linear forms g_1,…,g_k ∈ V such that
            {ℓ_1^q,…,ℓ_{k+1}^q, g_1^q,…,g_k^q}   is a K-basis of (V^{[q]}+E)/E ;
   (iv)  consequently   Λ/(g_1^q,…,g_k^q)Λ = R/m^{[q]}R = A .
```
The number of residual generators is therefore **exactly `k`**, for every `k` and every `q`.

*Proof.* (i) The kernel of `K^N → S_q/E_q`, `λ ↦ Σλ_i x_i^q`, is by (I2) the line `K·(1,…,1)`, whose image is `e_1^q` and `e_1 ∈ E`. Hence the image has dimension `N-1 = 2k+1`.

(ii) Write `ℓ_i = Σ_j a_{ij}x_j`, so `ℓ_i^q = Σ_j a_{ij}^q x_j^q`. Suppose `Σ_i c_i ℓ_i^q ∈ E` with `c_i ∈ K`. By (I2) the coefficient vector `(Σ_i c_i a_{ij}^q)_j` is constant in `j`, say `= t`; that is, `Σ_i c_i\,(a_{ij}^q)_j = t·(1,…,1)`. The vectors `(a_{ij}^q)_j` are the coefficient vectors of the linear forms `ℓ_i^{(q)} := Σ_j a_{ij}^q x_j`, images of the `ℓ_i` under the (bijective) Frobenius twist of coefficients; since `ℓ_1,…,ℓ_{k+1}` are a s.o.p. for `R = S/E` and `e_1 ∈ E`, they are independent modulo `e_1`, hence so are their coefficient-twists modulo `(1,…,1)`. Therefore all `c_i = 0`.

(iii) `K` is algebraically closed of characteristic `3`, so every `c ∈ K` has a unique `q`-th root. Hence **every** element of `V^{[q]}` is the `q`-th power of a linear form: `Σ_j c_j x_j^q = (Σ_j c_j^{1/q} x_j)^q`. Complete the `k+1` independent classes of (ii) to a basis of the `(2k+1)`-dimensional space of (i) by `k` further elements of `V^{[q]}`, and take `q`-th roots.

(iv) `m^{[q]}R` is generated by `V^{[q]}`, which by (iii) is spanned modulo `E` by the `ℓ_i^q` and the `g_j^q`. Quotienting `R` first by the `ℓ_i^q` (giving `Λ`) and then by the `g_j^q` therefore yields `R/m^{[q]}R = A`. ∎

> **Scope note 3.2.** Theorem 3.1 requires **no** transversality, **no** separation (SEP) condition and **no** lower bound on `q`. Only (I1), (I2) and Lemma 2.1 are used, all of which hold for every `k` and every `q`. The count "`k`, not `k+1`" was previously recorded as a correction without proof; this supplies the proof for all `k`.

---

## 4 · The top-degree target, relocated

**Corollary 4.1 (Relocation; `∀k ∀q`, unconditional).** With `σ = (k+1)(q+k-1)` from Theorem 2.5(b) and `T = (k+1)(q-1)`:
```
      σ - T = k(k+1)  identically in q,
```
and, `Λ` being Artinian Gorenstein with socle in degree `σ`,
```
      dim_K A_d = dim_K ann_Λ(g_1^q,…,g_k^q)_{σ-d}   for every d,
```
in particular
> **`dim_K A_T = dim_K \operatorname{ann}_Λ(g_1^q,…,g_k^q)_{k(k+1)}` .**

*Proof.* `σ - T = k(k+1) + (k+1)(q-1) - (k+1)(q-1) = k(k+1)`, with no residual `q`. For a graded Artinian Gorenstein ring `Λ` with socle degree `σ` and any homogeneous ideal `I`, the socle pairing gives `\operatorname{ann}_Λ(I) ≅ (Λ/I)^∨` with `dim \operatorname{ann}_Λ(I)_c = dim(Λ/I)_{σ-c}`. Take `I = (g_1^q,…,g_k^q)` and apply Theorem 3.1(iv). ∎

**Remark 4.2 (what this buys).** The target degree `k(k+1)` is `\operatorname{reg}(S/E)` and is **free of `q`**. Combined with a vanishing statement of the form `\operatorname{ann}_Λ(g^{[q]})_c = 0` for `c < \min(q,k(k+1))`, Corollary 4.1 says that the top-degree target is precisely the **first possibly-nonzero graded piece** of the annihilator. Note however that the two halves have different scopes: Corollary 4.1 is unconditional, whereas vanishing statements of that form carry a frame hypothesis; see §6.

---

## 5 · The free-module ceiling, and exactly why it is not enough

**Proposition 5.1 (Free-module ceiling; `∀k ∀q`).** For every `d`,
```
      dim_K A_d ≤ [z^d]\big( ∏_{j=1}^{k+1}[2j-1]_z · [q]_z^{k+1} \big) = dim_K Λ_d ,
```
and at the top degree, uniformly in `q`,
```
      dim_K A_T ≤ Γ_k := Σ_m g_m \binom{m+k}{k} = dim_K (S/E)_{k(k+1)} = [z^{k(k+1)}]\,Hilb(S/E)(z).
```

*Proof.* `A` is a quotient of `Λ` (Theorem 3.1(iv)), so `dim A_d ≤ dim Λ_d`, and `Hilb(Λ)` is Theorem 2.5(a). At `d = T`: by the symmetry `[z^{T-m}][q]_z^{k+1} = [z^m][q]_z^{k+1}` and the truncation bound `[z^m][q]_z^{k+1} ≤ \binom{m+k}{k}`, one gets `dim Λ_T ≤ Σ_m g_m\binom{m+k}{k}`, uniformly in `q`. Since `g(z)` is palindromic of top degree `k(k+1)`, `Σ_m g_m\binom{m+k}{k} = [z^{k(k+1)}]\,g(z)/(1-z)^{k+1} = [z^{k(k+1)}]\,Hilb(S/E)(z)`. ∎

**Theorem 5.2 (Structural insufficiency; `∀k ≥ 1`, every `q`).** `Γ_k > (2k+1)!!` strictly for every `k ≥ 1`, and the ratio is unbounded. Hence **no argument that bounds `dim A_T` through `Λ` alone — that is, with the `k` residual generators discarded — can prove `dim A_T ≤ (2k+1)!!` for any `k ≥ 1`, at any `q`.**

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 10, informe 138) — la prueba de 5.2 va en la dirección equivocada para la segunda frase.** `Γ_k` es una COTA SUPERIOR de `dim Λ_T` (Prop. 5.1); que `Γ_k > (2k+1)!!` no dice nada de si `dim Λ_T` supera `(2k+1)!!`. Lo que hace falta es `dim Λ_T > (2k+1)!!`. **Reparación de una línea para `q ≥ k+1`:** entonces `k(k+1) ≤ T`, todo `c_m := [z^m][q]_z^{k+1} ≥ 1` en el soporte de `g`, y `c_1 = k+1 ≥ 2` con `g_1 = k ≥ 1`, luego `dim Λ_T ≥ (2k+1)!! + k² > (2k+1)!!`. **Para `q < k+1` (el SUB-SUELO, la región abierta a `q = 3`) los `c_m` con `m > T` se anulan y la desigualdad queda MEDIDA, no probada:** `dim Λ_T(q=3) = 6, 71, 887, 11 208, 142 691, 1 827 956, 23 541 130, 304 537 231` para `k = 1..8`, todos `> (2k+1)!!`. Los `Γ_k` de la tabla, reproducidos `8/8`. El enunciado se sostiene; la prueba escrita no lo alcanza en el sub-suelo.


*Proof.* `Σ_m g_m = g(1) = (2k+1)!!` and `\binom{m+k}{k} ≥ 1` with strict inequality for `m ≥ 1`; `g` has positive coefficients up to `m = k(k+1) ≥ 2`, so `Γ_k > (2k+1)!!`. Explicitly (verified 8/8 against `dim_K(S/E)_{k(k+1)}`):

| `k` | `(2k+1)!!` | `Γ_k` | `Γ_k/(2k+1)!!` |
|---|---|---|---|
| 1 | 3 | 6 | 2.00 |
| 2 | 15 | 170 | 11.33 |
| 3 | 105 | 11 620 | 110.67 |
| 4 | 945 | 1 454 649 | 1 539.31 |
| 5 | 10 395 | 289 652 517 | 27 864.60 |
| 6 | 135 135 | 84 070 953 252 | 622 125.68 |
| 7 | 2 027 025 | 33 510 653 833 800 | 16 531 939.09 |
| 8 | 34 459 425 | 17 566 276 383 934 707 | 509 766 961.69 |
∎

> **Reading of Theorem 5.2.** The overshoot is `q`-free and **grows superexponentially**. It is the exact price of discarding the `k` residual generators of Theorem 3.1. Those `k` generators are not a detail of the bookkeeping: they carry the whole remaining content of the problem.

---

## 6 · Scope — what is claimed and what is **not**

**Claimed, for every `k ≥ 1` and every `q = 3^v`, over `K = \bar F_3`, with no threshold and no frame hypothesis:**
Theorem 2.5 (a)–(d); Theorem 3.1 (i)–(iv); Corollary 4.1; Proposition 5.1; Theorem 5.2.

**NOT claimed:**

1. **`dim_K A_T ≤ (2k+1)!!` is NOT proved here.** Corollary 4.1 relocates it to `\operatorname{ann}_Λ(g^{[q]})_{k(k+1)}`; it does not bound it. Theorem 5.2 proves that the machinery of §2 alone never will.
2. **No vanishing statement is proved here.** Statements of the form `α_c = 0` for `c < \min(q,k(k+1))` are not established in this document and are not used in §2–§5.
3. **No claim about `A_k(q) = P_k(q)`,** in any range.
4. **No claim that the `ℓ_i` can be chosen over `F_3` or `F_q`.** They are chosen over `K`, which is all Lemma 2.2 requires. Where a *separating* (SEP) frame over a finite field is needed for other purposes, that is a genuinely different and stronger hypothesis, and the obstruction at `k=3` over `F_3` recorded elsewhere is untouched by, and does not touch, this document.
5. **No claim of novelty for the objects.** The ring `Λ` and the duality `A_d = dim \operatorname{ann}_Λ(g^{[q]})_{σ-d}` appear in the closed `k=2` and `k=3` results with a frame hypothesis attached. What is new here is: the graded structure of `Λ` in closed form for all `k`; the proof that the residual count is `k`; and the removal of the frame hypothesis from both, hence from the relocation.
6. **The residual generators `g_j` are not canonical.** Theorem 3.1(iii) produces them from a choice of complement; nothing below depends on the choice, but no canonical choice is asserted.

---

## 7 · Verification record

| gate | result |
|---|---|
| `Λ` socle degree vs `k=2` shelf (`3q+3`) at `q=3,9` | **PASS 2/2** |
| `Λ` socle degree vs `k=3` shelf (`4q+8`) at `q=3,9,27` | **PASS 3/3** |
| `dim_K Λ` vs `k=2` shelf (`15q^3`, `v=1`: `405`) | **PASS 2/2** |
| closed forms (b),(c) at `k∈{1,2,3,4}`, `q∈{3,9}` | **PASS 8/8** |
| `σ - T = k(k+1)` at `k=1..5`, `q∈{3,9,27}` | **PASS 15/15** |
| `Γ_k = dim_K(S/E)_{k(k+1)}` for `k=1..8` | **PASS 8/8** |
| Prop 5.1 dominates full `HF(A)`, `(k,q) = (1,3),(2,3),(3,3),(1,9)` | **PASS 42/42 degrees** |
| independent engine: `dim A_T(q=3)`, `k=1,2,3` = `3, 15, 91` | **PASS 3/3 vs archive** |
| independent engine: `HF(A)(2,3) = [1,5,15,29,40,36,15]` | **PASS byte-exact vs archive** |

Engine: exact linear algebra over `F_3` on the monomial box `{0,…,q-1}^N`, computing `\operatorname{ann}_B(E·B)_T` as `\bigcap_{j\ \text{odd}}\ker U_j`; Hilbert-series arithmetic in exact integers. `Λ` structure derived by pencil (§2), verified numerically only.

---

## 8 · Provenance

Imports: (I1) the regular-sequence/complete-intersection property of `E` and `\operatorname{reg}(S/E) = k(k+1)`; (I2) the degree-zero case of the Recognition Theorem; the free-rank statement underlying Lemma 2.1. All three are campaign results proved for all `k` and are used exactly as stated, with no extension.

Cross-shelf verification data for §2 (`3q+3`, `15q^3`, `405`, `4q+8`) were supplied verbatim from the closed `k=2` and `k=3` documents and are used here only as gates against an independently derived formula.

Superseded by nothing. Supersedes nothing. **Pending P0.**

**— Bertillon.**
