> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-19
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CASING IMPOSSIBILITY THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CASING_IMPOSSIBILITY_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CASING IMPOSSIBILITY THEOREM

### No monomial degeneration computes the Fermat matching arrangement

**Rafael Amichis Luengo** · Madrid · 19 July 2026
*Chaise Longue campaign · standalone theorem document · **version 2***

---

## Abstract

Let `K` be a field of characteristic `3`, let `q = 3^v`, and let `E ⊂ S = K[x_0,…,x_{2k+1}]` be the ideal of the arrangement of the `(2k+1)!!` maximal isotropic coordinate matching subspaces, so that `E = (e_1, e_3, …, e_{2k+1})` is a complete intersection. Write `A_k(q) = dim_K S/(E + \mathfrak m^{[q]})` and `P_k(q) = |⋃_J L_J(\mathbb F_q)|`.

A natural strategy for bounding `A_k(q)` from above is *monomial degeneration*: replace `E` by an initial ideal, after which the quotient becomes a pure count of standard monomials inside the Frobenius box. Since the box `\mathfrak m^{[q]}` is invariant under `GL_n(K)` for every `K ⊇ \mathbb F_3`, one is free to optimise over all linear changes of coordinates, all monomial orders and all field extensions.

**We prove that this strategy cannot succeed for `k ≥ 2`.** For every monomial degeneration `M` of `E`, over every field and every monomial order,

> **`Casing_M(q) := dim_K S/(M + \mathfrak m^{[q]}) > P_k(q)`.**

The bound is therefore never tight in dimension `2k ≥ 4`. The obstruction is exhibited, not merely excluded: it is the odd power sum `p_{q+2}`.

For `k = 1` the inequality degenerates to an equality and one orbit survives — precisely the orbit realised by the good basis of the closed `k=1` column. The theorem does not bite where the method works.

---

## 1. Setting and notation

**1.1.** `K` is a field with `char K = 3`, `q = 3^v` for some `v ≥ 1`, and `N = 2k+2`. Write `S = K[x_0, …, x_{2k+1}]` with the standard grading, and `\mathfrak m^{[q]} = (x_0^q, …, x_{2k+1}^q)` for the *Frobenius box*.

**1.2.** For a perfect matching `J` of `{0,…,2k+1}` let

`L_J = \{ x_a + x_b = 0 : (a,b) ∈ J \} ⊂ \mathbb A^N`,

a linear subspace of dimension `k+1`. There are `(2k+1)!!` such subspaces. Write `I_J` for the (linear, hence prime) ideal of `L_J`.

**1.3.** Let `e_r` denote the elementary symmetric polynomial of degree `r` and set `E = (e_1, e_3, …, e_{2k+1})`.

> **Fact 1.3.1 (Odd Symmetric / Radicality).** `⋂_J I_J = E`, and `E` is a complete intersection of degrees `1, 3, 5, …, 2k+1`. In particular `E` is radical and `\dim S/E = k+1`, with Bézout number `1·3·5⋯(2k+1) = (2k+1)!!` equal to the number of sheets.

*(This is the first pillar of the campaign; it is used here as an input and is not reproved.)*

**1.4.** Set `A_k(q) = \dim_K S/(E + \mathfrak m^{[q]})` and `P_k(q) = |⋃_J L_J(\mathbb F_q)|`. The Degtyarev–Shimada conjecture, in its operational form, asserts `A_k(q) = P_k(q)`.

> **Proposition 1.4.1 (Floor).** `A_k(q) ≥ P_k(q)` for all `k` and all `q`.

*Proof (elementary and self-contained; no characteristic-zero input, no imported identification).* Let `F = K[x_0,…,x_{2k+1}]/(x_i^q - x_i)`, the algebra of `K`-valued functions on `\mathbb A^N(\mathbb F_q)` when `K = \mathbb F_q`, filtered by degree, and let `J ⊂ F` be the vanishing ideal of the finite set `⋃_J L_J(\mathbb F_q)`, so that `\dim_K F/J = P_k(q)`.

Passing to the associated graded ring for the degree filtration gives `\mathrm{gr}(F) = S/\mathfrak m^{[q]} = B`, since the initial form of `x_i^q - x_i` is `x_i^q`. We claim `E + \mathfrak m^{[q]} ⊆ \mathrm{gr}(J)`:

- each `e_r` is homogeneous and vanishes identically on the arrangement, hence on its `\mathbb F_q`-points, so `e_r ∈ J` and its initial form is `e_r` itself;
- `x_i^q - x_i ∈ J` trivially (it vanishes on all of `\mathbb A^N(\mathbb F_q)`), and its initial form is `x_i^q`.

Taking associated graded modules preserves dimension, so `\dim_K B/\mathrm{gr}(J) = \dim_K F/J = P_k(q)`. From `E + \mathfrak m^{[q]} ⊆ \mathrm{gr}(J)` we get a surjection `B/(E+\mathfrak m^{[q]}) ↠ B/\mathrm{gr}(J)`, whence

`A_k(q) = \dim_K B/(E+\mathfrak m^{[q]}) ≥ \dim_K B/\mathrm{gr}(J) = P_k(q)`. ∎

*(This replaces the campaign's earlier derivation via integral presentation and rank semicontinuity, which imported the characteristic-zero identification of `P` from [DS]. The present argument uses only Fact 1.3.1.)*

---

## 2. The reduction, and the object of study

**2.1.** Since `e_1 ∈ E`, we may eliminate `x_0 = -(x_1 + ⋯ + x_{2k+1})`. Let `n = 2k+1`, `R = K[x_1,…,x_n]`, let `\bar E ⊂ R` be the image of `E`, and let `\mathfrak b = (x_1^q, …, x_n^q)`.

**Lemma 2.2.** `\mathfrak b` is the image of `\mathfrak m^{[q]}` in `R`, and `A_k(q) = \dim_K R/(\bar E + \mathfrak b)`.

*Proof.* The image of `x_0^q` is `\bigl(-(x_1+⋯+x_n)\bigr)^q = -(x_1^q + ⋯ + x_n^q)` by the freshman's dream in characteristic `3`; this lies in `\mathfrak b`, so the extra generator is redundant. ∎

**2.3.** `\bar E` is a complete intersection of degrees `3, 5, …, 2k+1` in `n = 2k+1` variables, and is radical (a linear form belonging to a radical ideal may be divided out without destroying radicality).

**Definition 2.4 (monomial degeneration).** A *monomial degeneration* of `\bar E` is an ideal `M = \mathrm{in}_<(g·\bar E)` for some `g ∈ GL_n(K')`, `K' ⊇ K`, and some monomial order `<`. Set

`Casing_M(q) = \dim_K R/(M + \mathfrak b)`.

**Lemma 2.5 (the casing is an upper bound, unconditionally).** `A_k(q) ≤ Casing_M(q)` for every monomial degeneration `M`, every field extension and every order.

*Proof.* The box is `GL`-stable: if `y_i = \sum_j a_{ij} x_j` with `(a_{ij})` invertible over `K'`, then `y_i^q = \sum_j a_{ij}^q x_j^q`, and `(a_{ij}^q)` is invertible because `\det(a^q) = (\det a)^q ≠ 0`; hence `(y_1^q,…,y_n^q) = (x_1^q,…,x_n^q)`. Thus `g·\mathfrak b = \mathfrak b` and `\dim R/(g\bar E + \mathfrak b) = A_k(q)`. Since `\mathfrak b` is monomial, `\mathrm{in}(g\bar E + \mathfrak b) ⊇ \mathrm{in}(g\bar E) + \mathfrak b = M + \mathfrak b`, and passing to initial ideals preserves the Hilbert function of the quotient. Dimensions of quotients are reversed by inclusions of ideals, whence the claim. ∎

---

## 3. The slack identity

The following elementary identity is the engine of the whole proof: it removes the unknown quantity `A_d` from the bookkeeping.

For a degree `d`, write `r_d = \dim_K R_d`, `\beta_d = \dim_K (\mathfrak b)_d`, and `\mathrm{box}_d = r_d - \beta_d` for the number of monomials of degree `d` all of whose exponents are `< q`. Write `A_d`, `Casing_{M,d}` for the graded pieces.

**Definition 3.1.** Suppose `Casing_{M,d} = A_d`. The *slack* in degree `d` is the number of monomials of `M_d` lying outside the box:

`σ_d := \dim M_d - \#\{\text{box monomials in } M_d\}`.

**Theorem 3.2 (slack identity).** If `Casing_{M,d} = A_d`, then

> **`σ_d = \dim_K (\bar E ∩ \mathfrak b)_d`.**

In particular `σ_d` does not depend on `M`, on the order, or on the field, and is independent of any measured value of `A_d`.

*Proof.* By Macaulay, `\dim M_d = \dim \bar E_d`. The hypothesis gives `\#\{\text{box monomials in } M_d\} = \mathrm{box}_d - A_d`, so `σ_d = \dim \bar E_d - \mathrm{box}_d + A_d`. Now

`A_d = r_d - \dim(\bar E + \mathfrak b)_d = r_d - \dim \bar E_d - \beta_d + \dim(\bar E ∩ \mathfrak b)_d`,

and `\mathrm{box}_d = r_d - \beta_d`. Substituting,

`σ_d = \dim \bar E_d - (r_d - \beta_d) + r_d - \dim \bar E_d - \beta_d + \dim(\bar E ∩ \mathfrak b)_d = \dim(\bar E ∩ \mathfrak b)_d`. ∎

**Notation 3.3.** Write `\mathrm{rel}(j) := \dim_K (\bar E ∩ \mathfrak b)_{q+j}`.

---

## 4. The forced cubic and its unavoidable multiples

**Lemma 4.1.** Every monomial degeneration `M` of `\bar E` contains exactly one monomial of degree `3`.

*Proof.* `\dim M_3 = \dim \bar E_3`. Since `\bar E` is a complete intersection of degrees `3, 5, …`, its degree-`3` piece is spanned by the single cubic generator; hence `\dim \bar E_3 = 1`. ∎

Call this monomial `μ`. Up to permutation of the variables — and every quantity below is permutation invariant — `μ` lies in one of three orbits: `x_i^3`, `x_i^2 x_j`, or `x_i x_j x_l` with distinct indices.

**Lemma 4.2 (forced non-box multiples).** Since `M` is an ideal, every multiple of `μ` lies in `M`. The number of such multiples of degree `d` lying outside the box is:

| orbit of `μ` | degree `d` | non-box multiples | count |
|---|---|---|---|
| `x_i^3` | `q` | `x_i^q` | **1** |
| `x_i^2 x_j` | `q+1` | `x_i^q x_j` | **1** |
| `x_i x_j x_l` | `q+2` | `x_i^q x_j x_l`, `x_i x_j^q x_l`, `x_i x_j x_l^q` | **3** |

*Proof.* A multiple `μ·m` of degree `d` lies outside the box iff some exponent reaches `q`. For `q ≥ 3` no monomial of degree `≤ q+2` can have two exponents `≥ q`, since that would force degree `≥ 2q > q+2`. It therefore suffices to count, for each variable `x_s`, the multipliers `m` of degree `d - 3` with `μ_s + m_s ≥ q`.

*Orbit `x_i^3` at `d = q`:* `\deg m = q-3` and `3 + m_i ≥ q` forces `m_i ≥ q-3`, hence `m = x_i^{q-3}`; no other variable can reach `q`. Count `1`.

*Orbit `x_i^2 x_j` at `d = q+1`:* `\deg m = q-2`. For `x_i`: `m_i ≥ q-2`, so `m = x_i^{q-2}`, giving `x_i^q x_j`. For `x_j`: `m_j ≥ q-1 > q-2`, impossible. Count `1`.

*Orbit `x_i x_j x_l` at `d = q+2`:* `\deg m = q-1`. For each of the three variables, `m_s ≥ q-1` forces `m = x_s^{q-1}`, one multiplier each; the three resulting monomials are distinct. Count `3`. ∎

---

## 5. The three relation counts

**Lemma 5.1 `(\mathrm{rel}(0) = 0`, all `k`, all `q`).** `(\bar E ∩ \mathfrak b)_q = 0`.

*Proof.* A degree-`q` element of `\mathfrak b` has the form `\sum_i c_i x_i^q`. After the faithfully flat base change to `K^{1/q}` (which changes no dimension), write `c_i = d_i^q`; then, by the freshman's dream,

`\sum_i c_i x_i^q = \bigl(\sum_i d_i x_i\bigr)^q = \ell^q` with `\ell` linear.

Suppose `\ell^q ∈ \bar E`. Since `\bar E` is radical (2.3), `\ell ∈ \bar E`, so `\ell` vanishes on the whole arrangement. Any two distinct sheets already span `\mathbb A^n`, so `\ell = 0`, and hence the original element is `0`. ∎

**Lemma 5.2 `(\mathrm{rel}(1) = 0`, all `k`, all `q`).** `(\bar E ∩ \mathfrak b)_{q+1} = 0`.

*Proof.* A degree-`(q+1)` element of `\mathfrak b` has the form `F = \sum_i x_i^q \ell_i` with `\ell_i` linear. Assume `F ∈ \bar E`, i.e. `F` vanishes on every sheet.

Fix a sheet `L_J` with adapted coordinates `t_1,…,t_{k+1}` (one per matched pair). Restricting, `x_i|_L = \sum_p a_{ip} t_p` and hence `(x_i|_L)^q = \sum_p a_{ip}^q t_p^q`. Therefore

`0 = F|_L = \sum_p t_p^q \Bigl( \sum_i a_{ip}^q\, \ell_i|_L \Bigr)`.

The elements `t_1^q, …, t_{k+1}^q` form a regular sequence in `K[t]`, so the only relations among them are Koszul relations, which begin in degree `2q`. The coefficients `\sum_i a_{ip}^q \ell_i|_L` have degree `1 < q`; hence each vanishes.

Reading this pair by pair along the matching (where `x_a|_L = t_p`, `x_b|_L = -t_p`, and `(-1)^q = -1` since `q` is odd) yields `\ell_a ≡ \ell_b` on `L_J` for every `(a,b) ∈ J`, which forces `\ell_i = λ_i (x_0 + x_i)` in the unreduced coordinates. Testing a second matching that separates a previously matched pair `\{a,b\}` yields simultaneously `λ_a + λ_b = 0` and `λ_a = λ_b`, hence `2λ_a = 0`; since `2 ≠ 0` in characteristic `3`, all `λ_i = 0` and `F = 0`. ∎

**Lemma 5.3 `(\mathrm{rel}(2)`, all `q`).** `\dim (\bar E ∩ \mathfrak b)_{q+2} = 1` for `k ≥ 2`, and `= 3` for `k = 1`.

*Proof of the lower bound (by exhibition).* Let `p_m = \sum_i x_i^m` be the `m`-th power sum. For odd `m`, `p_m` vanishes on the arrangement: on a point of `L_J` the coordinates occur in pairs `\{a, -a\}` and `a^m + (-a)^m = 0`. By radicality (1.3.1), `p_m ∈ E` for every odd `m`. Since `q = 3^v` is odd, `q+2` is odd, so

> **`p_{q+2} = \sum_i x_i^{q+2} = \sum_i x_i^q · x_i^2 ∈ E ∩ \mathfrak m^{[q]}`**,

and its image in `R` is nonzero. Hence `\mathrm{rel}(2) ≥ 1`.

*Proof of the upper bound.* A degree-`(q+2)` element of `\mathfrak b` has the form `\sum_i x_i^q Q_i` with `Q_i` quadratic. Arguing as in 5.2 on the sheets through a fixed index, `Q_i` must vanish on every sheet matching `0` with `i`; the union of those sheets is the full matching arrangement on the remaining `2k` indices, whose ideal contains no quadric whenever `k ≥ 2` (its lowest-degree generator is `e_3`, of degree `3`). Hence `Q_i` is divisible by the linear form `x_0 + x_i`, and swap-connectivity of the matching graph forces a single common scalar, giving `Q_i = δ·(x_i^2 - x_0^2)`, a one-dimensional family. For `k = 1` the residual arrangement *is* a hyperplane, the step fails, and the space has dimension `3`. ∎

> **Evidence note.** The count `\mathrm{rel} = (0,0,1)` for `k ≥ 2` and `(0,0,3)` for `k = 1` has been verified by two independent implementations in the five cells `(k,q) = (1,3), (2,3), (3,3), (1,9), (2,9)`. The exhibited generator `p_{q+2}` was verified to lie in `\bar E`, to lie in `\mathfrak b`, and to be nonzero, in `(2,3)`, `(3,3)` and `(2,9)`. Lemma 5.1 and the lower bound of 5.3 are complete as written; Lemmas 5.2 and the upper bound of 5.3 are as stated above.

---

## 6. The theorem

> ### Theorem 6.1 (Casing Impossibility).
> Let `k ≥ 2`, let `q = 3^v`, let `K` be any field of characteristic `3`, and let `M` be any monomial degeneration of `\bar E` — over any field extension, with respect to any monomial order. Then
> **`Casing_M(q) > P_k(q)`.**

*Proof.* Suppose `Casing_M(q) = P_k(q)`. By Lemma 2.5, `A_k(q) ≤ Casing_M(q)`, and by the Floor Theorem 1.4.1, `A_k(q) ≥ P_k(q)`; hence `A_k(q) = Casing_M(q)`. Since `M + \mathfrak b ⊆ \mathrm{in}(g\bar E + \mathfrak b)`, we have `Casing_{M,d} ≥ A_d` in every degree, so equality of the totals forces equality in every degree, and Theorem 3.2 applies: the slack in degree `d` equals `\dim(\bar E ∩ \mathfrak b)_d`.

By Lemma 4.1 the degeneration contains a unique cubic `μ`, in one of three orbits. Comparing Lemma 4.2 with Lemma 5.1–5.3:

| orbit of `μ` | degree | forced non-box multiples | available slack `\mathrm{rel}(j)` | verdict |
|---|---|---|---|---|
| `x_i^3` | `q` | `1` | `0` | contradiction |
| `x_i^2 x_j` | `q+1` | `1` | `0` | contradiction |
| `x_i x_j x_l` | `q+2` | `3` | `1` | contradiction |

In each case the multiples of `μ` forced outside the box exceed the available slack. Hence `Casing_M(q) ≠ P_k(q)`, and since `Casing_M(q) ≥ A_k(q) ≥ P_k(q)`, the inequality is strict. ∎

**Corollary 6.2.** No amount of optimisation over bases, fields or monomial orders can make the monomial upper bound tight in dimension `2k ≥ 4`. The failure of the method is structural, not a failure of search.

**Corollary 6.3 (sharpness at `k = 1`).** For `k = 1` the orbit `x_i x_j x_l` has `3` forced non-box multiples and slack `\mathrm{rel}(2) = 3`: the inequality is not strict and the orbit survives. It is realised: in the basis `u = x_1+x_2`, `v = x_2+x_3`, `w = x_3+x_1` one has `\bar e_3 = -uvw` and `A_1(q) = \dim K[u,v,w]/(uvw, u^q,v^q,w^q) = q^3 - (q-1)^3 = 3q^2-3q+1 = P_1(q)`. The surviving orbit is exactly the squarefree cubic of that basis.

**Remark 6.4 (where `k ≥ 2` enters).** The hypothesis `k ≥ 2` is used at exactly one point: in Lemma 5.3, that the residual matching arrangement on `2k` indices is not a hyperplane. For `k = 1` it is, the argument stops, and the method survives. The theorem is therefore sharp.

---

## 7. Scope, and what is *not* claimed

**7.1.** Theorem 6.1 closes a **method**, not the conjecture. The Degtyarev–Shimada conjecture `A_k(q) = P_k(q)` remains open for `k ≥ 4`; the columns `k ≤ 3` are established by other means.

**7.2.** The theorem says nothing about upper bounds obtained by non-monomial means. In particular the remaining route — proving the *distributivity* identity `⋂_J (I_J·B) = E·B` in the box `B = S/\mathfrak m^{[q]}`, which is equivalent to the conjecture — is untouched by it.

**7.3.** The proof now uses **exactly one** campaign input as a black box: radicality (Fact 1.3.1). The floor is proved here from scratch (Proposition 1.4.1); no characteristic-zero input and no imported identification are needed. **No measured value of `A_k(q)` enters the proof anywhere** — that is the point of Theorem 3.2, and it is what makes the statement uniform in `q`.

---

## 8. Provenance

The strategy of monomial degeneration ("la funda") and its drawstring refinement originate with the Architect's physical analogies (an inflated tyre bounded by its casing; a hood tightened by its drawstrings) and were formalised as upper bounds in the campaign's bricks 32–34.

The impossibility argument in the present document arose in an adversarial two-auditor exchange. The slack identity (Theorem 3.2), Lemma 5.2 and the upper bound of Lemma 5.3 with its exhibited generator are due to the auditor *Vernier*. Lemma 5.1, the correction of scope that forced the argument away from measured censuses, and the reduction of the whole question to the three relation counts are due to the auditor *Locard*. The kill criterion for the search route was written before the search was run, and the search route was buried with data before the theorem was found.

**Independent verification.** All numerical claims were reproduced by two independently written engines. The five verification cells are `(k,q) = (1,3), (2,3), (3,3), (1,9), (2,9)`.

---

## 9. A methodological note

During this work two proposed laws, both fitted from three dimensions at `q = 3`, were falsified upon crossing to `q = 9` and `q = 27`. The cell `q = 3` collapses distinctions that exist higher in the Frobenius tower: there `q-1 = 2`, `q-2 = 1` and `q+3 = 2q` simultaneously. Any census read at `q = 3` should be treated as provisional until crossed with `q = 9`.

---

## 10 · Changes from version 1

**v2 (19 July 2026).** The floor (Proposition 1.4.1) is now proved from scratch via the associated graded ring of the function algebra `K[x]/(x_i^q - x_i)`, replacing the earlier route through integral presentation and rank semicontinuity. That route imported the characteristic-zero identification of `P_k(q)` from [DS]; the present one does not. **The document now rests on a single external input, radicality (Fact 1.3.1).** No other statement is altered.
