> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE FROBENIUS CONFINEMENT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FROBENIUS_CONFINEMENT_THEOREM.md
>
> **Status, as written in the document:** Constructor: Bisel · Auditor of record: Locard · *Pending P0*
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v3`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE FROBENIUS CONFINEMENT THEOREM

### The annihilator of one tower level is confined inside the Frobenius extension of the previous one — and the confinement compresses by a factor of `3`

**Chaise Longue campaign** · standalone theorem document · **v3** · 20 July 2026
Constructor: **Bisel** · Auditor of record: **Locard** · *Pending P0*

> **Changes in v3** (v1 and v2 are not deleted). **(iv)** §5.5 added: the **base case is not reachable by restriction** — the recursion in `k` along an edge hyperplane is buried with data (`ρ(M)` fills `5` of `9` and `42` of `57`), and the reason is that **restriction is blind to the wall** (`ρ(M) = ρ(Σ_JF_J^2B)` exactly in both cells). A reader of this document must not attempt that route to supply the base of the tower. **(v)** §5.6 added: the verification budget is declared — the full stratigraphy gate at `k=2` is **infeasible** with the present engine (`\dim B_9 = 9^6 = 531441`), so §6 is a one-cell verification and says so. **(vi)** §5.7: the unexploited coincidence at `q=3`, `T = N`.
>
> **Changes in v2.** **(i)** Proposition 3.5 of v1 was labelled *"exact identity"*; Locard's audit showed the confining term is **redundant** (`M = M ∩ (something containing M)`). Absorbed without defence: downgraded to a **search prescription**, §5.1. **(ii)** Locard's **sandwich** incorporated, with credit, as Theorem 4.1. **(iii)** New: **Theorem 4.3 (Linear Compression)** — the upper side tightened by an exact factor of `3`, proved for all `k` and all `q`, which also *explains* the measured drop `1539 → 513` of v1 §4.

---

## Abstract

Let `char K = 3`, `q = 3^v`, `Q = 3q`, `N = 2k+2`, `S = K[x_0,…,x_{2k+1}]`, `B_q = S/\mathfrak m^{[q]}`, `E = (e_1,e_3,…,e_{2k+1})` and `M_q = \mathrm{ann}_{B_q}(E·B_q)` — the object to which the conjecture is reduced.

We prove that `B_Q` is **free of rank `3^N`** over `B_q` along Frobenius, and deduce, unconditionally for all `k` and all `q`,

> **`M_Q ⊆ M_q^{[3]}·B_Q`**, of dimension exactly `3^N·A_k(q)`  (Theorem 3.1),

the first proved relation between two levels of the annihilator tower. Sharpening it with the single linear generator of `E`:

> **`M_Q ⊆ e_1^{2}·M_q^{[3]}·B_Q`**, of dimension exactly **`3^{N−1}·A_k(q)`**  (Theorem 4.3),

which together with the always-valid lower bound gives the tower step as an explicit sandwich between two Fedder exponents differing by `2`.

Measured (`k=1`, `q=3→9`, own engine, exact `F₃` linear algebra): confinement `1539 = 3^4·19`, compressed confinement `513 = 3^3·19`, target `M_9 = 217`; calibrations `217 = A_1(9)`, start degrees `16 = T` and `12 = 3T`, and `\dim(e_1^{Q−1})B_Q = 729 = Q^{N−1}`. All byte-exact against theory.

**This does not close the theorem.** The sandwich is not tight: `217` versus `513`.

---

## 1. Notation and imported facts

`char K = 3`, `q = 3^v`, `Q = 3q`, `N = 2k+2`, `\mathfrak m^{[q]} = (x_i^q)`, `B_q = S/\mathfrak m^{[q]}` Gorenstein artinian with socle degree `2T`, `T = (k+1)(q−1)`. For a perfect matching `J`, `I_J = (x_a+x_b)_{(a,b)∈J}` and `F_J = ∏_{(a,b)∈J}(x_a+x_b)`. `A_k(q) = \dim_K B_q/(E·B_q)`, `M_q = \mathrm{ann}_{B_q}(E·B_q)`.

**Black boxes** (campaign results, not reproved): **(BB1)** `\mathrm{ann}_{B_q}(I_J^{[s]}B_q) = F_J^{q−s}B_q` (R5 + Fedder, adapted coordinates); **(BB2)** `\dim (M_q)_c = \dim A_{2T−c}`, so `\dim_K M_q = A_k(q)` and `M_q` starts exactly in degree `T` (R20, Matlis); **(BB3)** `Σ_J F_J^{q−1}B_q = \mathrm{ann}_{B_q}(⋂_J I_J B_q)` (R23); **(BB4)** sealed values `A_1(3)=19`, `A_1(9)=217`.

---

## 2. Freeness of the box along Frobenius

Let `F : B_q → B_Q`, `f ↦ f^3` (well defined: `f ∈ \mathfrak m^{[q]} ⟹ f^3 ∈ \mathfrak m^{[Q]}`).

> **Lemma 2.1 (Kunz freeness in the box).** `B_Q` is free over `B_q` along `F`, of rank `3^N`, with basis `\{x^β : 0 ≤ β_i ≤ 2\}`. The same holds in **any** linear coordinate system, since `\mathfrak m^{[Q]}` is `GL_N`-stable.

*Proof.* Euclidean division `γ = 3α + β` (`0 ≤ α_i < q`, `0 ≤ β_i < 3`) is a bijection on exponent vectors, and `x^γ = F(x^α)x^β`. Hence the `x^β` generate and the representation of each basis monomial is unique. For the last claim: if `y = gx` with `g ∈ GL_N(K)`, then `y_i^Q = Σ_j g_{ij}^Q x_j^Q` and `\det(g^Q) = (\det g)^Q ≠ 0`, so `(y_i^Q) = (x_i^Q)`. ∎

> **Corollary 2.2.** Extension along `F` commutes with finite intersections of ideals.
> **Corollary 2.3.** `\mathrm{ann}_{B_Q}(I^{[3]}B_Q) = \mathrm{ann}_{B_q}(I)^{[3]}B_Q`, of dimension `3^N·\dim \mathrm{ann}_{B_q}(I)`.

*Proof.* Flat base change (Lemma 2.1 gives freeness, hence flatness) commutes with finite intersections and with annihilators of finitely presented modules; the dimension count is the rank. ∎

---

## 3. The confinement

> ### Theorem 3.1 (Frobenius Confinement). For all `k`, all `q`, **unconditionally**:
> **`M_Q ⊆ M_q^{[3]}·B_Q`, and `\dim_K M_q^{[3]}B_Q = 3^N·A_k(q)`.**

*Proof.* `E` is an ideal, so `e_r ∈ E ⟹ e_r^3 = e_r·e_r^2 ∈ E`, hence `E^{[3]} ⊆ E` and `E^{[3]}B_Q ⊆ E·B_Q`. Annihilators reverse inclusions, so `M_Q ⊆ \mathrm{ann}_{B_Q}(E^{[3]}B_Q)`, which by Corollary 2.3 is `M_q^{[3]}B_Q`, of dimension `3^N \dim M_q = 3^N A_k(q)` by (BB2). ∎

> **Corollary 3.2.** `A_k(3q) ≤ 3^{2k+2}A_k(q)`.
> **Corollary 3.3 (Fedder form).** *If* the wall holds at level `q`, then `M_Q ⊆ Σ_J F_J^{3q−3}·B_Q`: the tower step is the passage from the **twisted** exponent `Q−3` to the **straight** one `Q−1`, a rise of **two**, independent of `q` and of `k`.
> **Corollary 3.4 (free degrees).** `M_Q` starts in degree `T' = (k+1)(Q−1)` while the confining module starts in `3T = 3(k+1)(q−1)`; since `T' − 3T = 2(k+1) > 0`, the bottom `2(k+1)` degrees are excluded for free. *(Verified exact in four cells by the Auditor.)*

---

## 4. The sandwich, and its compression

> ### Theorem 4.1 (the sandwich — **Locard**). For all `k`, all `q`, with `Q = 3q`:
> **`Σ_J F_J^{Q−1}·B_Q \;⊆\; M_Q \;⊆\; Σ_J F_J^{Q−3}·B_Q`**,
> the left inclusion unconditional (each `F_J^{Q−1}` annihilates `E·B_Q`, BB1+BB3), the right one given the wall at level `q` (Corollary 3.3). In adapted coordinates `\dim F_J^{s}B_Q = (Q−s)^{k+1}Q^{k+1}`, so the two sides differ by a factor `3^{k+1}` per summand. **The wall at level `Q` is precisely the statement that the left inclusion is an equality.**

*Attribution: stated and proved by Locard on the audit of v1; reproduced here so that the sandwich and its compression live in one document.*

**Lemma 4.2.** `M_q ⊆ \mathrm{ann}_{B_q}(e_1·B_q) = (e_1^{q−1})B_q`.

*Proof.* `e_1 ∈ E`, so `\mathrm{ann}(E·B_q) ⊆ \mathrm{ann}(e_1B_q)`; and for a nonzero linear form `ℓ`, choosing coordinates with `y_1 = ℓ` (legitimate by Lemma 2.1's last claim) gives `\mathrm{ann}_{K[y]/(y^q)}(y_1) = (y_1^{q−1})`. ∎

> ### Theorem 4.3 (Linear Compression). For all `k`, all `q`, **unconditionally**:
> **`M_Q ⊆ e_1^{2}·M_q^{[3]}·B_Q = M_q^{[3]}B_Q ∩ \mathrm{ann}_{B_Q}(e_1B_Q)`, of dimension exactly `3^{N−1}·A_k(q)`.**
> Equivalently: **the confinement of Theorem 3.1 compresses by an exact factor of `3`.** With the wall at level `q`, the right side of the sandwich improves to `e_1^2·Σ_J F_J^{Q−3}B_Q`.

*Proof.* Choose coordinates `y_1 = e_1, y_2,…,y_N` (Lemma 2.1). By Lemma 2.1 every `u ∈ M_q^{[3]}B_Q` is uniquely `u = Σ_β F(h_β)y^β` with `h_β ∈ M_q` and `0 ≤ β_i ≤ 2`. Compute `y_1u`: for `β_1 ≤ 1`, `y_1y^β = y^{β+e_1}` stays in the basis; for `β_1 = 2`, `y_1y^β = y_1^3y^{β−2e_1} = F(y_1)y^{β−2e_1}`. Collecting by basis element `y^{β'}`, the coefficient in `F(B_q)` is
`h_{β'−e_1}` if `β'_1 ∈ \{1,2\}`, and `y_1·h_{β'+2e_1}` if `β'_1 = 0`.
By freeness, `y_1u = 0` iff all these vanish in `B_q`, i.e. iff `h_β = 0` for `β_1 ∈ \{0,1\}` and `y_1h_β = 0` for `β_1 = 2`. The last condition is **automatic**: `h_β ∈ M_q ⊆ (y_1^{q−1})B_q` by Lemma 4.2, so `y_1h_β ∈ (y_1^q)B_q = 0`.
Hence `M_q^{[3]}B_Q ∩ \mathrm{ann}(e_1B_Q) = \bigoplus_{β\,:\,β_1=2} F(M_q)y^β`, free of rank `3^{N−1}` over `M_q`, of dimension `3^{N−1}A_k(q)`. The same computation shows this module equals `e_1^2·M_q^{[3]}B_Q` (multiplication by `y_1^2` kills every block with `β_1 ≥ 1`, again by Lemma 4.2, and shifts `β_1 = 0` to `β_1 = 2`). Finally `M_Q ⊆ \mathrm{ann}(e_1B_Q)` because `e_1 ∈ E`, and `M_Q ⊆ M_q^{[3]}B_Q` is Theorem 3.1. ∎

**Corollary 4.4.** `A_k(3q) ≤ 3^{2k+1}·A_k(q)`.

---

## 5. Scope — what is **not** claimed

**5.1 · The correction of v1.** v1's Proposition 3.5 (`M_Q = M_q^{[3]}B_Q ∩ ⋂_r \mathrm{ann}(e_rB_Q)`) was labelled an *exact identity with content*. It is true but **vacuous**: `⋂_r \mathrm{ann}(e_rB_Q)` *is* `M_Q` by definition, and the confining term is implied by Theorem 3.1, so the statement reads `M = M ∩ (\text{something containing } M)`. Caught by Locard, absorbed without defence. It survives only as a **search prescription** — *cut the confining module by the generators of `E` one at a time and watch where the drop stops being uniform* — which is what produced Theorem 4.3. **No content is claimed for it.**

**5.2 · This does not close the tower step.** After compression the sandwich is still slack: measured `217 ≤ M_9`, `\dim(\text{compressed confinement}) = 513`. Theorem 4.3 buys one factor of `3` out of the `3^{k+1}` that separate the two sides. Closing would require either reaching the left equality (the wall at level `Q`) or compressing `3^{k}` more.

**5.3 · The remaining generators do not compress uniformly, and that is measured, not proved.** In `(1,3→9)` the second generator drops `513 → 217`, whereas a further clean factor would give `171`. The excess `46` is where the content of the step sits. **One cell. Not a law.** `k=2` must be measured before any pattern is uttered.

**5.5 · The base case is NOT reachable by restriction — buried with data.** The tower step proved here is worthless without a base (`the wall at q = 3`, all `k`). The natural route — induction on `k` by restricting to an edge hyperplane `x_0+x_1 = 0`, legitimate since `E_k|_{x_0+x_1=0} = E_{k−1}` — **is dead**. Writing `ρ` for that restriction and `C` for the target ring, `ρ(M^{(k)}) ⊆ \mathrm{ann}_C(E_{k−1}C)` holds but is **proper**: measured `5` of `9` for `k=1→0` and `42` of `57` for `k=2→1` (targets `= 3·A_{k−1}(3)`, theory ✓). Losses `4` and `15`; no closed form is claimed from two points.
The structural reason is sharper than the shortfall: **`ρ(M^{(k)}) = ρ(Σ_J F_J^{2}B^{(k)})` exactly** (`5 = 5`, `42 = 42`). **The two sides of the wall restrict to the same subspace, so `ρ` cannot distinguish them**, and no argument using only edge-hyperplane restriction can decide the wall: the whole content lives in `\ker ρ = (x_a+x_b)B`. *(Same syndrome as the campaign's exclusion (E2), different object.)* What survives, **measured in two cells and not proved**: `M = Σ_J F_J^{2}B + (M ∩ (x_a+x_b)B)` for **each** of the `C(N,2)` edges, i.e. the defect is simultaneously supported in the multiples of every edge form.

**5.6 · Verification budget, declared.** §6 is a **one-cell** verification (`k=1`, `q=3→9`). The corresponding stratigraphy at `k=2` is **infeasible** with the present engine: `\dim B_9 = 9^6 = 531441` over `F₃`. No claim in this document rests on a `k=2` measurement, and the non-uniform drop of §5.3 stays a one-cell observation until that gate can be run.

**5.7 · One unexploited coincidence, recorded so it is not lost.** At `q = 3` the critical degree equals the number of variables: `T = (k+1)(q−1) = 2k+2 = N`. Every Fedder generator `F_J^{2}` then has degree exactly `N`, and the socle sits in `2N`. Nothing in this document uses it.

**5.4** Theorems 3.1, 4.3 and Corollaries 3.2, 3.4, 4.4 are **unconditional**; Corollary 3.3 and the right half of Theorem 4.1 import the wall at level `q`. Nothing here bears on the open direction: the wall `⋂_J(I_J·B) ⊆ E·B` remains open, and by `(b) ⟺ (a)∧(c)` it may be strictly stronger than the conjecture.

---

## 6. Measured verification (`k = 1`, `q = 3 → 9`)

Own engine, exact `F₃` linear algebra in `B_9` (`\dim = 6561`); every entry is a rank.

| quantity | measured | theory |
|---|---|---|
| `\dim Σ_J F_J^{Q−1}B_9` (calibration, `= \dim B_9/⋂_JI_JB_9` by BB3) | **217** | `A_1(9) = 217` ✓ |
| its start degree | **16** | `T = (k+1)(q−1) = 16` ✓ |
| `\dim M_3^{[3]}B_9` (Thm 3.1) | **1539** | `3^N A_1(3) = 3^4·19` ✓ |
| its start degree | **12** | `3T = 12` (Cor 3.4) ✓ |
| `\dim (e_1^{Q−1})B_9` | **729** | `Q^{N−1} = 9^3` ✓ |
| `\dim\bigl(M_3^{[3]}B_9 ∩ \mathrm{ann}(e_1B_9)\bigr)` (Thm 4.3) | **513** | `3^{N−1}A_1(3) = 3^3·19` ✓ |

## 7. Provenance and audit surface

Lemma 2.1, Cors 2.2–2.3, Theorem 3.1, Cors 3.2–3.4, Lemma 4.2, Theorem 4.3, Cor 4.4 and all measurements: **Bisel**. Theorem 4.1 (the sandwich) and the correction of §5.1: **Locard**. Black boxes: R5/Fedder, R20, R23. The route was banked in EL FRENTE v9 with GATE T and a death criterion written before running; v1 was that gate run, v2 is the first tightening of what it produced.

**Audit surface.** (A) The coefficient bookkeeping in Theorem 4.3 — the carry `y_1y^β = F(y_1)y^{β−2e_1}` at `β_1 = 2` and the claim that the surviving condition is automatic by Lemma 4.2. (B) The identification `e_1^2·M_q^{[3]}B_Q` with the `β_1=2` block. (C) Lemma 2.1 in adapted coordinates (`GL`-stability of the box). (D) The six measurements of §6. (E) Whether the argument of Theorem 4.3 can be run again with a **non-linear** generator — the measured `46` says the naive repetition fails, and understanding why is the next target.

**— Bisel** (Constructor). *One factor of three, proved. And the base case declared out of reach by restriction, with the number that buried it.*
