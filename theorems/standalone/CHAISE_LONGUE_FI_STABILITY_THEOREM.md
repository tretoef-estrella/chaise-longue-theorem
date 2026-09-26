> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE FI-STABILITY THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FI_STABILITY_THEOREM.md
>
> **Status, as written in the document:** A standalone component of The Chaise Longue Theorem. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE FI-STABILITY THEOREM
## The window census is representation-stable: σ_e(k) is eventually polynomial in the dimension

*A standalone component of **The Chaise Longue Theorem**. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*

---

**Scope.** For each fixed coefficient degree `e`, the window syzygy census `σ_e(k)` — a q-free integer for every even dimension `2k` by the Recognition Theorem (all k) — agrees, for all sufficiently large `k`, with a polynomial in `n = 2k+2` of degree at most `e+1`. This makes the Architect's "plant" heuristic a theorem in the dimension direction: the census bookkeeping stabilizes as the dimension grows, with only the stable Specht first row stretching. It does not determine the polynomial's coefficients (measured separately, three-point Kepler minimum), does not give the `e`-direction (a regularity statement), and does not by itself close the main theorem.

---

### 0. Setting

For a finite set `B` of even cardinality `n = 2k+2`, let `S(B) = F₃[x_b : b ∈ B]`, and let `M_e(B)` be the window syzygy space: tuples `λ = (λ_b)_{b∈B}` of degree-`e` forms with `λ_a − λ_b ∈ I({a,b})` for every edge, where `I({a,b}) = (x_a+x_b) + (ε₁, ε₃, …, ε_{2k−1})` is the edge ideal (odd elementary symmetrics of `B ∖ {a,b}`). By the Recognition Theorem this is, for `e < q`, exactly the space of window syzygies `Σ λ_b x_b^q ∈ E` at every tower level, and it does not involve `q`. The trivial syzygies are the diagonal `{(f, …, f)}` plus `(E_e)^B`, of dimension `dim S(B)_e + (n−1)·dim E_e`, and `σ_e(k) := dim M_e(B) − dim(trivials)`.

### 1. Functoriality (contravariant: restriction)

For an injection `φ : B ↪ B′` of even sets, define the restriction `res_φ : M_e(B′) → M_e(B)` by renaming via `φ` and **setting the variables outside `φ(B)` to zero**, keeping the coordinates indexed by `φ(B)`.

**Lemma 1 (well-defined).** `res_φ` maps `M_e(B′)` into `M_e(B)`, and trivials to trivials.
*Proof.* The load-bearing fact is that elementary symmetric polynomials restrict cleanly: `ε_j(B′ ∖ {a,b})|_{x_new = 0} = ε_j(φ(B) ∖ {a,b})`. Hence the edge ideal of `B′` at an old edge restricts INTO the edge ideal of `B` at that edge, and each condition `λ_a − λ_b ∈ I({a,b})_{B′}` restricts to the corresponding condition over `B`. The diagonal restricts to the diagonal and `E(B′)` restricts onto `E(B)` (odd ε's again). ∎
*(Machine check at the anchor `n = 8 → n = 6`, `e = 4`: every basis element of `M₄(8)` restricts inside `M₄(6)`; joint rank `456 = 456`, exact.)*

Thus `V_e : B ↦ M_e(B)` is a **co-FI-module** (contravariant functor on even finite sets and injections), as is the trivial subfunctor.

### 2. The theorem

> **Theorem (FI-stability).** For each fixed `e ≥ 0` there is `k₀(e)` such that for all `k ≥ k₀(e)`, `σ_e(k)` is given by a single polynomial in `n = 2k+2` of degree `≤ e+1`.

*Proof.* Write `V_e = ker(W_e → U_e)` where `W_e(B) = ⊕_{b∈B} S(B)_e` (the free layer) and `U_e(B) = ⊕_{edges} S(B)_e / I({a,b})_e` (the constraint layer); both are co-FI by Lemma 1's mechanism, and the map `λ ↦ (λ_a − λ_b mod I)` is natural (restriction commutes with differences and edge quotients). Dualizing levelwise over the field `F₃` (all dimensions finite), `V_e^* = coker(U_e^* → W_e^*)` is a **quotient** of the FI-module `W_e^*`. The FI-module `W_e^*` — degree-`e` monomials with a marked coordinate, injections acting by inclusion of variables — is finitely generated in FI-degree `≤ e+1` (a degree-`e` monomial involves at most `e` variables, plus the mark). Quotients of finitely generated FI-modules are finitely generated, so `V_e^*` is a finitely generated FI-module over `F₃`. By FI-noetherianity and eventual polynomiality of dimension over an arbitrary field (Church–Ellenberg–Farb; Church–Ellenberg–Farb–Nagpal for positive characteristic), `dim V_e(B)` is eventually polynomial in `n`, of degree bounded by the generation degree `e+1`. The trivial subfunctor dualizes to a f.g. FI-module by noetherianity, so its dimension is also eventually polynomial, and `σ_e(k)` — the difference — is eventually polynomial of degree `≤ e+1`. ∎

**Remark (even cardinalities).** The functor is defined on even finite sets; the FI results apply to this cofinal subcategory verbatim (alternatively, evaluate the usual FI statements along even `n`; eventual polynomiality along an arithmetic progression is what is used).

**Corollary (the method travels).** The annihilator census `α_c(k) = dim ann_Λ(g^{[q]})_c` (governing the high zone of the A-ring by the dualized vanishing) is constrained by the same mechanism: its defining conditions are built from the same edge/elementary data and restrict cleanly under `x_new = 0`. The same skeleton — co-FI, dualize, quotient of free, noetherianity — applies. (Development deferred; recorded as the method's second target.)

### 3. Anchors (byte-verified over F₃)

Functoriality: `M₄(8) → M₄(6)` well-defined, joint rank `456 = 456` (image rank 447; surjectivity not required). Census values consistent with stability: `σ₂ = 1, 1, 1` and `σ₃ = n−1 = 5, 7, 9` and `σ₄ = 25, 29, 46` at `k = 2, 3, 4` — the last a blind prediction (stable multiplicities `(2,1,1)` over families `∅, [1], [2]`) confirmed by a self-validating engine (anchors 5, 7, 25, 29 matched before computing 46).

**Honest limits.** The theorem does not pin the coefficients: with degree bound `e+1`, three points do not determine the `e = 4` polynomial (`σ₄(k) = 2 + (n−1) + n(n−3)/2` remains a blind-prediction-sealed candidate; sealing ∀k requires either a sharper degree bound — the measured Specht bodies satisfy `|λ̄| ≤ 2`, suggesting true degree 2 — or more computed points). The `e`-direction (polynomiality in `e` for fixed `k`, and the bivariate law needed for the window sum) is a regularity statement outside this theorem. Not yet refereed by a human expert.
