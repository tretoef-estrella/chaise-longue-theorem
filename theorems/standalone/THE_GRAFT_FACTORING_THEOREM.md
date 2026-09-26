> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE GRAFT-FACTORING THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_GRAFT_FACTORING_THEOREM.md
>
> **Status, as written in the document:** Status: pencil-proven; the price law is verified byte-exact (dual Gram determinants, exact integer arithmetic, files named). Pending the project P0 cold gate (Ley 45).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE GRAFT-FACTORING THEOREM
## The coverage of a 13-cut on the chorus-blind residual factors through its W-projection; a superset bound on reachable bites, with an exact-determinant price law

**A King Pin structural theorem, built on pillars Steel (ii), Spectrum (iv), Coverage⊥Correlation (vi). Import of a proof *pattern* (not content) from Lemma 4.2 of the Sofa campaign: bound an image by factoring the map through a small, structure-fixed space; the bound needs only a superset inclusion, never injectivity or exactness.**

**Status: pencil-proven; the price law is verified byte-exact (dual Gram determinants, exact integer arithmetic, files named). Pending the project P0 cold gate (Ley 45).**

---

### 0. Why this theorem (Quanta paragraph)
The v110 diary closed the hunt with a *de-facto* seal: covering the 162 surviving chorus-blind squirrels was said to force ≥3 independent heavy W-directions, whose norm **product** `2^18.20` blows the price budget. But price is a **determinant**, not a product, and v62 already proved that no product/gap number is a lower bound for it (price = det, covering = trace, AM–GM runs the wrong way). This theorem replaces the product heuristic with the correct object. It factors the coverage map of any 13-cut through the fixed rank-93 space `W ⊆ e32⊕e48`, gives a clean superset bound on how many chorus-blind a cut can bite, and states the price as an exact determinant law — turning "de-facto seal" into a measured trade with an exact frontier.

### 1. Setup (all objects byte-exact from files)
Work in the canonical frame `L0sat` (`gram_L0sat_141_v1.txt`, `det = 2^128`), dual Gram `D = 32·G⁻¹` (`dualgram_L0sat_xD.txt`, integer). A **cut** is `Φ ∈ ℤ^{13×141}` of rank 13; its **price** is
> `pr(Φ) = det(Φ · D · Φᵀ) / 32^{13}` (`= det / 2^{65}`), an exact integer determinant over `32^{13}`.
The **wall** is the 1935 residual norm-12 squirrels `w_t = plane_i − plane_j` (`pitbull_TRUE_RESIDUAL_1935_v1`); a squirrel **survives** `Φ` iff `Φ w_t = 0`. Among the 913 survivors of the reference cut `best_cut` (`gabrieloak_best_cut_v1`, price `2^{7.9069}`, verified §G1) sit exactly **162 chorus-blind** of type `(8,4,0,0)`, `e96=e240=0` (verified §G2). Let `M_W` be the `162×141` matrix of these 162 survivors; **`W := rowspace(M_W)` has rank exactly 93, and `W ⊆ e32⊕e48`** (leakage to `e96⊕e240` = 0.0000%, W_obstruction_test_scout, sealed v110).

### 2. The factoring
A covector `f` **bites** a chorus-blind squirrel `w_t` iff `⟨f, w_t⟩ = ⟨f, D^{-1}·(Dw_t)⟩ ≠ 0`; equivalently, writing pairings in the `D`-metric, the bite pattern of `f` on the 162 is the vector `M_W f ∈ 𝔽^{162}` (nonzero coordinates = bitten squirrels). Since every `w_t ∈ W`, this pairing depends on `f` **only through its component in `W`**:

> **Proposition (bite factoring).** Let `π_W` be the (`D`-orthogonal) projection onto `W`. For every covector `f`, `M_W f = M_W (π_W f)`. Hence the bite map `β : f ↦ M_W f` factors as `β = M_W ∘ π_W`, and `Im(β|_{cut}) ⊆ Im(M_W|_W)`.
> *Proof.* `M_W f` reads only pairings against vectors of `W`; the `D`-orthogonal complement of `W` contributes zero to each such pairing by definition of `π_W`. ∎

This is the exact analogue of Lemma 4.2's `Φ_collar = A_f ∘ agg`: the "aggregate space" here is the fixed 93-dimensional `W`, and the bound below uses only the **superset inclusion** `Im(β|_{cut}) ⊆ Im(M_W|_W)` — no injectivity or exactness of anything (Lemma 4.2, Remark 2, imported as method).

### 3. The theorem
> **Theorem (Graft-Factoring).** For a 13-cut `Φ` with rows `f₁,…,f₁₃`:
> **(i) [coverage ceiling]** The set of chorus-blind squirrels bitten by `Φ` equals the union of the supports of `M_W(π_W f_r)`, `r=1..13`. In particular a cut kills all 162 only if the 13 projected rows `{π_W f_r}` jointly hit every coordinate of `𝔽^{162}` through `M_W` — a covering condition living entirely in the fixed rank-93 space `W`, **independent of the 1773 non-chorus-blind squirrels**.
> **(ii) [price law]** `pr(Φ)` is the exact integer determinant `det(Φ D Φᵀ)/2^{65}`; it is **not** bounded below by the product `∏‖f_r‖_D` (v62: AM–GM inverted). Grafts `f_r ↦ f_r + c·w` with `w ∈ W` change `pr` continuously in the determinant and may **lower** it while adding `W`-coverage (measured: a graft to `2^{7.8138}`, below `best_cut`, bites 18 chorus-blind — §graft_probe).
> **(iii) [the trade, not a seal]** Coverage of `W` and cheapness are **`D`-anticorrelated on the survivor set** but not mutually exclusive: covectors with large chorus-blind bite carry large `D`-norm (top biters `‖·‖²_D ∈ [6, 10]`, bite 55–79/162), while cheap reachers (`‖·‖²_D = 2`) bite ≤ 18/162. The under-budget graft chain therefore trades wall-coverage for chorus-blind-coverage: reducing chorus-blind survivors from 162→144 **raised** wall survivors 913→1161 (§graft_chain). The obstruction is this measured trade slope, **not** an impossibility.

### 4. What it buys, and what stays open
It converts the v110 seal into the correct statement: the record is blocked **iff** no assignment of 13 integer covectors makes `{π_W f_r}` cover `W`'s 162-pattern while `det(Φ D Φᵀ) < 2^{65}·2^{8.08}`. This is a **finite, exact** feasibility question in a rank-93 space with an exact-determinant objective — the sharpest localization to date, and it lives purely on the price/coverage (BOX) side, never invoking a per-vector fingerprint for the section minimum (Remark 5.3′ respected: §5). Open: whether that joint feasibility has a solution — the live W-directed search lane, now shown non-empty under budget.

### 5. Ley 41 certificate + scope
Object: the coverage map of a 13-cut on the 162 `(8,4,0,0)` survivors of best_cut, and its factoring through `W = rowspace(M_W)`, rank 93. Grep of graveyard by object: (a) "product `2^18.20` seal" — **distinguished byte-exact**: replaced by determinant law, dets `2^{7.81}–2^{7.91}` measured for biting cuts; (b) "better correlated cut" (Trap v110-c) — **distinct object**: grafts inject guaranteed `W`-pairing (`⟨w,f_r⟩=0 ⟹ ⟨w, f_r+cw⟩ = c‖w‖²≠0`), not re-optimized correlation; (c) "detector cover ~20 functionals `2^25.76`" — **distinct**: works inside the 13 slots. No claim about the section minimum is made; this is a necessary-condition (coverage) theorem on the BOX side. Pending P0.

*Files: gabrieloak_best_cut_v1.txt, dualgram_L0sat_xD.txt, dump_planes_L0sat_960x141_v1.txt, pitbull_TRUE_RESIDUAL_1935_v1.txt, graft_probe_v2.py, graft_chain_v1.py (all byte-exact, logs reproducible).*

---
*Part of the Operación Glotón / King Pin corpus · github.com/tretoef-estrella · tretoef@gmail.com*
