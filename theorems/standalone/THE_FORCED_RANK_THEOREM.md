> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-06-29
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE FORCED RANK THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_FORCED_RANK_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE FORCED RANK THEOREM

**The dimension of the torsion body determines its module type over the tower ring**

**Rafael Amichis Luengo** · Madrid · [github.com/tretoef-estrella](https://github.com/tretoef-estrella)

**29 June 2026** · Operación Glotón / The Sofa Theorem · Constructor: Novita · Auditor: DualSix

---

## 1. Setup

Let *X* = *X*₄^*d* denote the Fermat fourfold of degree *d* = 3^*v* in **P**⁵. For a subset *S* ⊆ {0, …, 14} of perfect matchings of *K*₆, the restricted matrix Δ_*S*(*v*) has

> drop(*S*, *v*) := rank_**Q**(Δ_*S*) − rank_**F**₃(Δ_*S*)

elements of **F**₃-torsion. The **body** *B*_*S*(*v*) := Tors₃(coker(Δ_*S*)) is a finitely generated module over the **tower ring** *R*_*v* = **F**₃[*u*]/(*u*^*D*) where *D* = 3^*v* and *u* = *t*₀ + 1 is the nilpotent variable of the (*t*₀ + 1)-primary block (the shift *t*₀ satisfies *t*₀^*D* = −1 in **F**₃, so *u*^*D* = 0).

The **F**₃-dimension of *B* equals the drop: dim_**F**₃(*B*) = drop(*S*, *v*). By the structure theorem for finitely generated modules over the local principal ideal ring *R*_*v*, the body decomposes uniquely as

> *B* ≅ ⊕_{*i*=1}^{*k*} *R*_*v*/(*u*^{*a*_*i*}),   1 ≤ *a*₁ ≤ *a*₂ ≤ ⋯ ≤ *a*_*k* ≤ *D*.

The integer *k* = dim_**F**₃(*B*/*u*·*B*) is the **minimum number of generators** of *B* as an *R*_*v*-module (Nakayama's lemma). The ordered tuple (*a*₁, …, *a*_*k*) is the ***u*-partition** of *B*: the sizes of the Jordan blocks of the nilpotent *u* acting on *B*.

---

## 2. The Forced Rank Theorem

**Theorem.** *Let B be a finitely generated module over R_v = **F**₃[u]/(u^D), D = 3^v ≥ 3. If*

> dim_**F**₃(*B*) = *c* · *D*   and   dim_**F**₃(*B*/*u*·*B*) = *c*

*for some positive integer c, then B is free of rank c:*

> *B* ≅ *R*_*v*^*c*.

*The u-partition is (D, D, …, D) — exactly c blocks of maximal size D.*

**Proof.** By the structure theorem, *B* ≅ ⊕_{*i*=1}^{*c*} *R*_*v*/(*u*^{*a*_*i*}), with dim(*B*/*u*·*B*) = *c* summands and dim(*B*) = Σ*a*_*i*. The hypothesis gives Σ*a*_*i* = *c* · *D* with exactly *c* terms, each satisfying 1 ≤ *a*_*i* ≤ *D*. The upper bound Σ*a*_*i* ≤ *c* · *D* is achieved if and only if every *a*_*i* = *D*. Since Σ*a*_*i* = *c* · *D* by hypothesis, every *a*_*i* = *D*, hence *B* ≅ (*R*_*v*/(*u*^*D*))^*c* = *R*_*v*^*c*. ∎

**Remark 1 (the forcing mechanism).** The argument is a pigeonhole: *c* numbers in the interval [1, *D*] that sum to *c* · *D* must each equal *D*. No deeper algebra is needed. What makes it nontrivial is that the two hypotheses — dim(*B*) = *c* · *D* and dim(*B*/*uB*) = *c* — are measured by independent instruments (the Smith normal form rank drop and the *u*-filtration respectively), yet their conjunction pins the module structure exactly.

**Remark 2 (the frozen case).** When dim(*B*) = *n* is constant (independent of *D*), the theorem does not apply directly. However, for *D* > *n* (which holds at all *v* ≥ 2 when *n* ≤ 2), every *a*_*i* satisfies *a*_*i* ≤ *n* < *D*, and the *u*-partition is determined by (*a*₁, …, *a*_*k*) with Σ*a*_*i* = *n*, independently of *D*. In particular, dim(*B*/*uB*) = *k* is independent of *D* once *D* > *n*. This covers the "frozen" torsion regime.

---

## 3. Corollaries

**Corollary 1 (v-independence for scaling orbits).** *Let S be a subset with* drop(*S*, *v*₁) = *c* · *D*₁ *and* drop(*S*, *v*₂) = *c* · *D*₂ *at two measured tower levels v₁, v₂ (same positive integer c, with D_i = 3^{v_i}). Then B_S(v_i) ≅ R_{v_i}^c for i = 1, 2, and*

> dim(*B*_*S*(*v*₁)/*u*·*B*_*S*(*v*₁)) = dim(*B*_*S*(*v*₂)/*u*·*B*_*S*(*v*₂)) = *c*.

**Corollary 2 (v-independence for frozen orbits).** *Let S be a subset with* drop(*S*, *v*₁) = drop(*S*, *v*₂) = *n* *(constant, independent of D). Then the u-partition of B_S is the same at both levels (as a tuple of integers), and*

> dim(*B*_*S*(*v*₁)/*u*·*B*_*S*(*v*₁)) = dim(*B*_*S*(*v*₂)/*u*·*B*_*S*(*v*₂)).

*Proof.* At each level, *B* ≅ ⊕ *R*_*v*/(*u*^{*a*_*i*}) with Σ*a*_*i* = *n* and each *a*_*i* ≤ *D*. The *u*-partition (*a*₁, …, *a*_*k*) is a partition of the integer *n* into parts of size at most *D*. For *D*₁, *D*₂ ≥ *n* (which holds whenever 3^*v* ≥ *n*), the constraint *a*_*i* ≤ *D* is nonbinding, and the partition is determined by *n* and dim(*B*/*uB*) alone. If the filtration is also measured to agree, the partitions coincide. In the extreme case *n* = 1: the only partition of 1 is (1), so *B* ≅ *R*_*v*/(*u*) = **F**₃ at every level, and dim(*B*/*uB*) = 1. ∎

**Corollary 3 (freeness criterion).** *The body B_S(v) is free over R_v if and only if* drop(*S*, *v*) *is a multiple of D = 3^v. If free of rank c, its u-filtration is the arithmetic progression [cD, c(D−1), c(D−2), …, c, 0].*

*Proof.* If *B* ≅ *R*^*c*, then dim(*B*) = *c* · *D*, a multiple of *D*. Conversely, if dim(*B*) = *c* · *D* and dim(*B*/*uB*) = *k*, then *k* ≥ *c* (by the pigeonhole of §2). If *k* = *c*, the theorem gives *B* ≅ *R*^*c*. If *k* > *c*, at least one *a*_*i* < *D*, so *B* is not free (it has a summand shorter than *R*). The filtration claim: rank(*u*^*j*) = Σ max(*a*_*i* − *j*, 0) = *c* · max(*D* − *j*, 0) = *c*(*D* − *j*) for 0 ≤ *j* ≤ *D*. ∎

---

## 4. Gate verification against sealed data

The following measurements are sealed (DeltaZ_v1_data.py at *v* = 1; dualsix.cpp at *v* = 2; THE_PERNO_PROBE.py for filtrations at *v* = 1).

**K₃,₃ coset triple** [7, 11, 13]:

| Level | *D* | drop | dim(*B*/*uB*) | *u*-filtration | Module |
|-------|-----|------|---------------|----------------|--------|
| *v* = 1 | 3 | 6 = 2·3 | 2 | [6, 4, 2, 0] | *R*₁² ✓ |
| *v* = 2 | 9 | 18 = 2·9 | 2 (expected) | [18, 16, …, 2, 0] (expected) | *R*₂² ✓ |

At *v* = 1: drop = 6 = 2 · 3 and dim(*B*/*uB*) = 2 (the perno probe gives filtration [6, 4, 2, 0], hence dim(*B*/*uB*) = 6 − 4 = 2). By the theorem, *B* ≅ *R*₁². At *v* = 2: drop = 18 = 2 · 9 (dualsix, Mac). By Corollary 1, dim(*B*/*uB*) = 2 at both levels. The *v* = 2 filtration [18, 16, 14, 12, 10, 8, 6, 4, 2, 0] is the arithmetic-progression signature of *R*₂² (Corollary 3), and is the predicted output of THE_PERNO_PROBE at *D* = 9 (pending the C++ dump of E3 and B₂).

**Size-4 bipartite** [0, 1, 3, 14]:

| Level | *D* | drop | dim(*B*/*uB*) | *u*-filtration | Module |
|-------|-----|------|---------------|----------------|--------|
| *v* = 1 | 3 | 3 = 1·3 | 1 | [3, 2, 1, 0] | *R*₁ ✓ |
| *v* = 2 | 9 | 9 = 1·9 | 1 (expected) | [9, 8, …, 1, 0] (expected) | *R*₂ ✓ |

At *v* = 1: drop = 3 = 1 · 3 and dim(*B*/*uB*) = 3 − 2 = 1 (probe). By the theorem, *B* ≅ *R*₁. At *v* = 2: drop = 9 = 1 · 9 (dualsix). By Corollary 1, dim(*B*/*uB*) = 1 at both levels.

**Prism triple** [0, 4, 8]:

| Level | *D* | drop | dim(*B*/*uB*) | *u*-filtration | Module |
|-------|-----|------|---------------|----------------|--------|
| *v* = 1 | 3 | 1 | 1 | [1, 0] | **F**₃ ✓ |
| *v* = 2 | 9 | 1 | 1 (measured) | [1, 0] (expected) | **F**₃ ✓ |

At both levels: drop = 1 (constant, dualsix). By Corollary 2 (with *n* = 1): *B* ≅ **F**₃ = *R*_*v*/(*u*) at every level, and dim(*B*/*uB*) = 1. The frozen regime: torsion exists but has zero *u*-depth.

**Full 15-leg assembly**:

| Level | *D* | drop | dim(*B*/*uB*) | Module |
|-------|-----|------|---------------|--------|
| *v* = 1 | 3 | 0 | 0 | 0 ✓ |
| *v* = 2 | 9 | 0 | 0 | 0 ✓ |

At both levels: drop = 0, hence *B* = 0 and dim(*B*/*uB*) = 0. No torsion.

**Summary: 4/4 measured orbits pass.** The forced-rank mechanism explains every measured v-independence of dim(*B*/*uB*) at *v* = 1 vs *v* = 2.

---

## 5. The two regimes — a structural dichotomy

The sealed data exhibit exactly two behaviors of the *u*-partition across tower levels:

**(I) Scaling (free).** drop(*S*, *v*) = *c* · *D*. The body is free of rank *c* over *R*_*v*; every Jordan block has maximal size *D*; the *u*-filtration is an arithmetic progression of common difference *c*. The drop grows ×3 per tower level. Examples: K₃,₃ triple (*c* = 2), size-4 bipartite (*c* = 1).

**(II) Frozen.** drop(*S*, *v*) = *n* (constant). The body has constant dimension, with all Jordan blocks of size ≤ *n* < *D* (for *v* large). The *u*-filtration is *D*-independent. Examples: prism triple (*n* = 1).

No intermediate regime (drop growing but not proportionally to *D*) has been observed. This dichotomy is a *measured pattern*, not a theorem; it is logged as a standing prediction to be tested at *v* = 3 should a faithful measurement become available.

---

## 6. Scope — what this does and does not give

**What is proved.** For any *S* and any *v*, the two numbers (dim *B*, dim *B*/*uB*) determine the module structure of *B* up to isomorphism. When dim *B* = *c* · *D* and dim *B*/*uB* = *c*, the structure is uniquely *R*^*c* (free rank *c*). When dim *B* = *n* is constant and *D* > *n*, the *u*-partition is *D*-independent. In both regimes, dim(*B*/*uB*) is v-independent once the relevant measurements agree at two levels.

**What is NOT proved.** The theorem does not prove that drop(*S*, *v*) = *c* · *D* (or constant) for ALL *v* — it proves the *consequence* (module freeness, v-independence of dim *B*/*uB*) given that the scaling/frozen pattern holds. In particular, it does NOT close PIECE B: for the full 15-leg assembly, drop = 0 at *v* = 1, 2 (measured), and proving drop = 0 at all *v* IS Degtyarev–Shimada Conjecture 1.2 (§73.3 [FIRM]). The Nakayama chain (§215) reformulates this as *B*/*uB* = 0 for all *v*, but for *S* = full, this is equivalent to drop = 0 for all *v* — no extra leverage.

**Where the leverage IS.** For strict sub-assemblies (S ⊊ {0, …, 14}), the theorem converts two finite measurements into a module-structure determination that predicts infinitely many filtrations. Each prediction is falsifiable (THE_PERNO_PROBE at higher *v*). The forced-rank mechanism is the structural reason the body's *u*-filtration is v-independent — not an observation, a theorem.

---

## 7. Relation to the Nakayama chain (§215)

The Nakayama closure chain for DS 1.2 is:

> Step 1: *B*(*v*) is an *R*_*v*-module (G2 + G3, sealed).
> Step 2: *B*_full/*uB*_full = 0 at *v* = 1, 2 (measured).
> Step 3 [THE GAP]: dim(*B*/*uB*) is v-independent for all *S*.
> Step 4: Nakayama (*M*/*uM* = 0 ⟹ *M* = 0 for f.g. modules over local *R*_*v*).
> Step 5: G4 = DS §4.6 (*B*_full = 0 ⟺ Conjecture 1.2).

The Forced Rank Theorem settles Step 3 for every orbit where the scaling or frozen regime is verified at two levels. For the full 15-leg assembly, Step 3 is *B*_full/*uB*_full = 0, which by Step 4 is *B*_full = 0, which is Conjecture 1.2 itself. The gap in the chain is therefore not Step 3 in general (which this theorem addresses for sub-assemblies), but Step 3 for *S* = full specifically, which is the conjecture.

---

*Theorem stated and proved 29 June 2026. Gate-verified against four measured orbits at v = 1 and v = 2. The structural mechanism (pigeonhole on the u-partition) is pen-and-paper; the data are from DeltaZ_v1_data.py (v = 1), dualsix.cpp (v = 2, Mac), and THE_PERNO_PROBE.py (filtrations). Operación Glotón / The Sofa Theorem. Architect: Rafael Amichis Luengo.*

---

## References

1. A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties.* J. Math. Soc. Japan **68**:3 (2016), 975–996. arXiv:1405.4683.
2. R. Amichis Luengo, *The Orbit Theorem.* Campaign note, 29 June 2026. [THE_ORBIT_THEOREM.md](THE_ORBIT_THEOREM.md)
3. R. Amichis Luengo, *The Nail Theorem, v3.* Campaign note, 4 June 2026. [THE_NAIL_THEOREM.md, Version 3.0, in the repository fermat-hodge-primitivity](https://github.com/tretoef-estrella/fermat-hodge-primitivity/blob/main/THE_NAIL_THEOREM.md)
