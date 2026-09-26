> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE ORBIT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_ORBIT_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE ORBIT THEOREM

**Torsion drop on Fermat fourfolds is an invariant of the matching type**

---

## 1. Setup

Let *X* = *X*₄^*d* denote the Fermat fourfold of degree *d* in **P**⁵, defined by
*x*₀^*d* + *x*₁^*d* + ⋯ + *x*₅^*d* = 0. Write *d* = 3^*v* for the tower
levels *v* = 1, 2, 3, … relevant to the integral Hodge conjecture at the prime
*p* = 3.

The six coordinates {0, 1, 2, 3, 4, 5} label the vertices of the complete graph
*K*₆. A **perfect matching** *J* of *K*₆ is a partition of the six vertices into
three disjoint pairs. There are exactly 15 such matchings:

> *J*₀ = {01, 23, 45}, *J*₁ = {01, 24, 35}, …, *J*₁₄ = {05, 14, 23}.

Each matching *J* indexes a sublattice *R̄*_*J* ⊂ *H*₄(*X*, **Z**) of Hodge
cycles supported on the three linear subvarieties cut out by the pairs of *J*
(Degtyarev–Shimada, §4). The saturation map is the diagonal

> Δ : ⊕_*J* *R̄*_*J* → *H*₄(*X*, **Z**) / (algebraic classes),

and the **torsion** in coker(Δ) is the obstruction to the integral Hodge
conjecture (DS Conjecture 1.2).

For a subset *S* ⊆ {0, …, 14} of matchings, the **restricted matrix** Δ_*S*
is the submatrix of Δ formed by the legs in *S*. Its **drop** is

> drop(*S*) := rank_**Q**(Δ_*S*) − rank_**F**₃(Δ_*S*),

which counts the **F**₃-torsion elements contributed by the partial assembly *S*.

---

## 2. The S₆ action

The symmetric group *S*₆ acts on *X* by permuting the six coordinates:

> σ · (*x*₀, …, *x*₅) = (*x*_{σ⁻¹(0)}, …, *x*_{σ⁻¹(5)}).

This is an automorphism of *X* (the defining equation is symmetric), and it
induces three compatible actions:

**(a)** On **characters**: the Hodge-theoretic data is indexed by tuples
β = (β₀, …, β₅) with 0 ≤ β_*i* ≤ *d* − 2 and the balanced-weight condition
Σ(β_*i* + 1)/*d* = 3. The action is σ · β = (β_{σ⁻¹(0)}, …, β_{σ⁻¹(5)}).
The index sets *I*₁ and *I*₂ of DS (equations 10–12) are preserved because the
balancing condition is symmetric.

**(b)** On **matchings**: σ sends matching *J* = {(*a*₁,*b*₁), (*a*₂,*b*₂),
(*a*₃,*b*₃)} to σ · *J* = {(σ(*a*₁),σ(*b*₁)), (σ(*a*₂),σ(*b*₂)),
(σ(*a*₃),σ(*b*₃))}. This permutes the 15 matchings; since *S*₆ acts
transitively (any matching can be sent to any other), there is a single orbit
of size 15 on individual matchings.

**(c)** On the **coefficient matrix** *Q* (DS, equation 13): the entry

> *Q*_{β,β'} = ∏_{*i*=0}^{5} (ζ_*d*^{(β_*i*+1)(β'_*i*+1)} − ζ_*d*^{β_*i*(β'_*i*+1)})

satisfies *Q*_{σ·β, σ·β'} = *Q*_{β,β'} for every σ ∈ *S*₆, because the
product is simply re-indexed — the *i*-th factor maps to the σ(*i*)-th factor,
and the product of all six is unchanged.

---

## 3. The Orbit Theorem

**Theorem.** *For every tower level v ≥ 1, the drop function*

> drop : 2^{0,…,14} → **Z**_≥0

*is invariant under the S₆ action on subsets of matchings. That is, for every
σ ∈ S₆ and every subset S ⊆ {0, …, 14},*

> drop(σ · *S*) = drop(*S*).

*More precisely, the entire Smith normal form of Δ_S (and hence the full
torsion structure, not merely its F₃-rank defect) depends only on the S₆-orbit
of S.*

**Proof.** Fix a tower level *v* (hence a degree *d* = 3^*v*). The restricted
matrix Δ_*S* has rows indexed by pairs (*j*, β_*j*) where *j* ∈ *S* and β_*j*
runs over the *D*³ characters within leg *j* (here *D* = *d*/3 = 3^{*v*−1} at
*v* ≥ 2, or *D* = 1 at *v* = 1, giving *D*³ = 27 rows per leg at *v* = 1).
Its columns are indexed by the target characters β' ∈ *I*₁ ∪ *I*₂.

A permutation σ ∈ *S*₆ induces:

- a **row permutation** *P*_σ that sends row (*j*, β_*j*) to row
  (σ·*j*, σ·β_*j*), and
- a **column permutation** *R*_σ that sends column β' to column σ·β'.

By property (c) above, the matrix entries satisfy

> (Δ_{σ·*S*})_{(σ·*j*, σ·β_*j*), σ·β'} = (Δ_*S*)_{(*j*, β_*j*), β'}.

In matrix notation: Δ_{σ·*S*} = *P*_σ · Δ_*S* · *R*_σ^*T*, where *P*_σ and
*R*_σ are permutation matrices (hence unimodular, with determinant ±1).

Since the Smith normal form is invariant under left- and right-multiplication
by unimodular matrices, the invariant factors of Δ_{σ·*S*} and Δ_*S* are
identical. In particular, rank over any field *k* satisfies
rank_*k*(Δ_{σ·*S*}) = rank_*k*(Δ_*S*), so

> drop(σ · *S*) = rank_**Q**(Δ_{σ·*S*}) − rank_**F**₃(Δ_{σ·*S*})
>             = rank_**Q**(Δ_*S*) − rank_**F**₃(Δ_*S*)
>             = drop(*S*). ∎

---

## 4. Corollaries

**Corollary 1 (Finite classification).** *The drop function factors through the
orbit projection:*

> drop = *f* ∘ π,  where  π : 2^{0,…,14} → Orb(*S*₆)

*and f : Orb(S₆) → **Z**_≥0 is a function on the finite set of orbits. The
number of S₆-orbits of size-k subsets of the 15 matchings is:*

| *k* | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|-----|---|---|---|---|---|---|---|---|---|----|----|----|----|-----|
| orbits | 1 | 2 | 5 | 9 | 15 | 21 | 24 | 24 | 21 | 15 | 9 | 5 | 2 | 1 |

*Total: 154 orbits classify the torsion behavior of all 32,766 nontrivial
subsets.*

**Corollary 2 (Complement compatibility).** *The complement operation
S ↦ S^c = {0,…,14} \ S commutes with the S₆ action: σ·(S^c) = (σ·S)^c.
Therefore the complement of an orbit is an orbit, and the orbit→drop table
has a natural pairing between sizes k and 15−k. However, the complement does
NOT preserve the drop: drop(S) + drop(S^c) is not constant (takes 20 distinct
values at v = 1).*

**Corollary 3 (Full Smith invariance).** *The entire torsion type — the list of
elementary divisors of Δ_S, not merely the count of those divisible by 3 — is
an S₆-invariant. Two subsets in the same orbit produce identical Smith normal
forms.*

---

## 5. Measured orbit→drop table at *v* = 1

Computed exhaustively by the **Electron Vein Scanner** (32,766 subsets, 4.3
minutes on Mac M2, independently verified in sandbox). Gate checks: full
15-leg drop = 0 ✓, triple [7,11,13] drop = 6 ✓, sextet drop = 0 ✓. All 154
orbits monochrome (zero exceptions).

**Size 1** — 1 orbit. All 15 matchings equivalent. Drop 0.

**Size 2** — 2 orbits. Drop 0 for both (whether the pair shares an edge or not).

**Size 3** — 5 orbits:

| Orbits | Count | Drop | Graph type |
|--------|-------|------|------------|
| 3 | 375 | 0 | assorted (β₁ ≤ 3) |
| 1 | 60 | 1 | prism graphs (β₁ = 4, 2 triangles) |
| 1 | 20 | 6 | K₃,₃ coset triples (β₁ = 4, 0 triangles) |

The 20 K₃,₃ triples carry the full (Z/3)⁶ torsion body; the 60 prism triples
carry one unit of torsion; 375 triples are torsion-free.

**Size 4** — 9 orbits: drops {0: 1035, 1: 60, 3: 60, 4: 30, 5: 180}.

**Size 5** — 15 orbits: drops {0: 1707, 2: 480, 3: 180, 4: 360, 5: 180,
8: 90, 11: 6}. The 6 subsets with drop 11 are the complements of the
size-10 subsets that omit an entire K₃,₃ coset triple plus two legs.

**Sizes 6–14** — orbit counts and drop distributions as in the full scan log
(ELECTRON_VEIN_SCANNER_v1.log, archived). Key features:

- **Size 14** (remove one leg): drop = 1 for all 15 subsets (one orbit). Every
  leg carries exactly one unit of healing power.
- **Size 13** (remove two legs): 2 orbits. drops {1: 45, 2: 60}. Removing a
  pair that shares an edge costs 2; removing a disjoint pair costs 1.
- The maximum drop observed is 13, achieved by a unique orbit at size 6
  (15 subsets).

---

## 6. Remarks

**What the theorem says.** The torsion contributed by any partial assembly of
matchings depends only on the abstract combinatorial type of the assembly —
its isomorphism class under vertex relabeling — not on which specific vertices
are involved. This is a structural rigidity that holds at every tower level.

**What the theorem does not say.** It does not say that the orbit→drop map *f*
is independent of *v*. At *v* = 1 the drop of the K₃,₃ triple is 6; at *v* = 2
it is 18 (the body fattens ×3 per level, §195). The S₆-orbit is the same, but
the drop value scales. Whether the *normalized* map *f*/*D* is *v*-independent
(where *D* = 3^{*v*−1}) is an open question that, if answered affirmatively,
would give a complete combinatorial classification of the torsion at all tower
levels simultaneously.

**Relation to prior routes.** The DS §4.5 equivariance formula uses the torus
group *G* = (Z/*m*)^{*n*+2}, which fixes each matching *J* and moves the
character fibre β. That is a DIFFERENT symmetry from the S₆ of this theorem,
which moves the matchings themselves. The regular-F₃[S₃] mechanism (§197,
dead) used the graph-automorphism S₃ of K₃,₃, a SUBGROUP of S₆ restricted to
the sextet. The present theorem uses the FULL S₆ on ALL 15 matchings, which
is a strictly larger and previously unexploited symmetry of the problem.

**Potential for closure.** The Čech differential in the Mayer–Vietoris complex
is S₆-equivariant (it is built from restriction maps between intersections of
sublattices, all of which transform compatibly). Therefore the cohomology
groups Ȟ^*q* are S₆-representations. If Tors(Ȟ¹) ≠ 0, it must carry a
nontrivial S₆-action consistent with every measured constraint. Determining
which S₆-representations are compatible with the full orbit→drop table —
and whether the zero representation is the only possibility — is the natural
next question.

---

*Theorem stated and proved 29 June 2026. Measured at v = 1 by the Electron
Vein Scanner (ELECTRON_VEIN_SCANNER.cpp + matrix_data.inc). Operación Glotón
/ The Sofa Theorem project. Architect: Rafael Amichis Luengo.*
