> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE ODD-ELEMENTARY COMPLETE INTERSECTION THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ODD_ELEMENTARY_CI_THEOREM.md
>
> **Status, as written in the document:** With piece (2) (Key Lemma) giving `Hilb(S/J) = prod(1−t^{2j+1})/(1−t)^{2k+2}` (PROVED forall k), this CI
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE ODD-ELEMENTARY COMPLETE INTERSECTION THEOREM
### CHAISE_LONGUE_ODD_ELEMENTARY_CI_THEOREM_v1 · standalone · PROVED forall k

**Theorem.** Over any field κ with char κ ≠ 2, in S = κ[x_1,…,x_{2k+2}] the odd elementary symmetric
polynomials `E = (e_1, e_3, e_5, …, e_{2k+1})` (k+1 generators, degrees 1,3,…,2k+1) form a **regular
sequence**; i.e. E is a **complete intersection** of codimension k+1. Consequently
    **Hilb(S/E) = prod_{j=0}^{k} (1 − t^{2j+1}) / (1 − t)^{2k+2}.**

## Proof (uniform in k)
S is Cohen–Macaulay, so k+1 homogeneous elements form a regular sequence **iff** the ideal they generate
has height (codimension) k+1. We compute `codim V(E)` over κ̄.

For x = (x_1,…,x_{2k+2}) put `P_x(t) = prod_i (1 + x_i t) = sum_{j=0}^{2k+2} e_j(x) t^j`. The generators
e_1,e_3,…,e_{2k+1} are **all** the odd-indexed elementary symmetrics (2k+1 is the largest odd ≤ 2k+2).
Hence
    x ∈ V(E)  ⟺  e_1(x)=e_3(x)=⋯=e_{2k+1}(x)=0  ⟺  P_x(t) is even in t  ⟺  P_x(t)=P_x(−t)
             ⟺  prod_i(1+x_i t) = prod_i(1−x_i t)  ⟺  {x_1,…,x_{2k+2}} = {−x_1,…,−x_{2k+2}} as multisets.
(The last step: a monic-in-form product prod(1+x_i t) determines and is determined by the multiset {x_i};
prod(1−x_i t) is the same construction for the multiset {−x_i}.)

The multisets fixed by negation are exactly those of the form (after permutation)
`(a_1,−a_1, a_2,−a_2, …, a_{k+1},−a_{k+1})`, a_i ∈ κ̄ (each value paired with its negative; 0 self-pairs).
The parametrizing map κ̄^{k+1} → 𝔸^{2k+2}, (a_1,…,a_{k+1}) ↦ (a_1,−a_1,…,a_{k+1},−a_{k+1}) has image of
dimension k+1, and V(E) is the union of the finitely many S_{2k+2}-coordinate-permutation translates of
this image; so **dim V(E) = k+1**, hence `codim V(E) = (2k+2) − (k+1) = k+1 = #generators`. Therefore E is
a regular sequence and a complete intersection. The Koszul resolution of a regular sequence of degrees
1,3,…,2k+1 gives `Hilb(S/E) = prod_{j=0}^{k}(1−t^{2j+1}) / (1−t)^{2k+2}`.  ∎

## Verification (numeric, byte-exact)
`Hilb(S/E)[0..8]` vs the CI prediction prod(1−t^{2j+1})/(1−t)^{2k+2}:
- k=2: [1,5,15,34,65,110,170,245,335] — MATCH.
- k=3: [1,7,28,83,203,433,833,1477,2451] — MATCH. [ci_check.py]

## Consequence for part (B) (grade honesty)
With piece (2) (Key Lemma) giving `Hilb(S/J) = prod(1−t^{2j+1})/(1−t)^{2k+2}` (PROVED forall k), this CI
theorem makes **`Hilb(S/E) = Hilb(S/J)` UNCONDITIONAL forall k** by two independent proofs. It does **NOT**
by itself prove `in(E)=J`: initial ideals of CIs need not be CIs (indeed in(E)=J has Σ C_i minimal
generators, far more than k+1), so a containment (`in(E)⊆J` or `J⊆in(E)`) is still required. The CI
structure (Gorenstein S/E, Koszul syzygies the only relations) is the natural engine for the remaining
independence/triangularity step of Route 2.

**Grade: PROVED forall k (char ≠ 2).** Does NOT close part (B), the s=0 block, or GAP 3.
