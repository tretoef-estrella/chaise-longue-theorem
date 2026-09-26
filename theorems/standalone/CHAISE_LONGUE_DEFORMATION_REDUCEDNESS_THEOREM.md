> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE — STANDALONE THEOREM: DEFORMATION_REDUCEDNESS_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEFORMATION_REDUCEDNESS_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE — STANDALONE THEOREM: `DEFORMATION_REDUCEDNESS_THEOREM_v1`
### GAP 3 is the reducedness of one explicit deformation, localized to a single point, with an exact measure.
### Lacassagne · char `p ≠ 2`, `q` odd · over a perfect field `K` (e.g. `\bar F_3`) · never `A≤P`
### Built on: `ODD_SYMMETRIC_GENERATION` (v63, `E=(e_1,e_3,…,e_{2k+1})` radical, point count), `NEGATION_DEFORMATION_THEOREM` (v64, `A = P + length(ε-torsion)`), and standard commutative algebra. Gated `k=1,2, q=3`.

## Setup
Let `q` be odd, `char K ≠ 2`, `k ≥ 1`, `n = 2k+2`, `S = K[x_1,…,x_n]`, `E = (e_1,e_3,…,e_{2k+1})` (odd
elementary symmetric CI). Let `Λ ⊂ \bar K` be **negation-closed** with `|Λ| = q` (for the prime field,
`Λ = {0, ±1, ±2, …}` reduced mod `p`; note `∏_{λ∈Λ}(x−λε) ≡ x^q − ε^{q-1}·(…)`, and at `ε=0` it is `x^q`). Put
```
        φ_i(x,ε) = ∏_{λ∈Λ} (x_i − λ ε) ∈ K[x_1,…,x_n, ε],
        B = K[x_1,…,x_n, ε] / ( E + (φ_1,…,φ_n) ),   graded by  deg x_i = deg ε = 1.
```
Then `B/(ε)` is the GAP-3 algebra `A = S/(E + m^{[q]})` (since `φ_i|_{ε=0} = x_i^q`), so `A_k(q) = dim_K B/(ε)`,
and the generic fibre `B/(ε-c)`, `c ≠ 0`, is the `P_k(q)` negation-closed points.

## Theorem
**(1) Localization / `R0`.** `B` is smooth (hence reduced) away from the irrelevant maximal ideal `m=(x,ε)`;
`Sing(B) = {origin}` (codimension one in `B`), and `B` is generically reduced.
*Proof.* For `ε ≠ 0`, `x_i ↦ x_i/ε` identifies the fibre with `{x : e_{odd}=0, x_i ∈ Λ}` = the `P_k(q)`
negation-closed points, which are **distinct and reduced** (v63 + the point count). Hence `B[1/ε]` is reduced;
geometrically `V(B)` is `P_k(q)` distinct lines through the origin, each smooth, pairwise meeting only at the
origin. So `B` is smooth off the origin and `Sing(B) = {origin}`, codim 1 ⟹ `B` is `R0`. ∎

**(2) Equivalence (the reducedness criterion).** The following are equivalent:
```
   (a) A_k(q) = P_k(q)                          [GAP 3 / the ceiling, at (k,q)]
   (b) ε is a non-zero-divisor on B             [flatness of the family over K[ε]]
   (c) B is reduced
   (d) E + (φ_1,…,φ_n) is a radical ideal
   (e) B is Cohen–Macaulay  (⟺ depth_m B ≥ 1 ⟺ Serre's S1)
```
*Proof.* `(a)⟺(b)`: `A = P + length(ε\text{-torsion})` (v64), so `A=P ⟺` no `ε`-torsion `⟺ ε` NZD. `(b)⟹(c)`:
`ε` NZD ⟹ `B ↪ B[1/ε]`, reduced by (1); a subring of a reduced ring is reduced. `(c)⟺(d)`: tautology.
`(c)⟹(b)`: if `B` is reduced then `Ass(B) =` its minimal primes = the `P` line-primes; `ε` vanishes only at the
origin, so `ε` lies in none of them, hence is a NZD. `(b)⟺(e)`: `B` is `1`-dimensional and `R0` by (1); for such a
ring `depth_m B ≥ 1 ⟺ S1 ⟺` CM, and a degree-one NZD exists iff `depth ≥ 1`; `ε` NZD gives `depth ≥ 1`, and
`depth ≥ 1` with `R0` gives reduced, hence `ε` NZD. ∎

**(3) Exact measure of the "arruga".**
```
        A_k(q) − P_k(q)  =  length_K  H^0_m(B)  =  length of the embedded component of (E+φ) at the origin.
```
*Proof.* `A − P = length(ε\text{-torsion})` (v64); the `ε`-torsion is `H^0_{(ε)}(B)`, supported at the origin by
(1), hence equals `H^0_m(B)`, the finite-length local cohomology = the embedded component at the origin. ∎

## Corollary (GAP 3 localized to one point)
> **The ceiling `A_k(q) ≤ P_k(q)` is equivalent to `H^0_m(B) = 0` — the single geometric statement that the
> `P_k(q)` concurrent lines carry no embedded fat point at their common origin** (equivalently, that `E` and the
> Frobenius grid `V(φ)` meet with no excess at the origin). The **floor `A ≥ P` is recovered for free** by
> upper-semicontinuity of fibre length (the special fibre can only be larger).

## Remark (genericity — NOT part of the theorem, stated honestly as a heuristic)
For a generic negation-closed grid the flat limit is reduced; the non-reduced locus in the space of grids is
closed, so GAP 3 asks whether the *specific* Frobenius grid lies in that closed locus. This is a framing, not a
proof: the Frobenius grid is a special (non-generic) point and its reducedness `∀k` is exactly the open content.

## What this does and does not do
**Does:** turns GAP 3 into the reducedness of ONE explicit ideal; **localizes it to a single point** (the origin),
with the defect measured exactly as `length H^0_m(B)`; recovers the floor for free; opens fresh tools
(radicality, saturation, local cohomology, linkage) not previously used on this gap. **Does not:** prove the
reducedness at the origin for the specific Frobenius grid at any `k ≥ 2` — the origin is a genuinely singular
point (the Jacobian has rank 1 there: only `e_1` is linear, while `e_{≥3}` and `φ_i` start in degree 3), so the
smoothness/Jacobian criterion is blind to it. **`G = 3` unchanged.**

## Gate (`verify_sing_locus.py`, `force_the_wrinkle.py`, GF(3))
`k=1,2, q=3`: generic fibre `= P_k` distinct reduced points (`19, 141`); special fibre `= A_k` (`19, 141`);
`H^0_m(B)` length `= A − P = 0` (no embedded point, `B` reduced); `ε`-torsion kernels `= 0` in every degree.
Positive controls only; the `∀k` reducedness at the origin is open.

— Lacassagne, Chaise Longue campaign
