# 1 October 2026 — Theorem A and Kostant's theorem: a correction of attribution

**What happened.** Versions 3 to 8 of the paper presented Theorem A,

`dim_F F[x_1, …, x_n]/(e_1, e_3, e_5, …; x_1^q, …, x_n^q) = n!·[y^n] e^y I_0(2y)^{(q−1)/2}`  (char `F ≠ 2`, `q` odd),

as new for every odd `q`, and named as precedent only the case `q = 3` (Steinberg modules, tilting theory). On 1 October 2026, while studying the graded structure of this ring, we found that **in characteristic 0 the statement follows from a classical theorem of Kostant (1963)**. Version 9 of the paper says so (Remark 8.4). Theorem A is not used in the proof of the Main Theorem, so nothing about Conjecture 1.2 is affected.

## The dictionary

Let `q = 2m + 1` and `V = F[x]/(x^q)` over a field of characteristic 0, with the form `⟨x^a, x^b⟩ = (−1)^a` if `a + b = q − 1` and `0` otherwise.
- The form is symmetric and nondegenerate, and multiplication by `x`, call it `e`, is skew. So `e` is a principal nilpotent element of `so(V) = so_{2m+1}`.
- Its centralizer is spanned by the odd powers `e, e^3, …, e^{2m−1}`. These are the exponents of type `B_m`.
- On `V^{⊗n} = F[x_1..x_n]/(x_i^q)`, the element `e^j` acts as multiplication by the power sum `p_j`, and in characteristic 0 the odd power sums and the odd elementary symmetric polynomials generate the same ideal.

So the ring of Theorem A is the space of coinvariants of the centralizer of a principal nilpotent element on the `n`-th tensor power of the vector representation of `so_{2m+1}`.

## Kostant's theorem

For a rational module `W` whose weights lie in the root lattice, `dim W^{𝔤^x}` is the same for every regular `x` (B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963); we read the statement in V. Ginzburg, arXiv:math/9803141, Proposition 4.2, not in the original). At a regular semisimple `x` this is the dimension of the zero weight space. The weights of `V` are `0, ±ε_i`, so the zero weight space of `V^{⊗n}` has one basis vector for each closed walk of length `n` on `Z^m` with steps `0, ±ε_i`. Their number is the right-hand side of Theorem A.

## What is Kostant's, and what is the paper's

| | whose |
|---|---|
| the count in characteristic 0, every odd `q`, every `n` | **Kostant's theorem**, through the dictionary above |
| the dictionary itself | we did not find it written; it is elementary |
| the count in every characteristic `p ≠ 2`, with no condition relating `p` and `q` | the paper (Theorem A, Appendix A) |
| no odd torsion in `Z[x]/(e_odd, x_i^q)` | the paper (Corollary 8.2) |

In characteristic `p` the argument above is not available: Newton's identities divide by odd integers, and Kostant's theorem is a statement in characteristic 0. Over any field in which 2 is invertible the ring is still a space of coinvariants: of the orthogonal transformations `(1 + te)(1 − te)^{−1}`, which act on `V^{⊗n}` as multiplication by `Π(1 + t x_i)/(1 − t x_i)`. Theorem A says that these coinvariants have the dimension of the zero weight space in every characteristic `≠ 2`. We do not know a version of Kostant's theorem in positive characteristic that gives this.

## Why the literature search had missed it

The search of the same morning looked for the ring: «odd elementary symmetric», «Hilbert–Kunz», «power sums». The object has a classical name that contains none of these words.

## Found the same day, computed and not yet written up

These are recorded here with their date. They are measured, not claimed as theorems, and will be written up separately. The engines and logs are in [engines/theorem-a-kostant/](../../engines/theorem-a-kostant/).

1. **The Hilbert series.** In 27 cells `(q, n)` with `3 ≤ q ≤ 13`, the Hilbert series of the ring is `Σ_λ c_λ t^{mn} m^0_λ(1/t)`: the sum, over the irreducible constituents of `V^{⊗n}`, of Lusztig's `t`-analogues of the zero weight multiplicity, reversed. In 56 cases the graded character of the symmetric group is given by the same formula, with the multiplicity spaces in place of the multiplicities. In characteristic 0 this is what the theory of generalized exponents predicts.
2. **The ideals of the proof are weight spaces.** Take the set of walks of length `n` that end at a weight `μ`, as a set of points, and the ideal of the top-degree forms of the polynomials that vanish on it; for `μ = 0` it is the ideal of Theorem A, and in general these are the ideals that the induction of Appendix A runs over. Its Hilbert series is the same sum, with Lusztig's analogue at the weight `μ` in place of `0`: 18 profiles computed directly from the points, and 133 through the statistic of item 3.
3. **A statistic on walks.** Read a closed walk from its end. At each step, rank the possible last steps by the number of walks that reach the previous position, largest first, and add the ranks. The generating function of this statistic over closed walks is the Hilbert series (40 of 40 cells). It follows from the row structure proved in Appendix A. For `q = 3` it reads: `n` minus the number of times the walk is at `0` having come from `0` or from `−1`.
4. **Even `q`.** For `q = 2m` the same dictionary gives the symplectic Lie algebra `sp_{2m}`. In characteristic 0 and for even `n`, Kostant's theorem gives the number of closed walks on `Z^m` with steps `±ε_i`. In 8 cells, the dimension in characteristics 3, 5 and 7 equals the dimension in characteristic 0, and for odd `n` it is the number of walks from `0` to `ε_1`. A proof in characteristic `p` is open (§13, problem 6, of version 9).

*Rafael Amichis Luengo, with Claude (Anthropic) as assistant and auditor. Not refereed.*
