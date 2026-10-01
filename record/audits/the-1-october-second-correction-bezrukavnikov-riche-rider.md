# 1 October 2026 — Theorem A: a second correction of attribution (Bezrukavnikov–Riche–Rider)

**What happened.** Version 9 of the paper, published earlier the same day, credited Theorem A in characteristic 0 to Kostant (1963) and said, about characteristic `p`: «We do not know a version of Kostant's theorem in positive characteristic that gives this». Two neighbouring papers were on our list of things to read, and had not been read. They were read a few hours later. **One of them contains a proposition from which Theorem A follows in every odd characteristic.** Version 10 of the paper says so (Remark 8.4(3)).

Theorem A is not used in the proof of the Main Theorem. Nothing about Conjecture 1.2 of Degtyarev–Shimada changes.

## The proposition

R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583 (read in version 2, 4 July 2024), **Proposition 2.12**:

> For any finite-dimensional `G`-module `V` which admits a good filtration and any regular unipotent element `u ∈ G`, `dim V^{Z_G(u)} = dim V^T`.

Here `G` is a connected reductive group over an algebraically closed field of characteristic `ℓ`, with simply connected derived subgroup, `ℓ` is good for `G`, and `X^*(T)/ZR` has no `ℓ`-torsion. The proof rests on results of Kumar, Lauritzen and Thomsen (1999).

## Why it gives Theorem A

The ring of Theorem A is the space of coinvariants of the centralizer of a regular unipotent element of `SO_q` on the `n`-th tensor power of the vector representation (the dictionary of the first note; it holds over every infinite field in which 2 is invertible, and over a finite field for the centralizer as an algebraic group — for the finite group of points it fails: 9 against 7 at `q = 3`, `n = 3` over `F_3`). For `G = Spin_q` and `ℓ` odd the hypotheses hold: every odd `ℓ` is good for `G`, and `X^*(T)/ZR = Z/2`. The vector representation is a simple Weyl module for `ℓ ≠ 2`, so it is tilting, and tensor products of tilting modules are tilting. So the dimension of the ring is the dimension of the zero weight space: the number of closed walks. That is Theorem A. The absence of odd torsion over `Z` (Corollary 8.2) follows from Theorem A over the fields `Q` and `F_p`, so it follows too.

## What is whose, corrected

| | whose |
|---|---|
| the count in characteristic 0 | **Kostant** (1963), through the dictionary |
| the count in odd characteristic, and the absence of odd torsion | **Bezrukavnikov–Riche–Rider** (2020), Proposition 2.12, through the dictionary |
| the same count for even `q` and even `n` (problem 6 of version 9) | the same two sources: it is no longer an open problem |
| the dictionary | this project; elementary; we did not find it written |
| an elementary proof of the count, with no algebraic groups, and the ideals `K_μ` of Appendix A, whose colength is the multiplicity of the weight `μ` (Corollary A.17 of version 10) | this project |
| **the Main Theorem (Conjecture 1.2 for odd degree), Theorem B, Theorem C** | **this project; not affected** |

The other paper, S. Riche, *Kostant section, universal centralizer, and a modular derived Satake equivalence*, arXiv:1411.3112, extends Kostant's results on the structure of the centralizers of regular elements to positive characteristic and to integral coefficients. We did not find the count in it.

## What the reading gave in return

The same dictionary applies to Theorem B, which for degree `p^v` is the algebraic form of the conjecture. Its generators `D_J` are the invariant tensors of the symplectic group `Sp_{q−1}` (the matchings of Brauer), and Theorem B says:

> the invariant tensors generate, under the commuting copies of a regular nilpotent element, a subspace of `V^{⊗(2k+2)}` whose dimension is that of the zero weight space, over every field.

With the proposition above, in characteristic `≠ 2` that subspace is the whole space of invariants of the centralizer of a regular unipotent element (Corollary 8.6 of version 10). In characteristic 0 this can also be derived from Kostant's theorem and the first fundamental theorem of invariant theory. In characteristic `p` we know no derivation from the literature.

The same statement for the orthogonal group (the box `q` instead of `q − 1`) holds in characteristic 0 and at every cell we computed. It is not proved in characteristic `p`: it is problem 7 of version 10.

Everything is written up in [paper/THE_REGULAR_CENTRALIZER_NOTE_v1.pdf](../../paper/THE_REGULAR_CENTRALIZER_NOTE_v1.pdf), with a table of what belongs to whom and a list of what was read in the original and what was not. Engines and logs: [engines/theorem-a-kostant/](../../engines/theorem-a-kostant/).

## The cold reading

The new material of version 10 and the supplementary note were read cold, before publication, by a separate instance of Claude working alone and with its own code. Verdict: holds; one gap (an inequality of Remark 8.7(3) whose argument did not cover characteristic 2), three errors (none in a proof that the paper uses), thirteen points of presentation. One of them was an under-claim: the upper bound of Theorem A.15 is an equality for every weight, which is now Corollary A.17. Another was the remark on finite fields quoted above. Report, grading and code: [record/cold-readings/12_internal-reader_on-v10/](../cold-readings/12_internal-reader_on-v10/REPORT.md).

## Why it was missed twice

The first search looked for the ring, and the object's name was «the centralizer of a principal nilpotent element». The second search looked for Kostant's theorem in characteristic 0, and the statement in characteristic `p` is written for modules with a good filtration, in a paper about perverse sheaves on affine flag varieties. The first note said «we do not know», not «there is none», and reading the two papers was the next thing done. That is the only reason the error lasted a few hours and not longer.

*Rafael Amichis Luengo, with Claude (Anthropic) as assistant and auditor. Not refereed.*
