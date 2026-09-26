> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE MUTE DECOMPOSITION THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_MUTE_DECOMPOSITION_THEOREM.md
>
> **Status, as written in the document:** Status: pencil-proven; every load-bearing number verified byte-exact this session (exact integer/rational arithmetic, files named, probes attached). Pending the project P0 cold gate (Ley 45).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE MUTE DECOMPOSITION THEOREM
## The wall defines a rank-13 mute lattice; every cut factors exactly into an audible block that does all norm-12 exclusion and a mute block that refunds price; the price champion is a 10+3 cut and the record's coverage budget is re-measured

**A King Pin structural theorem, built on pillars Star (i), Steel (ii), Coverage⊥Correlation (vi), and extending the Pattern Floor Theorem from the 162 chorus-blind to the full 1935 wall. New mathematics under Ley 14/15: a new invariant (the audible rank), a new fixed object (the mute lattice `K_full`), an exact multiplicative decomposition of the price, and a re-derivation of the coverage budget.**

**Status: pencil-proven; every load-bearing number verified byte-exact this session (exact integer/rational arithmetic, files named, probes attached). Pending the project P0 cold gate (Ley 45).**

---

### 0. Why this theorem (Quanta paragraph)
Why is `best_cut` so cheap, and why does every attempt to make it bite more (grafts, swaps, annihilators) explode in price? This theorem answers both with one object. The 1935 residual squirrels, viewed as linear conditions on covectors, have rank exactly **128** — so the covectors that bite *nothing* of the wall form a lattice of rank exactly **13**, the same 13 as the cut. We call it the **mute lattice**. It is astonishingly cheap (dual minima `1, 2, 5/2, …`). Every 13-cut then factors, exactly and unimodularly, into an **audible block** (the only part that excludes norm-12 vectors) and a **mute block** (invisible to the wall, but a full participant in the determinant). Measured on the price champion: `best_cut` is secretly a **10-audible + 3-mute** cut, and its mute block does not merely cost nothing — it *refunds* `5.13` bits. This converts the "12.6 bits over budget" reading of the annihilating cuts into a sharper, more hopeful accounting: the audible block of a record cut may spend up to `≈ 2^{13.2}`, not `2^{8.08}`, provided the mute refund is preserved — and `best_cut`'s audible block already kills 1022 of the 1935 for `2^{13.04}`.

### 1. The mute lattice (all numbers byte-exact from files)
Frame `L0sat` (`gram_L0sat_141_v1.txt`), dual Gram `D = 32·G^{-1}` (`dualgram_L0sat_xD.txt`). Wall = the 1935 residual norm-12 squirrels (`pitbull_TRUE_RESIDUAL_1935_v1`), matrix `M_{full} ∈ ℤ^{1935×141}`.

> **Proposition 1 (rank and the mute lattice).** `rank M_{full} = 128` (verified). Hence
> **`K_{full} := ker(M_{full}) ∩ ℤ^{141}`** — the lattice of covectors biting *no* wall squirrel — **has rank exactly 13**, and the bite pattern of any covector on the full wall determines it modulo `span(K_{full})` (same argument as Pattern Floor Prop 1, now on the full wall).
> The mute lattice is cheap: its LLL-reduced `D`-Gram has diagonal dnorm² values `1, 2, 5/2, 5/2, 2, 5/2, 3, 5/2, 5/2, 4, 9/2, 77/16, 39/8` (verified), with sublattice determinant minima over reduced-basis subsets `det₁ = 1`, `det₂ = 2`, `det₃ = 4` (dnorm² units).

**Remark (the coincidence that is not one).** `rank K_{full} = 141 − 128 = 13 = codim` of the cut. The wall's linear span has corank exactly equal to the number of slots of the cut: the mute lattice is precisely one full cut's worth of wall-invisible directions.

### 2. The audible rank and the unimodular isolation

> **Definition.** The **audible rank** of a 13-cut `Φ` is `rank(M_{full} Φ^T)` — the rank of its bite matrix on the wall. Equivalently `13 − dim(span_ℚ(rows Φ) ∩ span_ℚ(K_{full}))`.

> **Proposition 2 (isolation).** If `Φ` has audible rank `k`, there is a unimodular `V ∈ GL₁₃(ℤ)` such that `Φ′ = VΦ` has exactly `13−k` rows in `span(K_{full})` (mute rows) and `k` rows that bite. `V` changes neither the section `ker Φ ∩ V` nor the price `det(ΦDΦ^T)/32^{13}`.
> *Proof.* The mute coefficient combos `{a ∈ ℤ^{13} : M_{full}Φ^T a = 0}` form a saturated rank-(13−k) sublattice of `ℤ^{13}` (kernel of an integer homomorphism); complete a basis of it to a basis of `ℤ^{13}` (HNF completion) and let its rows be the first rows of `V`. Unimodularity preserves row lattice, hence section and determinant. ∎
> *Verification gate:* on `best_cut` the rewrite yields bite counts per row `(0,0,0,230,301,289,389,103,667,121,278,277,286)` and total price `2^{7.9069}` unchanged, byte-exact.

### 3. The theorem

> **Theorem (Mute Decomposition).** Let `Φ` be a 13-cut of audible rank `k`, isolated as in Proposition 2 with audible rows `A` (k of them) and mute rows `M` (13−k). Then, exactly:
> **`pr(Φ) = [det(A D A^T)/32^{k}] · [det(S)/32^{13−k}]`,**
> where `S` is the Schur complement of the audible block — the `D`-Gram of the mute rows projected `D`-orthogonally to the audible span. Moreover:
> **(i)** All norm-12 exclusion is done by the audible block alone: the wall survivors of `Φ` are exactly the wall vectors annihilated by `A`.
> **(ii)** `det(S) ≤ det(M D M^T)` (Schur complement of a PSD matrix is dominated by its diagonal block): the mute block never costs more than its own Gram, and can cost far less.
> **(iii)** The mute block is bounded below only by the geometry of `K_{full}` projected to the audible complement — for a *fixed* audible block, the optimal mute filler is the minimum of an exact determinant over 3-dim sublattices of the fixed rank-13 lattice `K_{full}`: a small, closed, computable problem.
> *Proof.* Gram–Schmidt block factorization of `det(Φ′DΦ′^T)` with audible rows first; (i) is the definition of mute; (ii) is PSD Schur monotonicity; (iii) is the definition of `S` with `A` fixed. ∎

> **Measured instance (the price champion unmasked).** `best_cut` has **audible rank 10** (verified: its bite matrix on the 1935 has rank 10; the mute combos include the single row `BEST[1]`, which bites nothing). Its exact decomposition:
> **`2^{7.9069} = 2^{13.0351} (audible, 10 rows, kills 1022/1935) × 2^{−5.1282} (mute, 3 rows, refund)`** — byte-exact.
> The three mute rows have dnorm² `5/2, 5, 11`, yet their projected block contributes `2^{−5.13}`: the mute block is not dead weight, it is a **refund** — the quantitative mechanism behind "cheap ⟺ correlated" (Coverage⊥Correlation), now an exact factor.

### 4. Corollaries

> **Corollary 1 (the re-budgeted coverage face).** A record cut must kill all 1935 (necessary for `min ≥ 14`, a fortiori for 24). By the theorem its price is `det_k(audible)·det_{13−k}(mute⊥)` and the audible block must do the whole kill. Hence the audible budget is
> **`det_k(audible) ≤ 2^{8.08} / det_{13−k}(mute⊥)`** — with a `best_cut`-class refund (`2^{−5.13}`), the audible allowance is `≈ 2^{13.2}`, **not** `2^{8.08}`. Measured landmarks on the audible frontier: kill 1022 → `2^{13.04}` (best_cut's audible block); kill 1927 → `≈ 2^{20.7}` (v112 annihilators, refund status unmeasured). The distance to the crown on this face is the gap between those landmarks *at fixed refund*, not the naive 12.6 bits.

> **Corollary 2 (why grafts and substitutions are expensive — the rent, measured).** Substituting any single vector into the isolated mute slot of `best_cut` was measured at `≥ 2^{12.81}` (a ~4.9-bit rent even for 6-bite vectors): naive edits do not buy audible coverage, they *destroy the refund*. Every prior frontier measurement on grafts/swaps (v111–v112) conflated the two effects; the decomposition separates them.

> **Corollary 3 (the audible Pattern Floor).** Combining with the Pattern Floor Theorem applied to the full wall: the audible block's price is bounded below by the pattern Gram determinant in the metric `H_{full}^+`, `H_{full}` = (Gram of the 1935)/32, over the rank-128 full-pattern lattice. The record's norm-12 face is therefore the joint minimization
> **`min [det_k(pattern Gram, full-kill) · det_{13−k}(optimal mute filler ⊥)] < 2^{8.08}`** — one exact, finite objective over one fixed pair of lattices (rank 128 audible, rank 13 mute).

### 5. Scope (stated straight)
- Everything here lives on the price/coverage (BOX) face; no claim touches the section minimum. Remark 5.3′ intact.
- Killing the 1935 is necessary for the record but not sufficient (`min ≥ 24` also requires the norm 14–22 strata; the mute rows, invisible to the norm-12 wall, may still be doing exclusion work on higher strata — the decomposition does not license discarding them for free at the *record* level, only at the norm-12 level).
- The `2^{−5.13}` refund is a property of `best_cut`'s specific blocks; whether full-kill audible blocks admit comparable refunds is the live measurement this theorem sets up (decompose the v112 annihilators; then optimize the filler by Theorem (iii)).

### 6. Verification record
`wall_quotient_v1/2.py` (rank 128, mute lattice minima, projected-det ⇒ singularity discovery), `mute_slot_v1.py` (audible rank 10, mute combos incl. row `BEST[1]`, unimodular rewrite gate `2^{7.9069}`, substitution rent frontier), `mute_decomp_v2.py` (saturated completion, 3 mute rows isolated, exact decomposition `2^{13.0351} × 2^{−5.1282} = 2^{7.9069}`, `K_full` minima `det₁,₂,₃ = 1, 2, 4`). Frames: `gram_L0sat_141_v1.txt`, `dualgram_L0sat_xD.txt`, `dump_planes_L0sat_960x141_v1.txt`, `pitbull_TRUE_RESIDUAL_1935_v1.txt`, `gabrieloak_best_cut_v1.txt`. Session gates re-verified: price `2^{7.906891}`, survivors `913/1935`, cb `162`.

### 7. Ley 41 certificate
Object: *the rank-13 kernel lattice of the full 1935-squirrel bite map, the audible-rank invariant of a cut, and the exact multiplicative factorization of the price into audible × mute-Schur blocks, with the measured 10+3 structure of best_cut.* Graveyard grep by object: (a) **coset reduction / rank-48 CVP** (v112) — distinct: that kernel was `ker` of the 162 chorus-blind (rank 48); this is `ker` of the full 1935 (rank 13), a different lattice with a different role (price factorization, not per-row norm reduction); (b) **product seal `2^{18.20}`** (v110) — distinct: this factorization is an exact identity (Gram–Schmidt blocks), not a product heuristic; equality holds, nothing is bounded by AM–GM; (c) **graft frontier** (v111) — distinct and *explained*: grafts measured price jumps without separating refund destruction from audible cost; the decomposition is the missing coordinate system; (d) **"better correlated cut"** (Trap v110-c) — distinct: no re-optimization of correlation is proposed; the mute lattice is a fixed structural object, and the refund is an exact Schur factor. No collision. Pending P0.

---
*Part of the Operación Glotón / King Pin corpus · github.com/tretoef-estrella · tretoef@gmail.com — Marlowe (Auditor), 10 July 2026.*
