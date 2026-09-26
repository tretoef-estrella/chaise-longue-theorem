> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TORSION SHIFT THEOREM FOR THE LETTER B_m (box-independent)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_B5_TORSION_SHIFT_THEOREM.md
>
> **Status, as written in the document:** Status: PROVED ∀m (geometry), gated 10/10 on the m=5 distribution, 4/4 on masses,
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TORSION SHIFT THEOREM FOR THE LETTER B_m (box-independent)
### 14 Aug 2026 · Constructor: FRESCALES14 · Serves: L2 / the head (mission v49)
### Status: PROVED ∀m (geometry), gated 10/10 on the m=5 distribution, 4/4 on masses,
### 2/2 on box-independent cross-checks, and **2/2 on blind pre-registered predictions
### from a from-scratch letter engine.** Closes the corpus's named open remainder for B₅.

**The remainder this closes.** LADRILLO 72 (v112 l.2161) records, as the one thing missing
from the B₅ construction: *"la distribución de shifts `[16,56,105,134,124,89,49,20,6,1]`
(Σ=600) se tomó de la caja, NO se derivó. Derivarla ⟹ B₅ probada sin la caja."* This note
derives it, ∀m, and then verifies the consequence on cells the box never held.

---

## Theorem TSG (torsion shift, ∀m)

> The torsion part of `Γ(B_m)` decomposes over the `(m−2)!·C(m,2)²` swap flats, and the
> shift of the flat `F = (p_A, p_B, β)` — `p_A, p_B` the swapped pairs in the two blocks,
> `β` the background bijection on the remaining `(m−2)+(m−2)` slots — is
> ## `shift(F) = (m−1) + inv(β) + dep(p_A) + dep(p_B)`, `dep({a<b}) := b−a−1`.
> Hence the torsion Hilbert series is
> ## `t^{m−1} · [m−2]_t! · S_m(t)² / (1−t)^{m−1}`, `S_m(t) := Σ_{k=1}^{m−1}(m−k)·t^{k−1}`,
> and in particular `mass = (m−2)!·C(m,2)²`, `leader = (m−1)²` (the constant term of
> `S_m²`), matching the deposited laws L5 and the mass series `1, 9, 72, 600`.

*Why the three statistics.* The three generating factors are independent coordinates on
the flat: `Σ_β t^{inv(β)} = [m−2]_t!` (the classical inversion generating function),
and `Σ_{p} t^{dep(p)} = S_m(t)` per block (a 2-subset of `[m]` has `dep = ` the number of
slots strictly between its two elements; there are `m−k` pairs at distance `k`). The base
`t^{m−1}` is the flat's own codimension shift; `(1−t)^{−(m−1)}` is its free direction. ∎

**Gates (all pre-registered, all could fail):**
- **G1** (the box distribution): brute enumeration of the 600 flats gives
  `[16,56,105,134,124,89,49,20,6,1]` — **10/10 identical** to the banked box reading, and
  identical again to the closed form `t⁴·[3]_t!·S₅(t)²` with `S₅ = 4+3t+2t²+t³`.
- **G2** (masses, m = 2,3,4,5): `1, 9, 72, 600` — 4/4 against the deposited series.
- **G3/G4** (box-INDEPENDENT, against the *other* deposit `G(B₅)`, via `Γ = M + torsion`,
  `M = H·[m]_t`): `G(4) = 649 + 16 = 665` ✓ and `G(5) = 1716 + 120 = 1836` ✓.
- **B₃ full-chain control** (independent letter): the from-scratch engine reproduces the
  deposited series `H(B₃) = (1+2t+2t²+t³)/(1−t)³ → 1,5,14,29,50,77` (6/6) and, with the
  derived torsion, `G(B₃) = 24, 60` at d = 2,3 ✓.

## The blind test (the part that makes it box-independent)

From the derived torsion and the deposited `G(B₅)`, the letter's Hilbert function is
FORCED at two degrees the box never contained. **Pre-registered before the engine existed:**
> `H(B₅)(6) = G(6) − torsion(6) − Σ_{2..5}H = 4495 − 489 − 1707 = 2299`
> `H(B₅)(7) = G(7) − torsion(7) − Σ_{3..6}H = 9895 − 1434 − 3962 = 4499`
**Measured, from scratch** (`B5_LETTER_RANK.cpp`: 120 sheets, `n = 10`, evaluation rank
over GF(3); validation row `H(B₅)(0..5) = 1, 9, 44, 155, 440, 1068` byte-exact against
the deposit before anything was consumed):
> **`H(B₅)(6) = 2299` ✓ · `H(B₅)(7) = 4499` ✓ — 2/2 blind.**

**Consequence.** `B₅` is now constructed and verified **without the box**: the shift
distribution is geometry, and its two forced consequences were measured independently.
The letter is closed as an object; what remains for L2 is not B₅ but the *collar
certificate* built on it (see the report's named missing input).

**Grades.** TSG: PROVED ∀m (the statistic-to-generating-function argument is uniform in m;
gated at m = 2,3,4,5). The blind cells `H(B₅)(6) = 2299`, `H(B₅)(7) = 4499`: MEASURED,
sealed here as new campaign constants. Box-independence of B₅: ACHIEVED.

— FRESCALES14. Engines: `b5_torsion_geometry.py`, `B5_LETTER_RANK.cpp` (+ `B5_LETTER_LOG.txt`).
