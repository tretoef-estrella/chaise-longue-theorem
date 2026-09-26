> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SHAVINGS LAW (the tail as uncovered skeleton-slices)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHAVINGS_LAW.md
>
> **Status, as written in the document:** - PROVED (framework, cited): tail = shavings `\` head-covered is MOLD minimality against the proved head.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SHAVINGS LAW (the tail as uncovered skeleton-slices)
### `CHAISE_LONGUE_SHAVINGS_LAW_v1` · standalone · char 3, F_3 only
### Rafa's metaphor: *"the metal shavings from filing the odd bars fall on the odd side; the even ones don't notice; hide the shavings, toss them discreetly in the yard."* The tail = the skeleton-slice shavings the head does not cover.

Notation as in `BUMP_FROBENIUS_STRUCTURE_v1`. Every `A_b = (s=0 head) ⊔ (s≥1 tail)`; head PROVED ∀k
(`SKELETON_LEADER_THEOREM_v1`), leader `∏x_{2i}²`. Write the skeleton by its `x_N`-slices:
`NF(e_N,E_k) = ∑_t x_N^{t}·σ_t`, where `σ_t` (a set of monomials in `x_2,…,x_{N-1}`) is a **support of the proved
skeleton** — an intrinsic, `q`-free, ∀k-known object.

## THE LAW (intrinsic — VALIDATED gen-1 at q=7 AND q=11, k=1→2; framework PROVED; ∀k CANDIDATE)
> The tail of `A_b` = `x_N^{q-1}·σ_{t(b)} \ {head-covered}` — the Frobenius stamp `x_N^{q-1}` times a proved
> skeleton slice `σ_{t(b)}`, minus the shavings divisible by a head leader (= MOLD minimality). **Both the source
> (`σ_t`, proved) and the covering (head-divisibility, proved) are intrinsic — no fitted `μ`-set.**

**Reconstruction (Gross-gated byte-exact, q=7 AND q=11, k=1→2, `gate_shavings_intrinsic.py`):**
- `σ_2={x_2²,x_2x_3,x_3²}`, `σ_3={x_2,x_3}` (k=1 skeleton slices, `q`-free).
- `tail(y_1) = x_N^{q-1}·σ_2 \ (x_2²x_N^{q-1} ⊂ head x_2²x_N²) = {x_2x_3,x_3²}·x_N^{q-1}` = the actual tail. ✓
- `tail(y_1^{q-1}y_2) = x_N^{q-1}·σ_3` (none head-covered) `= {x_2,x_3}·x_N^{q-1}` = the actual tail. ✓
Both at q=7 and q=11 — the tail is `q`-uniform (the slice is `q`-free; the stamp is `q−1`). Not a one-`q` fit.

## THE ODD-BIAS IS A COROLLARY (Rafa's yard)
The only removed shaving for `y_1` is the pure-even `x_2²x_N^{q-1}` (`x_2,x_N` even-indexed), absorbed by the even
head leader `x_2²x_N²`; the survivors carry the odd `x_3`. Where a letter's head has no matching even leader
(`y_1^{q-1}y_2`), nothing is absorbed. So "even shavings absorbed by the even head, odd ones escape to the yard" =
**exactly head-divisibility (MOLD)**, not a blanket "pure-even out."

## GRADE (honest, exact)
- **PROVED (framework, cited):** tail = shavings `\` head-covered is MOLD minimality against the proved head.
- **VALIDATED (k=1→2, q=7 AND q=11, intrinsic source):** the two gen-1 letters reconstruct exactly as
  `x_N^{q-1}·σ_t \ head`.
- **CANDIDATE (NOT proved ∀k):** (a) that the gen-1 shaving source IS the `x_N^t`-slice ∀k (needs the reduction
  cascade of `x_i^{q-1}y_2·Ω`); (b) the letter↔slice map; (c) gen-2 (`y_1²y_2` mixes `x_N^{q-2}·σ_2` with a gen-1
  bump on odd `x_3`).
- **Does NOT** close any `A_b`, the increment, GAP 3, or move `G`. `G` stays 3. **The tail law ∀k is NOT claimed
  from one `k` (death #4 avoided).**
Reference: `SKELETON_LEADER_THEOREM_v1` (source), `BUMP_FROBENIUS_STRUCTURE_v1` (the stamp), `MOLD_COLON_THEOREM_v1`
(covering).
