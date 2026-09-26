> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE DIAMOND LEMMA & THE COMPLETE DIM-2 CENSUS (the k=4 tower closes)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DIAMOND_CENSUS_THEOREM.md
>
> **Status, as written in the document:** Status: Theorem DIAMOND PROVED ∀k (every flat, every level — the Architect's
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE DIAMOND LEMMA & THE COMPLETE DIM-2 CENSUS (the k=4 tower closes)
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v43 continuation, "v44" leg)
### Status: Theorem DIAMOND PROVED ∀k (every flat, every level — the Architect's
### carbón→diamante made theorem); the dim-2 census of W₂⁽⁴⁾ EXHAUSTIVE (todas las casas —
### and the walk found a THIRD class invisible to sampling); **the k=4 descent tower is now
### UNCONDITIONAL.** ∀k residue compressed further. **NO NOTES — the standing order holds.**

---

## Theorem DIAMOND (the engineered residue is diamond-grade; ∀k, every flat, pencil)

> Let G be ANY flat of the intersection lattice, W any linear complement of G. Every
> component C ⊇ G splits as `C = G ⊕ (C ∩ W)` (for `w = pr_W(c)`, `w = c − g ∈ C`), so
> the through-G configuration is the PRODUCT `G × A_G`, `A_G` a transverse linear
> arrangement in W. Every functorially-local module of the tower — `Q_loc(G)`, the star
> modules, the local matryoshka `D_loc(G)` and all its iterates — is therefore a pulled-
> back module: `(transverse module) ⊗_F O_G ≅ ⊕_e (transverse piece)_e ⊗ O_G(−e)`,
> ## a FREE graded `O_G`-module, with shifts = the transverse Hilbert function. ∎

**What this kills:** the "species objection" (v43's named gap) at the LOCAL level, forever
— cokernels of pulled-back maps are pulled back; carbon in, diamond out, by construction.
The v43 dyes HAD to pass: retroactively they verify a theorem. What Diamond does NOT
provide by itself: the per-level SUPPORT catalogs (which flats carry each level) and the
transverse shift bounds — those remain census work per level.

## The complete dim-2 census of `W₂⁽⁴⁾` (exhaustive — every house visited)

Method: all 87,990 component pairs swept (rank-5 → the 2100 seams ✓ catalog control;
rank-6 → 1750 pairwise dim-2 flats) PLUS all wall-pair intersections inside every
component — catching flats invisible to pairs. **Completeness argument (pencil):** any
dim-2 lattice element, traced inside one component through it, is cut by two wall traces
or one deeper trace — both sweeps together are exhaustive. Result:
> **2170 dim-2 flats in exactly THREE classes: through-3 (420) · through-6 (1330) ·
> through-12 (420).** The through-3 class — 420 flats, a triangle of three components
> pairwise meeting in three S-type seams — **does not arise as any pairwise intersection
> and was invisible to v43's sample.** The full walk found the third house.

## Per-class germ spectra + the k=4 tower closure

By Diamond, every class germ is FREE; the machine computed the exact shift multisets:
> through-3: rank 1, shifts (0) · through-6: rank 5, shifts (0⁴,1) · through-12:
> rank 14, shifts (0¹¹,1³) — **max shift 1 ≪ the spoiling bound k²−k−2 = 10, all
> classes, PASS.** (The (…,1³) echo of k=2's global profile recurs; recorded.)
Therefore the level-1 notary step at k=4 has ALL its hypotheses verified — census
complete, freeness theorem, shifts bounded — and the deeper floors are IH≤1-automatic:
> ## **The k=4 descent tower is UNCONDITIONAL.** k = 2, 3, 4 now all mechanism-complete.

## The sealed propina

> **`Σ over all 2170 dim-2 flats of rank(D_loc) = 420·1 + 1330·5 + 420·14 = 12950`** —
> the stable degree of the k=4 level-1 assembly, sealed BEFORE any global level-1
> computation exists. The future k=4 tower engine must reproduce it or kill the census.

## Residue ∀k after this leg

> (R-A) the per-level catalogs + shift bounds for k ≥ 5 (levels j = 1..k−3; each rung is
> now ONLY a census problem — Diamond supplies the freeness at every rung for free);
> (R-B) the bottom's isotype count (the values `2k−1`, `4k(k−1)` ∀k); gen@2k transports
> by the banked equivalence. **The notes stay unsounded: (R-A) is an unbounded ladder in
> k until a uniform census theorem lands.**

**Grades.** DIAMOND: PROVED ∀k. Census completeness at k=4: PROVED (method) + COMPUTED
(2170/3-classes). k=4 tower: UNCONDITIONAL (theorem + verified bounds). Sealed 12950:
PRE-REGISTERED. (R-A) ∀k, (R-B) ∀k: OPEN. B(d) ∀k: OPEN. Reserved phrase: not spoken.

— FRESCALES14. Engine: `diamond_census_gates.py` (sweep timings, class table, and the
seam-catalog 2100-control in the log).
