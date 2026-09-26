> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SHIFT BOUND: THEOREM KU, THE FINE CENSUS, AND A SEALED NUMBER'S DEATH* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHIFT_BOUND_THEOREM.md
>
> **Status, as written in the document:** Status: Theorem KU (rung k-uniformity) PROVED ∀k — (R-A) compresses from a k-indexed
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SHIFT BOUND: THEOREM KU, THE FINE CENSUS, AND A SEALED NUMBER'S DEATH
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v45, T1/T2)
### Status: Theorem KU (rung k-uniformity) PROVED ∀k — (R-A) compresses from a k-indexed
### family of censuses to ONE j-indexed sequence σ(j). The fine census REPAIRED v44's class
### table (5 classes, not 3), KILLED my own sealed 12950 (replaced: 10010, sealed), and the
### k=4 tower closure SURVIVES on complete footing. σ(j) ∀j: OPEN — the residue.
### **Standing order: conditions NOT met. NO NOTES.**

---

## Theorem KU (rung k-uniformity; ∀k, pencil)

> Let G be a flat of dim k−1−j (rung j). Its equations pin the matching EXACTLY outside a
> bounded ACTIVE slot set A (|A| ≤ 4j+6): outside A, all parameters are free and
> antipodally paired, so any component C′ ⊇ G must reproduce G's pairing there (two free
> parameters are never equal or opposite identically), and C′'s doubled pair must sit
> inside A (value collisions occur only among active slots). Hence:
> **(i)** components through G differ only in their structure ON A ⟹ through-count
> ≤ c(j), independent of k; **(ii)** the transverse germ (fan + all its sub-flats +
> grading) is one of FINITELY many j-local types, the same list for every k ≥ k₀(type);
> **(iii)** by DIAMOND, the rung-j shifts are the transverse degrees of these fixed
> types: **σ(j) is a k-independent constant per rung.** ∎

**Corollary KU.1 (the compression of (R-A)):** with the window threshold k²−k−1−j, the
whole of (R-A) reduces to the single arithmetic criterion **σ(j) < k²−k−1−j for
j ≤ k−3** — one j-indexed sequence against a quadratic. Any sub-quadratic bound on σ
closes (R-A) ∀k. Measured anchors: σ(0) = 0 (TS), σ(1) = 1 (both k = 3, 4).

## The fine census (the gate that fired and repaired the map)

The cross-k gate EXPOSED that through-count is NOT a complete fingerprint (k=3's
through-6 germ has rank 3, k=4's dyed one rank 5). Fine fingerprints (through-count +
sorted seam-through profile), full exhaustive re-census:
> **k=3 (45 flats):** (3,(2³)): 15, shifts (0) · (6,(3⁴)): 15, shifts (0³) ·
> (12,(2⁶3⁸)): 15, shifts (0¹¹,1³).
> **k=4 (2170 flats), FIVE classes:** (3,(2³)): 420, (0) · (6,(2⁹)): 280, (0⁴,1) ·
> **(6,(2³3²)): 840, (0²) — new** · **(6,(3⁴)): 210, (0³) — new** ·
> (12,(2⁶3⁸)): 420, (0¹¹,1³). Totals 2170 ✓.
**Cross-k KU verification: the three fingerprints present at BOTH k match spectra
EXACTLY, 3/3** — germ types are k-uniform on the fine fingerprint, as KU proves; the two
k=4-only types need more slots (k₀(type) = 4), as KU permits.
**All five k=4 classes: max shift 1 ≤ 10 ⟹ the v44 k=4 tower closure SURVIVES the
repair, now on complete-fine-census footing.**

## A sealed number's death (protocol, not shame)

v44's propina `Σ rank(D_loc) = 12950` was computed on the COARSE class table.
**KILLED by the fine census before any external engine consumed it.** Replacement,
sealed on the complete table:
> **Σ over all 2170 dim-2 flats of rank(D_loc) = 420·1 + 280·5 + 840·2 + 210·3 + 420·14
> = `10010`** — the stable degree of the k=4 level-1 assembly. The future engine must
> reproduce 10010 or kill the fine census.

## T2 status and the residue

T2 (the two cells ∀k by isotypes) remains BLOCKED by exactly one item: the σ(j)-bound
∀j (candidate σ(j) ≤ j, anchors 0, 1; sub-quadratic suffices). With it: bottom assembly
⟹ isotype count ⟹ (Rc)+(V) ⟹ GP ⟹ B(d) ∀k. Without it: no notes, and none are sounded.

**Grades.** KU, KU.1: PROVED ∀k. Fine census k=3, k=4: COMPUTED-EXHAUSTIVE; cross-k 3/3.
Repair + reseal (10010): EXECUTED. σ(j) ∀j: OPEN (the single named residue of (R-A)).
(R-B): OPEN, blocked by σ only. Reserved phrase: not spoken.

— FRESCALES14. Engines: `shift_bound_gates.py` (the gate that fired), `ku_fine_census.py`
(the repair; both k's, all classes, in the log).
