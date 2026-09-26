> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TRANSVERSE ZOOM: THE SEAM CATALOG AND THE LOCAL LADDER* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TRANSVERSE_ZOOM_THEOREM.md
>
> **Status, as written in the document:** Status: Theorem SC (the seam catalog) PROVED ∀k, gate-verified by brute lattice
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TRANSVERSE ZOOM: THE SEAM CATALOG AND THE LOCAL LADDER
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v40, T1/T3)
### Status: Theorem SC (the seam catalog) PROVED ∀k, gate-verified by brute lattice
### enumeration at k = 2, 3 (after catching a dedupe bug in my own gate — the pencil
### stood, the machine was wrong); germ k-uniformity PROVED (D2 clear); the local-cohomology
### ladder PROVED (T3's identification). T2 NOT reached. **GAP 5 NOT closed. No shout.**

**Setting.** `Q = (⊕_C O_C)/O_{W₂}`, seams := the (k−1)-dimensional flats of the
intersection lattice of `W₂`. From v39: the two cells live on `Ext^{k+1}(Q, ω_S)`; the
window parameter is the prime-filtration twist over the seams.

---

## Theorem SC (the seam catalog, ∀k) — T1 Step 1, the heart

> Every (k−1)-dimensional flat of `W₂` is of exactly one of two types:
> **TYPE T ("3+1"):** `{x_P = t (|P| = 3), x_n = −t, antipodal pairs on the rest}` —
> count `C(2k,3)·(2k−3)·(2k−5)!!`; contained in exactly **3** components (the three
> choices of doubled pair inside P); local length of Q along it = **2**.
> **TYPE S ("swap wall"):** `{x_c = x_d = t; a 4-set Y split into two antipodal 2-sets
> at ±u; antipodal pairs on the rest}` — count `C(2k,2)·C(2k−2,4)·3·(2k−7)!!` (empty at
> k = 2); contained in exactly **2** components (the two matchings of Y refining the
> split); local length = **1**.

*Proof sketch (full case analysis in the body of the argument).* A (k−1)-flat equals a
pairwise intersection `C ∩ C′` (it lies in ≥ 2 components, and distinct k-planes meet in
dim ≤ k−1). Same doubled pair: matchings differing by one swap impose the single wall
`u_i = ±u_j` (Type S); more swaps drop dimension further. Doubled pairs sharing one index:
the collision `t = ±u_i` is the single wall exactly when the second component's remaining
matching conditions coincide with it — yielding the 3+1 locus (Type T); all other
configurations (shared matched pair ⟹ `u_i = 0` plus more; disjoint doubled pairs)
impose ≥ 2 conditions. Local lengths = (#components through) − 1. ∎

**Gates (pre-registered; the brute-force lattice enumeration could kill any line):**
k=2: 4 seams, all T, 0 S, no other through-multiplicities — PASS. k=3: 105 = 60 T + 45 S,
no others — PASS. Cross-checks against the banked leading terms of HF(Q):
`deg Q = 2·#T + 1·#S = 8 (k=2) and 165 (k=3)` — both PASS, byte-exact against v39's
dye-tables. **Bug log (owed):** the first run reported double T-counts; the cause was a
non-canonical RREF in MY dedupe (no back-reduction) — the same partial-reduction family
as v36V2's extractor bug; fixed, re-run, pencil unchanged.

## Corollary SC.1 (germ k-uniformity — T1 Step 3; D2 does NOT fire)

Transversally, the T-star is **three k-planes through a common (k−1)-plane** and the
S-star is **two k-planes through a common (k−1)-plane** — at every k the same two germs
(the k=2 T-line picture and the plain wall), thickened by `A^{k−2}` along the seam. The
star library needs no new fundamental object; the k-dependence of the endgame lives ONLY
in (i) the closed orbit counts above and (ii) the RELATIVE twist of the germ along the
seam (the "rotation of the mosaic tile"), which is the named open mechanism of Step 2.

## Step 2 — partial, with a fit-refusal recorded (the miopía guardrail, applied to myself)

Pointwise, the T-star's transverse Q-profile is length 2 concentrated at transverse
degree 0 (three concurrent lines in the transverse slice) and the S-star's is length 1.
The AMBIENT twists are governed by the rotation along the seam. **Fit-refusal:** the
naive uniform model (T-spectrum `(c₁,c₂)`, S-twist `c₃` with per-seam constancy and no
lower-dimensional filtration pieces) forces `4(c₁+c₂) + 3c₃ = 18` at k=3 and then an
EMPTY window at the target degrees — contradicting the nonzero anchors. Killed by
arithmetic before use; the correct bookkeeping must include the lower-dimensional
filtration pieces (dim ≤ k−2) that the collapse Theorem VP removes from Ext but NOT from
Hilbert-function additivity. The rel-twist computation is the remaining Step-2 content.

## Theorem LL (the local-cohomology ladder — T3's identification, ∀k, pencil)

From `0 → S/I → ⊕_C S/C → Q → 0` and `H^i_m(S/C) = 0` for `i < k`:
> `H⁰_m(Q) ≅ H¹_m(S/I(W₂))` and `H^i_m(Q) ≅ H^{i+1}_m(S/I(W₂))` for `1 ≤ i ≤ k−2`.
Hence the vanishing hypothesis (a) of Theorem DL is EXACTLY:
> **`H^i_m(S/I(W₂))_d = 0` for `2 ≤ i ≤ k−1` at `d = k²−2k` and `k²−2k−1`** —
Link 3's CM question localized to two degrees and two cohomological indices. The banked
torsion probes (`H⁰(Q)₀ = 0` at k = 2, 3) are its first floors. The k=3 `H¹(Q)`-probe
requires an Ext-resolution engine (named as the next machine task; not built this turn —
no written pencil step consumed it yet).

## Status of the endgame after v40

> Landed ∀k: the seam catalog (counts, multiplicities, lengths), germ uniformity, the
> ladder. Open: the rel-twist spectra (Step 2), the two character counts (T2), the
> two-degree vanishing (T3). The residue is unchanged in SUBSTANCE from v39 —
> (a), (b), (c) — but its geography is now fully mapped: everything lives on two
> k-uniform germs with closed orbit counts.

**Grades.** SC, SC.1, LL: PROVED ∀k (gates PASS after the bug-catch; pre-registrations
untouched). Step 2 rel-twists: OPEN (fit-refusal recorded). T2 cells: OPEN. (a): OPEN
(reformulated by LL). B(d) ∀k: OPEN. Reserved phrase: not spoken.

— FRESCALES14. Engine: `seam_catalog_gates.py` (same turn; the gate that fired, the fix,
and the pass are all in the log).
