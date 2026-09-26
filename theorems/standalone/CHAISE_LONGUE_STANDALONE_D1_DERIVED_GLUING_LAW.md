> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE DERIVED GLUING LAW AND THE INTERRUPTOR* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_D1_DERIVED_GLUING_LAW.md
>
> **Status, as written in the document:** Source of the complete derivation: CHAISE_LONGUE_MATRYOSHKA_QUADRATUM_v6 (D1, D2), audited in the Golpe-2 relay chain (CARDANO_SLACK_VERDICT_v1, CARDANO_G2_CLOSURE_AUDIT_v1). This referee edition states the law, the mechanism, and the verification record at ce…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE DERIVED GLUING LAW AND THE INTERRUPTOR
## The swap-stratum slack of the collar: `slack_swap(k; f) = C(k,2)·C(f+k−1, k−1)` for every dimension and every tower level below the branch point — and the branch switch at `f = q` as its corollary

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source of the complete derivation: CHAISE_LONGUE_MATRYOSHKA_QUADRATUM_v6 (D1, D2), audited in the Golpe-2 relay chain (CARDANO_SLACK_VERDICT_v1, CARDANO_G2_CLOSURE_AUDIT_v1). This referee edition states the law, the mechanism, and the verification record at certified grade; the full functional-by-functional derivation is in the source document, which this write-up indexes. Role: D1 is the codimension-1 layer of the Unified Slack Law of dimension six (companion standalone), i.e. the leading stratum of the sharpened collar ceilings of the Hammock Theorem.*

---

### 1. The object

In the collar of dimension `2k` (cofactor degrees `q + f`), the crude Koszul ceiling (Cascade Collapse, companion standalone) exceeds the true syzygy count by a **slack** which — this is the structural discovery of the Golpe-2 campaign, cold-audited — is an object of the **same species as the census**: it decomposes stratum-by-stratum over the flat lattice of the arrangement and composes by convolution, never by per-degree subtraction of raw values (the naive subtraction is a registered tombstone with killing numbers; see the Collar Budget standalone §4). The codimension-1 stratum consists of the swap flats — `N·k(k+1)/2` of them, each on exactly two sheets (Swap Theorem).

### 2. Theorem D1 (the law, every k, level 1)

> **Theorem D1 (Derived Gluing Law).** For `0 ≤ f < q` (level 1), the slack carried by EACH swap flat is
> **`slack_swap(k; f) = C(k,2) · C(f + k − 1, k − 1)`**
> — for every dimension `k` and every tower level `q`, with no `q`-dependence below the branch point.
*Mechanism (as derived in the source, indexed here).* On a swap flat the two sheets' pair structures differ in one exchanged 2×2 block; the gluing conditions between the two sheets' syzygy data are expressed by **dual functionals** on the flat; the exchanged block's four conditions are **symmetrized by the 4-cycle** (reducing the naive count); and at level 1 the heavy classes of the two sheets are **monomially disjoint** (a unique heavy slot, total pair-weight `q + f < 2q`), which makes the per-class constraint systems independent and the count exact rather than an inequality. The surviving discrepancy per flat is `C(k,2)` independent families, each of the dimension `C(f+k−1, k−1)` of the flat's degree-`f` functions. ∎(indexed)

> **Corollary D2 (the Interruptor).** The disjointness hypothesis fails exactly at `f = q` (a second heavy slot becomes available): the slack law **switches branch at `f = q`**, and the level-2 law is a different polynomial (in `g = f − q` and `q`), derived in the level-2 documents (Eigenvector Law standalone). The branch point is thus a THEOREM of the mechanism, not an empirical feature of the data.

### 3. Verification record
- **Dimension six, level 1:** the swap-stratum contribution `630 · 3 · C(f+2, 2)` is the leading term of the exact branch-1 identity `945f² + 350f + 1288` (Unified Slack Law standalone), verified against the measured slack at `f = 0..8` — the leading coefficient `945 = 630·3/2` is D1's prediction on the nose.
- **The branch point:** the measured slack changes law exactly at `f = q` in every dataset (`q = 3` and the indirect `q = 9` validations), as D2 requires.
- **Cross-dimension:** the same mechanism at `k = 2` feeds the Sofa's collar bookkeeping (its fixed four-degree band), consistent with the sealed Sofa collar data.
- **Audit:** the law and its role in the branch-1 identity passed the Golpe-2 cold audits (byte-exact re-derivations; the "subtraction of raw ceilings" alternative was buried by the same audits).

### 4. Attack surface
(A) The disjointness step (`f < q` ⟹ unique heavy slot ⟹ independent classes): re-derive the pair-weight inequality and check no boundary case at `f = q − 1` leaks. (B) The 4-cycle symmetrization count (why `C(k,2)` families and not `k(k−1)` — the symmetrization halves; the source's functional table is the place to fire). (C) The flat function-space dimension `C(f+k−1, k−1)` (the swap flat has dimension `k`; verify the degree bookkeeping of the discrepancy families lands in degree `f`). (D) External: any error in D1 shifts the `945` of the branch-1 identity, which is pinned by nine measured points and by the closure of the full law against both tower rungs.

**Anchors.** CHAISE_LONGUE_MATRYOSHKA_QUADRATUM_v6 (full derivation) · CARDANO_SLACK_VERDICT_v1, CARDANO_G2_CLOSURE_AUDIT_v1 (audits) · GOLPE2_CLOSURE_EIGENVECTOR_LAW_v1 (level 2) · Unified Slack Law standalone (the assembly). github.com/tretoef-estrella.
