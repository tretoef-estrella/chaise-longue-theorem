> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026-07-11
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE EXECUTIONER ORBIT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_EXECUTIONER_ORBIT_THEOREM.md
>
> **Status, as written in the document:** Status: pencil + exact-arithmetic certificate, byte-exact this session. Pending P0 (Ley 45: independent cold re-derivation).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE EXECUTIONER ORBIT THEOREM
### A single S₆-orbit of 720 norm-12 vectors closes the entire torus-invariant sublattice program for V(4,4)-prim
**King Pin / Operación Glotón · Constructor: Bisel · Architect: Rafael Amichis Luengo · Madrid · 11 Jul 2026**
**Status: pencil + exact-arithmetic certificate, byte-exact this session. Pending P0 (Ley 45: independent cold re-derivation).**

---

## Abstract

The dimension-128 sphere-packing record attempt of Operación Glotón seeks a rank-128 primitive sublattice `S ⊂ V(4,4)-prim` (rank 141, even, `det 2¹²⁸`) with minimum `≥ 24` and price `< 2⁸·⁰⁸`. The **coordinate torus** `T = (Z/4)⁶/diag` acts on the ambient lattice through the phases of the 960 planes. A natural and powerful strategy is to seek `S` as a **`T`-invariant** section, because invariance collapses both the coverage condition and the price to per-block data — the King Pin analogue of the Sofa Theorem's Ledger. We prove this strategy cannot succeed, and identify the exact obstruction:

> **Theorem (Executioner Orbit).** There is a single `S₆`-orbit `Ω` of **720** norm-12 vectors of `V(4,4)-prim`, each supported on exactly **three** conjugate character-pair blocks, such that no `T`-invariant (nor any `H`-invariant, `H ≤ T`) rank-128 section avoids `Ω`. Consequently **no torus-invariant rank-128 section of `V(4,4)-prim` has minimum `> 12`.** The obstruction is certified combinatorially: `Ω` contains **13 pairwise support-disjoint** members (`T`-pure route) and forces **`≥ 15` disjoint merged-supports** under the coarsest subtorus `2T`, both exceeding the `13` available covector rows.

The theorem does not decide the record: it **seals one wing** (torus-invariant designs) with a certificate, mapping the search the way the Sofa campaign mapped its cemetery, and it **extracts the design law** the surviving routes must obey — winning cuts must be *block-oblique*.

---

## 1. Setup: the torus and the collapse it promises

`V = V(4,4)-prim` decomposes under `T` over rational characters `a = (a₀,…,a₅) ∈ (Z/4)⁶` with `Σaᵢ ≡ 0`, each `aᵢ ≠ 0`, modulo the diagonal. Complex conjugation acts by `a ↦ −a`; the fixed character is the **impostor** `χ* = (2,2,2,2,2,2)`, and the remaining `140` characters form **70 conjugate pairs**, giving the `T`-isotypic decomposition
```
V ⊗ Q  =  χ*  ⊕  ⊕_{j=1}^{70} B_j ,   dim B_j = 2 (rational block of a conjugate pair).
```
(Construction and gates: the `T`-action is reconstructed from the lattice data itself — the family/matching dictionary, the phase-to-edge assignment, and six commuting order-4 generators whose product is the identity on all 960 planes; the `141` characters reproduce the sealed Spectrum realization census `{(0,6):1,(1,4):30,(2,2):90,(3,0):20}` byte-exact. See THE_T_DICTIONARY_FLOOR1 and THE_CHARACTER_FLOOR2_SEAL.)

**Why invariance is tempting.** A `T`-invariant corank-13 cut `Φ` is a union of whole blocks. Its kernel is a sum of blocks; parity forces `13 = 6·2 + 1`, so an invariant cut is **six conjugate pairs plus the forced impostor row**, kernel `= 64` pairs `=` rank `128` exactly. Coverage becomes a finite hitting-set question over the 70 pairs; price becomes a product of block determinants with a 2-adic glue. Both faces collapse — *if* such a cut can cover the wall.

## 2. The wall in character coordinates

The norm-12 wall (the vectors that must be avoided for minimum `> 12`) was censused this campaign: `|A ∪ B| = 320,700` explicit vectors, plus an open Class C. Projecting every wall vector onto the 71 blocks yields its **support fingerprint**. Two facts, byte-exact:
- `46,140` wall vectors carry impostor component (auto-excluded by the forced 13th row);
- the `287,520` impostor-free wall vectors have support **width ≥ 3** over the 70 pairs, the minimum width `3` realized by exactly **720** vectors.

## 3. The executioner orbit

**Definition.** `Ω` = the 720 impostor-free width-3 wall vectors. They fall into `90` distinct support-triples, and (measured) form **one** `S₆`-orbit: every triple's three pair-characters form a ladder generated by a single **order-4 edge-character** `δ_e = (…,1,…,3,…)` (example triple, verbatim from the log: characters `(2,3,1,1,3,2)`, `(2,2,2,1,3,2)`, `(2,1,3,1,3,2)`, differing by multiples of `(0,1,3,0,0,0)`).

**Lemma 1 (pure-`T` seal).** A `T`-invariant cut covers `w ∈ Ω` iff one of `w`'s three support pairs is among the six chosen. `Ω` contains **13 pairwise support-disjoint** triples — explicit witnesses `(1,23,60), (2,17,21), (4,27,58), (5,25,37), (6,29,67), (7,48,50), (9,31,53), (11,32,44), …` — each demanding a distinct chosen pair. Hence covering `Ω` needs `≥ 13` pairs, but only `6` are available. **No pure-`T` cut covers `Ω`.** ∎

**Lemma 2 (subtorus seal).** For a subtorus `H ≤ T`, characters merge by their `H`-reduction; a cut may then take whole merged components. Under the coarsest `H = 2T` the 70 pairs merge into `31` components (15 of dim 2, 15 of dim 6, one of dim 20). Measured: **0** of the 90 triples become intra-component, and `Ω`'s merged supports contain **`≥ 15` pairwise-disjoint** ones — exceeding 13 rows again. **No `2T`-invariant cut covers `Ω`.** ∎

**Lemma 3 (every subtorus, by the ladder).** To merge a triple, `H` must annihilate its generating `δ_e`. Since `Ω` is `S₆`-symmetric, its triples realize **all 15 edge-characters** `δ_e`, and the `δ_e` generate the full even-character group. Merging every triple therefore forces `H = 1` (no invariance left); any proper `H` leaves a subfamily of triples unmerged, and by the `S₆`-symmetry that subfamily still contains `> 6` disjoint supports. **No nontrivial `H`-invariant cut covers `Ω`.** ∎

**Theorem.** By Lemmas 1–3, no torus-invariant (pure or partial) rank-128 section avoids `Ω`; since every member of `Ω` has norm 12, every such section has minimum `≤ 12`. ∎

## 4. What the seal delivers (Ley 42)

A sealed route with a clean certificate is first-class progress — the Sofa campaign closed its cemetery street by street before the living path appeared. This theorem yields:
1. **The design law:** winning cuts must be **block-oblique** (rows mixing many characters); every block-aligned scheme meets the executioner. `Ω` joins the wound oracle as a fast rejection gate for all future designs.
2. **The permanent instruments:** the `T`-dictionary, the 141-character table, the wall's full support fingerprints.
3. **The named live wings:** `S₆`-symmetric (torus-oblique) designs — the untouched symmetry factor — and free oblique design instrumented by the character tables. Each wing that closes with certificate strengthens the eventual impossibility theorem, should the crown not exist at budget `2⁸·⁰⁸`.

## 5. Ley 41 certificate
Object: *the 720-vector width-3 orbit `Ω` and its role sealing all torus-invariant rank-128 sections.* Graveyard grep by object: the invariant route was never before reduced to a single orbit; prior seals (flat curve, kill-8 mirage, mute-refund) concern price and local repair, distinct objects. No collision. The witnesses and character ladders are byte-exact in this session's logs; independent cold re-derivation is **pending P0**.

---
*Part of the Operación Glotón / King Pin corpus · github.com/tretoef-estrella · Constructor: Bisel.*
