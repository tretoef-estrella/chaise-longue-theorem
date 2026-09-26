> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026-06-29
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE TEN HEN-HOUSES THEOREM (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_TEN_HEN_HOUSES_THEOREM.md
>
> **Status, as written in the document:** Status: byte-exact at `v = 1`, domain-bounded explicitly to PIECE B (= dim-1
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE TEN HEN-HOUSES THEOREM (v2)

**The v=1 PIECE B dirty torsion is housed, byte-exact, inside the 10 K_{3,3}
bipartite sextets of K_6 — not just balanced, but geometrically contained
WITHIN THE DIM-1 §182 DOMAIN.**

---

**Author**: this Claude (single-Claude session, dual hat Auditor + Constructor)  
**Architect**: Rafael Amichis Luengo  
**Date**: 29 June 2026 — v2 revision after Blas (Auditor) review  
**Status**: byte-exact at `v = 1`, domain-bounded explicitly to PIECE B (= dim-1
§182 strata). Sealable as a v=1 lemma. The all-`v` lift is a separate
conditional (see `THE_KEYSTONE_PENCIL.md` v2).

---

## CHANGE LOG (v1 → v2, per Blas's audit)

Blas (Auditor) verified the v1 statement byte-exact and found a DOMAIN AMBIGUITY:
the phrase "the 80 dirty strata are subsets of the 10 K_{3,3} bipartite sextets"
reads as universal but is meant restricted to PIECE B = dim-1 §182 strata.
A fresh reviewer measuring "all dirty subsets of {0..14}" finds 80 dirty triples
and 330 dirty 4-overlaps (410 total), of which only 80 are in hen-houses. The
mathematics is correct on PIECE B; the boundary was undrawn.

**Fixes applied in v2**:
1. Statement (§1, §3) explicitly restricts the domain to PIECE B = dim-1 §182.
2. The 10 hen-houses are enumerated explicitly (§2), each by bipartition and
   matching indices.
3. Containment verified byte-exact AGAINST the §182 census, not "all dirty":
   `20/20` dirty triples and `60/60` dirty 4-overlaps of PIECE B contained in
   some hen-house (script `hen_house_verification.py`, all gates PASS).
4. New §4 documents Blas's "outside the domain" observation: if one measures
   ALL subsets, dirty strata (410 total) are NOT all in hen-houses. The theorem
   does not claim that, and never did — v2 makes it impossible to misread.

The mechanism (K_{3,3}-spanning + 1 = half-kill 6→3) and the internal counts
(6+9 per hen-house for 4-subsets, 2 spanning triples per hen-house) are
unchanged.

---

## 1. Statement (domain-bounded)

Let `Δ_{v=1}` be the FIEL `405 × 729` integer gluing matrix of the Fermat
fourfold at `v = 1` (sealed §196 recipe, gate `rank_Q = rank_{F_3} = 141`,
md5-pinned data `delta_v1.txt = ace040f7296b7f323ccc81c8cdf34f0a`). Let
`drop_3(S) = rank_{F_5}(Δ_{v=1}|_S) − rank_{F_3}(Δ_{v=1}|_S)` be the faithful
3-torsion count (§211 sealed).

**Domain**. Let **PIECE B** denote the 350 dim-1 strata of the codim-2 K_6
subspace arrangement (sealed §182):

> PIECE B = (200 non-edge dim-1 triples) ⊔ (150 dim-1 4-overlaps).

The 15 edge-triples are NOT in PIECE B (they are dim-1 but K_4-clean per §178,
removed from PIECE B in the standard convention).

**Hen-houses**. The **10 K_{3,3} bipartite sextets of K_6** are the 10
distinguished 6-subsets of matchings indexed by the 10 bipartitions
`{a,b,c} | {d,e,f}` of `{0,1,2,3,4,5}` into two 3-element subsets (sealed
§190). Each consists of the 6 matchings whose 3 edges all cross the
bipartition.

**Theorem (THE TEN HEN-HOUSES, v=1)**.
The 350 strata of PIECE B at `v = 1` decompose under the natural `S_6` action
on the 15 matchings into **exactly 4 S_6-orbits**:

| Orbit canonical | Size | drop_3 | Identity |
|---|---|---|---|
| `[0, 1, 3]` | 180 | 0 | clean non-edge triple |
| `[1, 5, 7]` | 20 | 6 | K_{3,3} bipartite-spanning triple (sealed §190) |
| `[0, 1, 3, 4]` | 90 | 0 | clean dim-1 4-overlap |
| `[1, 2, 5, 7]` | 60 | 3 | K_{3,3} bipartite triple + 1 extra K_{3,3}-internal matching |

Moreover, every dirty stratum of PIECE B at `v = 1` (the 20+60 = 80 strata
with `drop_3 > 0`) is contained as a **subset** in at least one of the 10
K_{3,3} bipartite sextets.

The containment claim is **explicitly restricted to PIECE B**. Strata outside
PIECE B are not in scope (see §4).

**Corollary (THE COMB)**. Every dirty stratum of PIECE B at `v = 1` drains to
zero torsion upon completion to its containing K_{3,3} bipartite sextet (by
sealed §195's healing). Therefore the v=1 closure of dirty PIECE B reduces from
"80 stratum checks" to "10 K_{3,3} sextet drainage checks" — all 10 sealed
clean by §195.

---

## 2. The hen-houses, enumerated byte-exact

The 10 K_{3,3} bipartite sextets of K_6, indexed by bipartitions `A | B` with
`0 ∈ A`, listed with their member matchings (lex matching dictionary §196):

| Bipartition | Hen-house = matchings |
|---|---|
| `{0,1,2}\|{3,4,5}` | `[7, 8, 10, 11, 13, 14]` |
| `{0,1,3}\|{2,4,5}` | `[4, 5, 9, 11, 12, 14]` |
| `{0,2,3}\|{1,4,5}` | `[1, 2, 9, 10, 12, 13]` |
| `{0,1,4}\|{2,3,5}` | `[3, 5, 6, 8, 12, 13]` |
| `{0,2,4}\|{1,3,5}` | `[0, 2, 6, 7, 12, 14]` |
| `{0,3,4}\|{1,2,5}` | `[0, 1, 3, 4, 13, 14]` |
| `{0,1,5}\|{2,3,4}` | `[3, 4, 6, 7, 9, 10]` |
| `{0,2,5}\|{1,3,4}` | `[0, 1, 6, 8, 9, 11]` |
| `{0,3,5}\|{1,2,4}` | `[0, 2, 3, 5, 10, 11]` |
| `{0,4,5}\|{1,2,3}` | `[1, 2, 4, 5, 7, 8]` |

Each matching of K_6 appears in exactly 4 of the 10 hen-houses (verified:
15 × 4 = 60 = 10 × 6). Total incidences match the bipartition combinatorics
of K_6.

---

## 3. Proof of containment, byte-exact

Reproducible via `hen_house_verification.py` (sandbox, runs in ~5 seconds).

### 3.1 §182 dim-1 census reproduced (gate against the sealed)

Computed `intersection_dim(legs) = 6 − rank_A6(constraint matrix)` for every
triple and 4-subset:

| Sealed §182 claim | Measured | Status |
|---|---|---|
| dim-1 triples | 215 | PASS |
| dim-0 triples | 240 | PASS |
| dim-1 4-overlaps | 150 | PASS |
| dim-0 4-overlaps | 1215 | PASS |
| Edge-triples are dim-1 (15) | 15, all dim-1 | PASS |

PIECE B = `215 − 15 + 150 = 350` strata.

### 3.2 The 4 S_6-orbits of PIECE B at v=1 (sandbox byte-exact)

For each stratum of PIECE B, compute its S_6-orbit canonical representative
and drop_3. The output:

- 180 non-edge dim-1 triples in S_6-orbit of `[0, 1, 3]`, all drop_3 = 0
- 20 non-edge dim-1 triples in S_6-orbit of `[1, 5, 7]`, all drop_3 = 6
- 90 dim-1 4-overlaps in S_6-orbit of `[0, 1, 3, 4]`, all drop_3 = 0
- 60 dim-1 4-overlaps in S_6-orbit of `[1, 2, 5, 7]`, all drop_3 = 3

Sum: `180 + 20 + 90 + 60 = 350` ✓.

### 3.3 The 20 dirty triples ARE the 20 K_{3,3} bipartite-spanning triples

For each of the 20 dirty triples (orbit `[1,5,7]`, drop=6): its edge-union is
exactly the 9 edges of some K_{3,3}({A}|{B}) bipartition. Verified:

- The orbit representative `[1,5,7]` has edge-union
  `{01,02,03,14,15,24,25,34,35}` = `K_{3,3}({1,2,3}|{0,4,5})`.
- All 20 orbit members are K_{3,3}-spanning triples for some bipartition
  (sealed §190).
- A K_{3,3}-spanning triple is, by definition, a 1-factorization of its K_{3,3}
  into 3 disjoint matchings; these 3 matchings are all bipartite to the same
  bipartition, hence all in the corresponding hen-house.

**Verification (byte-exact)**: all 20 dirty triples ⊂ some hen-house. `20/20 PASS`.

### 3.4 The 60 dirty 4-overlaps ARE 4-subsets of hen-houses

For the orbit representative `[1,2,5,7]`: matchings
```
M_1 = {01, 24, 35}
M_2 = {01, 25, 34}
M_5 = {02, 15, 34}
M_7 = {03, 14, 25}
```
Edge-union = `{01, 02, 03, 14, 15, 24, 25, 34, 35}` = `K_{3,3}({1,2,3}|{0,4,5})`.
The sub-triple `[1,5,7]` is K_{3,3}-spanning for the same bipartition; adding
M_2 (also bipartite to this K_{3,3}) places the 4-overlap inside the hen-house
for `{1,2,3}|{0,4,5}`.

All 60 orbit members are S_6-translates of this canonical case, hence each is
contained in some hen-house.

**Verification (byte-exact)**: all 60 dirty 4-overlaps ⊂ some hen-house.
`60/60 PASS`.

### 3.5 Counting cross-check

Each hen-house contains:
- `C(6,3) = 20` internal 3-subsets, of which **exactly 2** are K_{3,3}-spanning
  (= the 2 internal 1-factorizations of K_{3,3}).
- `C(6,4) = 15` internal 4-subsets, of which **exactly 6** are dirty (drop=3)
  and **9** are clean (drop=0).

Aggregated over 10 hen-houses:
- Dirty triples: `10 × 2 = 20` ✓ (matches orbit `[1,5,7]`)
- Dirty 4-overlaps: `10 × 6 = 60` ✓ (matches orbit `[1,2,5,7]`)
- Clean 4-overlaps: `10 × 9 = 90` ✓ (matches orbit `[0,1,3,4]`)

The 90 clean 4-overlaps from hen-houses + 60 dirty = 150 dim-1 4-overlaps. ✓
sealed §182.

### 3.6 Combined containment (byte-exact, ALL 80 dirty)

```
PIECE B dirty (= dim-1 §182, drop_3 > 0):
  Triples:        20  ─── all in some hen-house: 20/20  PASS
  4-overlaps:     60  ─── all in some hen-house: 60/60  PASS
  TOTAL:          80  ─── all in some hen-house: 80/80  PASS
```

The containment claim of THE TEN HEN-HOUSES is verified byte-exact within the
PIECE B domain. **Sealable as a v=1 lemma**, pending fresh-reviewer ratification
of the orbit-counting argument in §3.4.

---

## 4. Outside the domain — Blas's observation (kept honest)

If one measures the 3-torsion of arbitrary leg-subsets (not just PIECE B
dim-1 strata), the result is different:

| Domain | Dirty count | In some hen-house |
|---|---|---|
| All triples `C(15,3)=455` | 80 (60 drop=1 + 20 drop=6) | 20/80 |
| All 4-subsets `C(15,4)=1365` | 330 (60 drop=1 + 60 drop=3 + 30 drop=4 + 180 drop=5) | 60/330 |
| Dim-1 §182 (= PIECE B) | 80 (20 + 60) | 80/80 |

**Reading**: the dirty strata that fall OUTSIDE PIECE B (the 60 drop=1 triples,
the 270 drop≠3 dirty 4-overlaps) are NOT in scope for THE TEN HEN-HOUSES.
They are dim-0 (transverse) intersections that carry torsion for OTHER reasons
not localized to a K_{3,3} bipartite arrangement.

**Conclusion**: the theorem applies STRICTLY to PIECE B. The S_6-orbit + dim-1
restriction is essential. The phrasing in §1 makes this explicit; v2 closes
the domain-ambiguity that v1 left implicit.

---

## 5. The all-v lift — explicit deferral

This theorem is **v = 1 byte-exact only**. The all-v extension requires:

**(a)** S_6-equivariance of `Δ_v` for all v (pencil, `THE_KEYSTONE_PENCIL.md`
v2 Lemma 1).

**(b)** `drop_3(K_{3,3} sextet) = 0` for all v (sealed only at v=1, v=2;
pending §198 STEP 2 v-induction = Keystone Lemma 3).

If (a) and (b) hold, THE TEN HEN-HOUSES extends to all v, and the v=1 corollary
(THE COMB) closes PIECE B for all v.

The all-v extension is the subject of `THE_KEYSTONE_PENCIL.md` v2, NOT of this
theorem. This theorem stands as a v=1 byte-exact lemma independent of the
all-v question.

---

## 6. Provenance — every number traces

| Claim | Source |
|---|---|
| 350 dim-1 strata = 200 + 150 | sealed §182 (gate cross-check, 4-PASS) |
| 20 K_{3,3} bipartite triples drop=6 | sealed §190 |
| K_{3,3} bipartite sextet drains drop=0 at v=1,2 | sealed §195 |
| Half-kill mechanism (parity-pairing coboundary) | sealed §198 |
| 60 dirty 4-overlap = K_{3,3}-internal augmentations | NEW — this work |
| 4-orbit decomposition of PIECE B at v=1 | NEW — this work |
| 80/80 dirty PIECE B ⊂ some hen-house (byte-exact) | NEW — `hen_house_verification.py` |
| 10 hen-houses enumerated explicit | this work, §2 |

The data file `delta_v1.txt` (md5 `ace040f7296b7f323ccc81c8cdf34f0a`) is the
sealed FIEL input. The verification script `hen_house_verification.py`
reproduces every byte-exact claim in ~5 seconds.

---

## 7. Cojoneril self-audit (v2)

(a) **Cera carnauba**: every claim file-traced; the 80/80 containment is
byte-exact verified, not asserted. PASS.

(b) **Perfume Chanel**: the statement carries no claim beyond the v=1 domain
PIECE B; no inflated structure. PASS.

(c) **Rectitud cojoneril**: domain explicit ("OF PIECE B"); Blas's observation
documented as §4, not buried. The v2 raises the bar (forces precision) over
the v1. PASS.

(d) **Limpieza de cojones**: builds on sealed §178, §182, §190, §195, §198
verbatim; v2 fixes the v1 boundary ambiguity without introducing new
structure. PASS.

Four cojoneril criteria PASS. v2 sealable v=1 grade.

---

## 8. PMC

The hen-houses are 10, explicitly enumerated. The 80 dirty tenants of PIECE B
all live in them, verified byte-exact. The boundary between "PIECE B" and
"all dirty subsets" is now drawn with chalk thick enough that no reviewer can
re-walk it.

Blas's audit closes. v2 stands ready for the all-v lift (separately, in
`THE_KEYSTONE_PENCIL.md` v2).

PMC.
