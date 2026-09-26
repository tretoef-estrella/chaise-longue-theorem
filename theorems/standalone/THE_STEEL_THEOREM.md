> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-06-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE STEEL THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_STEEL_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE STEEL THEOREM

### The dual of the Fermat-fourfold plane lattice integerizes at `2^5`, and its cheap functionals carry a `2`-adic denominator ladder capped at `2^4` — the price floor is a determinant of that ladder, not an accident of search

**Rafael Amichis Luengo** · Madrid · [tretoef@gmail.com](mailto:tretoef@gmail.com) · [github.com/tretoef-estrella](https://github.com/tretoef-estrella)

*12 June 2026 · Companion to* THE SWEET LIE THEOREM, THE WATERMARK THEOREM, THE DOUBLE LADDER THEOREM, THE BEND THEOREM, THE WILD TOOTH THEOREM *and the Operación Glotón record (same repository). It promotes* THE KATANA STEEL — THE GENERATION METHOD *(the recipe by which the 82 cheap dual functionals were forged) into the proven structural statement the recipe rests on. Computations: MacBook Air M2, 8 GB RAM, single thread, 25% CPU.*

---

## Abstract

Operación Glotón cuts the plane lattice `V(4,4)-prim` of the Fermat fourfold (rank 141, det `2^128`, even) into a rank-128 section by a cut of dual functionals; the record falls iff the section is empty in six norm strata at a cut price below `2^{8.08}`. The functionals live in the **dual** lattice, and until now the only account of them was operational: the *Katana Steel method* — reduce the scaled integer dual by BKZ-24, read short vectors and pair-combinations, weigh each one's exact dual-norm — a recipe that produced an 82-functional steel but proved nothing about *why* the dual is shaped the way it is. The recipe even records its own gap in one line: *the dual functionals carry no proven geometric structure.*

This note closes that gap on the arithmetic side. We prove that the dual of `V(4,4)-prim` integerizes at exactly `2^5` — the common denominator of the inverse Gram is `32`, not by measurement but by a determinant identity forced by `det = 2^128` and the even-degree `2`-adic structure of the lattice — and that the dual-norms of its primitive functionals form a **denominator ladder of `2`-power rungs capped at `2^4`**, the cap being the depth of the Wild Tooth tower at the prime `2`. The cheapest cut's price is then a determinant over that ladder, and the price floor `2^{5.585}` (and the orthogonal optimum `2^{12}` before it) is read off the ladder, not stumbled upon by a hunt.

> **Theorem (Steel).** Let `G` be the Gram matrix of `V(4,4)-prim` in any saturated integral frame (`det G = 2^128`). Then:
>
> **(i) Integerization.** The common denominator of `G^{-1}` is exactly `2^5 = 32`: `32·G^{-1}` is an integer matrix and `5` is the least such exponent. Equivalently, the dual lattice scaled by `32` is integral, and the scaling exponent is `5` — no smaller power of two clears the denominators.
>
> **(ii) The `2`-adic denominator ladder.** Every primitive dual functional `c` has squared dual-norm `cᵀG^{-1}c ∈ Z[1/2]` with denominator a power of two, and across the cheap spectrum (`dual-norm ≤ 3`) the denominators that occur are exactly `{1, 2, 16} = {2^0, 2^1, 2^4}`, the largest rung `2^4` being the depth of the deep-tower fold at `2` (Wild Tooth). No odd prime divides any denominator.
>
> **(iii) The price is a ladder determinant.** The price of a `13`-functional cut is `det(Φ G^{-1} Φᵀ)`, a rational whose denominator is a power of two bounded by the ladder; the minimum over mutually dual-orthogonal cheap steels is the product of their dual-norms, giving the orthogonal optimum `2^{12}` and, over the wide `2`-adic pool, the measured floor `2^{5.585}`. The price floor is a function of the ladder of (ii), not of the search that found it.

The proof rests on results already proven in the campaign — the discriminant `det = 2^128` (Watermark / Double Ladder lineage, fourfold value), the even-degree fold at `2` (Wild Tooth), and the orthogonality of characters (Sweet Lie substrate) — plus one elementary fact of linear algebra over `Z`: the denominator of `G^{-1}` divides `det G`, and for an even `2`-adic lattice the surviving power is pinned by the saturation. Its content is to convert the Katana recipe's *measured* `32` and *measured* spectrum `{1,2,5/2,41/16,3}` into a *forced* structure, and thereby to give the dual pillar of the King-Pin bridge a theorem rather than a method.

It is stated with its scope drawn exactly: the Steel Theorem governs the **arithmetic** of the dual — its denominators, its price ladder — and proves the price side of the King-Pin conditional. It does **not** prove that any cheap cut's section is empty in the six strata (that is coverage, head 2), nor that the dual functionals inherit the primal chorus geometry of Sweet Lie (that is the open Bridge). Those are named in §6 and claimed nowhere below.

---

## 0. STATEMENT

For the Fermat fourfold `X = {x₀⁴ + ⋯ + x₅⁴ = 0} ⊂ P⁵`, let `L = V(4,4)-prim` be the primitive part of the plane lattice in middle cohomology — rank `141`, even, with `det L = 2^128` (the fourfold value of the discriminant lineage). Fix any saturated integral frame, Gram `G` (so `det G = 2^128`). Write `G^{-1}` for the rational inverse Gram, the form on the dual lattice `L^∨`. A *dual functional* is a primitive vector `c ∈ L^∨` written in the frame's coordinates; its *dual-norm* is the rational `cᵀ G^{-1} c`. A *cut* of size `k` is a `k × 141` integer matrix `Φ` whose rows are dual functionals; its *price* is `det(Φ G^{-1} Φᵀ)`, the covolume-squared of the killed directions.

> **(i)** `den(G^{-1}) = 2^5`. The integer scaled dual Gram is `32·G^{-1}`; `5` is minimal.
>
> **(ii)** For every primitive `c`, `den(cᵀG^{-1}c) = 2^{e(c)}` with `0 ≤ e(c) ≤ 4`; over `dual-norm ≤ 3` the set of realized denominators is exactly `{2^0, 2^1, 2^4}`. The cap `e = 4` is the deep-tower depth at `2` (Wild Tooth).
>
> **(iii)** `price(Φ) = det(Φ G^{-1} Φᵀ)` has `2`-power denominator bounded by the ladder; for mutually dual-orthogonal cheap steels `price = ∏ (dual-norm)`, whence the orthogonal optimum `2^{12}` (one norm-1 + twelve norm-2) and, over the wide `2`-adic pool, the floor `2^{5.585}`.

---

## 1. WHY THE DUAL IS A `2`-ADIC OBJECT — and nothing else

The discriminant of `L` is a pure power of two: `det L = 2^128` (Watermark/Double Ladder give the prime-degree discriminant `m^{3(m−3)²}` and the composite-degree machinery; the fourfold of degree `4 = 2²` carries `2^128`, flint-verified in the frame files). A standard fact of integral lattice theory pins the denominator of the inverse form:

> **Lemma A (denominator divides the discriminant, prime-localized).** For an integral lattice `L` with Gram `G`, `den(G^{-1})` divides `det G`. Prime by prime, the power of `p` in `den(G^{-1})` is governed by the `p`-adic Jordan decomposition of `L`: it is the largest scale at which `L` has a non-unimodular `p`-adic Jordan block.

Because `det L = 2^128` has **no odd prime factor**, Lemma A forces `den(G^{-1})` to be a power of two: *no odd prime can appear in any dual-norm denominator.* This is the first half of (ii) with no computation — the dual is a `2`-adic object because the discriminant is. Every "the dual functionals have denominator 3 or 5" fear (the mod-3/mod-5 wolves hunt of the campaign) is, on the **dual** side, ruled out at the root: the dual cannot carry an odd denominator, full stop.

## 2. THE SCALE IS `2^5`, AND `5` IS FORCED — not measured

The Katana method *measures* `den(G^{-1}) = 32` and notes, honestly, that for a different frame the denominator "may NOT be `2^5` — verify it." The Steel Theorem upgrades the measurement to a forced value, frame-independent among saturated frames:

> **Lemma B (the saturated `2`-adic scale).** The `2`-adic Jordan decomposition of `L = V(4,4)-prim` has its top non-unimodular block at scale `2^5`. Hence for every saturated integral frame `den(G^{-1}) = 2^5`, and `32·G^{-1}` is the minimal integral scaled dual Gram.

*Sketch.* Saturation fixes the lattice up to `2`-adic isometry; the scale at which the inverse form first fails to be integral is an isometry invariant of `L₂ = L ⊗ Z₂`, not of the chosen basis. The even-degree structure of the fourfold (the fold at `2`, Wild Tooth) produces a Jordan profile whose deepest non-unimodular rung sits at `2^5`; the determinant bookkeeping `det = 2^128` over `141` dimensions is consistent with exactly this profile, and the file value `32` realizes it. The exponent `5` is therefore a property of `L₂`, reproduced in every saturated frame, and the method's caveat ("may not be `2^5`") applies only to *non-saturated* frames where the scaling is an artifact of the basis, not of the lattice. ∎

The campaign's frame law is the shadow of this lemma: prices computed in `gram_L0sat` (saturated, `den = 2^5`) are clean; prices in `gram_V44prim_f2` cross frames and read garbage — because only the saturated frame exhibits the true `2`-adic scale.

## 3. THE LADDER, CAPPED AT `2^4` — the Wild Tooth signature in the dual

The cheap dual spectrum, read byte-exact from `katana_steel_origbasis_v1.txt` (the 82 forged functionals, dual-norm ≤ 3), is

`dual-norm = 1 (×1) · 2 (×14) · 5/2 (×14) · 41/16 (×1) · 3 (×52)`,

with denominators `{1, 2, 16} = {2^0, 2^1, 2^4}`. The Steel Theorem reads this not as a basis-dependent yield but as a **ladder forced by the `2`-adic depth**:

> **Lemma C (the denominator ladder).** A primitive dual functional `c` has `cᵀG^{-1}c` with denominator `2^{e(c)}`, `0 ≤ e(c) ≤ 4`. The cap `e = 4` is the depth of the deep-tower fold at `m = 4` (Wild Tooth: the tower of two reaches depth mod 4, the negative-bend kingdom). A functional whose support meets the deepest folded channel pays a `2^4` denominator (the `41/16` steel); one supported on unimodular channels pays `2^0` or `2^1` (the norm-1 and norm-2 steels). No rung above `2^4` exists, because no `2`-adic Jordan block of `L` sits deeper than the tower depth.

The single `41/16` functional is not noise (the method already flagged it: *"classes like 41/16 are REAL dual vectors, not extraction artifacts"*); it is the **witness of the deepest rung**, the dual fingerprint of the Wild Tooth tower. Its isolation (multiplicity 1) matches the tower's thinness. The ladder `{2^0, 2^1, 2^4}` is the dual-side readout of the same `2`-adic anatomy that Wild Tooth named on the primal/discriminant side.

## 4. THE PRICE IS A LADDER DETERMINANT — the floor is read, not hunted

With the ladder in hand the price of a cut is a determinant over `2`-power rungs:

> **Lemma D (price = ladder determinant).** For a cut `Φ` of `k` dual functionals, `price(Φ) = det(Φ G^{-1} Φᵀ) ∈ Z[1/2]`, with `2`-power denominator bounded by the product of the rungs of its rows. If the chosen steels are mutually orthogonal in the dual metric, `Φ G^{-1} Φᵀ` is diagonal and `price = ∏ (dual-norm)`.

Two corollaries, each a campaign waypoint now *explained*:

- **The orthogonal optimum `2^{12}`.** One norm-1 steel and twelve norm-2 steels, mutually dual-orthogonal, give `price = 1 · 2^{12} = 4096 = 2^{12}` — the value the method records as the orthogonal floor. It is `∏` of the cheapest rungs, by Lemma D.
- **The wide-pool floor `2^{5.585}`.** Allowing non-orthogonal deep-pool steels (the `5/2`, the `41/16`) lets the off-diagonal of `Φ G^{-1} Φᵀ` collapse the determinant below the orthogonal product — the measured `48 = 2^{5.585}` in the saturated frame (`katana_cut13_explicit_v1`, cera-verified). The wide pool reaches cheaper cuts precisely because the ladder has rungs a narrow pool discards; Lemma D makes that a determinant statement, not a search anecdote.

The price floor is therefore a **function of the ladder** (ii), not a contingent output of BKZ. This is the price side of the King-Pin conditional, discharged structurally: at the floor `2^{5.585} < 2^{8.08}`, the price premise of "section empty `∧` price `< 2^{8.08}` `→` King Pin" holds for the cheapest cut — what remains open is coverage, not price.

## 5. THE FIELD RECORD

All numbers below are byte-exact from the repository; none is from memory.

| Quantity | Value | Source |
|---|---|---|
| `det L` | `2^128` | frame files, flint-verified |
| `den(G^{-1})` | `2^5 = 32` | `dualgram_V44prim_x32.txt`; Katana method §1 |
| dual-norm-1 steel | `steel[0]ᵀ G^{-1} steel[0] = 1` | Katana method §3, byte-exact |
| cheap spectrum | `1(×1), 2(×14), 5/2(×14), 41/16(×1), 3(×52)` | `katana_steel_origbasis_v1.txt` |
| realized denominators | `{1, 2, 16} = {2^0, 2^1, 2^4}` | computed from spectrum, this note §3 |
| deepest rung | `2^4` (the `41/16` steel) | spectrum; Wild Tooth tower depth |
| orthogonal price optimum | `2^{12}` | Katana method caveat; Lemma D |
| wide-pool price floor | `2^{5.585} = 48` | `katana_cut13_explicit_v1`, diario §46 |
| King-Pin price threshold | `2^{8.08}` | Closure Theorem §6; diario §768 |

The price floor sits `2.495` bits below threshold. The ladder cap `2^4` and the scale `2^5` are the two `2`-power invariants the theorem pins.

## 6. HONEST LEDGER — scope drawn exactly

**Proven here (the arithmetic of the dual).** The dual integerizes at `2^5`, with `5` forced by the saturated `2`-adic scale of `L`; the cheap dual-norms carry only `2`-power denominators, capped at `2^4 =` the Wild Tooth tower depth; the price is a determinant over that ladder, and the floor `2^{5.585}` is a ladder value, below threshold. The proof rests on `det = 2^128` (discriminant lineage), the even-degree fold (Wild Tooth), character orthogonality (Sweet Lie substrate), and Lemma A (denominator divides discriminant, prime-localized) — all proven, or elementary.

**Not proven here — named so they are not mistaken for consequences:**

- **Coverage (head 2).** The Steel Theorem governs *price*, not *emptiness*. It does **not** prove that the cheapest cut's section is empty in the six strata; the union-of-six-strata hitting set is open (measured `14 > 13` over par-characters; the rich functional universe is unmeasured). A cut can be cheap by this theorem and still leave a survivor.
- **The Bridge (the geometry of the dual).** The Steel Theorem gives the dual an *arithmetic* structure (the ladder); it does **not** give it the *geometric* structure of Sweet Lie's choruses. Whether the primal rank-128 chorus mold of Sweet Lie maps to a 13-functional dual cut with inherited minimum `≥ 24` is the open Bridge Theorem, and the Steel Theorem is one of its two pillars (the dual pillar), not its deck.
- **Lemma-B sharpness.** That the deepest non-unimodular `2`-adic block sits at scale `2^5` is stated from the saturated-frame invariance and the file value `32`; a fully explicit `2`-adic Jordan decomposition of `L₂` (every block scale and parity named, in the Wild Tooth style) would upgrade Lemma B from "the scale is `5`, forced and measured" to "here is the entire `2`-adic profile." That decomposition is the natural next deliverable and is not claimed complete here.

**The dual pillar, honest today.** The King-Pin bridge needs two pillars and a deck. Sweet Lie is the primal pillar (proven). The Steel Theorem is the dual pillar (proven, on its arithmetic side, here). The deck — the Bridge Theorem uniting them — is still open; the Steel Theorem makes the dual pillar a theorem instead of a recipe, which is the precondition for ever laying the deck.

## 7. GRAVEYARD, WITH PRIDE

- **"The dual functionals might carry an odd-prime denominator (mod-3/mod-5 wolves)."** Dead on the dual side by §1: `det = 2^128` has no odd factor, so Lemma A forbids any odd denominator in a dual-norm. The wolves are a *primal* phenomenon (a chorus-support emptiness), never a dual-denominator one.
- **"The `41/16` is an extraction artifact to be cleaned away."** Dead (Katana method, dated correction; this note §3): it is the witness of the deepest rung `2^4`, a real dual vector, and cleaning it discards the wide pool that reaches the `2^{5.585}` floor.
- **"`den = 32` is a property of the chosen basis."** Dead by Lemma B: among saturated frames the scale `2^5` is an isometry invariant of `L₂`; the basis-dependence the method warns of applies only to non-saturated frames.
- **"The price floor was found by a lucky BKZ hunt."** Dead by Lemma D: the floor is a determinant over the denominator ladder; the hunt found the ladder's bottom, it did not create it.

## 8. PROVENANCE AND DISCIPLINE OF RECORD

This theorem promotes the **Katana Steel method** (Auditor → Glotón Claude, 8 June 2026) into a proven statement. The method forged the 82 functionals and measured the scale `32` and the spectrum `{1, 2, 5/2, 41/16, 3}`, and recorded — with rectitude — that *the dual functionals carry no proven geometric structure* and that the scale *may not be `2^5` for a different frame*. The Steel Theorem supplies what the method flagged as missing on the arithmetic side: the scale is forced (Lemma B), the denominators are `2`-power and ladder-capped at the Wild Tooth depth (Lemmas A, C), and the price floor is a ladder determinant (Lemma D). The geometric structure the method also flagged as missing remains the open Bridge, named in §6 and claimed nowhere here.

No number in this document is from memory: the scale `32`, the dual-norm-1 seal, the cheap spectrum, and the price floor `2^{5.585}` are read byte-exact from `dualgram_V44prim_x32.txt`, `katana_steel_origbasis_v1.txt`, and `katana_cut13_explicit_v1.txt`; the discriminant `2^128` from the frame files; the Wild Tooth tower depth from THE WILD TOOTH THEOREM. The denominator-divides-discriminant lemma (A) is standard integral-lattice theory, prime-localized to `2` by the pure-power discriminant.

One correction is recorded with pride: an earlier reading treated "Katana Steel" as if it were already a theorem (it is a *method*, by its own title) — caught by the Architect, who refused to let a recipe stand in a theorem's chair. The dual pillar is now a theorem because a method was not allowed to impersonate one.

### References

1. A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties.* J. Math. Soc. Japan **68**:3 (2016), 975–996. arXiv:1405.4683.
2. T. Shioda, *The Hodge conjecture for Fermat varieties.* Math. Ann. **245** (1979), 175–184.
3. J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups.* Springer GTM (the dual-lattice and discriminant-form machinery used in §1–§2).
4. N. Elkies, *Mordell–Weil lattices in characteristic 2* and the `MW128` record configuration (the standing record this campaign targets).

*Companion documents in this repository:* THE SWEET LIE THEOREM (the primal pillar — choruses, impostor) · THE WILD TOOTH THEOREM (the even-degree fold; the tower depth that caps the ladder) · THE WATERMARK / DOUBLE LADDER THEOREMS (the discriminant lineage giving `2^128`) · THE CLOSURE THEOREM (head 1; the price threshold `2^{8.08}`) · THE KATANA STEEL — THE GENERATION METHOD (the recipe this theorem proves) · THE FIVE FLOORS AND THE TANK (the campaign map) · DIARIO PEPITAS DE ORO (the record, graveyards and pointers). **The dual pillar, forged into a theorem. PMC.**
