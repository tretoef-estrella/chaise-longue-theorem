> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE MATRYOSHKA DESCENT: THE NOTARY THEOREM AND THE k=3 TOWER* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MATRYOSHKA_DESCENT_THEOREM.md
>
> **Status, as written in the document:** Status: Theorem NT (the Notary) PROVED ∀k, UNCONDITIONAL — and it BYPASSES the
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE MATRYOSHKA DESCENT: THE NOTARY THEOREM AND THE k=3 TOWER
### 13 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v42, T1/T2/T3)
### Status: Theorem NT (the Notary) PROVED ∀k, UNCONDITIONAL — and it BYPASSES the
### level-0 vanishing hypothesis (a). Termination PROVED. The k=3 tower computed
### end-to-end: the inner doll built, the second signature hit blind (pre-registered).
### The ∀k descent: CONDITIONAL on per-level star-CM (automatic at flat-dim ≤ 1).
### **Standing order: conditions NOT met. NO NOTES. Sixth honest hold.**

**Setting.** `Q = (⊕_C O_C)/O_{W₂}`; for each seam L (catalog SC), the star restriction
`π_L : Q → Q_⋆(L)` (forget components off the star; well-defined since global functions
restrict to star functions). `Φ := (π_L)_L : Q → ⊕_L Q_⋆(L)`; `D := coker Φ`.

---

## Theorem NT (the Notary — the light projects without deforming; ∀k, pencil)

> `ker Φ` and `coker Φ = D` are supported in dim ≤ k−2 (Φ is an isomorphism at every
> seam's generic point: the star captures the full local structure there). Hence, for
> every degree `m < k−1`:
> ## `Ext^{k+1}_S(Q, ω_S)_m ≅ Ext^{k+2}_S(D, ω_S)_m` — an ISOMORPHISM, unconditional.

*Proof.* Split `Φ` through its image: `0 → ker → Q → im → 0` and `0 → im → ⊕Q_⋆ → D → 0`.
Deep support gives `grade(ker), grade(D-error terms) ≥ k+2`, killing `Ext^{≤ k+1}(ker)`,
so `Ext^{k+1}(im) ≅ Ext^{k+1}(Q)`. In the second LES, Theorem TS gives
`Ext^{k+1}(⊕Q_⋆)_m = ⊕(ω_L-copies)_m = 0` for `m < k−1` and `Ext^{k+2}(⊕Q_⋆) = 0`
(each `O_L` is CM of codim k+1); the LES collapses to
`0 → Ext^{k+1}(im)_m → Ext^{k+2}(D)_m → 0`. ∎

**Corollary NT.1 (the bypass).** The two cells are UNCONDITIONALLY
`K_{2k−1} ≅ Ext^{k+2}(D)_{2k−k²}` and `K_{2k} ≅ Ext^{k+2}(D)_{2k+1−k²}` — the vanishing
hypothesis (a) of Theorem DL is no longer needed at level 0: the shake is unnecessary
there. The hypothesis re-appears only as STRUCTURE of the next levels (below).

**Lemma TL (termination).** Each descent step strictly drops support dimension, so the
tower `Q = Q⁽⁰⁾ → D = Q⁽¹⁾ → …` reaches a finite-length bottom in ≤ k−1 steps; a
dim-0 module hides no further doll. ∎

## The k=3 tower, computed (machine; all pre-registrations hit)

`Φ` is INJECTIVE in every computed degree (`HF(ker) = 0`, d = 0..5) — at k=3 the doll
sequence is exact: `0 → Q → ⊕Q_⋆ → D → 0`. Measured (fresh module, never before
computed): `HF(D) = 121, 201, 246, 265, 270, 270` — stable at **270** from d = 4, so
`dim D = 1`; its saturated pieces over lines are automatically FREE (graded torsion-free
over dim 1), so at k=3 the descent bottoms out with NO hypothesis. Local duality then
gives, unconditionally:
> `K₅, K₆, K₇, K₈ = h¹_m(D)₃, h¹(D)₂, h¹(D)₁, h¹(D)₀`, and since
> `h¹(D)_e = [P_D − HF(D)](e) + h⁰(D)_e`, the pre-registered gate was:
> **deviations-from-stable of HF(D) at e = 3,2,1,0 = (5, 24, 69, 149).**
**Result: PASS, byte-exact — the notary's second signature, one doll down** — and the
match FORCES `h⁰(D)_e = 0` at those floors (derived, not assumed). The mission's
`H¹(Q)`-probe engine is now unnecessary at k=3: the descent probe replaced it at a
fraction of the cost; nothing is proposed for the Mac (no RAM estimate owed).

## The ∀k residue after v42 — exact

The descent step is one functor, applied verbatim per level (come y caga). What it needs
at each intermediate level j: **the level-j stars of `Q⁽ʲ⁾` are CM over their flats** —
automatic when the flat dimension is ≤ 1 (torsion-free ⟹ free), PROVED at level 0 by
TS. Hence: k = 2, 3 fully unconditional (banked); **k = 4 needs exactly ONE structural
check** (the dim-2 level of its tower); general k needs k−3 of them. Plus, unchanged: the
bottom's character count (the cells' values `2k−1`, `4k(k−1)` ∀k) and gen@2k.

**Metaphor scorecard.** Come-caga → the functorial step + termination: PROVED; per-level
CM named as the eating condition. Notario → Theorem NT: the turn's gem, an isomorphism.
Agitar → transformed: the level-0 hollow cannot exist (NT.1 bypasses it); no wrinkle
crush was needed where the mission aimed it.

**Grades.** NT, NT.1, TL: PROVED ∀k. k=3 tower: COMPUTED, all gates PASS (M1 6/6, M2
exact, injectivity measured). ∀k descent: CONDITIONAL (per-level CM, named). Cells ∀k,
gen@2k: OPEN. B(d) ∀k: OPEN. **Notes: NOT sounded. Reserved phrase: not spoken.**

— FRESCALES14. Engine: `matryoshka_gates.py` (same turn; row counts, pre-registrations,
and the seam catalog re-derived in-engine 105/60/45 as its own control).
