> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE VACUUM WINDOW: COLLAPSE, WINDOW BOUND, AND THE DEV-DICTIONARY* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_VACUUM_WINDOW_THEOREM.md
>
> **Status, as written in the document:** Status: Theorems VP and WB PROVED ∀k; Lemma G0 (with a CORRECTION to the chart) PROVED;
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE VACUUM WINDOW: COLLAPSE, WINDOW BOUND, AND THE DEV-DICTIONARY
### 12 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 (mission v39, T1)
### Status: Theorems VP and WB PROVED ∀k; Lemma G0 (with a CORRECTION to the chart) PROVED;
### Theorem DL (cells-as-deviations) PROVED conditional on one vanishing hypothesis, with
### 6/6 numeric confirmation including two unregistered bonus cells. W2/W3 OPEN.
### **GAP 5 is NOT closed this turn. No shout is owed.**

**Setting.** `Q := (⊕_C S/I(C)) / (S/I(W₂))`, supported on the sublattice (dim ≤ k−1);
`Z :=` union of flats of dim ≤ k−2; `F := Γ_Z(Q)` (sections supported in Z); `gr := Q/F`.
From v38: `K_{2k−1} ≅ Ext^{k+1}_S(Q, ω_S)_{2k−k²}`, `K_{2k} ≅ Ext^{k+1}(Q, ω_S)_{2k+1−k²}`.

---

## Theorem VP (the vacuum-pack, ∀k) — metaphor 1, upgraded to an ISOMORPHISM

> `Ext^{k+1}_S(Q, ω_S) ≅ Ext^{k+1}_S(gr, ω_S)` — the entire deep tower is packed away.

*Proof.* `supp F ⊆ Z` has dim ≤ k−2, so `grade F ≥ k+2`, hence `Ext^i(F, ω_S) = 0` for
`i ≤ k+1`. The long exact sequence of `0 → F → Q → gr → 0` between `Ext^k(F) = 0` and
`Ext^{k+1}(F) = 0` gives the isomorphism. ∎
(Three lines; no lattice hypotheses, no CM. The slow-motion camera cannot tear at the top
layer — this is metaphor 2's certificate FOR THE COLLAPSE; the internal connecting maps of
`gr`'s own layers are a separate matter, see DL.)

## Lemma G0 and the CORRECTION to the chart

> `Q` is generated in degree 0, for every k.

*Proof.* On any component, the restrictions of `x₁,…,x_{2k}` are `{t, t, ±u_i}` — they span
ALL parameter linear forms; so `S₁·(⊕-tuples of degree d−1)` already fills `⊕_C F[t,u]_d`
for `d ≥ 1`, a fortiori after passing to the quotient. ∎
**Consequence (the correction — same class as the v38 §B catch):** the window parameter
CANNOT be a generator degree (all are 0 while the cells are nonzero). The mission's clause
"up to CM-filtration" was load-bearing: **the window parameter is the PRIME-FILTRATION
TWIST** — the degrees of the flat-cyclic layers hidden inside `gr`, not of its generators.

## Theorem WB (the window bound, ∀k, subadditive form)

> Let `0 = M₀ ⊆ … ⊆ M_r = gr` be ANY prime filtration, with quotients `(S/q_i)(−a_i)`.
> Quotients with `dim S/q_i ≤ k−2` contribute nothing to `Ext^{k+1}`; hence, for every m,
> `dim Ext^{k+1}(gr, ω_S)_m ≤ Σ_{i: q_i = a (k−1)-flat prime, a_i ≥ (k−1)−m} HF(S/q_i)_{m+a_i−(k−1)}`.
> At the target degrees only flat layers of twist `≥ k²−k−1` (C1-cell) / `≥ k²−k−2`
> (C2-cell) can contribute: **a finite window**.

*Proof.* Small-dimension quotients have grade ≥ k+2, killing their `Ext^{k+1}`; for flat
quotients, `Ext^{k+1}((S/L)(−a), ω_S) = ω_L(a) = (S/L)(a−(k−1))`, vanishing below degree
`(k−1)−a`. Subadditivity is the middle-exactness of the Ext long exact sequences along the
filtration. ∎ (The bound is an ≤ — exactly the ECLIPSE half that remains open after LB.)

## Theorem DL (the dev-dictionary — the eclipse made literal; 6/6 gates)

By graded local duality, `Ext^{k+1}(Q, ω_S)_m ≅ H^{k−1}_m(Q)_{−m}^∨`, and
`HF(Q)_d − P_Q(d) = Σ_i (−1)^i dim H^i_m(Q)_d`. Therefore:
> **IF `H^i_m(Q)_d = 0` for all `i < k−1` at `d = k²−2k` and `d = k²−2k−1`, THEN**
> `dim K_{2k−1} = (−1)^{k−1}[HF(Q) − P_Q](k²−2k)` **and**
> `dim K_{2k} = (−1)^{k−1}[HF(Q) − P_Q](k²−2k−1)` —
> **the two cells are the deviations of `HF(Q)` from its own Hilbert polynomial** (for
> negative arguments, `HF = 0` and the polynomial value carries the cell alone).

**Gates (zero fitted constants):** k=2 (`P_Q = 8`): d=0: `8−5 = 3 = K₃` ✓; d=−1: `8 = K₄` ✓.
k=3 (`P_Q = 165d−105`): d=3: `5 = K₅` ✓; d=2: `24 = K₆` ✓; **bonus, unregistered:** d=1:
`69 = K₇` ✓; d=0: `149 = K₈` ✓ — the dictionary reproduces cells nobody aimed it at.
**First instances of the hypothesis gated:** `H⁰_m(Q)₀ = 0` at k=2 AND k=3 (torsion probes,
pre-registered 0, PASS — at k=2 this settles the full hypothesis for the C1 cell: dim Q = 1
there, only h⁰ is below the top).

## The residue of GAP 5 — final form after v39

> **(a)** `H^i_m(Q)_d = 0` for `i < k−1` at the two duality degrees, ∀k (the "missing
> light" is EXACTLY lower local cohomology of one explicit module at two degrees);
> **(b)** the deviation values `= 2k−1` and `4k(k−1)` ∀k (a Hilbert-polynomial-vs-HF
> statement about the arrangement at two LOW degrees — W2/W3's star-and-character count);
> **(c)** generation of K at degree 2k (unchanged from v38).
Six anchors + two bonus cells banked. The k=5 fishing engine was NOT built: T1 did not
land and no written pencil step consumes it this turn (the mission's own rule).

**Metaphor scorecard (honest):** vacuum-pack → Theorem VP, PROVED, upgraded to iso ·
slow-motion → the collapse half PROVED; the internal layer maps remain (that is (a)) ·
eclipse → Theorem DL, PROVED as conditional identity, 6/6 · dye → gates run, torsion
probes PASS · fishing net → not deployed (rule-bound) · deer/ball → open (W3).

**Grades.** VP, G0, WB: PROVED ∀k. DL: PROVED conditional on (a); COMPUTED 6/6.
(a), (b), (c): OPEN ∀k (gated instances pass). B(d) ∀k: OPEN. Reserved phrase: not spoken.

— FRESCALES14. Engine: `vacuum_window_gates.py` (same turn; pre-registered probes, 8/8).
