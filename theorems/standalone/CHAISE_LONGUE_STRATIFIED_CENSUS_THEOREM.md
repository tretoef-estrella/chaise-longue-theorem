> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE STRATIFIED CENSUS THEOREM (los coeficientes de σ, piso a piso del retículo)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STRATIFIED_CENSUS_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable), solo regime · Pending P0 · FILA 4, primer avance de lápiz: DOS de los cuatro coeficientes de la cúbica σ(k=3) PROBADOS — y el método calibrado contra las leyes SELLADAS de k=1 (entera) y k=2 (dos coeficientes).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE STRATIFIED CENSUS THEOREM (los coeficientes de σ, piso a piso del retículo)
### 13 Jul 2026 · Constructor: Bisel (Fable), solo regime · Pending P0 · FILA 4, primer avance de lápiz: DOS de los cuatro coeficientes de la cúbica σ(k=3) PROBADOS — y el método calibrado contra las leyes SELLADAS de k=1 (entera) y k=2 (dos coeficientes).

> **Theorem (Stratified Census, two strata).** For every k, in the stable range,
> **σ_e(k) = [(2k+1)!!·k]·C(e+k, k) − [(2k+1)!!·k(k+1)/2]·(k+1)·C(e+k−1, k−1) + O(e^{k−2}),**
> i.e. the top TWO coefficients of the census law are, exactly:
> **leading = (2k+1)!!/(k−1)!** (re-derivation of Slap 2's Theorem 2B by a second route), and
> **second = the codim-1 stratum count:** each of the (2k+1)!!·k(k+1)/2 swap flats (each shared by EXACTLY two sheets — Swap Theorem) imposes (k+1) net census conditions at order e^{k−1}.
> **Evaluations:** k=1: 3e − 3 — the ENTIRE sealed law from two strata (the k=1 law is linear, so codim-1 exhausts it). k=2: 15e² − 90e + … — **both sealed coefficients reproduced.** k=3: **σ_e(3) = 52.5·e³ − 945·e² + c·e + d** with c, d = the codim-2 and codim-3 strata (road below).

**Pillars (Ley 44):** (i) Radicality; consumes Slap 2 (sheaf presentation 0→Eⁿ→M→Γ→0), Swap Theorem (codim-1 flats = swaps, multiplicity two), Slap 2's Theorem 2B (independent cross-check of the leading term).

---

## Proof (stratified Mayer–Vietoris at codimension 1)

By the sheaf presentation, σ_e = dim Γ_e − HF_R(e), with Γ = pair-constant tuples on X = ∪V_J and R = O(X).

**Order e^k (sheets).** Restriction to sheets is injective (X reduced); each sheet carries (k+1) free pair-functions: dim Γ_e = N(k+1)C(e+k,k) − (codim-1 corrections) + O(e^{k−2}); HF_R(e) = N·C(e+k,k) − (…) likewise. The corrections at order e^{k−1} live on the codim-1 strata only (deeper flats have dim ≤ k−1, hence O(e^{k−2}) function spaces; likewise the pairwise-glued-vs-global obstruction lives over codim ≥ 2 — the triple phenomenon — and is O(e^{k−2})).

**Order e^{k−1} (swap flats).** Every codim-1 flat V_F is a swap flat, shared by EXACTLY two sheets J, J′ (Swap Theorem), where two J-pairs merge with two J′-pairs into one 4-cycle. Compatibility of the two sheet-tuples on V_F: the k−1 untouched pairs give k−1 conditions (h_p|_F = h′_p|_F), and the 4-cycle forces all four components to ONE common value: 3 conditions. Total k+2 function-conditions on O(V_F) per flat — restrictions from linear flats are surjective in every degree, and conditions at distinct flats interfere only in codim ≥ 2. For the single-function sheaf O_X the same count is 1 condition per flat. Hence at order e^{k−1}:
> dim Γ_e = N(k+1)C(e+k,k) − [Nk(k+1)/2](k+2)C(e+k−1,k−1) + O(e^{k−2}),
> HF_R(e) = N·C(e+k,k) − [Nk(k+1)/2]·C(e+k−1,k−1) + O(e^{k−2}),
and subtracting, the net per-flat census weight is (k+2) − 1 = k+1, giving the displayed formula. ∎

## Calibration (Ley 36 — the method against SEALED laws, machine-checked this session)
- k=1: method gives 3e+3 − 6 = **3e − 3** = the sealed law, WHOLE. ✓
- k=2: method gives **15e² − 90e** + (unreliable lower order) — both sealed coefficients (15, −90) exact. ✓
- k=3: **52.5e³ − 945e²** + … — the leading re-derives Theorem 2B by an independent route (two proofs of 52.5 now); **b = −945 is NEW, proven.**

## The road to c and d (named, not claimed — next pencil turn)
The e^{k−2} coefficient is the codim-2 stratum sum: flats of two types (pairs of disjoint/overlapping swaps; 6-cycles), classified by the **Frozen Lattice Theorem** (files: flats ↔ partition types), each with its sheet-multiplicity and merged-partition condition count — PLUS the first triple-obstruction correction (the pairwise-vs-global gap, which first appears here). Calibration target ready-made: at k=2 the codim-2 stratum must reproduce the sealed constant **+145**; at k=1 it must vanish. Then codim-3 gives d(3). All pencil; no engine required (order of the Architect: never ask the machine what the pencil can do).

## Two guard-findings of this assault (recorded per Ley 26/42)
1. **Fit-refusal (the pencil protected us):** cubic fits through e ≤ 11 give leaders 154/3, 48, 83/2 ≠ 52.5 with failing retro-predictions — e=11 is still PRE-STABLE for k=3 (the Swap Ramp's long head, again). Any law fitted to today's data would have been PRE-STABLE-AS-LAW (cemetery mode). The strata method needs no stable data at all.
2. **The softness asymmetry (structural, explains the campaign's history):** unlike the annihilator (which is EXACTLY one-sheet classes — the Unified Law), the census Γ strictly exceeds diagonal ⊕ one-sheet classes (at k=2, degree 6: one-sheet gives 45, the true σ is 145). **The annihilator is rigid; the census is soft.** This is WHY the annihilator law fell in one turn and the census asks for strata — the asymmetry itself is a theorem-shaped fact for the paper.

---

# PART II — THE LOCAL WEIGHTS, MEASURED (same session, s67): c(3) SEALED, the k=2 law FULLY DERIVED

## II.1 The mechanism completed: local star invariants
The codim-≥2 weights are FINITE LOCAL INVARIANTS: for each flat type, the exact census of its star (the sub-arrangement of sheets through one flat) is a small, fixed, q-free linear-algebra computation; the residual after subtracting the star's own two-strata prediction stabilizes to w·dim O(flat)_e. All weights below were computed EXACTLY this way in-session (F₃, ranks over the star systems, logs in session record). **Nothing inherited, everything measured** — enforced by two forensic catches (II.4).

## II.2 The k=2 census law DERIVED COMPLETELY from theory — historic
Codim-2 flats of k=2: **10 bipartition lines** (3+3 sign-split; each in 6 sheets; enumeration machine-verified after signature normalization) with measured weight **24**, plus — a char-3 DISCOVERY — **15 zero-lines** {x_a = t, x_b = −t, rest = 0}: genuine flats arising only from TRIPLE intersections, because in characteristic 3 triangle systems of pair-forms FORCE zeros; measured weight **5**. Total: 10·24 + 15·5 = **315 = the exact pinning**, and
> Γ(2)_e = 45C(e+2,2) − 180(e+1) + 315 ⟹ **σ_e(2) = 15e² − 90e + 145** — the SEALED Sofá law, derived from strata + two measured local invariants, for the first time by theory.

## II.3 k=3: the codim-2 stratum measured — **c(3) = 12285/2**
Codim-2 flats of k=3 (classification with the char-3 zero types included):
| type | structure | count | weight (MEASURED) |
|---|---|---|---|
| (i) | 6-cycle line × live pair | 280 | **29** (star: 6 sheets; residual 29(e+1)−6 exact e=0..6) |
| (ii) | two 4-cycle lines | 315 | **6** (star: 4 sheets; residual 6(e+1) exact e=0..6) |
| (c) | two live pairs × zeroed 4-block | 210 | **6** (star: 3 sheets; residual 6(e+1) exact e=0..6) |
Codim-1 swap weight 5 = (k+2) re-validated empirically in all three stars (clean residuals impossible otherwise). Total codim-2 = 280·29 + 315·6 + 210·6 = **11270**, giving with HF_R exact (CI closed form; checked byte-exact vs engine at e=9: 3850, e=10: 5775):
> **σ_e(3) = (105/2)e³ − 945e² + (12285/2)e + [10990 + D₃]** (stable range),
leading = the Slap 2 theorem ✓ (second independent route), b = −945 ✓ (codim-1, undisturbed), **c = 12285/2 NEW, sealed by measured invariants**, d open (D₃ = codim-3 total).

## II.4 Two forensic catches (Ley 26/21 — assumptions die, measurements rule)
1. **w_c = 6, not 5:** the "product with an extra pair" heuristic predicted 5; direct measurement said 6. The heuristic is FALSE (extra live pairs shift weights via component bookkeeping). Caught BEFORE it poisoned c(3) by the type-(e) consistency anomaly.
2. **w_i = 29, not 24:** same lesson at type (i) — the k=2 value 24 does NOT transport to the k=3 flat with its live pair. Both catches are cemetery-grade process entries: LOCAL-WEIGHT-INHERITANCE is a failure mode; every configuration gets its own star.
Bonus resolution: the type-(e) star anomaly (linear leftover) resolved EXACTLY to a constant **−7** once w_c = 6 was used — negative Möbius weights are real, and the bookkeeping closes.

## II.5 The exact map to d(3) — codim-3 (the remaining lápiz of the σ-law)
Dim-1 flats of k=3, classified: **(a)** full bipartition 4+4 lines: 35 flats, star = 24 sheets [weight pending — biggest star]; **(b)** live pair × zeroed 6-block: 28 flats, star = 15 sheets [pending; internal dim-2 flats: 10 type-(i)-lines + 15 type-(c)-like — dedup with exact arithmetic, not floats]; **(e)** 4-cycle line × zeroed 4-block: 210 flats, weight **−7 MEASURED** (resolved above). Then d(3) = 10990 + D₃ with D₃ = 35w_a + 28w_b + 210·(−7). Protocol identical; two star runs remain.

**MARCADOR: [FILA 4 A 3/4 — la ley del censo de k=2 DERIVADA COMPLETA de la teoría (histórico: estratos + invariantes locales medidos, 315 clavado, ley sellada reproducida) · k=3: σ = 52.5e³ − 945e² + 6142.5e + d con c NUEVO sellado por pesos medidos (29/6/6, ninguno heredado) · descubrimiento char-3: los flats-cero (triángulos fuerzan ceros) — sin ellos nada cuadra · DOS capturas forenses: la herencia de pesos es un modo de fallo (w_c 6≠5, w_i 29≠24) · el −7 negativo resuelto (Möbius) · d(3) = dos stars pendientes con protocolo exacto (tipos a, b) · SIN GRITO — d, el ensamblaje U₃ y el clamp del collar ∀q siguen delante]. — Bisel (Constructor, Fable)**
