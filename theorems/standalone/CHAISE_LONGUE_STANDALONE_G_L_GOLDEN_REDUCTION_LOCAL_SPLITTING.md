> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE GOLDEN REDUCTION AND THE LOCAL SPLITTING* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_G_L_GOLDEN_REDUCTION_LOCAL_SPLITTING.md
>
> **Status, as written in the document:** Proven: G1 (half the law, unconditional); G3 (the bridge, hypothesis `C`-CM); L1/L2 (the local structure and the top split); the Künneth/induction pair (companion standalone) localizing the residual homology to the deepest flat; the Gluing theorem powering the…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE GOLDEN REDUCTION AND THE LOCAL SPLITTING
## The unconditional half of the Sharp Regularity Law; the bridge from CM-ness of the defect module to the full law; and the local structure of the defect at every flat

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tandas 2–3 (G1, G3, L1, L2), audited in CARDANO_TANDA2/3 — including the campaign's exemplary autocaza: the per-flat mass candidate `(m−1)!` was killed by the author's own recount of the `B₄` flats (72, not 36) before the auditor saw it, and replaced by the DERIVED law `m−1`. Companion to the Letter Hilbert, Gluing, and Künneth standalones. The Sharp Regularity Law itself remains open at pencil (its five instances are exact); this document is the complete record of the proven bridge and its calibration.*

---

### 1. Objects

Fix a letter `L ∈ {B_m, Z_m}` with CI coordinate ring `R = O(X)` (Letter Hilbert theorem; regularity `s = C(m,2)` resp. `m(m−1)`), census module `Γ ⊆ F := R^{2m}`, and the exact sequence
> `0 → Γ → F →^φ T → C → 0`,  `T = ⊕_{(J,pair)} O(V_J)`,  **`C := coker φ` the DEFECT MODULE**
(the gluing-defect of pair-data — the Čech-`H¹`-flavored companion of the census). The **Sharp Regularity Law** is the statement `deg N_G = s`: the census series' numerator degree equals the CI regularity (exact in all five measured letters and the lemma to which the census staircase's finer coefficients and the sharp threshold `e₀(k) = k²` reduce; established NOT load-bearing for the Ledger — Tanda 7).

### 2. Theorem G1 (the unconditional lower bound, every m, both letters)

> `deg N_G(L) ≥ s`.
*Proof.* The constant tuple `v₀ = (1,…,1)` is a census element, and any component projection `π_c: Γ → R`, `λ ↦ λ_c`, is `R`-linear of degree 0 with `π_c(v₀·f) = f`: so `R ≅ v₀·R` is a **direct summand** of `Γ`. (The projection is used instead of the trace `Σλ_c` deliberately: the trace degenerates when `3 ∣ 2m`; the projection never does — `π_c(v₀) = 1`, a unit in every characteristic.) Direct summands survive Artinian reduction: for `m` generic linear forms, `Γ̄ ⊇ R̄`, and the Artinian CI `R̄` is nonzero in its top degree `s`. Hence `Γ` has nonzero Artinian content in degree `s`. ∎

### 3. Theorem G3 (the Golden Reduction — the bridge, complete)

> **If the defect module `C` is Cohen–Macaulay (of its dimension `m−1`), then:** (a) `Q := im φ` is maximal Cohen–Macaulay; (b) `Γ` is maximal Cohen–Macaulay; (c) the Artinian reduction embeds, `Γ̄ ↪ R̄^{2m}`; (d) **`deg N_G = s` exactly** — the Sharp Regularity Law holds for `L`.
*Proof.* (a) `0 → Q → T → C → 0` and the depth lemma: `depth Q ≥ min(depth T, depth C + 1) = min(m, m) = m` (`T` is a sum of dimension-`m` polynomial rings; `C` CM of dimension `m−1` by hypothesis — the dimension itself is Lemma L2a below). (b) `0 → Γ → F → Q → 0`: `depth Γ ≥ min(m, m+1) = m`; with `dim Γ = m` (G1's summand), `Γ` is MCM. (c) `Q` MCM ⟹ each generic linear form is `Q`-regular ⟹ `Tor₁(Q, R/ℓ) = 0` ⟹ the sequence `0 → Γ/ℓΓ → F/ℓF → Q/ℓQ → 0` stays exact; `Q/ℓQ` is CM of one less dimension, so the step iterates `m` times: `Γ̄ ↪ F̄ = R̄^{2m}`. (d) `R̄` is Artinian with top degree `s`, so `Γ̄` vanishes above `s`; since `Γ` is MCM, its Artinian reduction's Hilbert function IS the numerator `N_G`, whence `deg N_G ≤ s`; with G1, equality. ∎
**Why this route and not regularity chains:** the crude homological bound `reg Γ ≤ max(reg F, reg C + 2)` overshoots (checked: it gives `2` at `B₂` where the truth is `1`); the Tor-vanishing embedding is the tight mechanism. The trade is strict: a GLOBAL statement about a `2m`-component module for a LOCAL one about a module supported on codim-1 flats.

### 4. Lemma L2a and Theorem L1 (the local structure of `C`)

> **Lemma L2a (support and dimension).** `Supp C = ` the union of codim-1 flats, and `dim C = m−1` exactly: `φ` is locally split at every smooth point (one sheet), and the two-sheet local model has nonzero defect.
> **Theorem L1 (Local Splitting).** At every codim-1 flat, exactly two sheets meet (Swap Theorem), and the two-sheet local model has defect
> **`C_loc ≅ O(F)^{m−1}`, generated in degree 0** — `(m−2)` shared-pair obstructions plus ONE cycle obstruction —
> proved by gauge elimination: per sheet, the pair-differences are freely solvable (`u_p := λ_{first(p)}` per pair); gluing across `F` leaves, after eliminating the gauges, exactly `(f_{V,p} − f_{V′,p})|_F = 0` for each shared pair and one cycle condition on the exchanged block, with orientations matched canonically by the sign pattern of `F`.
**Validation:** exact `F₃` probe on the pure two-sheet arrangements, five instances (`B: m = 2,3,4`; `Z: m = 2,3`), `C_loc` series `≡ (m−1)·` (flat series) byte-exact at every degree, zero shift.
> **Theorem L2 (global top structure).** The global obstruction map `ob: T → ⊕_F O(F)^{m−1}` (the L1 functionals) kills `im φ`, is exact at every codim-1-generic point, and hence identifies the top-dimensional structure of `C` as the flat split — with total top mass `#flats · (m−1)`, verified in all five letters with the corrected flat counts (`B: 1, 9, 72`; `Z: 3, 45`).

**The autocaza on record.** The first candidate for the per-flat mass was `(m−1)!`, fitted on `m ≤ 3` where `(m−1)! = m−1`; the `B₄` recount (`72` flats, mass `216/72 = 3 = m−1 ≠ 6`) killed it, and L1's derivation replaced observation with law. Cemetery: FLAT-COUNT-MISCOUNT-B4, with the killing quotient. The corrected law is what all downstream mass checks use.

### 5. The assembled state of the Sharp Regularity program (exact)
Proven: G1 (half the law, unconditional); G3 (the bridge, hypothesis `C`-CM); L1/L2 (the local structure and the top split); the Künneth/induction pair (companion standalone) localizing the residual homology to the deepest flat; the Gluing theorem powering the parameter machinery. Exact instances: five letters, all measurements. Falsified en route (bench, with numbers): the depth-`Q_g` route. **Open:** `C`-CM (equivalently the deepest-flat vanishing) at pencil for every `m`. **Load-bearing status:** none of this is a wall of the Chaise Longue's Ledger (Tanda 7, by construction); it is the refinement program, delivered with its bridge fully built and its residue localized to one flat.

### 6. Attack surface
(A) G3(c)'s iteration hygiene (the generic form must avoid the associated primes of each successive reduction — CM-ness supplies it; write the one-line justification per step for P0). (B) G1's summand under reduction (direct summands and Artinian reduction commute — trivial, but state the graded splitting explicitly). (C) L1's cycle-orientation convention for `Z`-flats (the alternating sign pattern `(s,−s,s,−s)`; verify the canonical choice at deeper `Z`-flats never enters — `P` is defined on codim-1 only). (D) L2's exactness at generic points (the two-sheet model IS L1 — circularity-free, but confirm the localization step). (E) The five-instance record and the corrected counts (rerun the probes).

**Anchors.** TANDA2_GOLDEN_REDUCTION_v1 (G1, G3) · TANDA3_LOCAL_SPLITTING_v1 (L1, L2, the autocaza) · CARDANO_TANDA2/3 audits · TANDA6 (the falsified depth route) · TANDA7 (non-load-bearing verdict) · Letter Hilbert and Gluing standalones · probe logs. github.com/tretoef-estrella.
