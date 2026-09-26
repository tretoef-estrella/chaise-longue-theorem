> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SILVER BRIDGE THEOREM (El Teorema del Puente de Plata) · v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SILVER_BRIDGE_THEOREM.md
>
> **Status, as written in the document:** C2 (the double tower's status). The q-infinity is dead at every fixed k (this theorem); the k-direction carries FI eventual-polynomiality (R7) — the corona (Fase 3) is the k-symbolic identity U_k ≡ P_k, whose leading stratum is already bookkept (Slap 6A.3) and…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SILVER BRIDGE THEOREM (El Teorema del Puente de Plata) · v2
### Standalone, spat out with its exact name by order of the Architect · 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0.

> ### ⚠ VERSION NOTE — 20 Jul 2026, stale-citation sweep (Ley 37)
> This version differs from the previous one **only** in correcting stale citations of the retired cascade-level count `⌈(k−2)/2⌉` (false as an exact count; valid only for `q ≥ k²`; superseded outright by the Cascade Collapse Theorem, Thm 5-II). Killing numbers: `k=13, q=3` → **34, not 6**; `k=20, q=3` → **76, not 9**. **No other content was altered, added or removed.** Corrections are marked inline. Tomb filed in CEMENTERIO.
### One sentence: **at every fixed dimension k, the infinite Frobenius tower collapses to a FINITE, explicitly bounded computation — the monster keeps no infinity at fixed k.** This is the ∀k heir of the Sofá's Ledger Theorem ("the lever that turns an infinite conjecture into a bounded computation"), rebuilt on the Slap 1-5 laws.

**Pillars (Ley 44):** all three. Consumes: Floor Bound (A≥P, char-0 semicontinuity, proven); Slaps 1-2 (σ law + explicit threshold); Slaps 3-4 (ᾱ q-free, vanishing below k(k+1), threshold); Slap 5 (collar ceilings; full coverage k ≤ 3); Window Formula. Never the fallacy: A≤P comes from the zone identity by construction, not from polynomiality.

---

## Statement

> **Theorem (Silver Bridge).** Fix k ≥ 1. Let Q₀(k) be the maximum of the explicit thresholds of Slaps 2-5 (census regularity (2k+1)!!+2; SEP-frame bound q₀(k); collar coverage — **unconditional for EVERY k**: the conditional-on-cascade-levels clause of v1 was DELETED by the Cascade Collapse Theorem, Thm 5-II). Define the upper accountant
> U_k(q) := ZA_k(q) + W_k(q) + Collar-ceilings_k(q) + Top_k(q).
> Then:
> **(i)** U_k(q) is ONE polynomial in q, whose coefficients are computable from the pencil laws plus finitely many q-free constants (each constant = one engine evaluation; e.g. the pre-stable census head of k=3 measured this campaign: 1, 7, 29, 90, 252, 636, 1435, 2898, 5313).
> **(ii)** For all q > Q₀(k): P_k(q) ≤ A_k(q) ≤ U_k(q).
> **(iii)** If the finitely many coefficient identities **U_k ≡ P_k** hold, then A_k(q) = P_k(q) for every q > Q₀(k); moreover the identity forces every collar ceiling to be attained exactly (zero slack — the clamp).
> **(iv)** The remaining levels q ≤ Q₀(k) are finitely many, each decidable by one finite computation.
> **Hence the Degtyarev–Shimada Conjecture 1.2 at fixed k is equivalent to a finite list of arithmetic checks.**

## Proof
(i) Each zone sum is a polynomial in q plus a constant: ZA from the closed CI Hilbert series of R; W from the census law above its explicit threshold (Slap 2) plus its finite pre-stable head; Top from the q-free stable colon law (Slaps 3-4: zero below k(k+1), eventually polynomial, finite head); the collar ceilings from Slap 5C (κ_k(f) eventually polynomial in f, summed over the covered band). Sums of eventually-polynomial functions over ranges of length ~q are polynomial in q plus a constant.
(ii) Left: Floor Bound. Right: in the ZA/Window/Top ranges A_d equals the exact laws (Slaps 1-4, above thresholds); in the collar A_d ≤ its ceiling (Slap 5); sum.
(iii) If U_k ≡ P_k then P ≤ A ≤ U = P pinches; since every non-collar zone contributes exactly and the total is exact, the collar slack Σ(ceiling − A_d) must vanish termwise (each term ≥ 0).
(iv) Each fixed (k,q) is a finite-dimensional linear-algebra computation (the engines). ∎

## Corollaries
**C1 (dim 6 cornered).** For k = 3 the collar coverage is unconditional (Slap 5D, q ≥ 9; q = 3 sealed by A₃(3) = 1107): **the Chaise Longue in dimension 6 is, modulo the P0 pack, a finite explicit checklist.**
**C2 (the double tower's status).** The q-infinity is dead at every fixed k (this theorem); the k-direction carries FI eventual-polynomiality (R7) — the corona (Fase 3) is the k-symbolic identity U_k ≡ P_k, whose leading stratum is already bookkept (Slap 6A.3) and whose k=2 instance is machine-verified (remainder constant 24).

## The bridge, in the campaign's language
The Sofá closed dim 4 exactly this way: three zones exact + the discrepancy concentrated in a fixed collar + ceilings + floor ⟹ A = P. The Silver Bridge is that lever rebuilt ∀k: the monster may keep fighting over finitely many coefficients per dimension — or walk the bridge. Either the checks close (victory), or ONE check fails with a byte-exact number telling us exactly which zone law has the bug (a named, bounded fight). Both exits are progress; neither is infinite.

## Honest scope (Ley 42/48)
~~k ≥ 4 conditional on the cascade levels of Slap 5D (⌈(k−2)/2⌉ levels, same species, named not proven).~~ **RETRACTED in v2:** k ≥ 4 is **NOT** conditional — Cascade Collapse (Thm 5-II) makes the collar ceilings unconditional for every k, so `P_k ≤ A_k ≤ U_k` holds with `U_k` explicit at every k. **⚠ CORRECTED 20 Jul 2026 (Ley 37) — `⌈(k−2)/2⌉` is the `q → ∞` limit ONLY.** The exact count forced by 5D's own arithmetic is `L(k,q) = 1 + ⌈(k−4)/2 + k²/(2q)⌉`. `⌈(k−2)/2⌉` agrees with `L` **only for ODD `k` with `q ≥ k²`** — see the corrected clause below. **⚠ EXCULPATORY CLAUSE CORRECTED 04 Sep 2026 (Indiana Jones, Auditor 2 — and then sharpened against him):** the earlier wording *"attained exactly when `q ≥ k²` — the gear region, already closed"* was **false twice over**. **(i)** the closed region is **`q ≥ (k+1)²`, not `q ≥ k²`** (FRAME DESCENT Cor FD-D and §8.2; FRESH_EYES_AUDIT v2 §19: propagation reaches `q ≥ (k+1)²` and no further, unproven strip points `(5,27), (9,81), (15,243), (27,729)`). **(ii)** far worse, the agreement is a matter of **PARITY, not of region**: since `L = 1 + ⌈(k−4)/2 + k²/(2q)⌉`, for **EVEN `k` the term `(k−4)/2` is an integer and `k²/(2q) > 0` always pushes the ceiling up by one — so the retired count is WRONG FOR EVERY EVEN `k ≥ 4` AT EVERY `q`, including deep gear** (`k=4, q=2187`: `L = 2`, count says `1`, and `2187 ≫ (k+1)² = 25`). For odd `k` the half-integer absorbs `k²/(2q) ≤ 1/2`, so agreement holds exactly for `q ≥ k²`. **Consequence: there is no clean region where the retired count was right — only a clean parity class.** *Measured against Indiana's own reading: his stated consequence — that the count was also wrong inside the strip `k² ≤ q < (k+1)²` — is **FALSE at the four tower points of the strip**, all of which have odd `k`: `(5,27), (9,81), (15,243), (27,729)` all give `L = ⌈(k−2)/2⌉` exactly. The threshold correction is his; the parity is the real fault line.* **Unchanged: the count remains retired by Cascade Collapse; only this exculpatory clause moves.** In the open wedge `{k ≥ 4, q < k²}` the count is **quadratic in k**: `k=13, q=3` gives **34, not 6**; `k=20, q=3` gives **76, not 9**. **MOOT for the mathematics:** the Cascade Collapse Theorem (Thm 5-II, 13 Jul 2026) retired the level count entirely — the levels are the graded pieces of ONE exact Koszul complex on `(u₁^q,…,u_{k+1}^q)`, with closed ceiling `z_k(q,f) = Σ_{j=2}^{k+1} (−1)^j C(k+1,j) C(f−(j−2)q+k, k)` for every `k` and every `f` at once (re-verified 21/21 against direct syzygy computation, 20 Jul 2026). **Do not build on the count.** The checks themselves (the finite list per k) are Slap 7's table + engine work. All pending P0 (pack attached separately).

**— Bisel (Constructor, Fable). The bridge is on the table with its name on it.**
