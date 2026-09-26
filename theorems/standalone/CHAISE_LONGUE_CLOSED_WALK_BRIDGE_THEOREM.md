> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-27
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · CLOSED-WALK BRIDGE THEOREM — v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CLOSED_WALK_BRIDGE_THEOREM.md
>
> **Status, as written in the document:** the uniform law of the campaign (`A_k(q) = N(n,q)`: MEASURED, over 40 cells, char 0 and char 3;
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · CLOSED-WALK BRIDGE THEOREM — v2
### Standalone · Tardieu (auditor), 27 Jul 2026 · **v2: Theorem B cold-gated; Corollaries E and F added**

Notation: `k ≥ 0`, `n = 2k+2`, `q ≥ 3` an integer, `m = ⌊q/2⌋`, `δ = q mod 2`,
`S = K[x_0,…,x_{n−1}]`, `E = (e_1,e_3,…,e_{2k+1})`, `A_k(q) = dim_K S/(E + m^{[q]})`, and

> `N(n,q) := n!·[t^n] cosh(t)^δ · I_0(2t)^m`,  `I_0(2t) = Σ_{j≥0} t^{2j}/(j!)^2`,

the uniform law of the campaign (`A_k(q) = N(n,q)`: MEASURED, over 40 cells, char 0 and char 3;
PROVED in no cell — only the floor `A ≥ N` is proved, for every integer `q` and every field of
characteristic `≠ 2`).

Walk notation, following the Hodge project's `THE_CLOSED_WALK_LAW`:

> `cw(m,N)` := number of closed walks of `N` unit steps on `Z^m` returning to the origin
> `      ` = constant term of `( Σ_{i=1}^{m} (x_i + x_i^{-1}) )^N`;
> `cwr(m,N)` := the same with a **rest step** allowed, i.e. constant term of
> `( 1 + Σ_{i=1}^{m} (x_i + x_i^{-1}) )^N`.

---

## THEOREM A (the walk form of the uniform law) — **PROVED, every even `n`, every `q ≥ 1`**

> `N(n,q) = cwr(m, n)` when `q` is **odd**, and `N(n,q) = cw(m, n)` when `q` is **even**.

*Proof.* Distribute the `N = n` steps among the `m` directions, `n_i` steps in direction `i`, plus
`n_0` rest steps. A walk closes iff each `n_i` is even, say `n_i = 2j_i`, with the `+` and `−` steps
balanced; the number of such walks is
`Σ n!/(n_0!∏(2j_i)!) · ∏ C(2j_i, j_i) = Σ n!/(n_0!·∏(j_i!)^2)`,
which is `n!·[t^n] e^t · I_0(2t)^m` — the rest steps contributing `e^t`, each direction `I_0(2t)`.
Without a rest step, drop the `e^t`. Finally, `I_0(2t)^m` is even in `t`, so for **even** `n` only the
even part of `e^t` contributes: `[t^n] e^t I_0(2t)^m = [t^n] cosh(t) I_0(2t)^m`. ∎

*(Verified numerically as a control: 52/52 cells, `k = 1..4`, `q = 3..15`, both parities,
`tardieu_hodge_bridge_v1.py`.)*

---

## THEOREM B (imported, **not re-derived cold here**)

From the Hodge project, `THE_CLOSED_WALK_LAW__1_.md`, Theorem 1, reported there as **PROVED** for
every even `n'` and every degree `m' > 2`, with a self-contained byte-exact verifier:

> `DS_{n'}(m') = cwr((m'−2)/2, n'+2)` if `m'` is even; `DS_{n'}(m') = cw((m'−1)/2, n'+2)` if `m'` is odd.

**Evidence grade carried:** PROVED *in the sister project*. It is **imported**, not re-proved in this
campaign. Anyone using this standalone as a load-bearing step must cold-gate Theorem B first.

---

## COROLLARY C (**the bridge**) — for every `k` and every `q`

> ## `N(n,q) = DS_{2k}(q+1)`.

*Proof.* Put `n' = 2k = n−2` and `m' = q+1`. If `q` is odd then `m'` is even and
`(m'−2)/2 = (q−1)/2 = m`, so Theorem B gives `DS_{2k}(q+1) = cwr(m, n)`, which is `N(n,q)` by
Theorem A. If `q` is even then `m'` is odd and `(m'−1)/2 = q/2 = m`, so Theorem B gives `cw(m,n)`,
again `N(n,q)` by Theorem A. ∎

**Consequence, stated plainly.** The uniform law discovered in this campaign — the one labelled
*"the widest discovery of the campaign, PROVED in no cell"* — is **not a new closed form.** It is the
Degtyarev–Shimada recursive-dimension count `DS_{2k}` re-indexed by `q ↦ q+1`, and in that guise it
already carries a **general-`k` proof in a sister project**. The Chaise Longue conjecture, in its
`q`-free form, therefore reads:

> ### `A_k(q) = DS_{2k}(q+1)` for every `k` and every `q`.

---

## CROSS-PROJECT ANCHORS — 9/9, computed by disjoint machinery

Left column: this campaign (Gröbner / point count on the `(2k+1)!!`-sheet arrangement).
Right column: closed walks on `Z^m` (Hodge). No shared code, no shared method.

| `k` | `q` | archive value | `N(n,q)` recomputed | `DS` label |
|---|---|---|---|---|
| 1 | 3 | 19 | 19 | `DS_2(4)` |
| 2 | 3 | 141 | 141 | `DS_4(4)` |
| 3 | 3 | 1107 | 1107 | `DS_6(4)` |
| 4 | 3 | **8953** | **8953** | `DS_8(4)` |
| 5 | 3 | **73789** | **73789** | `DS_10(4)` |
| 3 | 5 | 18733 | 18733 | `DS_6(6)` |
| 3 | 7 | 103279 | 103279 | `DS_6(8)` |
| 3 | 9 | 345465 | 345465 | `DS_6(10)` |
| 4 | 5 | 375745 | 375745 | `DS_8(6)` |

**`8953` is the sharpest of the nine.** In this campaign it is `P_4(3)`, computed by Orfila from the
sheet arrangement; in the Hodge project `DS_8` is reported as a **new row** produced by the
closed-walk law. **Two campaigns, two methods, no shared code, the same integer.**

---

## COROLLARY D (**what the bridge buys for the ceiling**)

The floor `A_k(q) ≥ N(n,q)` is proved. The whole of `GAP 3` is the ceiling `A_k(q) ≤ N(n,q)`.
Writing `A_k(q) = #\{\text{standard monomials of } in_>(E + m^{[q]})\}` for any term order `>`,
Corollary C turns the ceiling into a statement with **no ideal, no Frobenius and no tower in it**:

> ## `#std\big(in_>(E+m^{[q]})\big) \;\le\; \mathrm{CT}\Big[\big(1 + Σ_{i=1}^{m}(x_i+x_i^{-1})\big)^{n}\Big]` (`q` odd)

Both sides are **combinatorial and indexed uniformly in `k`**: the left by the minimal generators of a
staircase (MEASURED to freeze affinely for `q ≥ 2k+1`, `k = 1,2,3`, char 0 and 3, three term orders),
the right by walks. **This is the form in which the `k`-axis and the `q`-axis can fall together**,
because neither side is computed per-`k`: both are described by a rule in `k`.

---

## COROLLARY E (**the single imported ingredient of the two deposited papers, discharged**)

Both `THE_SOFA_THEOREM` (`k=2`) and `THE_HAMMOCK_THEOREM` (`k=3`) prove their floor
`A_k(q) ≥ P_k(q)` in three steps: (I) integer presentation, (II) rank semicontinuity
`rank_{F_3} ≤ rank_Q`, and (III) *"the characteristic-0 dimension is `P_k(q)`. This is the [DS]
target itself — `P` is their rank polynomial."* Step (III) is flagged in both papers as **the single
imported ingredient**, and both referee guides list it among the load-bearing joints — the Hammock
calling it *"the geometric dictionary … which we cannot strengthen from inside."*

**It can now be strengthened from inside, by a chain each of whose links is checkable here:**

1. **`P_k(q) = N(n,q)` for odd `q`** — proved in one line: for odd `q`, `F_q` is a set of `q` elements
   closed under negation and containing `0`, so the `F_q`-points of `⋃_J L_J` are exactly the
   `n`-tuples over `F_q` whose multiset is closed under negation, which is the definition of `N`.
2. **`N(n,q) = cwr(m,n)`** — Theorem A above, proved.
3. **`cwr(m,n) = DS_{2k}(q+1)`** — Theorem B, whose own proof is the reading of the generating
   expression printed in Degtyarev–Shimada, Remark 4.4, as a walk generating function.

> ### Hence `P_k(q) = DS_{2k}(q+1)` for every `k` and every odd `q`, by an explicit chain.

**What changed.** The import does not disappear — it **shrinks**: from *"our point-count polynomial is
their characteristic-0 target"* (a dictionary claim between two frameworks, unverifiable from inside)
to *"their Remark 4.4 prints this constant term"* (a citation of a printed formula, checkable line by
line). **That is the difference between a joint a referee must take on trust and one they can audit.**

---

## COROLLARY F (**the `k`-axis is the walk length, and it carries a recursion**)

In the bridge the two axes separate cleanly:

> **`k`-axis = the walk LENGTH `n = 2k+2`.  `q`-axis = the lattice DIMENSION `m = ⌊q/2⌋`.**

Walk counts are diagonals of rational functions, hence **D-finite** (Lipshitz). Therefore, for each
fixed `q`, the sequence `k ↦ N(2k+2, q)` satisfies a **linear recursion with polynomial coefficients
in `k`**. Measured orders (`tardieu_k_axis_recursion_v1.py`):

| `q` | `m` | rest | order of the `k`-recursion |
|---|---|---|---|
| 3 | 1 | yes | **2** (coefficient degree ≤ 3) |
| 4 | 2 | no | 1 (degree ≤ 2) |
| 5 | 2 | yes | 3 (degree ≤ 7) |
| 6 | 3 | no | 2 (degree ≤ 3) |
| 7, 9 | 3, 4 | yes | not found with order ≤ 6, degree ≤ 8 |

At the base floor of the tower, `q = 3`, the recursion is explicit and verified on 25 consecutive
steps:

> ### `9(k+2)(2k+3)(4k+11)·b_k − (4k+9)(20k²+90k+97)·b_{k+1} + (k+3)(2k+5)(4k+7)·b_{k+2} = 0`

with `b_0, b_1, b_2, b_3 = 3, 19, 141, 1107` — **exactly the four cases this campaign has already
closed and deposited.** The recursion has order `2`; two anchors determine the whole sequence, and the
campaign owns four, leaving two as controls.

> **Consequence, stated as a target and not as a result.** If the algebraic side `A_k(3)` is shown to
> satisfy this same order-2 recursion, then `A_k(3) = N(2k+2,3)` for **every `k`**, seeded by the
> deposited cases — i.e. the uniform law in `k` at the base floor of the tower. **Nothing here proves
> that.** It identifies, for the first time, a finite target on the `k`-axis.

**The algebraic shadow of the walk's "+2 steps", and exactly where it fails.** The specialisation
`x_{n−1} = t`, `x_n = −t` gives, verified for `k = 1,2,3`:

> `e_{2r+1}(x', t, −t) = e_{2r+1}(x') − t²·e_{2r−1}(x')`, `r = 0,…,k`,

and in `2k` variables `e_{2k+1}(x') = 0`, so the last generator collapses to `−t²·e_{2k−1}(x')`.
The image ideal is therefore `(e_1, …, e_{2k−3}, t²·e_{2k−1})` — **not** `E'`, one generator short by
a factor `t²`. **Hence `A_k(q) ≥ q·A_{k−1}(q)` does NOT follow, and is not claimed.** The `t²` twist
on the last odd elementary is the exact defect of the `k`-step, and it is the object to study.

*(Independent corroboration that this is the right axis: `THE_CLOSED_WALK_LAW` §6 states that the
remaining inductive step `rec(d, ℓ−1) → rec(d, ℓ)` — which is precisely this `k`-step — reduces to
Lemma 4.5 of [DS] and is **"near-mechanical, but not proved here."** Two campaigns arrive at the same
missing rung from opposite sides.)*

---

## WHAT THIS STANDALONE DOES **NOT** CLAIM

1. **It does not prove `A_k(q) = N(n,q)` in any cell.** `GAP 3` is untouched; `G = 3`.
2. **Theorem B is imported, and is now COLD-GATED in this campaign (v2).** Its verifier was re-run
   here from scratch: the walk formula reproduces the published closed forms `DS_2, DS_4, DS_6` on all
   `30` points `m = 3..12` (0 discrepancies), the hardware anchor `DS_6(4) = 1107`, and the whole new
   row `DS_8(3..10) = 252, 8953, 63504, 375745, 1172556, 3595177, 7939008, 17605249` byte-exact.
   **What remains imported is not a conjecture but a citation:** that Remark 4.4 of [DS] prints this
   generating expression for the rank. Corollary C is proved modulo that citation and nothing else.
3. **It is not an escape from the wall.** The Hodge auditor's own report states it explicitly:
   *`GAP 3` and the Hodge swan are the same wall in recursive dimension `≥ 4`*; what Hodge closes for
   free is recdim `0` and `2` (DS Cor. 1.7), i.e. exactly the `k = 0,1` this campaign already
   deposited. **No shortcut is claimed on that face and none exists.**
4. **The `red link` — the Hodge name for the rust test — is OPEN there**, measured `1.000` and not
   sealed, with an explicit warning not to measure it by `dim_{F_p}` versus `dim_Q`. This standalone
   does not use it. *(Independently, this campaign has now MEASURED the staircase to be identical in
   char 0 and char 3 at `k=2`, `q=5,7,9` — that is our own rust datum, and it is a measurement,
   not the red link.)*
5. **Theorem A is a re-expression, not a discovery.** Its only content is the walk reading of an
   already-known generating function. It is stated because it is the hinge of Corollary C.

---

## PROVENANCE

Built by **Tardieu** (auditor) on 27 Jul 2026, from `HODGE_EXTRACTION_REPORT_para_Orfila_COMPLETO.md`
(Cárdano, auditor of the Hodge project), Part B, lever 3. **The extraction report offered the
closed-walk law as "the total, not the summands"; the identification of that total with this
campaign's uniform law `N(n,q)` is made here for the first time and is what makes it usable.**
Motors: `tardieu_hodge_bridge_v1.py`, `tardieu_k_axis_recursion_v1.py`. Consumed by: `EL FRENTE v107`.

**v2 (27 Jul 2026):** Theorem B cold-gated in this campaign; Corollary E (discharge of the deposited papers' single import) and Corollary F (the `k`-axis recursion) added, after reading `THE_CLOSED_WALK_LAW`, `THE_SOFA_THEOREM` and `THE_HAMMOCK_THEOREM` in full.
