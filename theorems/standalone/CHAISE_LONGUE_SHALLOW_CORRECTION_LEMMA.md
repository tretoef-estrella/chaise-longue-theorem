> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-15
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SHALLOW-CORRECTION LEMMA* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHALLOW_CORRECTION_LEMMA.md
>
> **Status, as written in the document:** Serves: lock L2 (the collar-slack head `H_k`). Consumes, each a cited campaign theorem: Onset Identification (the head is `k+2` Koszul tails whose onsets are the absolute codimensions of the `k+2` lattice levels, `c_{2k+2}=1` derived `∀k`); the Gluing Law (cod…
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SHALLOW-CORRECTION LEMMA
## The collar-slack head's lattice correction is **two numbers, for every `k`** — and they sit on the two strata the campaign has already closed `∀k`

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · Auditor: **GETTLER** · 15 August 2026
*Serves: lock **L2** (the collar-slack head `H_k`). Consumes, each a cited campaign theorem: **Onset Identification** (the head is `k+2` Koszul tails whose onsets are the absolute codimensions of the `k+2` lattice levels, `c_{2k+2}=1` derived `∀k`); the **Gluing Law** (codim-1 swap stratum, PROVED `∀k`, `q`-free); the **Third Coefficient Law** (census top-3 `∀k`). Engine: `GETTLER_METAPHOR_GATES_v1.py`, all gates PASS, death criteria written before running. Origin: measured from the Architect's bicycle-and-eagle images under Ley 28.*

---

## 1. Setting

Let `k ≥ 2`, `n = 2k+2`. The **collar-slack head** `H_k(f)` is the pre-stable transient of branch 1 of the collar slack: `slack(f) = [stable quadratic] − H_k(f)` for `f < q` (Hammock Thm 4.2; at `k=3`, `slack(f) = 945f² + 350f + 1288 − H₃(f)`). It is `q`-free and supported below `f = k+2`.

**Campaign theorem (Onset Identification, PROVED `∀k`).** The head is a sum of `k+2` Koszul tails,
> `H_k(f) = Σ_{a=k+1}^{2k+2} c_a(k) · C(a−f−1, k)`,

whose onsets `a` are exactly the absolute codimensions of the `k+2` levels of the flat lattice — from the **sheets** (`a = k+1`) through the **swap flats** (`a = k+2`) down to the **origin** (`a = 2k+2`) — with the tail identity `C(a−f−1,k) = h_V(relcodim − f)`. The coefficient `c_{2k+2} = 1` is derived (the origin), and the gcd obstruction proves the `c_a` are annihilator-kernel dimensions, not flat counts.

Write `c_a^{rec}(k)` for the value the lattice (Noether) recursion returns at onset `a`, `c_a(k)` for the true value, and `δ_a := c_a − c_a^{rec}`. Write `H_k^{rec}` for the head assembled from `c^{rec}`.

**Gate, at the one dimension where both vectors are on file (`k=3`, onsets `a=4..8`):**

| | `c₄` | `c₅` | `c₆` | `c₇` | `c₈` | head `H₃(0..5)` |
|---|---|---|---|---|---|---|
| true (forced) | 106 | 52 | 27 | 3 | 1 | `679, 210, 49, 7, 1, 0` |
| recursion | 90 | 60 | 27 | 3 | 1 | `695, 218, 49, 7, 1, 0` |
| `δ_a` | **+16** | **−8** | 0 | 0 | 0 | `−16, −8, 0, 0, 0, 0` |

Both rows reproduce their filed sequences byte-exact (6/6 and 6/6). **The recursion is exact on every onset `a ≥ k+3`.**

---

## 2. The Lemma

> ### Lemma SC (Shallow Correction — PROVED for every `k`).
> Suppose the lattice recursion is exact on every onset `a ≥ k+3`, i.e. `δ_a = 0` for `a ≥ k+3`. Then for every `k` and every `f`:
> ## `H_k(f) − H_k^{rec}(f) = δ_{k+1}·[f = 0] + δ_{k+2}·( (k+1)·[f = 0] + [f = 1] )`,
> that is
> ## `δH(0) = δ_{k+1} + (k+1)·δ_{k+2}` , `δH(1) = δ_{k+2}` , `δH(f) = 0` for all `f ≥ 2`.
> **Consequently the entire correction to the head is two integers, `δ_{k+1}` and `δ_{k+2}`, whatever `k` is.**

*Proof.* By hypothesis `δH(f) = δ_{k+1}·C(k−f, k) + δ_{k+2}·C(k+1−f, k)`. Now
`C(k−f, k) = 1` if `f = 0` and `= 0` for `f ≥ 1`, since `k−f < k`;
`C(k+1−f, k) = C(k+1,k) = k+1` if `f = 0`, `= C(k,k) = 1` if `f = 1`, and `= 0` for `f ≥ 2`, since `k+1−f < k`.
Substituting gives the display. ∎

*Verification.* Brute-force over `k = 2..12`, `f = 0..7`: the two binomial profiles equal `[f=0]` and `(k+1)[f=0] + [f=1]` with no exception. At `k = 3`: `δH(0) = 16 + 4·(−8) = −16` ✓ and `δH(1) = −8` ✓ against the filed near-miss.

### 2.1 Three corollaries, and each removes something from the open list

**Corollary SC.1 (the "ramp" is not a fact — it is a consequence).** The campaign recorded the `k=3` correction as *"one ramp `−8·(2−f)₊`"*, i.e. a linear ramp switching off at `f = 2`, and carried the switch-off point as an unknown that might be `2` or might be `k−1`. **Lemma SC shows the support `{0,1}` is forced for every `k` by the binomial profiles alone.** One free parameter leaves the problem.

**Corollary SC.2 (the two corrected onsets are named strata, and they are the two the campaign already owns).** The onsets `a = k+1` and `a = k+2` are, by Onset Identification, exactly the **sheet stratum** and the **swap stratum**. These are precisely the two strata whose contributions are PROVED `∀k` elsewhere in the campaign: the sheets give the census's leading coefficient (`THIRD_COEFFICIENT`), and the swap flats are the subject of the **Gluing Law** (`slack_swap = C(k,2)·C(f+k−1, k−1)` per swap flat, `q`-free, PROVED `∀k`). **The two missing numbers are therefore to be read off theorems already on file, not measured.** This is the route of record for L2.

**Corollary SC.3 (a pre-registered consequence at `k = 4`, and it is falsifiable).** At `k = 4` the onsets are `a = 5..10`, so the shallow pair is `(a=5, a=6)` and every onset `a ≥ 7` is deep. The campaign has a filed binary transfer test, `c₇(4) ∈ {471, 479}` with `C(4) = 489 − c₇(4)`. Since `a = 7 ≥ k+3 = 7`, **Lemma SC's hypothesis predicts that `c₇(4)` equals the uncorrected recursion value.** If the resolved value disagrees with the recursion, the hypothesis "exact at `a ≥ k+3`" fails at `k=4` and the Lemma's scope shrinks with that number. *This is a death criterion, written before the test is run.*

---

## 3. Scope, stated exactly

- **The Lemma is unconditional and `∀k`** as an implication: given exactness at the deep onsets, the correction is two numbers.
- **Its hypothesis — "the recursion is exact on every onset `a ≥ k+3`" — is MEASURED at `k=3` (three of five onsets, `27, 3, 1`, byte-exact) and is not yet proved `∀k`.** It is the natural statement to attack next, and Corollary SC.3 gives it a falsifiable test at `k=4`.
- The Lemma says nothing about the **values** of `δ_{k+1}`, `δ_{k+2}`. At `k=3` they are `+16` and `−8`; every proposed `∀k` reading of those two numbers is degenerate at `k=3` and separates at `k=4`. **No reading is adopted here — that would be fabrication.**

## 4. What this changes for L2

Before: `H_k` had `k+2` unknown coefficients, of which one (`c_{2k+2} = 1`) was derived.
After: given the recursion, **`H_k` has exactly two unknowns for every `k`, they are attached to two named strata, and both strata already carry `∀k` theorems.**

The head system built on the `d = 11` measurement remains a second, independent route to the same object; it is now bounded by Theorem MK (no multiplicative law survives) and gated by the `f = 2` window (`44 | δ(2)`, `δ(2) ∈ [846, 2596]`, `h(2) ∈ [9, 27]`). **Two independent routes to two integers is the strongest position this lock has ever been in.**

---

**Grades.** Lemma SC: **PROVED ∀k** (one-line binomial argument; brute-verified `k=2..12`). Its hypothesis: **MEASURED at `k=3`**, with a pre-registered falsification at `k=4`. Corollaries SC.1, SC.2: **PROVED** given the Lemma and the cited campaign theorems. The values `δ_{k+1}, δ_{k+2}`: **OPEN** — this is what remains of L2 on this route.

*Origin note (Ley 28).* The Architect's images measured this turn: **the bicycle** — *"at the start you wobble; it depends on the number of wheels, on a unicycle it is much harder, on three or four it does not happen"* → the wobble is the pre-stable head, the wheels are the `k+2` tails, and the Lemma's content is that **the wobble stays exactly two positions long however many wheels you add**. **The far-sighted eagle** — *"sees badly close up, much better far away"* → the recursion is exact at the deep (far) onsets and blurred at the two shallow (near) ones. Both mapped; both converted.

— **GETTLER**, auditor.
