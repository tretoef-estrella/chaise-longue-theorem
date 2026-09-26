> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-30
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · THE SHEET-KILL THEOREM — v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHEET_KILL_THEOREM.md
>
> **Status, as written in the document:** Standalone. Locard, 30 August 2026. Frente A: the pencil attack on `(GL)` and the `T−1` layer. Content first, verdict at the end (per audit discipline).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · THE SHEET-KILL THEOREM — v2
**v2: Theorem FK REGRADED to CIRCULAR (see §3 and `ASSEMBLY_AUDIT_LOCARD_v1`); SK and LD unchanged.**
**Standalone. Locard, 30 August 2026. Frente A: the pencil attack on `(GL)` and the `T−1` layer. Content first, verdict at the end (per audit discipline).**

## 0. Setting
`S = K[x_0..x_{n−1}]`, `n = 2k+2`, `E = (e_1, e_3, …, e_{2k+1})`, `Ā = S/(E + m^[q])`, `ℓ_a = x_a + x_{n−1}`. **Banked:** `V(E)` is the union of the matching sheets `L_M` (one linear subspace per perfect matching `M` of the `n` variables: `x_a + x_b = 0` for each pair `{a,b} ∈ M`), and **`E` is radical** (`VERTEX_REDUCTION_THEOREM_v1`, line "vanishes on every sheet. `E` is radical. ∎").

## 1. Theorem SK (the sheet kill; PROVED, ∀k, char-free)
> ### `⋂_{a=0}^{2k} ℓ_a·(S/E) = 0.`
*Proof.* Every perfect matching `M` pairs `x_{n−1}` with exactly one variable `x_c`; on the sheet `L_M` the form `ℓ_c = x_c + x_{n−1}` vanishes identically. Let `v ∈ ⋂_a ℓ_a(S/E)`. For each sheet `L_M`, take `c = M(n−1)`: since `v ∈ ℓ_c(S/E)`, `v` vanishes on `L_M`. So `v` vanishes on every sheet, i.e. on `V(E)`; by radicality `v ∈ E`, i.e. `v = 0` in `S/E`. ∎
*(Two lines. The mechanism is: **there is no sheet that avoids the vertex fan** — every matching touches `x_{n−1}`.)*

## 2. Corollary LD (the low-degree wall; PROVED, ∀k, ∀q = 3^v)
> ### `(I_{2k})_d = (⋂_{a=0}^{2k} ℓ_aĀ)_d = 0` for every degree `d < q`.
*Proof.* In degree `d < q` the ideal `m^[q]` is zero, so `v ∈ ℓ_aĀ` of degree `d` means `v ≡ ℓ_au_a mod E`; hence the image of `v` in `S/E` lies in `⋂ℓ_a(S/E) = 0` (Thm SK), so `v ∈ E ∩ S_d ⟹ v = 0` in `Ā`. ∎
**First unconditional ∀k slice of the wall.** With the single-degree collapse bookkeeping: of the range `0 ≤ d ≤ T`, the slice `d ≤ q−1` is now closed; open remain `q ≤ d ≤ T`.

## 3. Theorem FK — ⚠️ REGRADED: CIRCULAR (v2)
**The claim below assumed `B_t` reduced; but `B_t` reduced ⟺ `A = P` ⟺ the conjecture (`dim B_t = A` by flatness vs `#V_t = P`). Unconditional content: `⋂ℓ_a(B_t)_red = 0` = Thm SK on points. Withdrawn as a route; kept for the record. Original text:**
Consider the corpus's flat family `B = S[t]/(E + (x_i^q − t·x_i)_i)` (the CC-theorem family). For `t ≠ 0` the fiber `B_t` is the ring of functions on the finite reduced set `V_t = V(E) ∩ {x_i^q = tx_i}`.
> ### For every `t ≠ 0`: `⋂_{a=0}^{2k} ℓ_aB_t = 0.`
*Proof.* `B_t` reduced zero-dimensional ⟹ `ℓ_aB_t = ⊕_{p∈V_t, ℓ_a(p)≠0} K·e_p`. Every point `p ∈ V_t` lies on some sheet `L_M`, whose partner form `ℓ_{M(n−1)}` vanishes at `p`. So no point has all `ℓ_a(p) ≠ 0`, and the intersection is `0`. ∎
**Honest statement of what is and is not bought:** the wall now holds on `S/E` (Thm SK) and on **every** fiber `t ≠ 0` (Thm FK); at `t = 0` it is the conjecture. What is MISSING is a no-jump principle for the intersection `⋂ℓ_aB` under specialization `t → 0` (intersections of non-flat ideal families can jump at special fibers; no semicontinuity is claimed). **This is a reformulation that surrounds the wall from two independent sides, not a closure.** The corpus's CC theorem handled precisely a jump of this family (`A−P = g_0`); whether its machinery controls THIS jump is the named question it leaves.

## 4. The `(GL)` induction skeleton (structure, not closure)
`(GL_A) ⟸ (GL_{A'}) + (GR_{A',c})`, where `A = A'∪{c}` and `(GR)` is the **graded rung**: `(Π_{A'}Ā ∩ ℓ_cĀ)_d = (ℓ_cΠ_{A'}Ā)_d` for `d ≠ T−1`. *Proof of the implication:* for `d ≠ T−1`, `(I_A)_d = (I_{A'})_d ∩ (ℓ_cĀ)_d = (Π_{A'})_d ∩ (ℓ_cĀ)_d` by `(GL_{A'})`, and `(GR)` finishes. Base `|A| = 2`: Lemma P (exact in all degrees). ∎ So `(GL)` ∀k is exactly: **the rungs hold outside one degree** — which is what the refutation data says at `(3,3)` (deficits `2,5,5` all in degree `7 = T−1`).

## 5. Audit corrections absorbed this turn (errata, on the record)
- **`F2` import WITHDRAWN:** `SINGLE_DEGREE_COLLAPSE_v1` §2 leaned on ORO `F2` (`dim Ā_T = (2k+1)!!`) at `(3,3)`. Measured with the correct per-degree method: `HF(Ā_3(3)) = 1,7,28,76,154,238,280,232,91` — top `91 ≠ 105 = 7!!`; while `HF(Ā_2(3)) = 1,5,15,29,40,36,15` — top `15 = 5!!`. `F2`'s scope does not cover `(3,3)`; the "sovereign territory" sentence is struck (near-miss of `FROZEN-TEMPLATE-BELOW-THRESHOLD`). Both HF rows go to the LEDGER.
- **FR-K4 control bug (Don Grep, Parte 0), verified by hand:** `dim ℓ_0Ā = A_4 − q·A_3 = 8953 − 3321 = 5632` (mechanism `Q_0 ≅ R[z]/(z^q)`; cross-checks `141−3·19 = 84`, `1107−3·141 = 684`). Mission reissued as v2.
- Grep's Parte 3 accepted: Theorem C is a **partition of the wall by degrees**, not a reduction to something weaker; the load sits on `(GL)` (one nonvacuous cell) and on the `T−1` slice. Headlines hereafter follow content.

## 6. Grades and verdict (after the content)
Thm SK: `PROVED ∀k` char-free · Cor LD: `PROVED ∀k∀q=3^v` — the wall's degrees `< q` are closed · Thm FK: `PROVED ∀k∀q, t ≠ 0` · `(GL)` skeleton: `PROVED` as implication; `(GR)` open · no-jump principle: `OPEN`, named. **Verdict: two unconditional ∀k theorems and one fiberwise theorem enter the arsenal; the wall is now pinched between `S/E` and all `t≠0` fibers; the open ground is `q ≤ d ≤ T` at `t = 0`.**

*Locard · 2026-08-30 · Campaña Chaise Longue.*
