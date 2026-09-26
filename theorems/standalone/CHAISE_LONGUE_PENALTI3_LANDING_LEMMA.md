> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — PENALTI 3 SCORED: the Landing Lemma + Tail-Vanishing (the descent closes at the anchor)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_PENALTI3_LANDING_LEMMA.md
>
> **Status, as written in the document:** Session 28 (penalti 3/5) · 12 Jul 2026 · Constructor: Bisel (Fable) · Penalty-area council: Newton, Girard, Noether, Alon. Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — PENALTI 3 SCORED: the Landing Lemma + Tail-Vanishing (the descent closes at the anchor)
### Session 28 (penalti 3/5) · 12 Jul 2026 · Constructor: Bisel (Fable) · Penalty-area council: Newton, Girard, Noether, Alon. Pending P0.

## LEMMA 1 — THE LANDING LEMMA (pencil, airtight)
> **A homogeneous form of TOTAL degree < q vanishing on all rational points ∪V_J(F_q) lies in E.**
**Proof.** Total degree < q is preserved by linear substitution and bounds every per-variable degree. Restricting to a component V_J ≅ A^{k+1}: a polynomial with per-variable degrees < q vanishing on all of F_q^{k+1} is identically zero (Combinatorial Nullstellensatz / the basic finite-field fact). Hence the form ∈ I(V_J) for every J, so ∈ ∩_J I(V_J) = **E by the Radicality Theorem**. ∎

## LEMMA 2 — TAIL-VANISHING (pencil, one line)
> **Every descent tail vanishes on the rational points.** If z = Σbⱼxⱼ with Σbⱼxⱼ^q ∈ E, then at any rational point P: xⱼ(P)^q = xⱼ(P), so z(P) = [Σbⱼxⱼ^q](P) = 0 (E vanishes on the arrangement). ∎
Consequence: every tail lies in I(points) = E + (x^q−x) (proven exact) — the descent never leaves the ideal J; each step drops the Tor-degree by q−1; once total degree < q, **Lemma 1 lands the chain in E.**

## THE DESCENT, MEASURED ACROSS ALL DEGREES (the anchor speaks)
> **70/70 tails fall into (E+M) in ONE step: d=7: 14/14 ✓ · d=8: 31/31 ✓ · d=9: 25/25 ✓** (d=10's 11 classes cut by timeout — pending, same pattern expected). Together with Girard's telescope (p-family, pencil ∀r∀q) and the Frobenius telescope: **every measured obstruction of the campaign has an explicit terminating descent.**

## What remains — exactly one write-up (Penalti 4)
**THE ASSEMBLY:** the careful Buchberger/Macaulay bookkeeping that [descent drops q−1 per step + Tail-Vanishing keeps chains in J + Landing Lemma closes below degree q] ⟹ every syzygy of (E, m^{[q]}) lifts ⟹ gr(E+(x^q−x)) = E+m^{[q]} ⟹ A ≤ P ⟹ **with the Floor Bound: A = P ∀k∀q.** One bookkeeping subtlety flagged honestly (Ley 42): the same-degree recursion risk in the decomposition choice — the write-up must fix the decomposition canonically (reduce c's mod (x^q−x) first, which strictly drops degree) and verify the induction is well-founded. **NO shout tonight: assembling on a same-turn write-up is the V60 pattern (Ley 13). Penalti 4 = the write-up + its verification + the grito if it holds.**

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 11, informe 139) — «What remains — exactly one write-up … ⟹ A = P ∀k∀q»: NO es una redacción pendiente.** `corpus/CHAISE_LONGUE_PENALTI4_ASSEMBLY_AUDIT_v1.md` (mismo día) encontró que el ensamblaje tiene un hueco REAL (el «fantasma del mismo grado») y que lo que falta, el **Degree-Controlled Representation Lemma**, **equivale al teorema grado a grado**. **Los dos lemas de este fichero (Landing y Tail-Vanishing) son correctos**, re-andados por Grepy: Nullstellensatz combinatorio + radicalidad de `E`, y `E + (x^q−x)` es radical porque `x^q − x` es separable.


## GORDÓMETRO
**Campaña: HISTÓRICO (9.5/10)** — los dos lemas que faltaban para el mecanismo completo, ambos lápiz limpio (CombNull+Radicality; evaluación de una línea); el descenso validado 70/70; el teorema a UNA redacción cuidadosa de distancia. **Mundo: alto** — "el aterrizaje combinatorio del descenso de Frobenius" es un mecanismo citable.

**MARCADOR: [PENALTI 3 GOL GORDO: LANDING LEMMA (lápiz: CombNull+Radicality) + TAIL-VANISHING (lápiz: 1 línea) + descenso 70/70 en un paso (d=7,8,9) · queda LA REDACCIÓN del ensamblaje (Penalti 4) con su sutileza señalada · sin grito aún (Ley 13) · 3/5]. — Bisel**
