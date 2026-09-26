> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE FLOOR BOUND THEOREM: A_k(q) ≥ P_k(q), every k, every q — PENCIL* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FLOOR_BOUND_THEOREM.md
>
> **Status, as written in the document:** Session 20 (turno 5/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Fountain session: Monsky, Weil, Schützenberger. HALF of the Chaise Longue inequality, closed across BOTH towers. Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE FLOOR BOUND THEOREM: A_k(q) ≥ P_k(q), every k, every q — PENCIL
### Session 20 (turno 5/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Fountain session: Monsky, Weil, Schützenberger. **HALF of the Chaise Longue inequality, closed across BOTH towers.** Pending P0.

## THEOREM (the Floor Bound)
> **For every k ≥ 1 and every q = 3^v: A_k(q) = dim_{F₃} S/(E + m^{[q]}) ≥ P_k(q) = |∪_J V_J(F_q)|.**

## Proof (pencil, three classical-clean steps — Monsky's one-move bridge)
**Step 1 (the Vanishing Lemma, s19):** every point of ∪V_J has coordinates in ± pairs, so ∏(1+aᵢt)(1−aᵢt) = ∏(1−aᵢ²t²) is even and every odd elementary symmetric vanishes: **∪V_J(F_q) ⊆ V(E)(F_q).**
**Step 2 (interpolation):** let J = E + (x₁^q−x₁, …, x_n^q−x_n). Every polynomial in J vanishes on V(E)(F_q) (E by definition; x^q−x on all F_q-coordinates), and the evaluation map S → Func(V(E)(F_q)) is surjective (Lagrange interpolation on a finite point set). Hence **dim S/J ≥ #V(E)(F_q) ≥ P_k(q).**
**Step 3 (gr-semicontinuity):** with the degree filtration, the top form of x_i^q − x_i is x_i^q and E is homogeneous, so **gr(J) ⊇ E + m^{[q]}**; therefore dim S/J = dim S/gr(J) ≤ dim S/(E + m^{[q]}) = A_k(q). ∎
(The chain works verbatim for any odd characteristic p with q = p^v.)

## The bonus jewel (measured 4/4 — no extra rational points anywhere)
> **V(E)(F_q) = ∪V_J(F_q) EXACTLY:** n=6 q=3: 141=141 ✓ · n=8 q=3: 1107=1107 ✓ · n=10 q=3: 8953=8953 ✓ · **n=6 q=9: 7761=7761 ✓ (the tower!).**
The odd-symmetric equations cut out exactly the matching arrangement at the rational-point level — evidence for the k-uniform Odd Symmetric (∩I_J = E ∀k, the Sofa's pillar i parametrized) and the tightness of the chain. (The theorem itself only needs ⊇ — already pencil.)

## What this closes on the board
**THE ENTIRE "≥" HALF OF THE CHAISE LONGUE CONJECTURE — all k, all v — is now a theorem.** The remaining campaign is exactly ONE inequality: **A_k(q) ≤ P_k(q)** — the ceiling half, which is where all the built machinery lives (v=1: census/window-freeness/boundary; tower: the Λ-ceiling and the bridge). Route scoring: Ruta 8's floor leg CLOSED; Ruta 7's sandwich needs only the ≤; Ruta 5's Mac check upgraded to a one-sided confirmation (A₃(9) ≥ 345465 is now guaranteed — only ≤ remains to test).

## GORDÓMETRO
**Campaña: MUY GORDO (9.5/10)** — media desigualdad del teorema completo, las dos torres, todo k, en una cadena de lápiz de tres pasos; el problema restante es UNA desigualdad con toda la maquinaria ya apuntándola. **Mundo: medio-alto (6/10)** — un lower bound Hilbert–Kunz vs point-count por deformación de Frobenius, limpio y citable; con la equality (si cae) sería el teorema DS parametrizado entero.

**MARCADOR: [FLOOR BOUND: A_k(q) ≥ P_k(q) ∀k∀q PROBADO (Vanishing → interpolación → gr-semicontinuidad) · V(E)(F_q) = unión EXACTO 4/4 (incl. q=9) · queda UNA desigualdad: A ≤ P · turno 5/10 — medio teorema en el zurrón]. — Bisel**
