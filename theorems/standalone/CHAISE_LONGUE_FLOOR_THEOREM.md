> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE FLOOR THEOREM (P_k(q) closed, every dimension, every level)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FLOOR_THEOREM.md
>
> **Status, as written in the document:** Standalone · 12 Jul 2026 · ASALTO III CLOSED. The first complete standalone of Fase 2. Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE FLOOR THEOREM (P_k(q) closed, every dimension, every level)
### Standalone · 12 Jul 2026 · ASALTO III CLOSED. The first complete standalone of Fase 2. Pending P0.
### Born from the Architect's echolocation metaphor: ask the sonar the INVERSE question — which vectors are NOT in the union — and read all echoes at once. Pillar (Ley 44): Point-Count (ii), now a theorem.

## Theorem (the floor, closed form, both towers at once)
For every k ≥ 1 and every odd prime power q:
> **P_k(q) = |∪_J V_J(F_q)| = #{ x ∈ F_q^{2k+2} : for every v ≠ 0, #{i: x_i = v} = #{i: x_i = −v}, and #{i: x_i = 0} is even }.**
Equivalently, with m = (q−1)/2:
> **P_k(q) = (2k+2)! · [x^{2k+2}] cosh(x) · B(x)^m, where B(x) = Σ_{b≥0} x^{2b}/(b!)².**

## Proof (pencil, five lines)
Define the opposition graph G_x on [2k+2]: edge (a,b) iff x_a = −x_b (a ≠ b). Then x ∈ V_J ⟺ J ⊆ G_x; hence **x ∈ ∪V_J ⟺ G_x contains a perfect matching.** The components of G_x are: one complete bipartite K_{r_v, s_v} for each value-pair {v,−v} (r_v = #(x=v), s_v = #(x=−v)), and one complete graph K_{c₀} on the zero coordinates (0 = −0). A disjoint union of such graphs has a perfect matching ⟺ every K_{r,s} has r = s and c₀ is even. ∎
(Polynomiality in q: [x^{2k+2}] of B(x)^m is a polynomial in m of degree ≤ k+1 — **P_k is a degree-(k+1) polynomial in q, proven ∀k.**)

## Verification — every echo, all exact (19/19)
- **dim 4 vs P₂:** q = 3, 5, 7, **9 (= the Sofa's SEALED A(9) = 7761)**, 11, 13, **27, 81 (high tower)** — all ✓.
- **dim 6 vs P₃:** q = 3…13 (six values) ✓. **dim 8 vs P₄:** q = 3…11 (five values) ✓.

## Corollaries (the pincer absorbs the previous floor results)
1. **The Swap Theorem** and **the Depth-Two Census** become corollaries (coefficient extractions of the generating function).
2. **The trinomial identity for the floor, proven ∀k:** at q = 3 (m = 1), the balanced count is Σ_c (2k+2)!/(c!·c!·(2k+2−2c)!) = **[x^{2k+2}](1+x+x²)^{2k+2} = T(2k+2)** — one line. (The anchor identity A_k(3) = T(2k+2) is now equivalent to A_k(3) = P_k(3), the v=1 case of the conjecture.)
3. **P₅(q) — virgin dimension 10, complete:** 10395q⁶ − 155925q⁵ + 1074150q⁴ − 4178790q³ + 9317946q² − 10793475q + 4725700. Internal gates ALL passed: leading 11!! ✓ · Swap −155925 ✓ · **Depth-2's falsifiable prediction 1,074,150 CONFIRMED by an independent route ✓✓** · P₅(1)=1 ✓ · P₅(3) = 73789 = T(12) ✓ (fourth dimension of the trinomial identity).
4. The formula holds for EVERY odd q, not only 3^v — the floor is characteristic-free combinatorics.

## Honest scope (Ley 42/45/48)
This closes the **P side** (Asalto III) ∀k ∀q. The conjecture A_k(q) = P_k(q) remains the campaign (the A side: quotient dimensions). The cascade/template work targets A. Orphan datum from the sonar calibration, recorded: the line-interval Möbius numbers μ_b = +1, −4, +33 (b = 2,3,4) — no longer needed for P, possibly useful for the A-side lattice arguments.

## GORDÓMETRO
**Campaña: MUY GORDO (9.5/10)** — un asalto entero cerrado con fórmula cerrada, prueba de 5 líneas, 19 ecos, una dimensión virgen predicha completa con 5 gates internos, y dos teoremas previos absorbidos como corolarios. **Mundo: medio (5/10)** — una identidad combinatoria limpia y citable sobre arreglos de matchings; la prueba es elemental una vez vista (lo cual es su virtud).

**MARCADOR: [FLOOR THEOREM: P_k(q) = conteo balanceado = (2k+2)![x^{2k+2}]cosh(x)B(x)^{(q−1)/2} · 19/19 ecos incl. A(9) sellado y q=81 · P₅ completo con 5 gates (Depth-2 confirmado independiente) · trinomial-P probada ∀k (corolario 1 línea) · ASALTO III CERRADO · Swap+Depth2 absorbidos · μ_b = 1,−4,33 huérfanos registrados]. — Bisel**
