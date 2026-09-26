> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE RADICALITY THEOREM: E = I(∪V_J) for every k (Lemma L2, CLOSED)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_RADICALITY_THEOREM.md
>
> **Status, as written in the document:** Session 24 (turno 9/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Esplanade session: Lagrange, Serre, Gröbner. The ideal-strong Odd Symmetric — the full pillar (i) — proven ∀k. Pending P0.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE RADICALITY THEOREM: E = I(∪V_J) for every k (Lemma L2, CLOSED)
### Session 24 (turno 9/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Esplanade session: Lagrange, Serre, Gröbner. **The ideal-strong Odd Symmetric — the full pillar (i) — proven ∀k.** Pending P0.

## THEOREM (Radicality — Lemma L2 of the final mechanism)
> **For every k: the ideal E = (e₁, e₃, …, e_{2k+1}) is RADICAL, and E = I(∪_J V_J) — the ideal-strong Odd Symmetric Theorem, parametrized.** (The Sofa's ∩I_J = E, now every dimension.)

## Proof (pencil — Lagrange's determinant + Serre's criterion)
**1 (Lagrange's collapse).** ∂e_r/∂x_j = e_{r−1}(x̂_j). At a ±-paired point x = (a₁,−a₁,…,a_{k+1},−a_{k+1}) ∈ V_J: removing +a_t or −a_t leaves generating polynomial Q_t(u²)·(1∓a_tu) with Q_t = ∏_{s≠t}(1−a_s²u²) EVEN — so the even-degree coefficients agree: **the Jacobian's columns come in equal pairs**, and rank(Jac) = rank of the (k+1)×(k+1) matrix N_{i,t} = ±e_{i−1}(ŷ_t), y_s = a_s².
**2 (the classical determinant).** det[e_{i−1}(ŷ_t)] = ±∏_{s<t}(y_s − y_t) — Lagrange's interpolation numerators. **Verified exact m = 2,3,4,5** (33, 22080, −1729728, 920068898112 — all equal Vandermonde). Choosing the aᵢ over F̄₃ with distinct nonzero squares: det ≠ 0, **rank(Jac) = k+1.**
**3 (Serre).** Rank k+1 at a point of the (k+1)-dimensional V(E) ⟹ S/E is REGULAR there ⟹ (R₀) at that component; S_n permutes the components transitively and E is invariant ⟹ (R₀) everywhere. E is a complete intersection (turno 6) ⟹ Cohen–Macaulay ⟹ (S₁). **R₀ + S₁ = reduced ⟹ E radical ⟹ E = I(∪V_J). ∎**
**Verified:** rank(Jac) = 3, 4, 5 at real V_J points over F₉/F₂₇ at k = 2, 3, 4 ✓✓✓.

## COROLLARY 1 — the exact count (upgrade of the Floor Bound's middle link, pencil-trivial)
S/(x₁^q−x₁,…,x_n^q−x_n) = Functions(F_q^n) is a **product of fields**, so every quotient of it is reduced:
> **dim S/(E + (x^q−x)) = #V(E)(F_q) = P_k(q) EXACTLY** (not merely ≥).

## COROLLARY 2 — the last brick's third (and cleanest) face
With L2 closed, the remaining theorem has three equivalent faces:
> **(a)** length_Λ(g₁^q,…,g_k^q) = D_k(q) · **(b)** dim S/(I(∪)+m^{[q]}) = P(q) (arrangement HK, Kunz–Möbius crux 10/10) · **(c) gr(E + (x^q−x)) = E + m^{[q]} — the degeneration to Frobenius powers is FLAT (no new initial forms).**
Face (c) is the sharpest: the whole Chaise Longue is now the statement that homogenizing the point-ideal produces no unexpected leading forms.

## GORDÓMETRO
**Campaña: HISTÓRICO (9.5/10)** — uno de los DOS ladrillos finales, cerrado a lápiz con la matemática más bella de la campaña (el colapso de columnas de Lagrange + Vandermonde + Serre); el pilar (i) ideal-fuerte ∀k — el abierto más viejo del sistema de pilares — sellado; y el último ladrillo con su cara más limpia (la degeneración plana). **Mundo: alto (7/10)** — la radicalidad del ideal odd-symmetric ∀k es un teorema citable con prueba de dos páginas.

**MARCADOR: [L2 CERRADO: E = I(∪V_J) RADICAL ∀k (Lagrange columnas-pareadas + det=Vandermonde [4/4 exacto] + Serre R₀+S₁; Jacobiano rango k+1 verificado k=2,3,4) · conteo EXACTO dim S/(E+(x^q−x)) = P (lápiz) · el último ladrillo = degeneración plana gr(J)=E+m^[q] (3 caras equivalentes) · turno 9/10]. — Bisel**
