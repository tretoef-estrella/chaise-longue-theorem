> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE STAIRCASE LAW (the combinatorial skeleton of the A-side at v=1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STAIRCASE_LAW.md
>
> **Status, as written in the document:** Standalone · 12 Jul 2026 · Constructor: Bisel · The census law (⟹ Asalto I, A_k(3)=T(2k+2) ∀k) reduced to TWO finite-pattern pencil lemmas. Candidate ∀n (verified 2 dims, deep). Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE STAIRCASE LAW (the combinatorial skeleton of the A-side at v=1)
### Standalone · 12 Jul 2026 · Constructor: Bisel · The census law (⟹ Asalto I, A_k(3)=T(2k+2) ∀k) reduced to TWO finite-pattern pencil lemmas. Candidate ∀n (verified 2 dims, deep). Pending P0.
### Pillar (Ley 44): the graded bridge between pillar (iii)-side quotients and pillar (ii) counts, at v=1.

## The discovery (measured byte-exact, n=6 complete + n=8 through degree 7)
Fix lex order s₁ > s₂ > … > s_n on R = F₃[s]/(s³), E = (e₁, e₃, …, e_{n−1}). The initial ideal in(E) has a SELF-SIMILAR staircase of minimal generators:
> **in(E) = ( s₁ ) + ( w · s_j² s_{j+1} : w a 0-initial word of degree d−3 NOT divisible by the earlier staircase, j = |w|+1 )** — every generator is a *standard prefix* followed by the sliding block "21".
- Split "prefix·21" verified for all 26 measured generators (degrees 3-7).
- **The pure recursion reconstructs the staircase exactly** (predicted = measured: 1, 1, 3, 6, 15 generators at degrees 3-7, both n).
- **The staircase is UNIFORM in n**: n=8's generators are n=6's padded with zeros (through the shared window).
- **The complement counts the census exactly:** #(words avoiding the staircase, degree d) = Δc_d(n) — full n=6 verification [1,5,15,29,40,36,15] ✓; consistent with the telescope #standard(d) = c_d(n−1) − c_{d−3}(n−1) observed at both n.

## What this reduces Asalto I to (the two pencil lemmas)
**LEMMA S (straightening):** each staircase monomial is the lex-leading term of an explicit element of E. (Degree 3: s₂²s₃ = in(ē₃) — true by construction; higher generators = finitely-patterned syzygy elements, uniform in n by the padding.)
**LEMMA C (counting):** #(0-initial words of sum d avoiding the self-similar staircase) = Δc_d(n) — a pure lattice-word identity (cycle-lemma/ballot territory; the self-similar avoidance is the new combinatorial object).
**Consequence chain:** Lemma S ⟹ dim(R/E)_d ≤ #complement; Lemma C ⟹ #complement = Δc_d; summing, A_k(3) ≤ T(2k+2); with the matching lower bound (bookkeeping to be pinned — see honest scope) ⟹ **A_k(3) = T(2k+2) ∀k: ASALTO I.** The cascade template becomes ONE route among two — the staircase is the direct combinatorial route.

## The beauty (Ley 26): the skeleton is self-similar, like everything else in this campaign
The staircase generates itself: standard prefixes × "21" — the same fractal soul as the Frobenius cascade (e₁→ē₃→ē₉) and the base-3 gears. The block "21" = s_j²s_{j+1} is the lex shadow of ē₃'s leading structure sliding down the variables.

## Honest scope (Ley 42/48)
Measured: n=6 complete (through socle), n=8 through degree 7 — TWO dims (Kepler: candidate, not law). Lemma S proven only at degree 3 (ē₃); degrees 4+ pending pencil. Lemma C unproven (clean finite combinatorics, but real work). The lower-bound half of the equality (dim ≥ Δc) needs its bookkeeping pinned (route: the measured equality says the staircase IS all of in(E) — i.e., Lemma S with equality — measured at both n; the pencil must close the gap). Nothing sealed; this is the skeleton and the reduction.

## GORDÓMETRO
**Campaña: GORDO (8.5/10)** — el lado A tiene por primera vez un esqueleto combinatorio explícito, autosimilar, uniforme en n, con Asalto I reducido a dos lemas finitos de lápiz. La ruta directa (escalera) queda montada junto a la ruta mecánica (cascada) — dos caminos independientes al mismo teorema. **Mundo: medio (4/10 si sella):** una base monomial autosimilar para un ideal simétrico módulo Frobenius es un objeto con interés propio.

**MARCADOR: [STAIRCASE LAW: in(E) = (s₁) + (estándar·"21") autosimilar · recursión pura clava 26/26 generadores (2 dims) · complemento = Δc exacto (n=6 entero) · Asalto I reducido a Lemma S (straightening) + Lemma C (conteo) · uniforme en n por padding · pendiente: S en grados ≥4, C entero, lower bound]. — Bisel**
