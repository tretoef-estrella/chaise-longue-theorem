> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SANDWICH TRIPLE: Converse Vanishing · Regular Sequence ∀k · The Ceiling ∀k∀q* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SANDWICH_THEOREMS.md
>
> **Status, as written in the document:** Session 21 (turno 6/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Waterfall session: Bézout, Macaulay, Noether. THREE pencil theorems in one turn — the sandwich architecture of the conjecture, complete. Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SANDWICH TRIPLE: Converse Vanishing · Regular Sequence ∀k · The Ceiling ∀k∀q
### Session 21 (turno 6/10) · 12 Jul 2026 · Constructor: Bisel (Fable) · Waterfall session: Bézout, Macaulay, Noether. THREE pencil theorems in one turn — the sandwich architecture of the conjecture, complete. Pending P0.

## THEOREM 1 — CONVERSE VANISHING (the k-uniform Odd Symmetric, set-theoretic — one paragraph)
> **Over any field of characteristic ≠ 2: V(e₁, e₃, …, e_{2k+1}) = ∪_J V_J set-theoretically, for every k.**
**Proof.** (⊇ is the Vanishing Lemma, s19.) (⊆): if every odd e vanishes at x, the generating polynomial p(t) = ∏(1+xᵢt) is EVEN, so p(t) = p(−t) and its root multiset is symmetric under negation: the nonzero coordinates pair up as {a, −a}, and (n even) the zero coordinates are even in number. Pairing the ±-partners and the zeros arbitrarily gives a perfect matching J with x ∈ V_J. ∎
Rational-point confirmation (s20): 141/1107/8953/7761 — exact, 4/4, including the tower.

## THEOREM 2 — THE ODD e's ARE A REGULAR SEQUENCE, ∀k (pencil)
By Theorem 1, dim V(E) = dim ∪V_J = k+1: the k+1 forms e₁, e₃, …, e_{2k+1} cut the 2k+2-dimensional space down by exactly k+1 = their number; since S is Cohen–Macaulay, **codim = count ⟹ (e₁, e₃, …, e_{2k+1}) is a regular sequence for every k.** The Sofa's pillar (i), parametrized. **Verified: Hilbert series of S/(E) = ∏(1−x^{2i−1})/(1−x)^n EXACT, 18/18 degrees (n=6: d≤8; n=8: d≤7).**

## THEOREM 3 — THE CEILING, ∀k ∀q (pencil)
Over F̄₃ choose k+1 generic linear forms ℓᵢ (transverse to the finitely many k+1-planes V_J — generic works over an infinite field; dim_F₃ is preserved by base change). Then ℓᵢ^q = Σaᵢⱼ^q xⱼ^q ∈ m^{[q]}, so (E, ℓ₁^q, …, ℓ_{k+1}^q) ⊆ E + m^{[q]}, and by Theorems 1-2 the 2k+2 forms are a full regular sequence of degrees 1,3,…,2k+1, q,…,q:
> **A_k(q) ≤ (2k+1)!! · q^{k+1} — the ceiling, every k, every q.** (Anchored at the Sofa's sealed Λ = 405 at k=2, q=3.)

## THE SANDWICH — the conjecture's architecture, now complete and pencil on both legs
> **P_k(q) ≤ A_k(q) ≤ (2k+1)!!·q^{k+1}** — floor (s20) and ceiling (today) proven ∀k∀q, sharing the leading term (2k+1)!!q^{k+1} (the Floor Theorem's leading coefficient).
The remaining campaign, exactly: close the gap ceiling→A→floor — the BRIDGE (the Sofa's presentation: A = ceiling − length of a k-generator ideal) and the lower-order terms. Every remaining route (5, 6, 7, 8 rest, 9 rest) is now a statement about the gap of a sandwich whose two slices are theorems.

## Honest scope (Ley 42)
Set-theoretic Odd Symmetric closed; the IDEAL-theoretic strong form (∩I_J = E as ideals, the Sofa's full pillar) is NOT claimed — it needs the scheme structure (radical/CM saturation) and remains open ∀k (true for k=2 by the Sofa). The ceiling's frame is generic over F̄₃ (existence, not explicit); explicit F₃-frames per k remain the certificate route if ever needed.

## GORDÓMETRO
**Campaña: HISTÓRICO (9.5/10)** — tres teoremas de lápiz en un turno; el pilar (i) set-teórico ∀k (un pendiente de campaña entero); la sucesión regular ∀k; el techo ∀k∀q; y la arquitectura sandwich completa con las dos rebanadas probadas. **Mundo: medio-alto (6/10)** — la descripción set-teórica de la variedad odd-symmetric + el sandwich HK es material de paper por sí solo.

**MARCADOR: [TRIPLE: Converse Vanishing (V(E)=∪V_J set, ∀k, char≠2, 1 párrafo) · sucesión regular ∀k (18/18 Hilbert=CI) · TECHO A_k(q) ≤ (2k+1)!!q^{k+1} ∀k∀q · SANDWICH completo P ≤ A ≤ techo (dos rebanadas lápiz) · pilar (i) ideal-fuerte: abierto honesto · RUTA 9 (objetivo Λ): CERRADA · turno 6/10]. — Bisel**
