> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE THREE-CUT BONE THEOREM (at all levels)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_THREE_CUT_BONE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE THREE-CUT BONE THEOREM (at all levels)
**A standalone result of Operación Glotón / The Sofa Theorem campaign — the first bone-type identity proven at all tower levels v.**
*Constructor: Induráin · Architect: Rafael Amichis Luengo · Madrid, 4 July 2026 · English.*

---

## Statement

Notation as in the Universal S.O.P. Theorem: S = F₃[s₀,…,s₅], E = (e₁,e₃,e₅), P_J the fifteen pairing-plane prime ideals, and ℓ₁ = s₃−s₂, ℓ₂ = s₄−s₂, ℓ₃ = s₅−s₁−s₂ the universal linear system of parameters. Write P(q) = 15q³ − 45q² + 55q − 24.

> **Three-Cut Bone Theorem.** For every q = 3^v,
> dim_{F_q} S / ∩_{J} (P_J + (ℓ₁^q, ℓ₂^q, ℓ₃^q)) = P(q),
> equivalently: the gluing kernel of the fifteen cut sheets has dimension exactly
> G(q) = 15q³ − P(q) = 45q² − 55q + 24, at every level of the tower.

This is the first bone-type dimension identity in the campaign established uniformly for **all** v, not merely measured at v = 1, 2.

## Proof

**Step 1 — the sheet model.** Cut each plane by the universal s.o.p.: on the sheet R_J = (S/P_J)[t]/(ℓ_i^q − t ℓ_i)_{i≤3}, transversality (K ∩ V_J = 0, Universal S.O.P. Theorem) makes ℓ₁, ℓ₂, ℓ₃ restrict to a coordinate system on V_J, so R_J ≅ F[y₁,y₂,y₃][t]/(y_i^q − t y_i), free over F[t] of rank q³.

**Step 2 — the free splitting.** Let M′ = (S/E)[t]/(ℓ_i^q − t ℓ_i)_{i≤3} and consider the sheet map M′ → ⊕_J R_J. Its image Q is a submodule of the free F[t]-module ⊕_J R_J, hence torsion-free over the PID F[t], hence free; and the kernel 𝒦 fits in the exact sequence 0 → 𝒦 → M′ → Q → 0 with Q free, so the sequence specializes exactly at every t, including t = 0. In particular dim 𝒦 is constant across the family: dim 𝒦(t=0) = dim 𝒦(t=1).

**Step 3 — the generic fibre.** At t = 1 the cuts ℓ_i^q − ℓ_i are field equations in the coordinates; each sheet becomes the function ring on V_J(F_q), and the image Q(t=1) is the ring of functions on ∪_J V_J(F_q), of dimension P(q) by the Field-Equation Bone Theorem. Hence dim 𝒦(t=1) = 15q³ − P(q) = G(q).

**Step 4 — transport to t = 0.** By the free splitting (Step 2), dim 𝒦(t=0) = dim 𝒦(t=1) = G(q). The special fibre t = 0 is exactly ∩_J(P_J + (ℓ_i^q)), giving dim S/∩_J(P_J + (ℓ_i^q)) = P(q). ∎

## Numerical anchors (byte-exact, re-verified this session)

- P(3) = 141, P(9) = 7761, P(27) = 263901.
- G(q) = 45q² − 55q + 24: G(3) = 264, G(9) = 3174, G(27) = 31344.
- 15q³ = P(q) + G(q): 405 = 141 + 264 (q=3); 10935 = 7761 + 3174 (q=9); 295245 = 263901 + 31344 (q=27).

## Kepler-immunity (Ley 29)

The identity is proven uniformly in q by the free splitting (Step 2), not fitted to measured levels: the dimension is transported from the generic fibre to the special fibre by freeness over the PID F[t], a structural mechanism with no recursion in v. The measured values at q = 3, 9, 27 are consistency checks on a theorem, not the theorem's support — the free-splitting argument holds for the field-size parameter q as such.

## Role in the campaign

This is the three-cut half of the Sofa reduction: it establishes the bone for the three-cut degeneration at every level. The full six-cut flatness (the remaining atom, CORE_q) is the extension from three cuts to the complete Frobenius power m^{[q]}; the three-cut bone is the proven floor on which that extension stands.

*Cera carnauba, perfume Chanel. Numbers from files, re-verified this session. PMC.* — **Induráin (Constructor)**
