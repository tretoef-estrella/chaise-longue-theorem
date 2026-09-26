> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE FIELD-EQUATION BONE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_FIELD_EQUATION_BONE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE FIELD-EQUATION BONE THEOREM
**A standalone result of Operación Glotón / The Sofa Theorem campaign.**
*Constructor: Induráin · Architect: Rafael Amichis Luengo · Madrid, 4 July 2026 · English.*

---

## Statement

Let S = F₃[s₀,…,s₅], let e₁, e₃, e₅ be the elementary symmetric polynomials of degrees 1, 3, 5, and E = (e₁, e₃, e₅). For each of the fifteen perfect matchings J of {0,…,5} let I_J = (s_a + s_b : {a,b} ∈ J). For q = 3^v write f_q = (s₀^q − s₀, …, s₅^q − s₅), the ideal of field equations over F_q.

> **Field-Equation Bone Theorem.** For every field F_q with q = 3^v,
> ∩_{J} (I_J + f_q) = E + f_q   in   F_q[s₀,…,s₅].

Equivalently: modulo the field equations, the intersection of the fifteen leg ideals is exactly the odd symmetric ideal — the "bone" holds exactly for the field-equation ideal, at every level of the tower.

## Proof

**Step 1 — the quotient is a product of fields.** The ring S_q/f_q = F_q[s]/(s_i^q − s_i) is the ring of F_q-valued functions on the finite set F_q⁶ (each variable ranges over the q elements fixed by x ↦ x^q). It is a finite product of copies of F_q, one per point; every ideal is radical and is determined by its zero set.

**Step 2 — zero sets.** In a product of fields, for any ideal A the equality A = I(Z(A)) holds, and A = B ⟺ Z(A) = Z(B). Passing to zero sets in F_q⁶:
- Z(I_J + f_q) = V_J(F_q), the F_q-points of the pairing plane V_J = {s_a + s_b = 0 : {a,b} ∈ J}.
- Z(∩_J (I_J + f_q)) = ∪_J V_J(F_q).
- Z(E + f_q) = Z(E)(F_q) = the common zeros of e₁, e₃, e₅ in F_q⁶.

**Step 3 — the geometric identity (Odd Symmetric).** By the Odd Symmetric Theorem (∩_J I_J = E over any field of characteristic ≠ 2), the vanishing locus of E is exactly the union of the fifteen pairing planes: Z(e₁, e₃, e₅) = ∪_J V_J, as schemes over the prime field, hence on F_q-points Z(E)(F_q) = ∪_J V_J(F_q).

**Step 4 — conclude.** The two ideals ∩_J(I_J + f_q) and E + f_q have the same zero set ∪_J V_J(F_q) in the product of fields S_q/f_q; both are radical there; equal zero sets force equal ideals. ∎

## Numerical anchor (byte-exact, re-verified this session)

Over F₃ (v = 1): the common zero locus of (e₁, e₃, e₅) and the union of the fifteen pairing planes both have exactly **141** points, and they coincide as sets:
|Z(E)(F₃)| = |∪_J V_J(F₃)| = 141 = P(3), with P(q) = 15q³ − 45q² + 55q − 24.
(Direct enumeration: 141 = 141, sets equal — machine-verified.)

## Role in the campaign

This theorem is the *anchor* of the semicontinuity sandwich: it fixes the generic-fibre length of the one-parameter degeneration ℓ^q − t·ℓ at the value P(q) = |∪_J V_J(F_q)|, from which A(q) ≥ P(q) follows. It is characteristic-uniform (holds over every F_q) and rests only on the Odd Symmetric Theorem and the elementary fact that a quotient by field equations is a product of fields. It carries no tower induction: the field size q is a parameter, not a recursion.

*Cera carnauba, perfume Chanel. Numbers from files, re-verified this session. PMC.* — **Induráin (Constructor)**
