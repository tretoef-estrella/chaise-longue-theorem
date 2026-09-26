> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE UNIVERSAL SYSTEM-OF-PARAMETERS THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_UNIVERSAL_SOP_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE UNIVERSAL SYSTEM-OF-PARAMETERS THEOREM
**A standalone result of Operación Glotón / The Sofa Theorem campaign.**
*Constructor: Induráin · Architect: Rafael Amichis Luengo · Madrid, 4 July 2026 · English.*

---

## Statement

Let S = F₃[s₀,…,s₅], E = (e₁, e₃, e₅), and S/E the odd-symmetric quotient — a reduced Cohen–Macaulay graded ring of Krull dimension 3 and degree 15, whose vanishing locus is the union of the fifteen pairing planes V_J (Odd Symmetric Theorem). Let

ℓ₁ = s₃ − s₂,  ℓ₂ = s₄ − s₂,  ℓ₃ = s₅ − s₁ − s₂    (F₃-linear forms).

> **Universal S.O.P. Theorem.** The forms ℓ₁, ℓ₂, ℓ₃ are transverse to every one of the fifteen pairing planes: their common zero 3-plane K = V(ℓ₁, ℓ₂, ℓ₃) meets each V_J only at the origin. Consequently (ℓ₁, ℓ₂, ℓ₃) is a **linear system of parameters on the Cohen–Macaulay ring S/E over every field F_{3^v} simultaneously**, and for every q = 3^v,
> dim_{F_q} (S/E)/(ℓ₁^q, ℓ₂^q, ℓ₃^q) = 15 q³   (exact).

## Proof

**Step 1 — the parametrised 3-plane.** Solving ℓ₁ = ℓ₂ = ℓ₃ = 0 gives s₃ = s₂, s₄ = s₂, s₅ = s₁ + s₂, so K = {(a, b, c, c, c, b+c) : a,b,c ∈ F₃-span}, a 3-dimensional linear subspace defined over F₃.

**Step 2 — transversality to all fifteen planes (exhaustive).** For each matching J, restrict the three leg forms {s_a + s_b : {a,b} ∈ J} to K and check the 3×3 coefficient matrix has rank 3 over F₃. All fifteen matchings pass (exhaustive check, machine-verified this session). Hence K ∩ V_J = {0} for every J, so K meets the union ∪_J V_J only at the origin.

**Step 3 — field-stability.** The rank-3 condition is a non-vanishing of a 3×3 determinant over F₃; a nonzero element of F₃ stays nonzero under any field extension F₃ ↪ F_q. Therefore transversality holds over every F_q, and (ℓ₁, ℓ₂, ℓ₃) is a linear system of parameters on (S/E) ⊗ F_q for all v at once — one set of F₃-forms, every level.

**Step 4 — the exact length.** On the Cohen–Macaulay ring S/E of dimension 3 and degree 15, a linear system of parameters ℓ₁, ℓ₂, ℓ₃ is a regular sequence; raising to the q-th power, (ℓ₁^q, ℓ₂^q, ℓ₃^q) is again a regular sequence, and
dim (S/E)/(ℓ₁^q, ℓ₂^q, ℓ₃^q) = q³ · e(ℓ; S/E) = q³ · deg(S/E) = 15 q³,
exactly, for every q = 3^v. ∎

## Numerical anchors (byte-exact, re-verified this session)

- Transversality: all fifteen restricted 3×3 matrices have rank 3 over F₃ (exhaustive, verified).
- deg(S/E) = 15 (the fifteen pairing 3-planes).
- dim (S/E)/(ℓ₁^q, ℓ₂^q, ℓ₃^q) = 15q³: 405 at q=3, 10935 at q=9, 295245 at q=27.
- Complementary count G(q) = 15q³ − P(q) = 45q² − 55q + 24: G(3)=264, G(9)=3174, G(27)=31344.

## Role in the campaign

This theorem supplies the *cutting frame* that turns the tower problem into one flat family: the three F₃-forms are transverse at every level at once, so the degeneration (S/E)[t]/(ℓ_i^q − t ℓ_i) is a flat Cohen–Macaulay family with all fibres of length 15q³. It is the scaffold on which the three-cut bone and the Nakayama reduction stand, and it is characteristic-uniform: one explicit s.o.p., valid for the whole tower, no induction on v.

*Cera carnauba, perfume Chanel. Numbers from files, re-verified this session (PROBE_UNIVERSAL_SOP_v1). PMC.* — **Induráin (Constructor)**
