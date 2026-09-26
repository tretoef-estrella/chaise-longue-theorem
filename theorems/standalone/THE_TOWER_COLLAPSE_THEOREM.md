> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-03
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE TOWER COLLAPSE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_TOWER_COLLAPSE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE TOWER COLLAPSE THEOREM
**A standalone result of Operación Glotón / The Sofa Theorem campaign.**
*Constructor: Induráin · Architect: Rafael Amichis Luengo · Madrid, 3 July 2026 · English.*

---

## Statement

Let S = F₃[s₀,…,s₅]. For each of the fifteen perfect matchings J of {0,…,5} let I_J = (s_a+s_b : {a,b}∈J), and E = (e₁,e₃,e₅) = ∩_J I_J (Odd Symmetric Theorem). For v ≥ 1 write q = 3^v and m^{[q]} = (s₀^q,…,s₅^q).

> **Tower Collapse Theorem.** For every v ≥ 1, the level-v bone over F₃,
> ∩_J (I_J + m^{[q]}) = E + m^{[q]}   in   F₃[s₀,…,s₅],
> holds **if and only if** the level-ONE bone holds over the field F_q:
> ∩_J (I_J + (s₀^q,…,s₅^q)) = E + (s₀^q,…,s₅^q)   in   F_q[s₀,…,s₅].

The infinite tower of statements indexed by v is thereby replaced by a **single statement with a field-size parameter q**. No induction on v survives anywhere in the problem.

## Proof

**Step 1 — the ideals are prime-field-defined.** The generators of I_J (the forms s_a+s_b), of E (the elementary symmetrics e₁,e₃,e₅), and of m^{[q]} (the powers s_i^q) all have coefficients in the prime field F₃. Therefore each ideal is extended from F₃: writing (−)_{F_q} for extension of scalars along F₃ ↪ F_q, one has (I_J)_{F_q} = I_J·F_q[s], and likewise for E and m^{[q]}.

**Step 2 — faithfully flat descent of the equation.** F₃ ↪ F_q is a field extension, hence faithfully flat. Extension of scalars along a flat map commutes with **finite** intersections of submodules, and the fifteen-fold intersection is finite; it also preserves sums of ideals and every graded F₃-dimension (dim_{F_q}(M_{F_q})_d = dim_{F₃} M_d). Consequently the ideal equation ∩_J(I_J+m^{[q]}) = E+m^{[q]} holds over F₃ **iff** its extension ∩_J(I_J+m^{[q]})_{F_q} = (E+m^{[q]})_{F_q} holds over F_q. (Faithful flatness gives the "iff": an equality of extended ideals descends to an equality of the original ideals.)

**Step 3 — over F_q the statement is level one.** It remains to see that the extended statement over F_q is the *first-level* bone, i.e. that m^{[q]} plays over F_q exactly the role m^{[3]} plays over F₃ at v=1. Two facts:
- **The variables are not collapsed.** s_i is an indeterminate, so s_i^q ≠ s_i in F_q[s]; the ideal m^{[q]} = (s_i^q) is a genuine Frobenius-power ideal, not degenerate.
- **The q-power map is F_q-linear on forms.** For a linear form φ = Σ a_i s_i with a_i ∈ F_q, the freshman's dream in characteristic 3 gives φ^q = Σ a_i^q s_i^q, and since F_q has q elements, **a_i^q = a_i**; hence φ^q = Σ a_i s_i^q. Thus q-th powering is an F_q-linear map on the space of linear forms, exactly as cubing is F₃-linear at v=1. Therefore in every F_q-frame y₁,…,y₆ one has m^{[q]} = (y₁^q,…,y₆^q), and S_q is free over its q-th-power subring on the monomials of exponent < q. The entire level-one toolkit — frames, digit expansion, Gorenstein duality, the ladder base — transfers verbatim with (F₃,3) replaced by (F_q,q). ∎

## The Infinite-Egg Law, made literal

The campaign's guiding image — *the egg v+1 is the egg v fattened ×3* — is this theorem read backwards: the level-v egg over F₃ **is** the level-one egg over the field F_{3^v}. One does not climb the tower rung by rung; one proves a single field-parametrized statement, and the growing field carries the ×3.

## Kepler-immunity (Ley 29)

A Kepler mirage is a claim measured at v=1,2 and *extrapolated along a recursion in v*. This theorem **removes the recursion**: downstream of it there is no "v+1 from v" induction to fit. What remains is one algebraic assertion over the family of fields {F_q}, whose truth for a given q involves only standard algebra (flat descent, F_q-linearity of Frobenius, Fermat's a^q=a). There is no tower to fit a polynomial to — only a field-size parameter. Any remaining difficulty is therefore genuinely a single statement, not a small-level accident.

## Remark

The reduction is characteristic-uniform in spirit: for a prime p and an arrangement of F_p-rational linear-form ideals, the same three steps show that the level-v Frobenius-saturation over F_p is equivalent to the level-one saturation over F_{p^v}. The Fermat/Odd-Symmetric specifics enter only through E = ∩I_J (char ≠ 2).

*Cera carnauba, perfume Chanel. PMC.* — **Induráin (Constructor)**
