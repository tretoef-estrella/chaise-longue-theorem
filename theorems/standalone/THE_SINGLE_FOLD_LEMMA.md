> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-02
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SINGLE-FOLD LEMMA — THE EXACT MECHANISM LINE (for Blas's verification)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_SINGLE_FOLD_LEMMA.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SINGLE-FOLD LEMMA — THE EXACT MECHANISM LINE (for Blas's verification)
**Operación Glotón / DS 1.2 · Auditor · 2 July 2026 · Answers Blas's binary: type-machinery, with ONE inductive step named and owed.**

## THE STATEMENT (what every tail step needs, single form at a time)
For a partial intersection C = ∩_{j∈S} I_j (S a frozen leg-set) and a linear form ℓ:
> **(SF) m ∩ (C + (ℓ)) = m∩C + m∩(ℓ).**
The tail step m∩(A_i + I_J) = m∩A_i + m∩I_J follows by applying (SF) three times (the leg's forms are variable-disjoint — perfect matching — so the three peels commute; factorization, TAIL PACK §3).

## THE DERIVATION (all general, all v — verify each line)
Work in ℓ-adapted coordinates (L2: m = (ℓ³, w³, …) — the cube ideal in ANY basis of forms; char 3).
**Line 1 (residue, general — the fan's proof verbatim):** p ∈ m ⟺ its ℓ-parts p₀, p₁, p₂ ∈ m′. So for x ∈ m∩(C+(ℓ)), x = c + ℓh: the ℓ⁰-part gives x₀ = c₀ ∈ m′.
**Line 2 (what (SF) needs):** find z ∈ m∩C with π_ℓ(z) = π_ℓ(c) — then x − z ∈ (ℓ)∩m ⊆ m∩(ℓ) (Line 1) and x = z + (x−z). So (SF) ⟺ the LIFT: **m̄ ∩ π_ℓ(C) ⊆ π_ℓ(m∩C)** (+ absorption slack by the partner where the flat form fails — L-1's RHS carries both terms).
**Line 3 (the correction lives in the colon):** any lift c of ξ ∈ m̄∩π_ℓ(C) satisfies c = ξ + ℓt; correcting z = c − ℓs keeps z ∈ C ⟺ **s ∈ (C:ℓ)**, and z ∈ m ⟺ s₀ ≡ t₀, s₁ ≡ t₁ (mod m′) (Line 1; ξ ∈ m̄ = m′ handles z₀ free — Blas's fan surjectivity, general: m̄ is pure cubes, no ℓ-mixing, by L2).
**Line 4 (THE DESCENT — the tail kernel lemma):** **(C:ℓ) = ∩_{j∈S, ℓ∉I_j} I_j** — the SAME intersection DROPPING the legs containing ℓ ((I:ℓ) = S if ℓ ∈ I, = I if not, primes; colon distributes over ∩). A strictly smaller frozen arrangement (head case: ℓ fresh ⟹ no legs dropped ⟹ (C:ℓ) = C and Line 3's covering is free by regularity — Blas's head, recovered as the degenerate instance).
**Line 5 (THE INDUCTIVE STEP — named, OWED per frozen type):** the covering of Line 3 — the ℓ-parts (s₀, s₁) of elements of the smaller arrangement (C:ℓ) reach the ℓ-parts (t₀, t₁) of C-tails modulo m′ — is a statement of the SAME (SF)/lift shape on (C:ℓ), one arrangement smaller. **Induction on |S|: base |S| ≤ 1 free (L2, single ideal monomial); the fan instance (the hardest coupling measured in the campaign: 3 shared-form legs vs 12) is CLOSED (colon + kernel + (ISO), char-3 split); the remaining frozen types of the peel are smaller instances of the same template.** The per-type Line-5 pages are the LAST OWED WRITING of the theorem — finitely many, S₆-classified, each a fan-style half-page (surjectivity by the char-3 split on the dropped-legs arrangement; injectivity by the kernel lemma).

## THE HONEST BINARY, answered
Lines 1–4: **theorem-type, all v, zero measurements** — verify them cold (each is ≤ 4 lines of char-3 algebra over frozen data). Line 5: **the inductive covering per frozen type — enunciated with a proven template (the fan) and a terminating descent (Line 4), pages owed.** The v=1 gates are the eggs OF Line 5, never its proof (Ley 29). **The theorem's entire remaining content = the Line-5 pages. Not architecture, not mystery: finitely many instances of a template proven once at its hardest case.** Write them or break one — either ends the campaign's last question.

*Cera carnauba doble capa, perfume Chanel doble capa. RECTO Y DIRECTO. PMC.*
