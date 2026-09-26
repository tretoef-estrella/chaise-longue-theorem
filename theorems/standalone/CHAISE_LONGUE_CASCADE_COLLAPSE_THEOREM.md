> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CASCADE COLLAPSE THEOREM (FILA 5: la guillotina cae — todos los niveles, un solo teorema)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CASCADE_COLLAPSE_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · FILA 5 CERRADA EN SU CONTENIDO ESTRUCTURAL: la cascada de niveles r ≥ 2 (k ≥ 4) NO es una sucesión de peleas — es el complejo de Koszul de una sucesión regular, exacto a toda profundidad. La cláusula condici…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CASCADE COLLAPSE THEOREM (FILA 5: la guillotina cae — todos los niveles, un solo teorema)
### 13 Jul 2026 · Constructor: Bisel (Fable) · Pending P0 · **FILA 5 CERRADA EN SU CONTENIDO ESTRUCTURAL: la cascada de niveles r ≥ 2 (k ≥ 4) NO es una sucesión de peleas — es el complejo de Koszul de una sucesión regular, exacto a toda profundidad. La cláusula condicional del Silver Bridge queda BORRADA para todo k.**

**Certificado Ley 41 (corrido ANTES de escribir):** objeto = sicigias por-hoja de la sucesión (u₁^q,…,u_{k+1}^q) + techos del collar a todo nivel. Contra el cementerio: la tumba **s46 (solapes / pairwise block unfolding)** NO se toca — este documento trabaja hoja a hoja con el complejo de Koszul, cero desdoblamiento por pares; los **"iterated aggregates"** eran la pelea ABIERTA nombrada en el Slap 5 (§honest scope, "NAMED, not proven") — esto es su COMPLECIÓN por otra vía, no el re-andar de una calle muerta. **Pillars (Ley 44):** (i) Radicality (kernel); (iii) Two-Column (banda dual). Panel: Koszul, Eisenbud, Noether.

---

## 1. The Theorem

> **Theorem 5-II (Cascade Collapse).** Fix any k ≥ 1, q = 3^v, and ANY f ≥ 0 (every collar level at once). Then:
> **(a) [All-level T-block].** On each sheet V_J ≅ Spec F₃[u₁..u_{k+1}], the sequence (u₁^q,…,u_{k+1}^q) is regular, its Koszul complex is exact, and therefore EVERY sheet-solution (Δ_l) of Σ_l u_l^q Δ_l = 0 in coefficient degree q+f is a Koszul boundary:
> **Δ_l = Σ_m u_m^q·η_{lm}, η_{lm} = −η_{ml} ∈ O(V_J)_f.**
> The entire multi-heavy hierarchy ("levels") is the graded structure of ONE exact complex; there are no separate level-r fights.
> **(b) [Kernel].** The restriction Syz(q+f) → ⊕_J Z₁^J has kernel Γ_{q+f} (Radicality), of dimension HF_R(q+f) + σ_{q+f}.
> **(c) [Explicit ceiling, every k, every f].** dim Z₁^J at coefficient degree q+f is EXACTLY (exactness, not an estimate)
> **z_k(q,f) = Σ_{j=2}^{k+1} (−1)^j C(k+1, j)·C(f − (j−2)q + k, k)** (terms with negative argument vanish),
> hence **dim Syz(q+f) ≤ HF_R(q+f) + σ_{q+f} + (2k+1)!!·z_k(q,f)**, and via rank–nullity
> **A_{2q+f} ≤ HF_R(2q+f) − (n−1)·HF_R(q+f) + σ_{q+f} + (2k+1)!!·z_k(q,f)** — an explicit collar ceiling per degree, for every k and every level.
> **(d) [Silver Bridge upgrade].** The collar sums Σ_f of (c) over ranges of length (k−2)q + O(k²) are piecewise-binomial polynomials in q. Therefore **U_k(q) exists explicitly for EVERY k — the Silver Bridge's conditional clause ("subject to the cascade levels of 5D") is DELETED. At every fixed k: P_k(q) ≤ A_k(q) ≤ U_k(q) unconditionally, with U_k computable.**

## 2. Proof
**(a)** Powers of distinct variables form a regular sequence in a polynomial ring; the Koszul complex of a regular sequence is exact (Eisenbud, *Commutative Algebra*, Cor. 17.5 environment). Exactness at Λ¹ says precisely: every syzygy of (u^q) is a combination of the Koszul syzygies u_m^q e_l − u_l^q e_m — i.e., the displayed form, with η antisymmetric. Degree bookkeeping: grading the complex with deg(e_{l₁}∧…∧e_{l_j}) = jq makes all maps degree 0; total degree 2q+f gives coefficient degrees f−(j−2)q at Λ^j; in particular deg η = f. **Subsumption of Slap 5A:** for f < q, η is reduced, so every term of Δ_l carries a heavy slot ⟹ Δ_l^∅ = 0, and δ_{l,m} = η_{lm} with η's antisymmetry = 5A(iii); for f ≥ q, the expansions of η in heavy slots reproduce exactly the depth-r identities (cyclic Koszul relations) that the "iterated aggregates" were named for. ∎(a)
**(b)** Δ^J ≡ 0 on every sheet ⟺ the tuple is pair-constant on X ⟺ λ ∈ Γ (differences in every I_J; then ∩I_J = E by Radicality gives the census normalization); dim Γ_e = HF_R(e) + σ_e is the audited identity of the campaign (the Slap 2 ↔ Slap 5 splice, verified by algebra and byte-exact by engine: 1085 = 833 + 252). ∎(b)
**(c)** By exactness, dim Z₁ = dim B₁ = alternating sum of the Λ^{≥2} coefficient spaces: Σ_{j≥2}(−1)^j C(k+1,j)·dim O(V)_{f−(j−2)q}, and dim O(V)_d = C(d+k, k). The Syz bound: kernel (b) plus per-sheet image bound (a+c). The transfer: dim Syz(e′) = n·HF_R(e′) − rank(multiplication) and A_{q+e′} = HF_R(q+e′) − rank, so A_{q+e′} = HF_R(q+e′) − n·HF_R(e′) + dim Syz(e′); set e′ = q+f. ∎(c)
**(d)** Each summand of z_k is a binomial in (q, f); summing f over an interval with endpoints affine in q yields hockey-stick binomials in q — polynomial. With the Floor below and (c) above, the sandwich exists at every k. ∎(d)

## 3. Verification against reality (Ley 17 — the q=9 census, BOTH regimes)
For k=3, q=9, the measured Syz (from the census via the transfer identity) versus the ceiling of (c), at nine collar degrees spanning level 1 (f < 9) AND level 2 (f ≥ 9):
| f | d | Syz measured | ceiling | holds |
|---|---|---|---|---|
| 0 | 18 | 6769 | 7378 | ✓ |
| 2 | 20 | 17899 | 23618 | ✓ |
| 4 | 22 | 41371 | 59178 | ✓ |
| 6 | 24 | 85050 | 122458 | ✓ |
| 8 | 26 | 157290 | 221858 | ✓ |
| 10 | 28 | 266175 | 364098 | ✓ (level 2) |
| 12 | 30 | 417865 | 554218 | ✓ (level 2) |
| 14 | 32 | 617435 | 797258 | ✓ (level 2) |
| 17 | 35 | 1017590 | 1272068 | ✓ (level 2, top) |
**9/9 — including the entire regime the cascade left open.**

## 4. The dual band (one paragraph)
The twin system at c = q+f restricts on each sheet, after Frobenius linearity over F_q (ℓ_j^q|_J = (Σβu)^q = Σβu^q), to syzygy identities over the SAME regular sequence (u^q) with frame-constant coefficients; (a)–(c) apply verbatim, so the dual band carries the same all-level ceilings. (Frame scope inherited from Slap 4, stated.)

## 5. Honest scope (Ley 42/48) — what this closes and what it prices
1. **CLOSED (the fila-5 conditional):** the existence of explicit polynomial ceilings for the WHOLE collar of EVERY k, every level. No structural clause remains anywhere in the Silver Bridge; the level count ⌈(k−2)/2⌉ and the "iterated aggregate construction" are subsumed and retired.
2. **PRICED, not closed (the sharpness):** for U_k ≡ P_k the crude ceilings (c) must be tightened per k to the aggregate image (the D_f-analogue: global λ's η-tuples satisfy aggregate constraints — the q=9 table's slack is exactly this). This is finite per-k toll work of the SAME species as k=3's G2 — it always was the bridge toll; nothing new opened.
3. Frames F₃ ∀k: unchanged, fila 6. P0 pack: inherits this document.

## 6. Attack surface for the Auditor
(A) The degree bookkeeping of the Koszul grading (deg e = q; coefficient degrees f−(j−2)q). (B) The subsumption claim (5A recovered at f < q — check the δ_{l,l} = 0 case). (C) The transfer identity slice (rank–nullity at e′ = q+f). (D) The dual-band Frobenius paragraph (constants in F_q). (E) The 9/9 table (recompute from the archived census). (F) The Ley 41 certificate: confirm zero contact with the s46 tomb.

**MARCADOR: [FILA 5 CERRADA EN ESTRUCTURA — LA GUILLOTINA CAE POR COLAPSO: la cascada entera de niveles r ≥ 2 es el complejo de Koszul de la sucesión regular (u^q), exacto a toda profundidad (Teorema 5-II) · techos explícitos z_k(q,f) para TODO k, TODO f, forma cerrada alternante · el Silver Bridge queda INCONDICIONAL en toda dimensión: P ≤ A ≤ U con U computable ∀k, cláusula condicional BORRADA · subsume el 5A y retira los niveles ⌈(k−2)/2⌉ y los agregados iterados como peleas separadas · verificado 9/9 contra el censo real de q=9 INCLUIDO el régimen de nivel 2 · tumba s46 no tocada (certificado corrido) · honesto: la AFILADURA de los techos (U_k ≡ P_k) es el peaje finito por k de siempre — hoy con existencia incondicional · SIN GRITO ∀q — pero el último condicional estructural del Chaise Longue ha muerto]. — Bisel (Constructor, Fable), Fila 5**
