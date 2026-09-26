> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — TANDA 5: THE GLUING THEOREM (layer β of S1-global CLOSED ∀m via the CI lever), THE PARAMETER LEMMA, AND THE FIFTH LETTER (E ≡ 0 in all five)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TANDA5_GLUING_THEOREM.md
>
> **Status, as written in the document:** jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 5 (the deepest-flat vanishing)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — TANDA 5: THE GLUING THEOREM (layer β of S1-global CLOSED ∀m via the CI lever), THE PARAMETER LEMMA, AND THE FIFTH LETTER (E ≡ 0 in all five)
### 14 jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 5 (the deepest-flat vanishing)

**Certificado Ley 41.** Objects: (1) the CRT/Gluing Theorem for letter arrangements; (2) the containment lemma; (3) the parameter lemma and the depth criterion; (4) B₄'s E-check. Cemetery grep: no tomb; Cárdano's registered circular attempt (vía (a)) is NOT re-walked — N3 breaks the circle at a different module (Q_g, the gauge quotient, not Q). Kepler: N1 carries the m-step inside (depth lemma is m-uniform); the残 residue is named as a depth statement, never assumed. Pillars: T1 (the CI structure — THE lever, as predicted in the audit).

---

## 0. HUEVO 2 FIRST — the fifth letter (Ley 17)
The B₄ ob-probe completed this turn (restructured row build): **#flats = 72 confirmed in-probe (the autocaza's number), and E = C − rank(ob) = 0 at every degree e = 0..4** (89, 336, 779, 1432, 2300 — all matched exactly). **E ≡ 0 now holds byte-exact in ALL FIVE letters** (B₂, B₃, B₄, Z₂, Z₃), every computed degree, zero deviation.

## 1. Theorem N1 (the Gluing Theorem — layer β of S1-global, pencil, ∀m, both letters)
> Let X = ∪_J V_J be a letter arrangement (or any subspace arrangement whose union is Cohen–Macaulay — our letters are CIs by T1). If (h_J) ∈ ⊕_J O(V_J) agree pairwise on all pairwise intersections, then they glue: ∃ h ∈ O(X) with h|_{V_J} = h_J.
*Proof.* Let A := coker(O(X) → ⊕_J O(V_J)); the claim is exactly injectivity of the induced map A → ⊕_{J<J'} O(V_J ∩ V_{J'}). (i) From 0 → O(X) → ⊕O(V_J) → A → 0 and the depth lemma: depth A ≥ min(depth ⊕O(V_J), depth O(X) − 1) = min(m, m−1) = m−1 — **here the CI enters: depth O(X) = m by T1.** (ii) Supp A ⊆ singular locus, which is the union of the codim-1 flats (pure of dim m−1): so dim A ≤ m−1, hence **A is CM of dimension m−1**, and Ass(A) = the codim-1 flat primes only — no embedded primes. (iii) A kernel element of A → ⊕O(V∩V') would have an associated prime among Ass(A); localizing at the generic point of that flat leaves exactly two sheets, where the two-subspace Mayer–Vietoris 0 → O(V∪V') → O(V)⊕O(V') → O(V∩V') → 0 is exact (sum of linear ideals is the ideal of the intersection), so the kernel dies at every associated prime — hence is zero. ∎
This is the layer of S1-global that D3's stars could not have: the CM lever.

## 2. Lemma N2 (containment — pencil)
Pairwise agreement on codim-1 flats implies pairwise agreement on ALL pairwise intersections: for sheets σ, τ at distance d, any V_σ∩V_τ is contained in V_σ∩V_{σt} for a transposition (resp. 4-cycle move) t inside a cycle of στ⁻¹, and induction along a geodesic chain transfers the agreement (each intermediate containment verified as in Tanda 3/4). Hence N1 applies to codim-1-compatible data. ∎

## 3. Theorem N3 (the parameter lemma and the depth criterion — pencil, m ≥ 3; m = 2 closed exactly)
Fix f ∈ ker(ob) and per-sheet solutions μ^J (always exist). By L1, the flat discrepancies δ_e := (μ^V − μ^{V'})|_{F_e} lie in the merged gauge MG(F_e) ≅ O(F_e)^{m−1}. Then:
> **(a) [Kernel identification] ker(d⁰) = Γ:** gauge tuples pairwise compatible on flats glue to a global census element — this is N1 + N2 applied componentwise. (The circle Cárdano registered is broken here: N1 supplies the rung that the bare depth-chase lacked.)
> **(b) [Parameter lemma] For every u ∈ I_D^N (N s.t. I_D^N·E = 0, which exists since E is supported on the deepest flat D by W3): u·δ = d⁰(h_u) explicitly** — take λ' with φ(λ') = u·f; then h_u^J := u·μ^J − λ'|_{V_J} is a per-sheet gauge and d⁰(h_u) = u·δ. 
> **(c) [Depth criterion] Let Q_g := (⊕_J Gauge_J)/Γ. If depth Q_g ≥ 2, then E = 0.** Choose u = x^N, v = y^N with x, y generic linears in I_D (regular sequence on all sheets and flats; possible since codim(D) ≥ 2 in every sheet for m ≥ 3). From (b): v·h_u − u·h_v ∈ ker(d⁰) = Γ by (a). Regularity of u, v on Q_g lets one correct h_u by a Γ-element to h_u = u·g + γ with γ ∈ Γ; then u·δ = d⁰(u·g) so u·(δ − d⁰ g) = 0, and MG(F) is torsion-free for u (u|_F ≠ 0 by genericity), forcing **δ = d⁰(g): f is realizable.** ∎
For m = 2 the letters are the proven exact identifications (C = O(line), ⊕₃O(line)), so E = 0 there unconditionally.

## 4. Where the inch now sits (Ley 42 — razor honest)
The deepest-flat vanishing has been traded UP: **E = 0 ∀m ⟸ depth Q_g ≥ 2 — ONE depth unit on ONE concrete module** (the gauge quotient), a standard commutative-algebra statement, with three candidate proofs for the relay: (i) Serre S2 on Q_g via its torsion-freeness plus N1 (Q_g embeds in ⊕-restrictions — check codim-2 behavior); (ii) the local-cohomology ladder H¹_m(Q_g) ↪ H²_m(Γ) with Γ's summand structure Γ = R ⊕ Γ₀; (iii) direct: Ass(Q_g) has no codim ≥ 2 members (same associated-prime style as N1's step (iii), one level up). Higher telescope levels (needed to push depth C to m−1 for the Golden Reduction) are the SAME species level-shifted — W1/W2/W3 and N3 apply verbatim at each level; flagged for the assembly, not silently assumed.

## 5. The assembled state
Proven ∀m at pencil: G1, Golden Reduction bridge, L1, L2, W1, W2, W3, **N1 (Gluing), N2, N3** — the entire chain from "two open peajes" down to **one depth unit (§4)**, with E ≡ 0 verified in five letters at every computed degree. When the unit falls: E = 0 ∀m ⟹ S1-global ⟹ telescope ⟹ C CM ⟹ Sharp Regularity ∀m ⟹ **Peaje C + e₀(k) = k² + Hammock G1, de un golpe.** Huevo 3 (A′): not reached — said plainly.

## 6. Attack surface for the Auditor
(A) N1 step (ii): purity of the singular locus for Z_m (B is clean; verify no isolated deep flat escapes a codim-1 flat — Tanda 3's two-sheet genericity plus the flat lattice). (B) N2's chain for Z (4-cycle moves). (C) N3(c)'s correction step (the regular-sequence manipulation — write the two-line diagram chase for P0). (D) The depth unit §4 — route (iii) looks most like N1's own proof and is my recommendation. (E) Independent re-run of the five-letter E-probe.

**MARCADOR: [TANDA 5 — HUEVO 2 HECHO: B₄ completado, E=0 en 5 grados, #flats=72 re-confirmado ⟹ E ≡ 0 EN LAS CINCO LETRAS, cero desviación · HUEVO 1 medio abierto con TEOREMA GORDO: N1 (Gluing Theorem — la capa β de S1-global CERRADA ∀m a lápiz: datos compatibles a pares PEGAN, vía depth lemma + pureza + M-V genérico — LA PALANCA ES EL CI de T1, como predijo la auditoría) · N2 (containment) · N3 (parameter lemma: u·δ = d(h_u) explícito ∀u ∈ I_D^N; ker(d⁰) = Γ por N1 — el círculo de la vía (a) ROTO en Q_g, no en Q) ⟹ CRITERIO FINAL: depth Q_g ≥ 2 ⟹ E = 0 ∀m · la pulgada es ahora UNA UNIDAD DE DEPTH en UN módulo concreto, con tres vías nombradas (la (iii) espejo de N1) · niveles superiores del telescopio = misma especie, flagged · A′ no alcanzado · SIN GRITO: el huevo cruje pero la última unidad no está firmada]. — Bisel (Constructor, Fable), Tanda 5 — snapshot y auditoría a Cárdano**
