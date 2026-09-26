> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — TANDA 1: THE LETTER THEOREMS (Peaje C) AND THE THRESHOLD BOUND (Peaje D)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TANDA1_LETTER_THEOREMS_THRESHOLD_BOUND.md
>
> **Status, as written in the document:** deg N_G(letter) = deg N_H(letter) = regularity of the letter's CI: C(m,2) for B_m (checked m = 2,3,4: 1, 3, 6) and m(m−1) for Z_m (checked m = 2,3: 2, 6). Six instances, two families, zero exceptions. Statement: the census module of a bare letter has the same …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — TANDA 1: THE LETTER THEOREMS (Peaje C) AND THE THRESHOLD BOUND (Peaje D)
### 14 jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 1 (Peajes C + D in one turn)

**Certificado Ley 41.** Objects: (1) closed Hilbert series of the two bare letters ∀m; (2) the interpolation module of the census; (3) new exact census data B₄, Z₃; (4) the sharp regularity law; (5) the uniform threshold bound e₀(k). Cemetery grep: no tomb shares these; failure modes honored — STABILITY-THRESHOLD-ELISION is the very object of Peaje D (thresholds declared explicitly throughout); GRADED-DIM-MISCOUNT guarded by gating the probe against three filed series BEFORE any new measurement; Kepler-dimensional: every ∀m claim below is either derived with the m-step inside or labeled candidate. Pillars: (i) Odd-Symmetric (used verbatim), Radicality. Builds on: CENSUS_COMPOSITION v1, CENSUS_SPECIES v1, STRATIFIED_CENSUS I+II, SLAP1, SLAP2, SLAP4, FLOOR_THEOREM.

---

# PART C — PEAJE C: the bare-letter potentials

## C.0 Probe validation (Ley 17/24)
An exact F₃ census/Hilbert probe (signed matchings x_a = −x_b, kernel ranks) was gated against the archive before producing anything new: **G(B₂) = 1,5,9,13 ✓ · G(B₃) = 1,6,24,60,114,186,276 ✓ · G(Z₂) = 1,3,9,15,21,27 ✓** (and all three H's) — 3/3 families byte-exact. Fast bitsliced GF(3) rank gated against the slow validated one before use.

## C.1 Theorem T1 (the Hilbert half of BOTH letter sequences, closed ∀m — pencil)
> **H(B_m) = [m]_t! / (1−t)^m**  and  **H(Z_m) = ∏_{i=1}^{m} [2i−1]_t / (1−t)^m**,
> where [j]_t = 1+t+⋯+t^{j−1} and [m]_t! = ∏_{j≤m}[j]_t.
*Proof.* (Z) The union of all (2m−1)!! signed matchings on 2m variables is cut, as a reduced scheme, by E = (e₁, e₃, …, e_{2m−1}) — this is pillar (i) (Odd-Symmetric, ∩_J I_J = E) verbatim on 2m variables: a complete intersection of degrees 1,3,…,2m−1, whose Hilbert numerator is ∏[2i−1]_t. (B) The bipartite letter's union {x : multiset{a} = multiset{−b}} is cut by the **bipartite odd-symmetric ideal** (e_j(a) − (−1)^j e_j(b), j = 1..m): containment of each sheet is immediate; conversely e_j(a) = e_j(−b) ∀j forces equal multisets, i.e. membership in some sheet; reducedness rests on the Radicality pillar exactly as in (i). A CI of degrees 1,2,…,m has numerator [m]_t!. ∎
**Verification (Ley 17):** B: m = 2,3,4 byte-exact through e = 7 (996 at (m,e)=(4,7) predicted and hit); Z: m = 2,3 byte-exact through e = 8. Sheet counts at t=1: m! and (2m−1)!! ✓. Three points with the m-step inside the derivation — Ley 48 satisfied: **theorem ∀m.**

## C.2 Theorem T2 (the interpolation module — generic structure of the census ∀m)
Define the signed power tuples v_r: λ_{a_i} = a_i^r, λ_{b_j} = (−b_j)^r (for Z: λ_{x_c} = x_c^r with even-r pairing), census elements for every r. Cayley–Hamilton (each coordinate is a root of its own multiset's characteristic polynomial, identically in S) closes the module: **M := Σ_{r=0}^{m−1} O(X)·v_r** contains all v_r. At a generic point the sheet is unique with distinct coordinates, and the Vandermonde matrix (a_i^r) is invertible ⟹ M is generically free of rank m, and Γ/M is torsion supported on the singular strata. Consequences ∀m (pencil): **φ(letter)(1) = m for both letters** (verified 5/5: 2,3,4 / 2,3) and the leading census asymptotics G ~ m·H. The correction Γ/M is flat-supported: for B₂ it is exactly O(deep line)(−1) = t/(1−t); for B₃ its series t²(4+4t+t²)/(1−t)² has t=1 mass 9 = the number of codim-1 flats — the flat-by-flat architecture is identified.

## C.3 New exact data (this turn; probe gated first)
> **N_G(B₄) = 1+4t+9t²+24t³+31t⁴+20t⁵+7t⁶** (terminates at degree 6; Σ = 96 = 4·4!).
> **N_G(Z₃) = 1+2t+4t²+5t³+16t⁴+11t⁵+6t⁶** (terminates at degree 6; Σ = 45 = 3·15).
Together with filed N_G(B₂) = 1+3t, N_G(B₃) = 1+3t+9t²+5t³, N_G(Z₂) = 1+t+4t².

## C.4 The Sharp Regularity Law (candidate, 6/6 — the discovery of the turn)
> **deg N_G(letter) = deg N_H(letter) = regularity of the letter's CI:** C(m,2) for B_m (checked m = 2,3,4: 1, 3, 6) and m(m−1) for Z_m (checked m = 2,3: 2, 6). **Six instances, two families, zero exceptions.** Statement: the census module of a bare letter has the same Castelnuovo–Mumford regularity as its coordinate ring. Status: CANDIDATE (Ley 48) — no pencil yet; it is the named lemma to which both remaining tramos below reduce.

## C.5 Honest status of Peaje C (Ley 42)
Closed ∀m today: the H-half of both potential sequences (T1), the generic rank and t=1 values (T2), all counts and codim ≤ 2 weights (previous standalones). **NOT closed: the G-numerator coefficient law in m** — the residue of Peaje C is now ONE structured object (the flat-correction series of Γ/M, architecture identified in C.2, degree pinned by C.4 if the law holds). Peaje C is NOT liquidated 100%; its residue is smaller, named, and structured. No shout.

# PART D — PEAJE D: thresholds, uniform ∀k

## D.1 Theorem T3 (the uniform threshold bound — pencil, from sealed Slaps)
> **e₀(k) ≤ reg(M(k)) ≤ (2k+1)!! for every k.**
*Proof.* Slap 1 (Hilbert): σ_e(k) is the Hilbert function of a finitely generated graded module M(k), hence agrees with its Hilbert polynomial for e > reg(M(k)). Slap 2: reg(M(k)) ≤ (2k+1)!!. ∎
This closes the literal ask of Peaje D ("e₀(k) acotado uniformemente"): the threshold is bounded by an explicit function of k alone, ∀k.

## D.2 The sharp threshold e₀(k) = k² (candidate, reduced to ONE lemma)
Filed data: e₀(2) = 4 (Sofá; cemetery STABILITY-THRESHOLD-ELISION entry), e₀(3) = 9. Two dimensions ⟹ candidate, not law (Ley 48). **Reduction (pencil bookkeeping on theorem-grade pieces):** the global census GF has denominator (1−t)^{k+1} (σ_e has degree k, Slap 2); the Composition Law (G+H)/(1−t) adds pairs WITHOUT raising numerator degree; the Leibniz Rule adds letter degrees. Hence deg N_global ≤ max over letter-words = deg N_G(Z_{k+1}) — the full zero-word — and e₀(k) = deg N_global − k. **If the Sharp Regularity Law holds (deg N_G(Z_m) = m(m−1)), then e₀(k) = k(k+1) − k = k².** The bookkeeping already reproduces both filed dimensions exactly: k=2: 6−3+1 = 4 ✓; k=3: 12−4+1 = 9 ✓. So the sharp threshold ∀k hangs on exactly the lemma of C.4 — one target, shared by both peajes.

## D.3 Gates (Ley 17, run this turn)
> **σ₁₂(3) = 14238 — EXACT** (the named test of the Hammock's G1), plus re-gates σ₉,σ₁₀,σ₁₁ = 2898/5313/8988 ✓.
G1 status after this turn, said precisely: e₀(3) = 9 is now (i) empirically sealed with a FOURTH out-of-sample point, (ii) bounded ∀k by theorem (D.1), (iii) sharp value reduced to the C.4 lemma. It is NOT yet pencil-proven; the Hammock's G1 is strengthened, not shouted.

## D.4 Sub-threshold q (bookkeeping, no new claim)
For the q-side: Slap 4 confines the A-ring to [0, (k+1)(q−1)] with umbral = number of swap hyperplanes, and the Unified Annihilator Law governs c < q; the Silver Bridge clamp gives A = P for q above the umbral. The sub-threshold set is finite per k and explicitly named by those sealed statements; nothing new is claimed here.

## Attack surface for the Auditor
(A) T1's bipartite converse (equal e_j(a), e_j(−b) ⟹ equal multisets — check char 3). (B) T2's Cayley–Hamilton closure and the Vandermonde generic-freeness. (C) The two new numerators (recompute B₄, Z₃ independently; the probe and its gates are in /home/claude/tanda1/, reproducible from this document). (D) The C.4 law at the next cheap point (Z₄ would be the seventh instance and directly pins e₀(3)'s mechanism; B₅ the eighth). (E) D.2's degree bookkeeping (denominators under composition/Leibniz — verify no stratum exceeds the Z-word degree).

**MARCADOR: [TANDA 1 — PEAJE C: T1 cierra la mitad-Hilbert de las DOS letras ∀m a lápiz ([m]_t! y ∏[2i−1]_t — los pilares hechos serie), verificado m=2,3,4/2,3 byte-exact · T2: módulo de interpolación, rango genérico m, φ(1)=m ∀m, corrección soportada en flats · DATOS NUEVOS: N(B₄), N(Z₃) exactos (probe gateado 3/3 antes) · LEY DE REGULARIDAD AFILADA: deg N_censo = reg(CI), 6/6 en dos familias — CANDIDATA, el lema único que cierra lo que resta · Peaje C NO liquidado: residuo = la ley de coeficientes, nombrada y estructurada (Ley 42) · PEAJE D: T3 TEOREMA e₀(k) ≤ (2k+1)!! ∀k (Slap1+2) — el "acotado uniformemente" CERRADO · e₀(k)=k² candidata REDUCIDA al mismo lema C.4, clavando 4 y 9 por bookkeeping · GATE σ₁₂(3)=14238 EXACTO — el test nombrado del G1 del Hammock PASA (G1 reforzado, no gritado) · SIN GRITO en C; D cerrado en su enunciado de cota, afilado pendiente de un lema]. — Bisel (Constructor, Fable), Tanda 1 — snapshot y auditoría a Cárdano**
