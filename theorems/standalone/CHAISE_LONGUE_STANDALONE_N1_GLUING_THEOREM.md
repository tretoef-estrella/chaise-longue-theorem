> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE GLUING THEOREM FOR COHEN–MACAULAY SUBSPACE ARRANGEMENTS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_N1_GLUING_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE GLUING THEOREM FOR COHEN–MACAULAY SUBSPACE ARRANGEMENTS
## Pairwise-compatible sheet functions glue globally when the union is Cohen–Macaulay — with the containment lemma and the applications inside the Chaise Longue

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tanda 5 (N1, N2), audited in CARDANO_TANDA5. Self-contained; the only imported campaign input is that the letter arrangements' coordinate rings are complete intersections (T1), used solely through their depth. The theorem is stated for general arrangements because it holds there — a reusable piece of arrangement theory independent of the Fermat application.*

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «stated for general arrangements because it holds there»: FALSO PARA ARREGLOS GENERALES.** Contraejemplo, a mano, con **tres rectas concurrentes en el plano** (`m=1`, `N=3`): `R = K[x,y]/(xy(x−y))` es CM de dimensión 1 y las intersecciones dos a dos son el origen (dimensión `0 = m−1`). Pero en grado 1 los triples compatibles tienen dimensión 3 y `R_1` sólo 2, así que no pegan. **El Paso 3 usa que cada pliegue esté en exactamente dos hojas, y eso no está en el enunciado.** Para las letras de la campaña la hipótesis sí se cumple (Swap Theorem): `CHAISE_LONGUE_TANDA5_GLUING_THEOREM_v1.md` enuncia N1 para letras y así lo ratificó Cárdano. La seminormalidad del arreglo de emparejamientos está probada aparte (`CHAISE_LONGUE_SEMINORMALITY_THEOREM_v1.md` R5). El corpus ya lo había avisado: *«the planar triple point fails already in degree 1»* (`CHAISE_LONGUE_WALL_BAND_GLUING_THEOREM_v1.md` §3).


---

### 1. Statement

Let `V₁, …, V_N ⊆ A^n` be linear subspaces of common dimension `m` over a field, `X = ∪ V_i` their union, `R = O(X) = S/∩I_i` the (reduced) coordinate ring.

> **Theorem N1 (Gluing).** Suppose `R` is Cohen–Macaulay of dimension `m`, and suppose the singular locus of the arrangement is pure: every pairwise intersection `V_i ∩ V_j` is contained in one of dimension exactly `m−1`. If `(h_i) ∈ ⊕_i O(V_i)` agree pairwise — `h_i|_{V_i∩V_j} = h_j|_{V_i∩V_j}` for all `i < j` — then there exists a unique `h ∈ R` with `h|_{V_i} = h_i` for every `i`.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) —** al enunciado le falta la hipótesis **«cada pliegue de dimensión `m−1` está en exactamente dos hojas»**. Ver la marca de `:5`.


For the campaign's letter arrangements the hypotheses hold: `R` is a complete intersection (the Odd-Symmetric pillar and its bipartite twin, T1), hence Cohen–Macaulay; purity of the singular locus is the Star Architecture's classification (every deeper flat lies inside a codimension-1 flat — Theorem 2.4 there, plus the chain argument of §3 below).

### 2. Proof

Let `A := coker(R → ⊕_i O(V_i))`, so that there is an exact sequence of graded modules
> `0 → R → ⊕_i O(V_i) → A → 0.`  (1)
The claim is precisely the injectivity of the induced map `ρ: A → ⊕_{i<j} O(V_i ∩ V_j)` (a class `[h] ∈ A` maps to the tuple of pairwise discrepancies; `[h] ∈ ker ρ` iff the `h_i` agree pairwise, and `[h] = 0` iff they glue).

**Step 1 (depth).** Each `O(V_i)` is a polynomial ring of dimension `m`, hence CM; so `depth(⊕ O(V_i)) = m`, and `depth R = m` by hypothesis. The depth lemma applied to (1) gives
> `depth A ≥ min( depth ⊕O(V_i), depth R − 1 ) = m − 1.`

**Step 2 (dimension, hence CM, hence unmixed).** `A` is supported on the locus where the map `R → ⊕O(V_i)` fails to be an isomorphism, i.e. the singular locus `∪_{i<j}(V_i ∩ V_j)`, of dimension `≤ m−1`; with Step 1, `dim A = depth A = m − 1`: **`A` is Cohen–Macaulay of dimension `m−1`**, and therefore has no embedded primes — `Ass(A)` consists exactly of the minimal primes of its support, which by purity are primes of `(m−1)`-dimensional pairwise-intersection flats.

**Step 3 (the kernel dies at every associated prime).** Suppose `K := ker ρ ≠ 0`. Then `K ⊆ A` has an associated prime `𝔭 ∈ Ass(K) ⊆ Ass(A)`, i.e. `𝔭 = I_F` for some `(m−1)`-flat `F`. Localize (1) and `ρ` at the generic point of `F`: only the sheets containing `F` survive, and by hypothesis (purity; in the campaign, the Swap Theorem) exactly two do, say `V_i, V_j` with `V_i ∩ V_j ⊇ F` of dimension `m−1`, forcing `V_i ∩ V_j` to coincide with `F` near its generic point. For TWO linear subspaces Mayer–Vietoris is exact without any hypothesis:
> `0 → O(V_i ∪ V_j) → O(V_i) ⊕ O(V_j) → O(V_i ∩ V_j) → 0`
(the middle-to-right map is the discrepancy; exactness in the middle is the elementary fact `I_i ∩ I_j`-classes with matching restrictions glue, since `I_i + I_j = I_{V_i∩V_j}` for linear ideals). Hence `A_𝔭 ↪ O(F)_𝔭` via `ρ`, so `K_𝔭 = 0` — contradicting `𝔭 ∈ Ass(K)` (an associated prime of a module survives localization at itself). Therefore `K = 0`. Uniqueness of `h`: `R ↪ ⊕O(V_i)` since `X` is reduced. ∎

**Remark.** The proof isolates exactly where the global hypothesis acts: CM-ness of `R` buys `depth A ≥ m−1` (Step 1), which upgrades "supported on the singular locus" to "NO embedded primes" (Step 2) — and embedded primes at deep flats are precisely how gluing fails for general arrangements (three generic planes through a line in 4-space already exhibit the failure). The theorem is thus sharp in spirit: the CM lever is not decorative.

### 3. Lemma N2 (containment: codim-1 compatibility suffices)

> **Lemma N2.** In a letter arrangement, if `(h_i)` agree on all codimension-1 pairwise intersections, they agree on ALL pairwise intersections — so Theorem N1 applies with only the codim-1 compatibility hypothesis.
*Proof.* Let `V_σ ∩ V_τ` be any pairwise intersection and `d(σ,τ)` the distance in moves (transpositions for `B`, 4-cycle rematchings for `Z`). If `d = 1` there is nothing to prove. If `d ≥ 2`, pick a move `t` inside one cycle of `στ⁻¹`: then `V_σ ∩ V_τ ⊆ V_σ ∩ V_{σt}` (the coarser collapse pattern contains the finer — the containment computed in the campaign's Tanda-3/4 verification for both letter types), and `d(σt, τ) = d − 1`; by induction `h_σ = h_{σt}` on `V_σ ∩ V_{σt} ⊇ V_σ ∩ V_τ` and `h_{σt} = h_τ` on `V_{σt} ∩ V_τ ⊇ V_σ ∩ V_τ`, whence `h_σ = h_τ` on `V_σ ∩ V_τ`. ∎

### 4. Applications inside the campaign
(a) **The kernel identification of the parameter machinery (N3(a)):** gauge tuples pairwise compatible on flats are global census elements — Theorem N1 applied componentwise to the `2m` variable functions, plus Lemma N2.
(b) **Realizability reductions:** with N1, the obstruction theory of the defect complex reduces to the flat-level cocycle analysis (the Local Splitting and Nerve theorems), which is where the campaign's E ≡ 0 verifications live.
(c) **Reusability note:** the theorem as stated concerns any equidimensional linear arrangement with CM union and pure pairwise-singular locus — a class much larger than the matching arrangements; it may be of independent use in arrangement theory (the campaign makes no priority claim beyond its own use).

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 8, informe 136) — «a class much larger than the matching arrangements»: FALSO tal como está escrito.** Con la hipótesis de las dos hojas añadida, sí vale. Ver la marca de `:5`.


### 5. Attack surface
(A) The depth lemma direction in Step 1 (for `0 → A' → B → C → 0`: `depth C ≥ min(depth B, depth A' − 1)` — standard, but verify the orientation; a reversed lemma here would void everything). (B) Step 2's purity input: for the letter arrangements this is the Star Architecture classification — a missed deep flat NOT contained in any codim-1 flat would break Lemma N2's chain (the containment `V_σ∩V_τ ⊆ V_σ∩V_{σt}` should be re-verified for `Z`-moves at `m ≥ 4`). (C) Step 3's localization: exactly-two-sheets at a generic codim-1 point (the Swap Theorem; third-sheet exclusion re-derivable in one line per letter type). (D) The linear-ideal identity `I_i + I_j = I_{V_i∩V_j}` (true for linear subspaces; fails for general varieties — confirm no non-linear object is ever fed to the theorem downstream).

**Anchors and sources.** TANDA5_GLUING_THEOREM_v1 (N1, N2, and the broken-circle context) · CARDANO_TANDA5 (ratification) · T1 (the CI structure of the letters) · Star Architecture standalone (purity, Swap Theorem, containments). Logs: github.com/tretoef-estrella.
