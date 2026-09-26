> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE V-ENGINE KERNEL THEOREMS: THE DEATH MODULE NAMED, THE SYMMETRIC SECTOR SOLVED EXACTLY (∀k∀q), AND THE ONE-BANK CAM SOLVED IN CLOSED FORM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_VENGINE_KERNEL_THEOREMS.md
>
> **Status, as written in the document:** Certificado Ley 41. Objects: (1) the per-sheet death module's identity; (2) the symmetric-sector death criterion; (3) the one-bank annihilator. Streets: the fire-test discipline of the mission is the governing constraint — NOTHING below uses the q=27 table as …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE V-ENGINE KERNEL THEOREMS: THE DEATH MODULE NAMED, THE SYMMETRIC SECTOR SOLVED EXACTLY (∀k∀q), AND THE ONE-BANK CAM SOLVED IN CLOSED FORM
## Frobenius linearity (the Sofá's own Prop-1.4 tool) unlocks the kernel: the per-sheet death module IS ann_Q(Π) — the apolar annihilator of the discriminant-product in the Frobenius-power quotient, a basis-free standard object. Within it: the symmetric sector falls EXACTLY for every k and q (alternant criterion λ₁ ≥ (q−1)/2 − k, one-line proof, gated both directions), re-deriving the onset AND half of the sign lemma as corollaries; and the single-bank cam is solved in closed form (ann = the corner ideal (v₁^{q−1}, v₂^{q−1})). The V-assembly (the timing chain between the two banks) is the one named remaining montage — the fire test is NOT passed this turn, and is not sold as passed.

**Chaise Longue campaign — mission MOTOR_V delivery** · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits with own code) · All pencil (Ley 49); symbolic checks are minute-long verifications of pencil claims.

**Certificado Ley 41.** Objects: (1) the per-sheet death module's identity; (2) the symmetric-sector death criterion; (3) the one-bank annihilator. Streets: the fire-test discipline of the mission is the governing constraint — NOTHING below uses the q=27 table as input, and the fire test's status is declared honestly in §5. The 6-vs-9 flag is SEALED per Locard's resolution (§4). No tomb touched (grep: apolar/annihilator-of-discriminant/corner ideal — absent from corpus).

---

## §0. Para Rafa — clave de motor (tu V, horas bien estrujadas)

Tu V era exacta y hoy tiene piezas torneadas: **cada árbol de levas, POR SEPARADO, está resuelto al micrómetro** — el contacto de una leva con el muro es un ideal de esquina, fórmula cerrada, todas las revoluciones (§3). Y el **semieje simétrico del motor entero** (el sector donde los dos brazos giran en fase) está derivado EXACTO para todos los cilindros y regímenes (§2): sabemos exactamente qué formas caben y cuáles tocan el muro, con un criterio de una línea. Lo que falta — y no te lo vendo como hecho — es **la cadena de distribución entre los dos árboles**: cómo se acoplan los dos bancos al girar juntos contra el muro. Esa cadena es la prueba de fuego q=27, y este turno queda NOMBRADA con todas sus piezas listas, no montada. Pero el motor ya no tiene ninguna pieza misteriosa: el kernel entero tiene nombre y apellidos de catálogo (§1).

## §1. Theorem KERNEL-ID (the death module named — the montage's foundation)

By **Frobenius linearity** — (aℓ+bℓ′)^q = aℓ^q + bℓ′^q in char 3, hence m^[q] = (ℓ^q : ℓ ANY linear form), the Sofá's own Prop 1.4 mechanism — the quotient **Q := F₃[u₁,…,u_{k+1}]/m^[q] is basis-free** (GL-stable: any linear change of coordinates preserves it). Therefore:

> **Theorem KERNEL-ID.** The per-sheet death module of the transient is **ann_Q(Π)**, Π = ∏_{i<j}(u_i²−u_j²) — the apolar annihilator of the discriminant-product in the Frobenius-power complete intersection. It is one fixed-type, Gorenstein-framed (socle degree (k+1)(q−1)), GL(k+1)-structured object; **diana 3 = its Hilbert function**, a finite well-posed computation, no longer a mist.
*Consequence used below:* coordinates may be chosen PER FACTOR of Π — the unlock for §3.

## §2. Theorem LEVAS-SYM (the symmetric sector, solved exactly, ∀k ∀q)

Odd alternants: for a partition λ, det[u_i^{2(λ_j+k+1−j)−1}] = e_{k+1}(u)·Π·s_λ(u²) (bialternant, one line — Locard's Ley de Levas). **Every monomial of the determinant uses each column exactly once**, so every monomial carries the SAME exponent multiset {2(λ_j+k+1−j)−1}. Hence:

> **Theorem LEVAS-SYM.** The symmetric-sector deaths (h symmetric, Π·h alternating) at cofactor degree h₀ = (k+1)+2|λ| are EXACTLY the span of { e_{k+1}(u)·s_λ(u²) } with
> **λ₁ ≥ (q−1)/2 − k** — membership in m^[q] holds if and only if the top column exponent 2(λ₁+k)+1 ≥ q. (Gated both directions at k=2, q=9: columns {7,5,1} NOT in m^[q] ✓; {11,3,1} in ✓.)
**Corollaries (each one line):**
- **(i) The onset re-derived:** minimal |λ| with λ₁ ≥ (q−1)/2−k is the single row λ = ((q−1)/2−k), unique ⟹ Theorem MS's element and its uniqueness fall as corollaries.
- **(ii) HALF THE SIGN LEMMA PROVEN:** any symmetric-sector death has h₀ = (k+1)+2|λ| ≥ (k+1)+2λ₁ ≥ q−k — **no symmetric death below the wall onset, for every k and q.** (Task 6, symmetric case closed; general sectors remain named.)
- **(iii) The symmetric per-degree count, exact:** # partitions λ of (h₀−k−1)/2 with λ₁ ≥ (q−1)/2−k and ≤ k+1 parts... [generating function ∏(1−t^{2j})⁻¹ with the largest-part threshold — closed combinatorics, filed for the assembly].

## §3. Theorem BANK (the single cam solved in closed form — Rafa's leva, exact)

A bank (one heavy slot's 2 pair-coordinates at k=3) carries the block discriminant π_B = u₁²−u₂². By Frobenius linearity choose bank coordinates v₁ = u₁−u₂, v₂ = u₁+u₂ (the ideal m^[q] is unchanged): π_B = v₁v₂ and Q₂ = F₃[v₁,v₂]/(v₁^q, v₂^q). Multiplication by v₁v₂ shifts the exponent box; the kernel is the corner:

> **Theorem BANK.** **ann_{Q₂}(π_B) = (v₁^{q−1}, v₂^{q−1})** exactly; its Hilbert function is **2 in every degree e ∈ [q−1, 2q−3] and 1 at e = 2q−2**, zero elsewhere. (Brute-force gate at q=3: kernel monomials ≡ corner ideal box, byte-exact; the general statement is the one-line box-shift argument.)
*Reading:* one cam's full contact law with its own wall, closed form, all q. The two eigen-directions v₁, v₂ (the ± sign branches) are literally the two corner generators — Locard's sign-coherence structure materialized inside a single bank.

## §4. Sealed and absorbed this turn
- **6-vs-9: SEALED** (Locard's resolution adopted verbatim): 9 = edges of K(3,3) (the internal sheets), 6 = vertices, b₁ = 9−6+1 = 4 = the filed Betti number. Diana 2's mechanism (unique minimal shape per sheet + sgn-multiplicity-1 gluing over the 9 edges) stands without the flag.
- **The deeper family confirmed** (feeds the head hunt, no claims): Π·(u_i−u_j)^{q−1} ∈ m^[q] (gated k=2, q=3) — factor-annihilator deaths at h₀ = q−1, i.e. depth g = k−1; these overlap the leva families and the exact HF of §1 will sort the count.

## §5. The fire test — status said with the knife (Ley 42; the mission's hard limit)
**NOT PASSED THIS TURN, and not sold otherwise.** What the fire test requires: the V-assembly (the coupling of the two solved banks through the sheet/star gluing) spitting the q=27 per-degree values with zero input from them. What this turn changed: the kernel is a NAMED standard module (§1) whose HF is a finite computation; the symmetric sector of it is EXACT ∀k∀q (§2); each bank factor is EXACT (§3); the sign lemma is half-proven; and 6-vs-9 is sealed. The remaining montage is ONE well-posed object: **the two-bank coupling** (formally: the bipartition-star sector of ann_Q(Π) as a module over Q₂ ⊗ Q₂ with the transposition) — pencil-first; its smallest instances (g = 0: must give 1 ✓ already forced by MS+gluing; g = 1: must give 9 per bipartition) are the next construction's first dianas, derivable before touching q = 27.

## §6. Attack surface for Locard
(i) LEVAS-SYM's one-line proof (the full-exponent-multiset observation) — try to break it with a non-partition column multiset. (ii) BANK: re-derive the corner ideal independently and its HF (2,…,2,1); check the k-general bank ((k−1) rows: is ann of the block-discriminant still a "corner-type" ideal in Frobenius coordinates? — the k=4 bank is the first test). (iii) The corollary chain (onset + half-sign-lemma) — three lines each. (iv) KERNEL-ID: verify ann_Q(Π)'s socle-degree bookkeeping ((k+1)(q−1)) and that the transient's per-sheet deaths embed exactly there (degree dictionary c = k(k+1)+h₀). (v) The g=1 diana: from §2's count + §3's banks + the 9-edge gluing, hand-derive the per-bipartition death dimension at depth 1 — target 9, ZERO inputs. **This is the first link of the timing chain and the natural next mission.**

**Anchors.** MISION_BISEL_MOTOR_V + LOCARD_VENGINE_AUDIT.py (the V, the Architect's prediction, measured) · MOORE_WALL_ONSET_THEOREM_v1 · Sofá Prop 1.4 (Frobenius linearity) · Golpe-2 4.2′ · session gates (alternant both-directions; bank q=3 byte-exact; ℓ^{q−1} family).

**MARCADOR: [EL KERNEL CON NOMBRE Y LAS PRIMERAS PIEZAS TORNEADAS — THEOREM KERNEL-ID: el módulo de muertes por sheet ES ann_Q(Π), el aniquilador apolar del producto-discriminante en el cociente de potencias Frobenius, objeto ESTÁNDAR basis-free (la linealidad de Frobenius del propio Sofá como llave); diana 3 = su función de Hilbert, cómputo finito bien puesto · THEOREM LEVAS-SYM (∀k∀q, EXACTO): el sector simétrico resuelto — muertes = alternantes impares e_{k+1}·s_λ(u²) con criterio λ₁ ≥ (q−1)/2 − k, prueba de UNA LÍNEA (cada monomio del determinante usa cada columna una vez), gateado en AMBAS direcciones; corolarios de una línea: el onset re-derivado (MS cae como corolario) y MEDIO LEMA DE SIGNOS PROBADO (ninguna muerte simétrica bajo q−k, ∀k∀q) · THEOREM BANK (la leva de Rafa, resuelta en forma cerrada): en coordenadas Frobenius del banco, ann_{Q₂}(v₁v₂) = (v₁^{q−1}, v₂^{q−1}) — el ideal de ESQUINA, HF = (2,…,2,1) en [q−1, 2q−2], gate q=3 byte-exact; las dos direcciones propias v₁,v₂ son los dos generadores de la esquina — la coherencia de signos materializada dentro del banco · 6-vs-9 SELLADO (9 = aristas K(3,3), 6 = vértices, b₁ = 4 ✓, resolución de Locard adoptada) · familia profunda ℓ^{q−1} confirmada (alimenta la caza de la cabeza, sin claims) · PRUEBA DE FUEGO: NO PASADA Y NO VENDIDA — el montaje restante es UNO y bien puesto (el acople de los dos bancos por el star; primer eslabón: la diana g=1 = 9 por bipartición, derivable con cero insumos — la siguiente misión natural) · TODO LÁPIZ · SIN GRITO ∀k∀q — pero LEVAS-SYM y BANK son granito ∀k∀q y el kernel dejó de ser niebla para siempre]. — Bisel (Constructor, Fable), misión Motor V**
