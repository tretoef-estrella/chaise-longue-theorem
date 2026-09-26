> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE EQUIVARIANT MIRROR THEOREM AND THE EXACT ALTERNATING CRITERION* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MIRROR_ALT_THEOREMS.md
>
> **Status, as written in the document:** The Architect's "stop before reverse spin" made exact — and generalized: the Gorenstein pairing of A(P*) is sgn-equivariant, so EVERY irreducible sector mirrors to its sign-twist at the complementary degree (HF_χ(e) = HF_{χ⊗sgn}(s−e), ∀k∀q, three lines). Sign …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE EQUIVARIANT MIRROR THEOREM AND THE EXACT ALTERNATING CRITERION
## The Architect's "stop before reverse spin" made exact — and generalized: the Gorenstein pairing of A(P*) is sgn-equivariant, so EVERY irreducible sector mirrors to its sign-twist at the complementary degree (HF_χ(e) = HF_{χ⊗sgn}(s−e), ∀k∀q, three lines). Sign calibration: the BANK swap is even (P* bank-symmetric — the V's τ); the ARM swap is odd (the true mirror). Plus a new exact tool: an alternating polynomial lies in m^[q] iff EVERY bialternant component has top exponent ≥ q (disjoint supports) — the alternating sector of the wall completely solved. And one atomic autocaza: LEVAS-SYM's "exactly" is downgraded to family-exact, with the completeness gap named and its repair route built from the new criterion. Fire status: pencil not closed this turn — the 3-degree engine memo is prepared for the Architect's OK, not executed.

**Chaise Longue campaign — mission ESPEJO_FUEGO delivery** · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits with own code) · Pencil; symbolic checks verify pencil claims (Ley 49/51).

**Certificado Ley 41.** Objects: (1) the sgn-equivariant mirror on A(P*); (2) the alternating membership criterion; (3) LEVAS-SYM's completeness status. Streets: the fire-test discipline governs (§4 declares NOT closed; nothing q=27 used as input); the engine memo is delivered as a MEMO awaiting the Architect's explicit OK (Ley 29/49 — mission's own condition). Ley 37 applied to my own LEVAS-SYM (§3).

---

## §0. Para Rafa — clave de motor (tu stop, hecho teorema y calibrado al átomo)

Tu "stop antes del giro inverso" es un teorema de tres líneas — y la calibración atómica descubrió el matiz que lo hace redondo: **hay DOS intercambios distintos en el motor y tienen paridades opuestas.** Intercambiar los dos ÁRBOLES enteros (banco A ↔ banco B) es una permutación PAR: el discriminante ni se entera (por eso la V es serena — P* es simétrica bajo el swap de bancos). Intercambiar los dos BRAZOS de un mismo árbol (la leva v₁ ↔ v₂) es IMPAR: **ahí el signo se invierte — ese es tu espejo, el giro inverso.** Y el teorema dice más de lo que pedíamos: cada "modo de vibración" del motor (cada representación irreducible) se refleja en su gemelo de signo cambiado al grado complementario. El sector antisimétrico no es un misterio aparte: es el simétrico leído en el espejo del zócalo. El fuego a lápiz no cayó este turno — te lo digo sin maquillaje — porque al montar el espejo cacé una tolerancia floja en mi pieza de anteayer (§3) y la relojería atómica no monta sobre holguras. El tiro limpio de tres grados al banco Macaulay2 queda preparado en memo, esperando tu OK.

## §1. Theorem MIRROR (the equivariant mirror, ∀k∀q — the Architect's idea, generalized and calibrated)

Let A = A(P\*) be the coupling algebra (APOLAR), s = (k+1)(q−1−k) its socle degree, and let S_{k+1} act by permuting the sheet coordinates (m^[q] is invariant — Frobenius linearity; the Π-configuration is invariant up to sign).

> **Theorem MIRROR.** (a) σ·Π = sgn(σ)·Π and hence σ·P\* = sgn(σ)·P\* for every σ ∈ S_{k+1}. (b) The Gorenstein pairing ⟨a,b⟩ := (ab-coefficient along P\*) is **sgn-equivariant**: ⟨σa, σb⟩ = sgn(σ)⟨a,b⟩. (c) Therefore the perfect pairing matches isotypic components sign-twisted: for every irreducible χ of S_{k+1},
> **HF_χ(A, e) = HF_{χ⊗sgn}(A, s−e).**
*Proof.* (a) Π is the Vandermonde in the squares — alternating; contraction commutes with the (signed) action on G = (∏u_i)^{q−1} (symmetric). (b) direct. (c) if a, b lie in isotypics χ, χ′ with χ′ ≇ χ⊗sgn, equivariance + Schur force ⟨a,b⟩ = 0 (char 3, 2 invertible for the involution argument); perfectness then pairs χ_e with (χ⊗sgn)_{s−e} in full rank. ∎
**Corollaries (each one line):** (i) total palindromy HF_A(e) = HF_A(s−e) (Locard's measured Gorenstein check — now a corollary); (ii) for any ODD involution τ (an arm swap): **HF_anti-τ(e) = HF_sym-τ(s−e)** — the mission's mirror; (iii) self-sgn-dual irreps (at k=3: the 2-dim [2,2]) are self-palindromic; (iv) **sign calibration (measured this session):** the bank swap (u₁u₃)(u₂u₄) is EVEN — P\* is bank-swap SYMMETRIC (the V's exchange lives in the trivial sign class ✓ consistent with Sym²), while the arm swap (u₁u₂) is ODD — the true mirror. *(This corrects a conflation risk in the mission text: the mirror is the ARM involution, not the bank exchange; both statements are now exact.)*
**New testable prediction filed (from combining (i)+(ii) with Locard's k=2, q=9 measurement anti(e) = sym(e−1)):** the τ-symmetric sector must satisfy **sym(s−e) = sym(e−1)** — a shifted self-palindromy of the sym sector alone. Checkable from his existing run; if it fails, his shift or my mirror has a bug — a mutual gate.

## §2. Theorem ALT-CRITERION (the alternating sector of the wall, completely solved — ∀k∀q)

> **Theorem ALT.** Distinct bialternants a_μ = det[u_i^{μ_j}] (distinct exponent vectors μ) have **pairwise disjoint monomial supports** (each monomial of a_μ carries the exponent multiset μ). Consequently, for any alternating polynomial F = Σ c_μ a_μ:
> **F ∈ m^[q] ⟺ every a_μ with c_μ ≠ 0 has max(μ) ≥ q.**
*Proof.* A monomial of a_μ is u_{π(1)}^{μ_1}⋯; its exponent multiset is exactly {μ_j}, which identifies μ. Membership in the monomial ideal m^[q] is checked monomial-by-monomial. ∎ *(Gate: a_{(7,5,1)} + a_{(9,3,1)} at q=9 — supports disjoint ✓, the sum leaks via the low component ✓.)*
**What this buys:** the intersection m^[q] ∩ (alternating) is a MONOMIAL-like object in the bialternant basis — the entire alternating side of the wall is now solved by inspection. Every death question reduces to tracking bialternant supports through explicit expansions.

## §3. Autocaza (Ley 37/51 — the loose tolerance in LEVAS-SYM, caught before mounting the mirror on it)

LEVAS-SYM v1 said the symmetric-sector deaths are "EXACTLY" the odd-alternant family e_{k+1}·s_λ(u²) with λ₁ ≥ threshold. **The family's criterion is exact (both directions, gated); the COMPLETENESS ("exactly") was not proven** — a general symmetric h has Π·h a COMBINATION of bialternants, and by Theorem ALT it dies iff every component clears the top-threshold: combinations could conspire beyond the single-alternant family. **Corrected statement:** the family is exact as a family and a LOWER BOUND for the sector; the full symmetric-death space = ker of the explicit map (Littlewood–Richardson supports of Π·s_μ(u) against the low-top bialternants), now well-posed by ALT. Completeness = **named P0 gap with its repair route**; the c=36 fire point survives (there the threshold forces the unique (10), and ANY conspiring combination would need components below threshold — impossible at that degree by dimension: |λ| = threshold exactly). The corollaries (onset, half sign lemma) survive as lower-bound statements plus the onset's uniqueness argument.

## §4. Fire status (the knife) + the ENGINE MEMO (prepared, NOT executed)

**Pencil: NOT closed this turn.** The mission's lever ("sym is LEVAS-SYM territory, mirror gives anti") needs, at full rigor, the χ-isotypic symmetric data beyond the S-trivial family — exactly the §3 gap. Rather than mount the fire on a loose tolerance, the honest path per the mission's own fallback:

> **ENGINE MEMO (awaiting the Architect's explicit OK — Ley 29/49).** Macaulay2 v1.26.06, native. Ring F₃[u₁..u₄]. Build P\* = Π ∘ (u₁u₂u₃u₄)^{26} explicitly (contraction of the 12-factor discriminant's expansion — small support). Ideal I = fromDual/inverseSystem(P\*). Compute hilbertFunction(I, e) for **e = 24, 25, 26 only** (q = 27, k = 3). Sizes: dim F₃[u₁..u₄]_{25} = C(28,3) = 3276 — matrices of a few thousand, minutes, single thread, RAM well under the 5.4 GB guard. Output: three raw numbers; Locard crosses them against S2 (via ann_e = HF_Q(e) − HF_A(e), dev(c) at c = 36, 37, 38: targets 35, 315, 1225). **Degree 25 (c = 37) is the killer.**

**What the mirror already pins ∀q, awaiting only those numbers:** by MIRROR(ii), the c=37 anti-sector value equals a sym-sector value at the mirrored degree s−25 = 67 — so the engine's three numbers simultaneously gate BOTH ends of the transient (the junction/head side rides for free: the head's five values are the mirror-deficits of A's first five degrees — forensic thread, HF_A(0) = 1 matching the head's extremal 1, filed report-only).

## §5. Attack surface for Locard
(i) MIRROR's three lines — try to break (c)'s Schur step in char 3 (the 2-invertibility is the only char-sensitive point). (ii) The sign calibration (even/odd) — one determinant each. (iii) The new mutual gate: check sym(s−e) = sym(e−1) on your k=2 q=9 run. (iv) ALT's disjoint-support lemma (one paragraph). (v) §3's correction: verify the c=36 survival argument (threshold-exact degree). (vi) The engine memo's sizing (C(28,3) = 3276) and the fromDual route — pre-flight before the Architect's OK.

**Anchors.** MISION_BISEL_ESPEJO_FUEGO + LOCARD_MIRROR_THEOREM_AUDIT.py (the Architect's stop; Locard's k=2 split) · ACOPLE_APOLAR_THEOREM_v1 · VENGINE_KERNEL_THEOREMS_v1 · session gates (parity calibration; ALT leak test).

**MARCADOR: [EL ESPEJO DEL ARCHITECT HECHO TEOREMA EQUIVARIANTE — THEOREM MIRROR (∀k∀q, tres líneas): σP\* = sgn(σ)P\* ⟹ pairing sgn-equivariante ⟹ **HF_χ(e) = HF_{χ⊗sgn}(s−e) para CADA irreducible** — palindromía total como corolario, anti(e) = sym(s−e) para involuciones impares, el [2,2] auto-palindrómico; CALIBRACIÓN ATÓMICA: el swap de BANCOS es PAR (P\* banco-simétrica — la serenidad de la V) y el swap de BRAZOS es IMPAR (el espejo verdadero — el stop de Rafa vive en la leva, no entre árboles); PREDICCIÓN MUTUA NUEVA filada: sym(s−e) = sym(e−1) en el run k=2 de Locard · THEOREM ALT-CRITERION (∀k∀q, EXACTO): alternantes distintos tienen soportes DISJUNTOS ⟹ F alternante ∈ m^[q] ⟺ cada componente tiene top ≥ q — el sector alternante del muro COMPLETAMENTE resuelto por inspección (gate del leak ✓) · AUTOCAZA (Ley 37/51): el "exactly" de LEVAS-SYM degradado a familia-exacta + cota inferior; la completitud = gap P0 NOMBRADO con ruta de reparación vía ALT (combinaciones LR contra tops bajos); el punto de fuego c=36 SOBREVIVE (grado umbral-exacto, sin espacio para conspirar) · FUEGO: lápiz NO cerrado este turno — dicho sin maquillaje; ENGINE MEMO de TRES grados preparado y dimensionado (C(28,3)=3276, minutos, single thread, bajo la guardia de RAM) ESPERANDO EL OK EXPLÍCITO DEL ARCHITECT, no ejecutado; el espejo hace que los tres números gateen las DOS puntas del transitorio a la vez (la cabeza cabalga gratis como déficit-espejo de los primeros grados) · SIN GRITO ∀k∀q del conteo — pero MIRROR y ALT son GRANITO ∀k∀q]. — Bisel (Constructor, Fable), misión Espejo-Fuego**
