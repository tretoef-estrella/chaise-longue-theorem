> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CENTRAL DEFECT LAW (ALL-k): CLOSURE DELIVERY (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CENTRAL_DEFECT_LAW_ALLK.md
>
> **Status, as written in the document:** Certificado Ley 41. Objects: (1) the zone-vs-CB convention dictionary; (2) the Top-law window; (3) the ∀q status of the k=3 transient law. Tombs touched by content: TRANSFER-CEILING-AS-CLAMP — this document REINTERPRETS that tomb with a symbolic identity (the …
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CENTRAL DEFECT LAW (ALL-k): CLOSURE DELIVERY (v2)
## Tarea 0 closed as a theorem: the Dictionary — B_k^CB = Collar_zone − (the k stolen mirror degrees), the mysterious 15(q−4)² unmasked as ᾱ_q + ᾱ_{q+1}, and the Tanda-11 tomb reinterpreted (the transfer ceilings clamp the zone collar EXACTLY at k=2). Plus the honest kill of the naive ∀q transient extension, with its killing polynomial.

**Chaise Longue campaign — Step 2b closure delivery per MISION_BISEL_STEP2b_CIERRE** · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits with own code)
*Scripts: inline symbolic gates (this session, deposited in snapshot trail). Sources: A′1/CB standalone, Tanda 11, ZETA_RECURSION (whose own label — "tabla de calibración q=9" — turns out to be the exact truth), THE_HAMMOCK final (σ₃ heads 0,0,1,7,29,90,252,636,1435; the named "fine ignition of the pre-stable head H(f)"), Sofá Thm 4.3, Step-1/2b-opening objects.*

**Certificado Ley 41.** Objects: (1) the zone-vs-CB convention dictionary; (2) the Top-law window; (3) the ∀q status of the k=3 transient law. Tombs touched by content: **TRANSFER-CEILING-AS-CLAMP** — this document REINTERPRETS that tomb with a symbolic identity (the tomb's kill numbers were a convention artifact; the honest correction is filed in §2, the tomb is not silently re-walked); **NAIVE-TRANSIENT-Q-EXTENSION** — NEW street buried here with its killing polynomial (§4). BAND-CONVENTION-MISMATCH discipline applied throughout: every identity states its convention.

---

## §0. Para Rafa — el estado en clave de motor (petición transmitida por Locard, aplicada desde hoy)

El teorema es un motor de **k cilindros** (doblados: dimensión 2k), con **2k+2 válvulas** (las variables). **P es la presión nominal** que el cilindro debe aguantar sobre el plano; **A es la presión que medimos** — el teorema dice que el motor rinde exactamente la presión nominal en todos los regímenes (todo q) y con cualquier número de cilindros (todo k).

**Lo de hoy:** descubrimos que el banco de pruebas tenía **dos manómetros con el cero descalibrado entre sí** (la convención "zona" y la convención "CB"). Nadie mentía — pero comparar la lectura de uno con la escala del otro producía "fugas fantasma" (el famoso −191836 y el "overshoot" de la Tanda 11 eran ESO). Hoy los dos manómetros quedan calibrados con fórmula exacta (§1) — y al recalibrar, resulta que **el cilindro k=2 rinde la presión nominal EXACTA en todo el rango**: no había fuga ninguna (§2). En el cilindro k=3, la cámara central (el transitorio, ancho fijo 9 grados) tiene su ley de compresión medida en banco a q=9 (los dos cubos + cinco chicharros de la cabeza), pero al subir de revoluciones la mezcla cambia con q: la extensión ingenua "constantes fijas" **petardeó en el banco simbólico** — y tenemos el polinomio exacto del petardeo (§4), que es información de diseño, no un misterio. Faltan dos piezas: la ley de compresión con q dentro (el T-block de nivel 2) y el origen de los cinco chicharros.

## §1. Theorem Dict (Tarea 0 — the Dictionary, closed ∀k)

**Convention fixed (the ONE convention for Step 4): ZONE.** Collar_zone(k,q) := Σ_{d=2q}^{σ−q} A_d — the census truth. All squeeze identities in Step 4 use zone quantities.

> **Theorem Dict.** The filed CB/A′1 budget and the zone collar differ by exactly the k top mirror degrees of the collar, which the filed Top law absorbs: the Unified Top law Top_k(q) = N·C(q−k²+k, k+1) equals, by the hockey-stick identity, **Σ_{c ≤ q+k−1} ᾱ_c^{stable}** — a window that overshoots the true Top zone (c < q) by the k degrees c = q, …, q+k−1. Hence
> **B_k^CB(q) = Collar_zone(k,q) − N·Σ_{j=0}^{k−1} C(q−k²+j, k).**
**Gates (byte-exact / symbolic):**
- **k=2, symbolic ∀q:** stolen = 15[C(q−4,2)+C(q−3,2)] = **15(q−4)²** — *the CB "slack_total₂" was never slack: it is ᾱ_q + ᾱ_{q+1}, the two collar mirror degrees double-booked between conventions.* And Collar_zone(2,q) = Σ_{f=0}^{3} 15·C(q−1−f,2) = **30q²−180q+300** (hockey stick), so Collar_zone − B₂^CB = 15(q−4)² ✓ — Locard's 1110 − 735 = 375 identity, now a theorem ∀q.
- **k=3, q=9:** stolen = 105[C(0,3)+C(1,3)+C(2,3)] = **0** — explaining exactly why the two conventions silently agreed at the Hammock's anchor (and why Step 1's gates never saw the gap).
- **k=3, q=27 — falsifiable prediction:** stolen = 105[C(18,3)+C(19,3)+C(20,3)] = **307125**. Any future q=27 bookkeeping must show B₃^CB = Collar_zone − 307125, or Dict is wrong.

## §2. The Tanda-11 tomb, reinterpreted (a cemetery correction, filed with its identity)

Tanda 11 killed "transfer ceilings as the clamp" with: Σcrude₂ = 30q²−180q+300 vs B₂ = 15q²−60q+60, overshoot 15(q−4+…)². **The symbolic identity of §1 shows Σcrude₂ = Collar_zone(2,q) EXACTLY** — the transfer-form sharp ceilings (coarse + κ) don't overshoot the collar; **they clamp the ZONE collar perfectly at k=2** (as they must: per-degree A = coarse + κ is the Sofá's own equality). The tomb's kill numbers compared a zone quantity against a CB quantity. **Correction filed:** the tombstone's negative knowledge survives as "never compare across conventions" (it is the same lesson as BAND-CONVENTION-MISMATCH, now with its second instance); its old interpretation ("the transfer ceilings are not the clamping ones") is WITHDRAWN. Corollary: the −191836 single-κ inconsistency was the same disease at k=3 — a convention-mixed diana — consistent with the probe's finding that nothing structural was broken.

## §3. The head H₃ — status (task b)

The Hammock final itself **names this object**: "the fine ignition of the pre-stable head H(f) (living entirely below f = 5, q-free, not touching the seal) remains a named write-up, not a structural gap" — that is precisely our five values (679, 210, 49, 7, 1 at f = 0..4; equivalently 1, 7, 49, 210, 679 at g = 4..8, onset at the self-mirror center σ/2). One object, three sightings (U1 table, probe deviations, Hammock's declaration). Forensic note, reported not forced: the k=3 census pre-stable deviations (true−law = 189, 48, 7, 0 at e = 6..9) share the decaying shape and the 7-tail with H₃ but are **not equal** (48 ≠ 49, 189 ≠ 210) — the direct Noether scan stays negative, as Locard instructed. The self-mirror route: the mirror alone cannot determine H (both tables are affine in the same A; the reflection symmetry of H is consumed by Theorem M, verified, not new information). **H's first-principles derivation = the level-2 kernel computation — the one genuinely open construction of S2b**, now cleanly isolated.

## §4. The naive ∀q extension of the transient: KILLED, with its polynomial (tasks a/c — honest no-close)

Attempting to derive the two-cubes law ∀q from the filed pieces (mirror + zone laws + Koszul + rama1-as-fixed-constants) yields, symbolically:
> dev(g,q) + H(8−g) = 35[g³+(g+1)³] + **35(q−9)·[6g² + 6g(q−8) + 2q² − 33q + 138]**.
The correction term vanishes identically at q = 9 (re-confirming the 9/9 law there) and is NONZERO for q > 9. Conclusion, with the knife:
- **The fixed-constant per-degree transient law does NOT extend ∀q.** ZETA's own label was exact: the U1 table is a **q=9 calibration**, never an ∀q per-degree filing. The per-degree transient law is genuinely q-dependent in its polynomial part; only its q=9 slice is the two-cubes + head.
- **NEW STREET BURIED: NAIVE-TRANSIENT-Q-EXTENSION** — killing polynomial 35(q−9)(6g²+6g(q−8)+2q²−33q+138). Whoever derives the true ∀q law must reproduce this as the difference between the q-law and the q=9 slice.
- Contrast, for calibration: at **k=2 the analogous holgura IS q-free** (symbolic: the q², q coefficients cancel — 35, 80, 125, 170 for all q), consistent with its pure-mirror collar. The q-dependence is a genuine k≥3 transient phenomenon — the ENMIENDA's fingerprint at per-degree resolution.
- Task (c) is therefore **resolved negatively-with-structure**: the transient is NOT q-free per degree; the correct ∀q object is the two-variable law dev(g,q), constrained by (i) the q=9 slice (two-cubes + head, 9/9), (ii) the killing polynomial's shape, (iii) the aggregate seal (Golpe-2 ∀q: the SUM is pinned ∀q), and (iv) the self-mirror symmetry ∀q. Four constraints, one named construction (the level-2 T-block) to close it.

## §5. Task (d) — the ∀k candidate, restated at its true grade

dev_k(g, q)|_{q=q_k*} = [C(2k+2,k+1)/2]·[g^k + (g+1)^k] − H_k(g − (k²−1)/2) at the self-mirror calibration point, with H₂ ≡ 0 (gated) and the box reading |[0,g)^k| + |[0,g]^k| (the two eigen-branches of the K(k,k) transposition). **Grade: candidate (2 anchors + structural reading).** k=4 falsification: 126·[g⁴+(g+1)⁴] against the level-2-mirrored k=4 data once Step 3 writes the level-r bands — plus the new constraint that the ∀q correction must specialize per §4's polynomial at k=3.

## §6. What S2b hands forward (exact residual, and it shrank again)
The residual is now ONE construction with four constraints: **the level-2 twin T-block on the C(2k+2,k+1)/2 bipartitions**, which must produce (a) the two-cubes q=9 slice, (b) the head H_k, (c) the q-dependence matching §4's killing polynomial, (d) the k-step via its 5A-type degree arithmetic. Everything else in the mission is closed or corrected: Tarea 0 theorem (§1), tomb corrected (§2), head isolated and thrice-sighted (§3), q-freeness question answered (negatively, with structure, §4), candidate restated (§5). The Dictionary makes Step 4 unambiguous: zone convention, with B_k^CB translated by the closed stolen-degrees formula.

## §7. Attack surface for Locard
(i) Re-derive Dict's hockey-stick window (Top law = Σ_{c≤q+k−1}) independently; check k=1 (the mantel: does 3·C(q−1+1,2)... the k=1 instance of Dict). (ii) The q=27, k=3 prediction 307125 — file it as a named diana. (iii) The Tanda-11 correction: verify Σcrude₂ = zone-collar₂ symbolically and re-word the tombstone (cemetery edit, careful: the lesson survives, the interpretation flips). (iv) §4's killing polynomial: re-run the symbolic computation with independent code; confirm the q=9 root and the (q−9) factorization. (v) The k=2 q-freeness contrast (holgura₂ symbolic cancellation) — three-line check. (vi) Probe the level-2 T-block's degree arithmetic for whether 2q² −33q+138's shape is predicted by the j=3 Koszul window shifts (forensic thread for the ∀q law).

**Anchors.** MISION_BISEL_STEP2b_CIERRE (Locard) · A′1/CB · TANDA11 · ZETA_RECURSION ("calibración q=9") · THE_HAMMOCK final (σ₃ heads; fine-ignition naming; H7) · Sofá Thm 4.3 · STEP1_BRIDGE · CENTRAL_DEFECT_LAW_ALLK_v1 · symbolic gates this session.

**MARCADOR: [S2b CIERRE — TAREA 0 TEOREMA COMPLETO (THE DICTIONARY): B_k^CB = Collar_zone − N·Σ_{j<k}C(q−k²+j,k) — la ventana del Top law es c ≤ q+k−1 por hockey-stick, roba los k grados espejo superiores del collar; el 15(q−4)² DESENMASCARADO: es ᾱ_q+ᾱ_{q+1}, nunca fue slack; gates k=2 simbólico ∀q + k=3 q=9 (robo=0, por eso nadie lo vio) + PREDICCIÓN falsificable q=27: 307125 · TUMBA TANDA-11 REINTERPRETADA con identidad simbólica: Σcrude₂ = Collar_zone(2,q) = 30q²−180q+300 EXACTO — los techos de transferencia CLAVAN el collar-zona en k=2; el "overshoot" era el diccionario; el −191836 = la misma enfermedad; lección superviviente = no comparar entre convenciones (2ª instancia de BAND-CONVENTION-MISMATCH) · CABEZA H₃ AISLADA Y TRES VECES AVISTADA (U1 + probe + el "fine ignition" que el propio Hammock nombra q-free bajo f=5); resonancia censo pre-estable (189,48,7,0) reportada como near-miss NO forzado · CALLE NUEVA ENTERRADA: NAIVE-TRANSIENT-Q-EXTENSION con polinomio asesino 35(q−9)(6g²+6g(q−8)+2q²−33q+138) — la ley per-degree del transitorio NO es q-libre (ZETA tenía razón: era calibración q=9); contraste: k=2 SÍ es q-libre simbólico; la q-dependencia es la firma de la ENMIENDA a resolución per-degree · RESIDUAL DE S2b = UNA construcción con CUATRO constraints (T-block nivel 2: slice q=9, cabeza, polinomio asesino, paso k) · Step 4 desambiguado: convención ZONA + traductor cerrado · SIN GRITO ∀k∀q — pero la Tarea 0 es avance tipo (b) con derivación y el diccionario cierra la ambigüedad que Locard señaló como carga]. — Bisel (Constructor, Fable), S2b cierre**
