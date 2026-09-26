> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-17
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE MIRROR THEOREM, THE THREE PENCILS AUDITED, AND THE ENGINE UNLOCKED: THE PER-SHEET PROFILE IS NOW A THREE-LAW OBJECT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MIRROR_THEOREM_ENGINE_UNLOCKED_SNAPSHOT.md
>
> **Status, as written in the document:** Locard's turn (Architect's challenge "collejas cuelleriles"): (1) THE MIRROR — Gorenstein duality of the apolar quotient forces rank Cat_d = rank Cat_{σ−d}; verified 3/3 on EXISTING data (k=3 q=9: the onset 12/28/56 and the window top 266/328/384 are exact mir…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v144`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE MIRROR THEOREM, THE THREE PENCILS AUDITED, AND THE ENGINE UNLOCKED: THE PER-SHEET PROFILE IS NOW A THREE-LAW OBJECT
## Locard's turn (Architect's challenge "collejas cuelleriles"): (1) THE MIRROR — Gorenstein duality of the apolar quotient forces rank Cat_d = rank Cat_{σ−d}; verified 3/3 on EXISTING data (k=3 q=9: the onset 12/28/56 and the window top 266/328/384 are exact mirror pairs) AND 3/3 by A-PRIORI PREDICTION on never-measured degrees (k=3 q=27: ann(66,67,68) predicted 5606/5488/5346 before touching a matrix — measured identical). The per-sheet profile is now: onset law (below center) + central defect (q-invariant, the self-pairing price) + MIRROR (theorem). (2) The three pencils audited: shift gate stands, y-derivation arithmetic exact ∀k, Top_k dimensional check passes, k=4 frame consistent. (3) THE ENGINE UNLOCKED: v2's lock reproduced byte-exact (determinism works); root cause caught — NOT small-field: the x-factor interpretation of the minimal polynomial; two-line structural fix (read the top Berlekamp-Massey connection coefficient); with the fix BOTH calibrations pass through the Wiedemann route → **v3 delivered, GREEN for the Mac.** (4) The size law: k=4-II central defect measured (−1,−4,−9,−14) vs k=3 (−2,−8,−22,−48,−92) — two honest profiles, NO common law offered.

**Chaise Longue campaign — Locard construction turn (explicit challenge, Ley 3/15)** · 17 July 2026 · Pending P0 · Zero fits.

---

## §1. THE MIRROR THEOREM (the free half of every profile)

> **Theorem MIRROR (per-sheet, ∀k ∀q — Gorenstein duality).** The coupling algebra A(P*) is an Artinian Gorenstein quotient (apolar algebra of the Moore determinant) with socle degree σ = (k+1)(q−1) − k(k+1). Macaulay duality forces **rank Cat_d = rank Cat_{σ−d}**, hence
> **ann(σ−d) = HF_B(σ−d) − HF_B(d) + ann(d)** — the upper half of the per-sheet profile is the exact reflection of the lower half.
**Gates.** (i) k=3, q=9 (σ=20), existing data: pairs (6,14), (7,13), (8,12) → 3/3 (the onset values and the head-window top values were mirror pairs all along). (ii) k=3, q=27 (σ=92), **a-priori**: predicted ann(66)=5606, ann(67)=5488, ann(68)=5346 from duality alone, then measured by the determinant route: **3/3 identical.** (iii) The center σ/2 is SELF-dual — which is WHY the central defect lives exactly there: it is the price of self-pairing (this closes the loop with the break-location law g_break = σ/2 − h₀_onset).

**Consequence (the turn's structural yield):** the complete per-sheet profile at every (k, q) is determined by **three laws + one invariant**: the onset Newton law (below center; measured 3 dims), the central defect (q-invariant profile on the window; measured 10/10 at k=3), and the MIRROR (theorem) — with the freeness line now needed only on the LOWER half (the mirror gives the upper half for free): **the P0 target is cut in half.**

## §2. The three pencils — audit verdicts
**Pencil 1 (shift):** gate 5/5 stands (my measured δ); the cut at g_break correctly placed by the center law. The freeness line: by L1 (closed), freeness at fixed offset is a FINITE q-independent statement, measured at every offset reached; the honest caveat (said with the knife): offsets beyond those measured, for large q, still ride on the polynomial structure — the freeness line remains the P0 sentence, now needed only below σ/2 (MIRROR halves it). **Pencil 2 (y-derivation):** arithmetic exact ∀k (2·C(k+1,2) = k(k+1), checked k=3..6); 12/20/30 reproduced as consequence ✓; same freeness line — plausibly ONE lemma for both, as Bisel says. **Pencil 3 (Ledger ∀k):** Top_k = (2k+1)!!·C(q−k², k+1) dimensional check ✓ (945 = 9!! at k=4); triple-gate previously verified 15/15; k=4 frame (collar onset at h₀ = q−k = 23) consistent with my measured strata. Grades as declared by Bisel — no over-claim found.

## §3. The engine — lock reproduced, root cause caught, FIXED, unlocked
Reproduced v2's lock byte-exact (same 3140 at h₀=46 — the determinism condition works). **Root cause (audit):** all three projections AGREED (L = 1144); the failure was the interpretation heuristic "singular ⟹ rank = L−1". When the random projections do not see ker(B), the minimal polynomial lacks its x-factor and L = rank, not rank+1 — subtracting 1 produced the undershoot. **The structural fix (not F₈₁):** x | minpoly ⟺ the top Berlekamp–Massey connection coefficient C[L] vanishes; subtract 1 exactly then, per projection, combine by max. Two lines. **Result: BOTH calibrations pass byte-exact through the Wiedemann route** (q=9: 146…384 5/5; q=27: 3134…4236 5/5). Delivered as **`CHAISE_LONGUE_WIEDEMANN_CENTER_ENGINE_v3.cpp`** (new filename, Ley 38), fix documented in header. **GREEN for the Mac**: `g++ -O2 -std=c++17 -o chaise_engine_v3 CHAISE_LONGUE_WIEDEMANN_CENTER_ENGINE_v3.cpp && ./chaise_engine_v3 calib` — then `./chaise_engine_v3 q81` for the q=81 window (calibration re-runs first by construction; single thread; Mac patience).

## §4. The size law — two honest profiles, no fit
k=4 band-II central defect measured this session: **−1, −4, −9, −14** (g = 5..8, q=9). Against k=3's −2, −8, −22, −48, −92: no common law visible at two profiles. Filed as the open cross-k object it is — the mechanism (self-pairing structure at the center per (k, band)) is the route, not a fit.

## §5. What stands, exactly (the knife)
CLOSED-or-theorem this turn: the MIRROR (theorem + 6 gates, 3 a-priori) · the engine v3 (unlocked, doubly calibrated) · the freeness target HALVED. STILL OPEN (named, not hidden): the freeness line (ONE P0 sentence, lower half only) · the head (Johnson assault, gate q=9 → 1,7,49,210,679/946 — the Paso 2 resident) · diana-III + 6º punto k=5 + q=81 + k=4 center (ALL now one Mac run away on v3) · the size law · P0 cold gate (the Architect's). **"Todo cerrado definitivamente" would be smoke (Ley 13) — but the table has never been this closed, and every remaining item has a name, a gate, and a vehicle.**

---

# CHAISE LONGUE — HANDOFF SNAPSHOT LIVE · v144 (embedded)
### SE LEE ANTES QUE NADA (Ley 10). Snapshot de turno (LOCARD, reto "collejas"). Cadena: …→v142 (Locard: el centro + peinado v32)→v143 (Bisel: 3 lápices + motor v2 con lock)→**v144 (este, LOCARD: MIRROR + motor DESBLOQUEADO v3 + tamaño medido)**.

**★ PARA RAFA — SUBIR:** `CHAISE_LONGUE_WIEDEMANN_CENTER_ENGINE_v3.cpp` (el motor VERDE — v2 queda superseded) · este doc (`CHAISE_LONGUE_MIRROR_THEOREM...`) · `CHAISE_LONGUE_LOCARD_MIRROR_APRIORI_GATE.py` · `CHAISE_LONGUE_LOCARD_SIZE_LAW_K4II.py`. **Y EN TU MAC:** compilar v3 y correr `calib` (debe clavar 10/10); cuando quieras, `q81` — decide q=81 con certificado.

**TABLA EXACTA:** 1 ✓ · 2 mod {cabeza} · 3 mod {línea-libertad (mitad inferior)} · 4 triple-gateado + esqueleto ∀k · 5 teorema-módulo-{línea-libertad, diana-III} · 6 pendiente. **El espejo REDUJO el P0 a la mitad; el motor v3 puso las 4 dianas grandes a UN run de Mac.**

**VERSIONES:** huevos v32 (peinado v142) · concentrado v11 · REFEREE_VERIFIER v2 (v3 pendiente: añadir MIRROR + esqueleto ∀k) · snapshot **v144** · motor **v3 VERDE**.

**MISIÓN BISEL (embebida):** (1) LA LÍNEA DE LIBERTAD — un lema, mitad inferior solamente (el espejo te regala la de arriba): escríbela o rómpela; cierra Pasos 3 y 5 juntos. (2) LA CABEZA (asalto Johnson, gate q=9 → 1,7,49,210,679/946; los per-sheet de la ventana están ya completos por las tres leyes — el nervio es lo único que falta encima). (3) REFEREE_VERIFIER v3 (añade MIRROR + Ledger-∀k + frame k=4). NO toques el motor — está verde; los runs son del Mac. Ley 48/41/42 como siempre; snapshot al terminar.

**PENDIENTE-POR-PEINAR (append-only):** [v1-v142] ✓ peinados v1-v32 · [17jul·PENCILS v143] → PENDIENTE · [17jul·MIRROR v144·LOCARD] **MIRROR theorem (6 gates, 3 a-priori: 5606/5488/5346) · lápices auditados sin over-claim · motor v2 lock reproducido + causa (factor-x) + FIX + v3 VERDE doblemente calibrado · tamaño k=4-II medido (−1,−4,−9,−14) sin fit · P0 de libertad REDUCIDO a media caja.** → PENDIENTE [próximo peinado]

**LEYES DEL MINUTO:** Ley 26 (el lock de Bisel leído como dato: las 3 proyecciones coincidían — la avería no era ruido de cuerpo pequeño sino interpretación, y la cabecera del minpoly la delataba) · Ley 24/38 (el fix de 2 líneas testeado con la calibración doble ANTES de entregar; filename v3 nuevo) · Ley 51 (el espejo entró con 3 gates a priori en grados vírgenes — la forma más fuerte) · Ley 42 (el tamaño sin ley: dicho; "todo cerrado" NO cantado: la cabeza, la libertad y las dianas tienen nombre y vehículo) · Ley 20 (los lápices de Bisel + el espejo del auditor + el Mac del Architect: el perfil entero es de los tres).

— Locard (Auditor forense + Constructor por reto, Fable) · 17 jul 2026
