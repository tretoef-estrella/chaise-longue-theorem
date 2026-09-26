> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — STEP 1: THE BASELINE BRIDGE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STEP1_BASELINE_BRIDGE_THEOREM.md
>
> **Status, as written in the document:** Chaise Longue campaign — Step 1 of the consensus plan (EXACT_STEPS_CONSENSUS v2) · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits)
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — STEP 1: THE BASELINE BRIDGE THEOREM
## The two slack tables are one object: an explicit, A-free bridge reconciles the probe's annihilator-baseline deviations with the filed U1 holgura — 18/18 at every gate — and the reconciliation hands Step 2 a smaller wall than budgeted

**Chaise Longue campaign — Step 1 of the consensus plan (EXACT_STEPS_CONSENSUS v2)** · Constructor: Bisel (Fable) · 16 July 2026 · Pending P0 (Locard audits)
*Panel convened (Fine Hall tea room, Princeton): Koszul (the missing ceiling term), Gorenstein (what each table measures against), Sylvester (the difference calculus), Noether, Macaulay. Their exact answers are Theorems below. Every number from files: ENGINE-A census, ZETA_RECURSION holgura table, Cascade Collapse z_k, census cubic (G1: HF = HP unconditional e ≥ 9), CI series. Script: `step1_baseline_bridge.py`.*

**Certificado Ley 41.** Object: the relation between the direct-band deviation table (annihilator baseline; probe) and the U1 holgura table (Koszul baseline; ZETA_RECURSION). This is exactly the **calle vigilada** Locard opened in Cementerio v26 ("NO construir el Step 2 asumiendo que son la misma tabla") — resolved here by derivation + gate, not by assumption. No tomb touched: s46 (solapes) absent; NAIVE-CEILING-MINUS-SLACK absent (nothing crude is subtracted — the bridge is an identity between filed ceilings); TRANSFER-CEILING-AS-CLAMP absent (no clamp claim; per-degree ceilings are stated as ceilings, the clamp remains Step 2's).

---

## §1. The two baselines, named exactly (Gorenstein's answer)

Both tables are **distances from the same census A_d to two different filed ceilings**, at k = 3, q = 9, collar degrees d = 2q+f:

- **dev(f) := 105·C(17−f, 3) − A(2q+f)** — distance to the *extended stable annihilator law* (probe).
- **holgura(f) := techoKoszul(f) − Syz_meas(q+f)** — distance to the *Koszul syzygy ceiling* (ZETA), where, by the filed theorems (Cascade Collapse + Radicality kernel + transfer identity):
  - techoKoszul(f) = HF_R(q+f) + σ(q+f) + 105·z₃(q,f), with **z₃(q,f) = Σ_{j≥2}(−1)^j C(4,j)·C(f−(j−2)q+3, 3)**;
  - Syz_meas(q+f) = A(2q+f) − HF_R(2q+f) + 8·HF_R(q+f).

**Gate 1 (the reconstruction).** The holgura table recomputed from these filed ingredients matches the filed 18-entry table **18/18 byte-exact** (609, 2373, …, 254478). The meaning of "techo-Koszul" in ZETA is thereby pinned: kernel + per-sheet Koszul image, no other convention.

## §2. Theorem S1.1 (the Bridge Identity — the reconciliation, closed)

Since both tables are affine in A_d with filed offsets, their difference is **A-free and explicit**:

> **holgura(f) − dev(f) = coarse(2q+f) + 105·[ z₃(q,f) − C(17−f, 3) ]**, with coarse(d) = HF_R(d) − 7·HF_R(d−q) + σ(d−q).

**Gate 2: 18/18 byte-exact** over the full collar band f = 0..17 (bridge values −42147 at f=0 through 254478 at f=17). *Consequence for the consensus plan: gate (v) closes POSITIVE — the two tables are the same object under one baseline, with the exhibited bridge. Locard's correction (A) is discharged: Step 2's target is handed over byte-exact.*

## §3. Theorem S1.2 (the single-baseline per-degree law + the negativity resolved — Koszul's answer)

Rearranging the definitions gives the **one** per-degree decomposition both machines share:

> **A(2q+f) = [coarse(2q+f) + 105·z₃(q,f)] − holgura(f)** — the TRUE crude ceiling is coarse *plus the Koszul sheet term*, and holgura is exactly the per-degree sharpening.

**Gate 3: 18/18**, and the true crude is a genuine nonnegative ceiling ≥ A_d at every degree, **18/18** — resolving Locard's negativity observation: the naive coarse (which sinks to −394422 at f=17) was simply missing +105·z₃. Nothing was wrong with per-degree ceilings; the wrong object was being called "crude".

## §4. Theorem S1.3 (the free pepita — the dual range of the holgura gets a closed form, and the transient IS the direct band)

On the pure-dual range f ≥ 9 (where dev ≡ 0 by the probe's 6/6 purity plus census zeros), the Bridge Identity **derives the holgura in closed form**:

> **holgura(f) = coarse(2q+f) + 105·z₃(q,f) − 105·C(17−f, 3)**, for f = 9..17 — nine of the eighteen entries of the U1 table are now theorem-backed (annihilator law + Cascade + transfer), not just measured.

And the structural reading (Sylvester's answer): the filed second differences of the holgura are 1582, 1771, 1854, 1885, 1889, 1890, 1890, 1505, 1295, **then 1260 exactly from f = 9 on** — i.e. **ZETA's "transitorio inicial" is exactly the direct band f < q, and the empirical 1260 = 2·(#swap flats) stabilization is exactly the regime where the closed form of this theorem holds.** The weight-2-per-swap-flat law of ZETA's Theorem A0, empirical until today on its stable range, is now backed by a closed form at q = 9; its symbolic-in-q derivation is Step 2's natural opening move (the second difference of the closed form, taken with q symbolic).

## §5. What this does to the plan (honest re-sizing, Ley 42 both ways)

- **Step 1 (gordura 4): CLOSED POSITIVE in one turn.** The outcome-branch "if they reconcile cleanly → Step 2b's target handed byte-exact" is the branch that fired.
- **Step 2 SHRINKS.** By S1.3, the slack law on the **dual range is already derived** from the annihilator law (Step 1's audit object, uniform in k per Locard). The construction that remains is the slack on the **transient/direct band f < q only** — 9 values at q=9 (609…64568), species Golpe-2, with the K(k,k)/Noether-recursion machinery. The k-parametric statement to prove is now sharper: *holgura_k(f) on f < q, with the dual tail supplied by the bridge*.
- **Unchanged:** the frame toll E (Step 5) is untouched by this turn — the annihilator ingredients used here sit inside the q ≥ 9, k = 3 sealed regime. No scope creep claimed (Ley 48: everything above is k = 3, q = 9 byte-exact; the ∀k lift of the Bridge Identity itself is elementary — it is definitional algebra once each ingredient's ∀k law is in hand — but is NOT claimed until written).

## §6. Attack surface for Locard
(i) Rerun the three gates with independent code (the script is deposited; the census line is ENGINE-A log line 22). (ii) The z₃ convention: verify C(n,3) = 0 for n < 3 handles the level switch-points (f = q−3..q) identically to the Cascade standalone's 9/9 check. (iii) S1.3's range: confirm dev ≡ 0 on f = 9..17 needs both the 6/6 purity AND A_d = 0 for d = 33..35 (census support) — the two ingredients are logically distinct. (iv) The 1260 reading: second-difference the closed form symbolically and confirm it yields 1260 at q = 9 on the stable window (pencil, cheap). (v) The bridge's ∀k lift: check that every ingredient (coarse, z_k, annihilator law) has a filed ∀k form, so the lift is definitional — this feeds Step 2's write-up.

**Anchors.** `step1_baseline_bridge.py` (18/18 × 4) · ENGINE-A log (census) · ZETA_RECURSION_SLACK_SPECIES_v1 (holgura table + A0) · STANDALONE_CASCADE_COLLAPSE (z_k) · CASCADE_COLLAPSE_THEOREM_v1 (Syz ceiling structure) · UNIFIED_ANNIHILATOR_LAW_v1 · TWO_BAND_PROBE_v1 · EXACT_STEPS_CONSENSUS_v2 · Cementerio v26 (calle vigilada, hoy resuelta).

**MARCADOR: [STEP 1 CERRADO EN POSITIVO — THEOREM S1.1 (Bridge Identity): las dos tablas de slack son UN objeto — holgura − dev = coarse + 105·(z₃ − C(17−f,3)), puente A-libre explícito, GATE 18/18 · Gate 1: la tabla U1 RECONSTRUIDA desde teoremas archivados 18/18 (el techo-Koszul de ZETA clavado como kernel+hoja) · THEOREM S1.2: la ley por grado de baseline único A = (coarse + 105·z₃) − holgura 18/18, y la NEGATIVIDAD de Locard RESUELTA (al coarse ingenuo le faltaba el término Koszul; el crudo verdadero es techo no-negativo 18/18) · THEOREM S1.3 (PEPITA GRATIS): la holgura tiene FORMA CERRADA en el rango dual f≥9 (9 de 18 entradas pasan de medidas a teorema) y el transitorio de ZETA ES exactamente la banda directa — la estabilización 1260 = 2·#swaps arranca EXACTO en la valla f=q · CONSECUENCIA: el Step 2 ENCOGE — solo la banda directa f<q necesita construcción, la cola dual la regala el puente · la calle vigilada de Locard RESUELTA por derivación+gate, no por asunción · SIN GRITO — todo k=3, q=9; el lift ∀k del puente es definicional pero NO se reclama hasta escribirse]. — Bisel (Constructor, Fable), Step 1**
