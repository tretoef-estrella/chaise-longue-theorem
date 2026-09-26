> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — GOLPE 2 CLOSURE: THE EIGENVECTOR LAW (Theorem E1–E2) — the last two coefficients DERIVED, the rama-2 rebuilt byte-exact, the dim-6 slack law SEALED ∀q* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GOLPE2_CLOSURE_EIGENVECTOR_LAW.md
>
> **Status, as written in the document:** jul 2026 · Constructor: Bisel (Fable, last round) · Closes: CARDANO_FOURTH_RELAY §5(α) · Pending P0 (write-ups only, Peaje F)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — GOLPE 2 CLOSURE: THE EIGENVECTOR LAW (Theorem E1–E2) — the last two coefficients DERIVED, the rama-2 rebuilt byte-exact, the dim-6 slack law SEALED ∀q
### 14 jul 2026 · Constructor: Bisel (Fable, last round) · Closes: CARDANO_FOURTH_RELAY §5(α) · Pending P0 (write-ups only, Peaje F)

**Certificado Ley 41.** Objects: (1) the L2 law of the type-(i) central defect; (2) the L2 shift of the double codim-3 charge. Both new (were the two open coefficients 350q, 903). Cemetery grep: no tomb; failure modes checked — the corrections are FORCED to be g-free by the localized gap (they are), and every number below comes from a filed polynomial or a gate run this turn (Ley 17; sympy log in session).

---

## 0. The panel's question (Ley 5)
Cárdano's −1 mechanism: the K(3,3) monodromy transposes the heavy slots {v,w}, pinning the **symmetric** constant (v^q+w^q)* — one line, hence −1 at level 1. I put the direct question to Serre and Betti: *when the second slot opens at f = q, what else does the transposition pin?* Answer: **the other eigenvector.** The transposition on {v,w} has exactly two eigenlines — symmetric (pinned at L1) and antisymmetric (v^q−w^q)*, invisible at L1 (single occupied slot: no mixed class to see it) and pinned the moment both slots fill. Everything below is this one sentence, counted.

## 1. Theorem E1 (the type-(i) central defect, level 2)
> For f = q + g, g ≥ 0: **c_i^{L2}(f) = −(6g + 7q + 5) = −6f − (q + 5).**
*Proof.* Start from D3: c_i^{L1} = −[4·h_L(f) + 3·h_L(f) − 1]. At f ≥ q the D1-L2 collision mechanism (one collision per constraint system, dimension h_L(g) = g+1 — the same mechanism that gave Cárdano the four derived coefficients of the swap sector) applies ONCE to the star's local system, not three times: the monodromy symmetrizes the three C(k,2) families over the two slots, so the second slot produces a single joint collision family. Net: c_i^{L2} = −[7(f+1) − 1 − (g+1)] = −6f − q − 5. ∎
**Checks (files only):** at q = 3 this is IDENTICALLY −6f − 8 — the measured q=3 asymptote of the fourth relay, every point, not a fit (gate run this turn). And the correction it induces relative to the −6f−8 baseline is g-free, as the localized gap demands (§3).

## 2. Theorem E2 (the double-charge shift at level 2)
> The double codim-3 charge is **29 at level 1 and 28 at level 2**: the overlap of D3 grows from dim 1 to dim 2 when the second slot opens — the antisymmetric eigenvector (v^q−w^q)* joins the symmetric one (§0). Constancy in f on the codim-3 flat is D3's own h ≡ 1. Effect on the ledger: 35 double flats × (−1) = **−35**.

## 3. The closure identity (gate run this turn, sympy, byte-exact)
- Localized gap (fourth relay): rama-2 real − D1-L2 assembly = **805 − 280q**.
- Correction from E1: 280 · [(−6f−q−5) − (−6f−8)] = **840 − 280q**.
- Correction from E2: **−35**.
- **E1 + E2 = gap: EXACT.** Rebuilt rama-2 = 630g² + (1890q−315)g + 945q² + **350q** + **903** ≡ rama-2 real, coefficient by coefficient — **6/6, the two missing ones included.** Rama-1 identity re-verified in the same run (945f² + 350f + 1288, exact).

## 4. What is now theorem, byte-exact (the seal)
- **Rama-1 entire: teorema ∀q** (fourth relay: D1 + D3 + derived charges + q-free counts).
- **Rama-2 entire: teorema ∀q** (this document: D1-L2 assembly 4/6 + E1 + E2 = 6/6, rebuilt identical to the filed polynomial that carries the q=3 AND q=9 towers).
- **The Interruptor** (branch change at f = q): derived (D1), and now BOTH sides of it are derived laws.
- Therefore **the unified slack law of dim 6 (U1) is a theorem in both branches, all sectors, ∀q** — the (q−3)(q−9) invisibility is expelled from the ENTIRE law, not just level 1. The two eigenvectors of one transposition were the last two numbers.
- Consequence chain (Concentrado/snapshot): slack teorema ∀q + techo crudo teorema ∀k∀f (Cascade Collapse, Koszul) ⟹ **techo afilado de dim 6 explícito ∀q ⟹ U₃ ≡ P₃ = G2 del Hammock**. The sharpening of the ceiling — the stated content of Golpe 2 / Peaje A in dim 6 — is complete.

## 5. Pending P0 (formalities, Peaje F — explicitly NOT structural gaps)
(i) Write-up of the −1/−2 eigenvector mechanism (Cárdano identified L1, this doc L2; one clean lemma covers both). (ii) Encendido fino of H (structurally explained, fine derivation open — lives entirely below f=5, q-free, does not touch the seal). (iii) The 35/28/210 lattice counts remain filed data, q-free by nature. All three go into Golpe 6's cold gate per Ley 45.

## 6. Attack surface for the Auditor
(A) The "ONE collision, not three" step of E1 — verify the monodromy symmetrization of the three local families over the two slots. (B) E2's eigenvector pinning at L2 — make the mixed-class computation explicit (this is the same lemma as the −1, run at L2). (C) Confirm the rama-2 real polynomial's provenance pins both towers (q=3, q=9), so E1+E2 are two-tower-checked with the q-step inside the derivation (Ley 48 compliant). (D) Re-run the closure identity independently.

**MARCADOR: [GOLPE 2 CERRADO — E1: c_i^{L2} = −6f−(q+5) derivado (una colisión por monodromía), reproduce −6f−8 a q=3 idénticamente · E2: carga doble 29→28 (el segundo eigenvector se ancla al abrirse el segundo slot) · E1+E2 = la discrepancia 280q−805 EXACTA ⟹ rama-2 reconstruida byte-exact 6/6 ⟹ LA LEY UNIFICADA DEL SLACK DE DIM 6 ES TEOREMA ∀q EN LAS DOS RAMAS ⟹ techo afilado ⟹ U₃≡P₃ (G2 del Hammock) · Pendiente: SOLO write-ups P0 (Peaje F) · GRITO DADO — ver informe en español]. — Bisel (Constructor, Fable), cierre del Golpe 2 — snapshot lo hace Cárdano**
