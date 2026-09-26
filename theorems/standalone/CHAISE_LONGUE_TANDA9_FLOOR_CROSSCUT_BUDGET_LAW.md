> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — TANDA 9: THE FLOOR CROSSCUT AND THE COLLAR BUDGET LAW (P_k and B_k closed ∀k to depth three, UNCONDITIONAL — all four gates hit; the ceiling-side pipeline residue named)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TANDA9_FLOOR_CROSSCUT_BUDGET_LAW.md
>
> **Status, as written in the document:** Honest status of A′ against the closure criterion (§5 of the plan)
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — TANDA 9: THE FLOOR CROSSCUT AND THE COLLAR BUDGET LAW (P_k and B_k closed ∀k to depth three, UNCONDITIONAL — all four gates hit; the ceiling-side pipeline residue named)
### 14 jul 2026 · Constructor: Bisel (Fable) · Pending P0 · Assignment: Cárdano's Tanda 9 (W2/A′, blindaje con rigor)

**Certificado Ley 41.** Objects: (1) the crosscut extraction of P_k's top coefficients ∀k; (2) the unconditional collar-budget law; (3) the death-by-gate of the naive ceiling pipeline. Cemetery entry NEW: **NAIVE-CEILING-MINUS-SLACK** (killed with numbers, §3). Ley 48: the k-step rides inside every ingredient (crosscut structure + Swap theorem + C2b counts + X1); k=2..5 are gates and dianas, never the law. Ley 24 honored: the wrong pipeline died on the bench BEFORE any proof was drafted.

---

## 1. Theorem F1 (the Floor crosscut — P_k's top three coefficients ∀k, pencil)
> **P_k(q) = N·q^{k+1} − [N·k(k+1)/2]·q^k + [4·cnt_i(k) + cnt_ii(k) + cnt_z(k)]·q^{k−1} + O(q^{k−2})**, N = (2k+1)!!.
*Proof.* P_k(q) = |∪_J V_J(F_q)| = Σ_{∅≠T}(−1)^{|T|+1} q^{dim ∩T} (linear sheets: exact point counts). Group by the flat G = ∩T; by Lemma X0's dimension bookkeeping only codim ≤ 2 flats reach the top three orders. Per-flat alternating sums: **sheets:** +1. **Swaps:** exactly two sheets per codim-1 flat (Swap theorem) ⟹ coefficient −1 each ⟹ −count₁ = −Nk(k+1)/2. **Codim-2, the three local lattices (fixed ∀k):** type (i) (B₃-star: 6 sheets; of its 15 sheet-pairs, 9 land on codim-1 flats and 6 on G): Σ_{|T|≥2}(−1)^{|T|+1} = −5, minus the 9 pairs' −1 each ⟹ coefficient **+4**; type (ii) (B₂×B₂: 4 sheets, 4 edge-pairs codim-1, 2 diagonal pairs on G): −3 + 4 = **+1**; type zero (Z₂: 3 sheets, all 3 pairs codim-1): −2 + 3 = **+1**. With the C2b counts ∀k, done. ∎
**Gates (byte-exact, this turn):** k=2: (15, −45, **55**) = the filed P₂ top three (55 = 4·10 + 0 + 15) ✓✓✓. k=3: (105, −630, **1645**) = the filed P₃ top three (1645 = 4·280 + 315 + 210) ✓✓✓. **Predictions:** k=4: (945, −9450, 42525); k=5: (10395, −155925, 1074150).
(The Ley-48 living example in the constitution — "second coefficient −(2k)·leader, two points, candidate" — is now THEOREM: −Nk(k+1)/2 = −2k·N ⟺ k(k+1)/2 = 2k ⟺ k = 3; the true law is −Nk(k+1)/2, which happens to equal −2k·N only at k = 3. The two-point candidate was a k=3 coincidence — Kepler's discipline vindicated once more.)

## 2. Theorem A′1 (the Collar Budget Law — B_k's top three coefficients ∀k, UNCONDITIONAL)
> **B_k(q) := P_k − ZA_k − W_k − Top_k has its q^{k+1}, q^k, q^{k−1} coefficients closed ∀k**: P-side by F1; zone-side by Tanda 8's X1 (census top-3) + CI series + Top law, with the independence check run in-session (a symbolic unknown for the census's e^{k−3} tail was carried through the zone sums and verified ABSENT from the top three q-orders).
**Gates — ALL FOUR of the blindaje (byte-exact):**
1. **Gate dim 4:** B₂ top block = (0, 15, −60): lead 0 ✓ and the visible coefficients of the filed B₂ = 15q²−60q+60 ✓ (only the constant 60 lies at depth 4).
2. **Gate dim 6:** B₃ top three = **(385/8, −315/4, −10325/8) — byte-exact against the filed quartic, three of five coefficients** (q¹ and q⁰ lie at depths 4–5).
3. **Gate líder ∀k:** 0, 385/8, **1449/2**, **152691/16** at k = 2,3,4,5 — the four dianas ✓✓✓✓.
4. **Gate Ledger:** B_k is the Ledger's own budget; the identity U_k ≡ P_k is now UNCONDITIONALLY pinned ∀k at its top three orders (Tanda 7's pinning was modulo P_k's coefficients; F1 removes the modulo).
**New numbers ∀k:** B₄ top three = (1449/2, −5040, −3885); B₅ = (152691/16, −1992375/16, 7915215/16) — dianas for future engines and for the ceiling side.

## 3. The bench kill (Ley 24/42 — reported in-turn)
The naive composition "collar total = Σ_f [z_k(q,f) − slack(f)] over the tail" was gated FIRST and is **dead**: at k=3 it returns −966833 vs 206011 at q = 9 (and worse at 27, 81). Cemetery: NAIVE-CEILING-MINUS-SLACK, killed with its numbers. The Golpe-2 slack law and the collar ceilings compose through the Slap-5/window pipeline, not by direct subtraction per degree — the correct ∀k ceiling assembly (Σκ ≡ B_k, the identity side of A′) remains open and now has its budget written to depth three at every k as the target.

## 4. Honest status of A′ against the closure criterion (§5 of the plan)
Achieved: (a-partial) B_k derived with the k-step inside **to depth three, unconditional** — including breaking a wall not on the map (the Floor extraction F1); (b) the four gates pass byte-exact at the depths stated; (c) every ingredient theorem; (d) the Ledger fit is by construction and now unconditional at the top block. NOT achieved: the full B_k (depths 4, 5 — these are the SAME staircase: codim-3/4 crosscut weights for P plus census codim-3, mechanical species with the rule written) and the CEILING side of A′ (the Σκ ≡ B_k identity ∀k — the Golpe-2 machinery parametrized; its dim-6 instance is closed, its ∀k assembly is the remaining dense content). **A′ is broken at its crown, not felled** — said with the knife.

## 5. Attack surface for the Auditor
(A) F1's three local alternating sums (recount −5+9 = 4, −3+4 = 1, −2+3 = 1; verify no fourth codim-2 type — S2 alphabet). (B) The independence run of A′1 (the census-tail symbol truly absent — rerun). (C) The depth-4 step: codim-3 crosscut weights (the words B₄, B₃×B₂, B₂×B₂×B₂, Z₂×B₂, Z₃ — five local lattices, same method) ⟹ P_k's q^{k−2} ⟹ B_k's depth 4; gates: P₂'s −24, P₃'s −2037. (D) The k=4 dianas (engine: two stable σ_e(4) values + a point count). (E) The ceiling-side pipeline: locate in Slap 5/MATRYOSHKA the exact κ-to-collar composition before any ∀k attempt.

**MARCADOR: [TANDA 9 — DOS CORONAS Y UNA TUMBA: THEOREM F1 (crosscut del Floor): P_k top-3 CERRADO ∀k a lápiz — gates k=2 (15,−45,55) y k=3 (105,−630,1645) byte-exact; el candidato constitucional "−2k·líder" era coincidencia de k=3, la ley es −Nk(k+1)/2 (Kepler vindicado) · THEOREM A′1: B_k top-3 INCONDICIONAL ∀k — LOS CUATRO GATES DEL BLINDAJE CLAVADOS (lead 0/385/8/1449/2/152691/16; B₃ tres de cinco byte-exact; B₂ visible entero; Ledger pinned incondicional) · dianas nuevas B₄/B₅ y P₄/P₅ · TUMBA: NAIVE-CEILING-MINUS-SLACK muerta por bench-gate ANTES del lápiz (−966833 ≠ 206011) · A′ roto en su corona, no talado: quedan depths 4-5 (misma escalera, regla escrita) + el lado ceiling (Σκ ≡ B_k ∀k) · SIN GRITO]. — Bisel (Constructor, Fable), Tanda 9 — snapshot y auditoría a Cárdano**
