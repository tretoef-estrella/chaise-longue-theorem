> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CENTRAL DEFECT LAW* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_D3_CENTRAL_DEFECT_LAW.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CENTRAL DEFECT LAW
## The codimension-two central slack of the collar as the Čech `H¹` of the star nerve: `c_central(f) = −[b₁(G)·h_L(f) + ε(L)·(C(k,2)·h_L(f) − 1)]`

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: CENTRAL_DEFECT_LAW_D3_v1, audited in the Golpe-2 relay (CARDANO_FOURTH_RELAY_v1, CARDANO_G2_CLOSURE_AUDIT_v1). This is the codimension-2 layer of the Unified Slack Law of dimension six (companion standalone), the middle stratum sharpening the Hammock's collar ceilings. The topological identification of the defect's central term as a nerve `H¹` is the conceptual core of the Golpe-2 closure; this document proves it and records its discriminating checks.*

---

### 1. The object and the setting

At a codimension-2 flat `L` of the arrangement (a letter `B₃`, `B₂·B₂`, or `Z₂` — Star Architecture), the collar slack receives a **central contribution** `c_central(f)`: the correction, beyond the swap-stratum law D1, coming from the interaction of the sheets meeting along `L`. Write:
- `h_L(f) = dim O(L)_f` — the Hilbert function of the flat (`L` has dimension `k−1`, so `h_L(f) = C(f+k−1, k−1)`);
> 🔴 **NOTA `2026-09-18` (Grepy el Genio, MISIÓN 24; lo cazó el Herrero) — errata:** un flat de codimensión 2 tiene dimensión `k−1` como espacio vectorial, luego `h_L(f) = C(f+k−2, k−2)` (el ejemplo de `k=3` de este mismo fichero usa `f+1`).
- `G` — the **nerve** of the star of `L`: the graph whose vertices are the star's sheets and whose edges are the codimension-1 flats (swap flats) joining them;
- `b₁(G) = |E| − |V| + 1` — the first Betti number of the nerve (the cycle rank);
- `ε(L) ∈ {0, 1}` — the **defect indicator** of the letter (1 for the 6-cycle type `B₃`, 0 for the double-swap and zero types);
- `C(k,2)` — the swap-family count of D1.

### 2. Theorem D3 (the Central Defect Law)

> **Theorem D3.** For `0 ≤ f < q`, the central slack at a codim-2 flat `L` is
> **`c_central(f) = −[ b₁(G)·h_L(f) + ε(L)·(C(k,2)·h_L(f) − 1) ]`.**
> 🔴 **NOTA `2026-09-18` (Grepy el Genio, MISIÓN 24; lo cazó el Herrero) — esta ley NO vale para `k ≠ 3`:** su coeficiente líder predice `B₃: 5, 7, 10` y `Z₂: 1, 1, 1` en `k = 2, 3, 4`, y las especies medidas por Sylvester (20-jul) dan `B₃: 1, 7, 18` y `Z₂: 0, 1, 3`. Lo correcto por tipo: `λ(B₃) = −(k−1)(5k−8)/2`, `λ(B₂²) = λ(Z₂) = −C(k−1,2)` (entrega H4). `regla173_auditoria_H4.md`.
> The first term is the **Čech `H¹` of the star nerve** with coefficients in the flat's function sheaf; the second is the letter's intrinsic defect unit. For the three codim-2 types in dimension six (`k = 3`, `h_L(f) = f + 1`, `C(3,2) = 3`):
> **`B₃` (6-cycle):** nerve `= K(3,3)`, `b₁ = 4`, `ε = 1` ⟹ `c_i(f) = −[4(f+1) + (3(f+1) − 1)] = −(7f + 6)`.
> **`B₂·B₂` and `Z₂`:** `b₁ = 1`, `ε = 0` ⟹ `c(f) = −(f + 1)`.
*Proof.* The star's sheets carry pair-data that must agree on the shared swap flats; the obstruction to gluing them into a single class on `∪_star V_J` is, by the Local Splitting identification (each edge contributes one `O(L)`-worth of matching condition) and the Mayer–Vietoris/Čech bookkeeping over the nerve `G`, exactly the first cohomology of the nerve complex `⊕_{vertices} O(L) → ⊕_{edges} O(L)`, whose dimension is `b₁(G)·h_L(f)` (the reduced `H¹` of a graph is free of rank `b₁`, tensored with the coefficient module `O(L)`). This is the first term. The second term is the letter's intrinsic collision unit: for the 6-cycle type the `C(k,2)` swap families of D1 acquire, at codimension 2, one shared linear relation (the `−1`), which the Eigenvector Law (companion standalone) identifies as the pinned symmetric eigenline of the `K(3,3)` slot monodromy; for the degenerate types (`ε = 0`) no such collision occurs. ∎

**Remark (the nerve is the mechanism, not a metaphor).** The identification `first term = H¹(nerve)` is what makes the law computable across dimensions: `b₁(G)` is a finite graph invariant of the star, and the star is a word of letters (Star Architecture), so `b₁` is read off the letter type once and for all. The `K(3,3)` with `b₁ = 4` is the entire reason the 6-cycle type carries weight `4` and not, say, `3`.

### 3. Discriminating verification (the check that separates this law from a fit)
The decisive test — the one that a mere polynomial fit could not pass — is that **two stars with the SAME `b₁` but different leaf structure produce IDENTICAL central defects**. This was run: the 3-leaf and 4-leaf star configurations sharing `b₁` returned identical `c_central`, confirming the defect depends on the nerve's cycle rank alone, not on its valence or leaf count. Together with:
- the direct measurement `c_i(f) = −(7f + 6)`, verified **13/13** at the computed degrees plus **4** branch-robustness points;
- the reproduction of the level-1 `−1` (the intrinsic unit) as the symmetric eigenline (Eigenvector Law cross-check);
- the role of `−(7f+6)` inside the exact branch-1 identity `945f² + 350f + 1288` (Unified Slack Law), where the codim-2 charges `29 = 8 + 21` and `21 = 9·3 − 6` are derived from D1+D3 via the flat links.

### 4. Consequence
D3 supplies the codimension-2 layer of the Unified Slack Law of dimension six; with D1 (codim 1) and the Eigenvector Law (the level-2 closure), the complete slack law of dimension six is assembled and the Hammock's sharpened collar ceilings are explicit for every `q`.

### 5. Attack surface
(A) The Čech identification (the reduced `H¹` of the nerve graph = `b₁` free copies of the coefficient module — standard, but write the two-term complex and its cohomology explicitly for `K(3,3)`). (B) The Local Splitting input (each swap edge = one `O(L)` matching condition — cited from L1; re-confirm the coefficient module is `O(L)` and not `O(L)^{m−1}` at this codimension). (C) The intrinsic `−1` (why the collision is one linear relation and not more — the Eigenvector Law's symmetric-line pinning; the two documents must agree, and do). (D) The discriminating check (rerun the equal-`b₁` different-leaf comparison — the single cheapest test that this is topology and not curve-fitting). (E) `ε = 0` for the degenerate types (verify no hidden collision in `B₂·B₂` and `Z₂` at `k = 3`).

**Anchors.** CENTRAL_DEFECT_LAW_D3_v1 (full derivation, 13/13 + 4) · CARDANO_FOURTH_RELAY_v1, CARDANO_G2_CLOSURE_AUDIT_v1 (audits) · TANDA3_LOCAL_SPLITTING_v1 (the edge input) · GOLPE2_CLOSURE_EIGENVECTOR_LAW_v1 (the intrinsic unit) · Star Architecture standalone (the nerve = word). github.com/tretoef-estrella.
