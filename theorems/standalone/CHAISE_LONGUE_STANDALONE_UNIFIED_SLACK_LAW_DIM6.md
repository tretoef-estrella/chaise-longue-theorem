> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE UNIFIED SLACK LAW OF DIMENSION SIX* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_UNIFIED_SLACK_LAW_DIM6.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE UNIFIED SLACK LAW OF DIMENSION SIX
## The complete collar slack of the Fermat sixfolds, both branches, every tower level: assembling the Gluing Law, the Central Defect Law, and the Eigenvector Law into the sharpened ceilings that clamp the Hammock's collar

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: the Golpe-2 closure chain — MATRYOSHKA_QUADRATUM_v6 (D1), CENTRAL_DEFECT_LAW_D3_v1 (D3), GOLPE2_CLOSURE_EIGENVECTOR_LAW_v1 (E1/E2), assembled and ratified in CARDANO_G2_CLOSURE_AUDIT_v1 (four byte-exact checks; the branch-2 polynomial pins both tower rungs). This is the capstone of the dimension-six sharp-ceiling program — the object the Hammock Theorem's ceiling identity `Σ(sharp) ≡ B₃(q)` consumes. It cites its three component standalones (D1, D3, Eigenvector) and assembles them; it introduces no new derivation.*

---

### 1. The role of the object

The Hammock reduces (Ledger, companion) the tower statement `A₃(q) = P₃(q) ∀q` to the ceiling identity `Σ(sharp collar ceilings) ≡ B₃(q)`. The sharp ceilings are the crude Koszul ceilings (Cascade Collapse, companion) MINUS the **slack** — and the entire content of "Golpe 2", the campaign's hardest dimension-six fight, was to derive that slack in closed form, for every `q`, across the branch structure of the collar. The result is a single law in two branches.

### 2. The two branches

The collar of dimension six has cofactor degrees `q + f`. The heavy-slot count changes at `f = q` (D1's Interruptor): **branch 1** is `f < q` (one heavy slot), **branch 2** is `f ≥ q` (two heavy slots, `g := f − q`).

> **Theorem (Unified Slack Law of dimension six).**
> **Branch 1 (`f < q`):** `slack(f) = 945f² + 350f + 1288 − H(f)`, where `H(f) = 1603 − charges(f)` is the pre-stable head, saturating (`H = 0`) at `f = 5`; head values `H(0..5) = 679, 210, 49, 7, 1, 0`.
> **Branch 2 (`f ≥ q`, `g = f − q`):** `slack(f) = 630g² + (1890q − 315)g + 945q² + 350q + 903`.

### 3. The assembly (each coefficient to its component law)

**Branch 1 — the exact identity.** The three strata sum by convolution (not raw subtraction — the buried tombstone):
- **Codim-1 (swaps):** D1 gives `630 · 3 · C(f+2, 2) = 945f² + ...` — the leading `945`.
- **Codim-2 (central):** D3 gives the three type charges; the derived codim-3 charges via the flat links are `29 = 8 + 21` (double flat, `ε=1` type) and `21 = 9·3 − 6` and `0`, assembling the `350f` and the constant `1288`.
- **Head:** `H(f) = 1603 − charges(f)`, the pre-stable correction, `1603 = 35·29 + 28·21 + 210·0` (the codim-3 charge total), saturating at `f = 5`.
The identity `945f² + 350f + 1288 − H(f)` is verified at `f = 0..8` (source log).

**Branch 2 — the closure (the two coefficients that resisted).** Assembling branch 2 with the type-(i) sector carried at its `q = 3` shadow `−6f − 8` leaves a localized gap `805 − 280q` in the `q` and constant coefficients. The **Eigenvector Law** closes it exactly:
- **E1:** the type-(i) level-2 defect is `c_i^{L2}(f) = −6f − (q+5)`, whose correction over the `−6f−8` baseline is `280·(3 − q) = 840 − 280q`;
- **E2:** the double codim-3 charge drops `29 → 28` (the antisymmetric eigenline joining the symmetric), contributing `−35`;
- **total `805 − 280q`** — closing branch 2 to `630g² + (1890q−315)g + 945q² + 350q + 903`, **all six coefficients derived** (including the `350q` and `903` that the pre-Eigenvector assembly could not reach).

### 4. Verification record (the four ratified checks)
| Check | Result |
|---|---|
| Branch 1 identity `945f²+350f+1288−H(f)` | `f = 0..8` byte-exact ✓ |
| E1 reproduces measured `−6f−8` at `q=3` | identity, 5/5 ✓ |
| E1 + E2 = localized gap `805 − 280q` | exact (symbolic) ✓ |
| Branch 2 pins both tower rungs | `A₃(3)=1107`, `A₃(9)=345465` ✓ |
The assembly passed the Golpe-2 cold audit; the auditor's own false-crack pursuit (a double-counting suspicion) closed at zero. The one declared scope reserve — the type-(i) level-2 law at `q = 9` validated indirectly through the branch-2 polynomial rather than by direct star measurement — is stated verbatim in the Eigenvector Law standalone §7 and is the cheapest independent test on offer.

### 5. Consequence (into the Hammock)
Crude ceiling (Cascade Collapse, theorem ∀k∀f) minus slack (this law, both branches, ∀q) = the sharpened collar ceilings of dimension six, explicit for every `q`; their sum equals `B₃(q)` (the Ledger's collar budget), closing the ceiling identity and hence the `A₃ ≤ P₃` jaw of the Hammock's sandwich for `q ≥ 9`. This is the sense in which "Golpe 2 cerrado" is the load-bearing sharpening of the Hammock Theorem.

### 6. Attack surface
(A) The convolution composition (branch 1's three strata sum by convolution — verify the stratum-to-slack bookkeeping against the buried per-degree-subtraction tombstone, `−966833 ≠ 206011`, to see why the surviving composition is the right one). (B) The codim-3 charge derivations `29, 21, 0` from D1+D3 via flat links (the source's link computation). (C) The head saturation at `f = 5` (why `1603` and why `f = 5` — the charge total and the Swap-Ramp scale). (D) The Eigenvector closure (deferred to that standalone's attack surface; the mechanism lemmas are the target). (E) The scope reserve (measure `c_i^{L2}` directly at `q = 9`).

**Anchors.** MATRYOSHKA_QUADRATUM_v6 (D1) · CENTRAL_DEFECT_LAW_D3_v1 (D3) · GOLPE2_CLOSURE_EIGENVECTOR_LAW_v1 (E1/E2) · CARDANO_G2_CLOSURE_AUDIT_v1 (ratification) · component standalones D1, D3, Eigenvector, Cascade Collapse, Ledger. github.com/tretoef-estrella.
