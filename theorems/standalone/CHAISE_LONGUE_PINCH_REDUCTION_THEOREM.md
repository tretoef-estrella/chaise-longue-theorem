> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-30
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE · THE PINCH REDUCTION — v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_PINCH_REDUCTION_THEOREM.md
>
> **Status, as written in the document:** Notation: `I_j := ⋂_{a=0}^{j} ℓ_aĀ`; `I^{(ĉ)} := ⋂_{a≠c, a≤2k} ℓ_aĀ` (omit one form); `Π := ∏_{a=0}^{2k}ℓ_aĀ = 0` (PROVED ∀k: N15 + closure).
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (2 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE · THE PINCH REDUCTION — v1
**Standalone. Locard, 30 August 2026. Mission 3 exit: the repaired route after the middle-rung refutation.**

## 0. Position
The wall `⋂_{a=0}^{2k} ℓ_aĀ = 0 ⟺ (I')_k ⟺` conjecture (given `(I)_{k−1}`; `VERTEX_REDUCTION`). The product ladder `(L_j)` is dead in the middle (`FROBENIUS_TRANSPORT_AND_LADDER_REFUTATION_v1`: `114≠112, 54≠49, 22≠17` at `(3,3)`). This document replaces it with a two-statement route, one of which is proved here as an implication, and gates every measurable piece.

Notation: `I_j := ⋂_{a=0}^{j} ℓ_aĀ`; `I^{(ĉ)} := ⋂_{a≠c, a≤2k} ℓ_aĀ` (omit one form); `Π := ∏_{a=0}^{2k}ℓ_aĀ = 0` (PROVED ∀k: N15 + closure).

## 1. The measured structure of the failure (forensics)
**(M1) Graded localization.** At `(3,3)` (engine `GRADED33`): the deficits `dim I_j − dim ∏_{a≤j}ℓ_aĀ = 2, 5, 5` (`j = 3,4,5`) live **entirely in degree `T−1 = 7`** — one below the top degree `T = 8` of `Ā_3(3)`. In every other degree, intersection = product. `MEDIDO (3,3)`.
**(M2) The ℓ-torsion law.** At `(3,3)`, `j = 3,4,5`: `ℓ_b·I_j ⊆ ∏_{a≤j}ℓ_aĀ` for **every** `b = 0..j` **and even for the outside form** `ℓ_6` — `18+3` checks, all `True` (engine `DEFECT33`). The defect classes are killed into the product by every vertex form. `MEDIDO (3,3)`.
**(M3) Two-levels-down candidate (`CONJETURA`, pre-registered).** The defect masses are `Ā_{k−2}` figures: `2 = m_{q−1}(Ā_1(3))` (broken tiles), `5 = dim w^{q−1}Ā_1(3)`. At `k = 2` the governing ring would be `Ā_0`, a single Jordan block of size `q` — no short blocks, defect `0` — **consistent with the middle rungs being TRUE at `k=2` (proved `(L_2)` ∀q; measured `8=8`)**. Pre-registered predictions that would kill or promote: `(4,3)`, `j=3` defect `= 12 = m_{q−1}(Ā_2(3))`; any other value kills `DEFECT-TWO-LEVELS-DOWN`.

## 2. The pencil piece: the Second-Socle Pinch
**Proposition A (PROVED, ∀k∀q, two lines).** Suppose the torsion law holds at level `2k−1` for every omitted index:
> `(TL)`  for all `b, c`:  `ℓ_b · I^{(ĉ)} ⊆ ∏_{a≠c} ℓ_aĀ`.
Then every `v ∈ I_{2k}` satisfies `ℓ_bℓ_c v = 0` for **all** pairs `(b,c)` (including `b=c`), i.e.
> ### `I_{2k} ⊆ P2 := ⋂_{a=0}^{2k} ℓ_aĀ ∩ (0 :_Ā (ℓ_bℓ_c)_{0≤b≤c≤2k})`.
*Proof.* `v ∈ I_{2k} ⊆ I^{(ĉ)}`; by `(TL)`, `ℓ_bv ∈ ∏_{a≠c}ℓ_aĀ`; multiplying by `ℓ_c`: `ℓ_cℓ_bv ∈ ∏_{a=0}^{2k}ℓ_aĀ = Π = 0`. The case `b=c` uses the omission `ĉ = b̂`. ∎

**Corollary (the repaired route).**
> ### **WALL ⟸ `(TL)` ∀k  +  `PINCH`: `P2 = 0` ∀k.**
Two named, independent, ∀k statements replace the false ladder. Both are gateable, and both pass every available cell:

## 3. Gates
| statement | cells | result |
|---|---|---|
| `(TL)` at level `2k−1` (and `j=3,4`) | `(3,3)`, all `b` incl. outside form | **21/21 True** |
| `P2 = 0` | `(1,3), (2,3), (3,3), (1,9)` | **0, 0, 0, 0** |
| `P1 := ⋂_a(ℓ_aĀ ∩ (0:ℓ_a)) = 0` (stronger pinch, single-socle) | same 4 cells | **0, 0, 0, 0** |
`P1 = 0` is logged because it is the stronger statement in the native language of the corpus's Jordan/tile machinery: no nonzero element sits simultaneously at `image ∩ kernel` of **every** vertex form. If `P1 = 0` is proved ∀k, the route closes with the FULL torsion law (level `2k`); the `P2` route needs only level `2k−1`, which is the nonvacuously measurable one. `(1,9)` crosses the `q`-transition: the pinch is not a `q=3` artifact.
Engines: `CHAISE_LONGUE_GRADED33_ENGINE_v1.py`, `CHAISE_LONGUE_DEFECT_TORSION_GATE_v1.py`, `CHAISE_LONGUE_PINCH_GATE33_v1.py`, `CHAISE_LONGUE_PINCH_GATE_MULTI_v1.py`.

## 4. Grades and the corrected GAP block (for the ASSEMBLY)
- Proposition A: `PROVED ∀k∀q` (conditional implication; unconditional as an implication).
- `(TL)`: `MEDIDO (3,3)` nonvacuously; `OPEN ∀k` — target 1.
- `PINCH P2 = 0`: `MEDIDO 4/4` cells; `OPEN ∀k` — target 2.
- `DEFECT-TWO-LEVELS-DOWN`: `CONJETURA` with pre-registered kill numbers.
Proposed GAP text (English, to supersede §106.17): *"OPEN. The product ladder is refuted at `(3,3)` (`114≠112`). The wall reduces (Prop. A, PINCH_REDUCTION v1) to two ∀k statements: `(TL)` `ℓ_b·⋂_{a≠c}ℓ_aĀ ⊆ ∏_{a≠c}ℓ_aĀ`, and `PINCH` `⋂ℓ_aĀ ∩ (0:(ℓ_bℓ_c)) = 0`. Both measured true in all available cells incl. `(1,9)`. Defect masses live in degree `T−1` only and match `Ā_{k−2}` figures (candidate, kill number pre-registered at `(4,3)`: `12`)."*

*Locard · 2026-08-30 · Campaña Chaise Longue.*
