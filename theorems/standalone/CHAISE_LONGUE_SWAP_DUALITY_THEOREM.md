> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SWAP DUALITY LAW — CHAISE_LONGUE_SWAP_DUALITY_THEOREM_v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SWAP_DUALITY_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SWAP DUALITY LAW — `CHAISE_LONGUE_SWAP_DUALITY_THEOREM_v2`
### The self-duality of the defect module is the outer involution, not a character; and the equivariant Betti table of `C(B_3)`
**Chaise Longue campaign · 23 Jul 2026 · Orfila (auditor)** · **v2: sign corrected.**

> ### ⛔ CORRECTION CARRIED IN THIS VERSION
> `v1` stated the law as `β_{c−i,s−j} = (−1)^c · ι^*(β_{i,j})`. **The sign does not belong on the cells** — a multiplicity has no sign. It belongs to the K-polynomial identity `E_{s−j}(α,β) = (−1)^c E_j(β,α)`, where it comes from reindexing `i ↦ c−i` inside an alternating sum. **The cell law is `β_{c−i,s−j} = ι^*(β_{i,j})`, with no sign**, and that is the form verified 9/9 against the table. Everything measured is unchanged; only the statement was sloppy.

> **Summary.** The campaign spent several turns hunting a linear character `χ` of `S_m × S_m` such that
> `β_{c−i, s−j} = β_{i,j} ⊗ χ`. **No such character exists.** The measured law is
>
> > ### `β_{c−i, s−j}(C) = ι^*( β_{i,j}(C) )`
>
> where `ι` is the outer involution `a ↔ b`. The twist is the **swap itself**, an element of the outer
> automorphism group, not of the group being represented. This is why `χ` never closed: it was being
> looked for inside a group where it does not live. As a by-product the **complete equivariant Betti
> table of `C(B_3)`** falls out, all nine cells, and it independently reproduces every cell the
> constructor had derived on the restored branch.

---

## 0. THE INSTRUMENT — WHY NO CELL HAD TO BE ASSUMED

Let `V = R_1` and let

>  `K(g;t) = Σ_{i,j} (−1)^i tr( g | β_{i,j} ) t^j`

be the equivariant K-polynomial, so that `Hilb_C(g;t) = K(g;t) / det(1 − t·g|V)`. Write `E_j(g)` for the
coefficient of `t^j` in `K(g;t)`. Then `K` is computed from the **graded character of `C` alone**:

>  `K(g;t) = ( Σ_d tr(g|C_d) t^d ) · det(1 − t·g|V)`,

and `det(1 − t·g|V) = Π_{cycles of α} (1 − t^{len}) · Π_{cycles of β} (1 − t^{len})` for `g = (α,β)`.

**Nothing about any Betti cell is assumed.** The only structural inputs are `c = m+1` and
`s = m + binom(m,2)`, both proved, and the traces of `g` on the graded pieces of `C`.

Any duality law of the form `β_{c−i,s−j} = τ(β_{i,j})` implies, comparing coefficients,

>  `E_{s−j}(g) = (−1)^c · E_j(τ^{-1} g)`  for every `j` and every `g`.

So the two hypotheses separate cleanly: a **linear character** `τ = ⊗χ` predicts
`E_{s−j}(g) = (−1)^c χ(g) E_j(g)`, whereas the **swap** `τ = ι^*` predicts
`E_{s−j}(α,β) = (−1)^c E_j(β,α)`. They are distinguished by data, not by argument.

---

## 1. GATES, DECLARED BEFORE THE VERDICT

| gate | requirement | source | result |
|---|---|---|---|
| G1 | Hilbert numerator `2 + 5T + 2T²`, `dim 2`, `degree 9` | sealed closed form | **pass** |
| G2 | minimal graded Betti table, totals `2,10,16,10,2`, `pd = 4` | evidence dossier §3 | **pass** |
| G3 | `tr(1 | C_d)` reproduces `HF(C) = 2,9,18,27,36,45,54` | evidence dossier §2.1 | **pass** |
| G4 | `E_0` equals the character of `std_a ⊗ triv_b` | **proved** value of `β_{0,0}` (`LINEAR_STRAND_THEOREM_v1`) | **pass** |

G4 is the honest gate on the whole machine: it checks the traces, the permutation of the module
coordinates and the K-polynomial assembly against a value that was proved on paper beforehand.

**Characteristic 0.** Ordinary character theory of `S_3` is not available in characteristic 3, and a
character read mod `p` is a different object. The run is in `Q`. The Betti table over `Q` is
`2,10,16,10,2` with `pd = 4`, identical to characteristic 3, cell by cell.

**Note on equivariance.** The presentation must be kept on the ambient `R^m`, whose coordinates are the
`a`-vertices and on which the group acts by permutation. Pruning to a minimal presentation changes the
ambient and destroys the action; it is used only to print the Betti gate.

---

## 2. THE MEASUREMENT

`E_j` as `3 × 3` tables (rows = class of `α`, columns = class of `β`; classes `e, (12), (123)`):

```
 E_0  [ 2  2  2]     E_1  [-3 -3 -3]     E_2  [-6 -2  0]     E_3  [14  4 -1]
      [ 0  0  0]          [-1 -1 -1]          [ 0  0  0]          [ 4  2  1]
      [-1 -1 -1]          [ 0  0  0]          [ 3  1  0]          [-1  1  2]

 E_4  [-6  0  3]     E_5  [-3 -1  0]     E_6  [ 2  0 -1]
      [-2  0  1]          [-3 -1  0]          [ 2  0 -1]
      [ 0  0  0]          [-3 -1  0]          [ 2  0 -1]
```

### 2.1 The linear-character hypothesis is refuted

If `β_{c−i,s−j} = β_{i,j} ⊗ χ` with `χ` linear, then `χ(g) = (−1)^c E_s(g)/E_0(g)` wherever `E_0(g) ≠ 0`.
Reading it off:

```
 g = (e,e)        chi = 1
 g = (e,(12))     chi = 0            <- impossible for a character
 g = (e,(123))    chi = -1/2         <- impossible
 g = ((123),e)    chi = -2           <- impossible
 g = ((123),(123)) chi = 1
```

A linear character takes only the values `±1` on real classes and never vanishes. **No linear character
`χ` satisfies the duality.** *(This also disposes of the earlier enumeration that had excluded
`sgn_a ⊗ sgn_b`: correct conclusion, wrong universe — none of the four survives.)*

### 2.2 The swap law holds, exactly

> **`E_{s−j}(α,β) = (−1)^c · E_j(β,α)` for every `j` in `0..s` and every one of the nine class pairs.**
> Tested: `7 × 9 = 63` identities, all satisfied, `(−1)^c = +1` at `m = 3`.

Visibly, `E_6` is `E_0` with the two factors exchanged, `E_5` is `E_4` exchanged, `E_4` is `E_2`
exchanged, and `E_3` is symmetric under the exchange, as the law requires at the self-paired degree.

> ### **The twist is the outer involution `ι : a ↔ b`. It is not an element of `S_m × S_m` and no
> ### character of that group can express it.**

---

## 3. THE EQUIVARIANT BETTI TABLE OF `C(B_3)`, COMPLETE

Decomposing each `E_j` and separating the two internal degrees where two cells share a degree (using the
linear strand `0 → triv → V_a → std_a → 0`, now proved, which gives `β_{2,2} = triv ⊗ triv`):

| cell | representation | dim |
|---|---|---|
| `β_{0,0}` | `std_a ⊗ triv_b` | 2 |
| `β_{1,1}` | `triv⊗triv ⊕ std_a⊗triv_b` ( `= V_a` ) | 3 |
| `β_{1,2}` | `triv⊗triv ⊕ std_a⊗triv_b ⊕ std_a⊗std_b` | 7 |
| `β_{2,2}` | `triv ⊗ triv` | 1 |
| `β_{2,3}` | `2(triv⊗triv) ⊕ triv_a⊗std_b ⊕ std_a⊗triv_b ⊕ 2(std_a⊗std_b)` | 14 |
| `β_{2,4}` | `triv ⊗ triv` | 1 |
| `β_{3,4}` | `triv⊗triv ⊕ triv_a⊗std_b ⊕ std_a⊗std_b` | 7 |
| `β_{3,5}` | `triv⊗triv ⊕ triv_a⊗std_b` | 3 |
| `β_{4,6}` | `triv_a ⊗ std_b` | 2 |

Column totals `2, 10, 16, 10, 2` — the sealed table, cell by cell. Every row of the right half is the
`ι`-image of its partner on the left, and the middle cell `β_{2,3}` is `ι`-symmetric, exactly as the law
demands.

**Independent confirmation of the constructor's cells.** On the restored branch the constructor had
derived `β_{1,1} = V_a = triv ⊕ std_a`, `β_{2,2} = triv`, and
`β_{1,m−1} = triv ⊕ std_a ⊕ std_a⊗std_b`. All three are reproduced here from the graded character alone,
with no cell assumed. In particular the glue `T_2 = std_a ⊗ std_b` appears inside `β_{1,2}` exactly as
recorded.

---

## 4. WHAT THE LAW SAYS ABOUT `ω_C` — READ, NOT PROVED

For `C` Cohen–Macaulay of codimension `c`, dualising the resolution gives a resolution of `ω_C`, so a
duality of the Betti table is a statement about `ω_C`. The measured law reads as

> **`ω_{C_a} ≅ C_b(−s)` up to a linear twist**, with `C_b = ι^* C_a`,

which is consistent with everything already on file: the Hilbert series is palindromic (the swap does not
change dimensions), `C_a ≇ C_b` as representations, and there is no internal self-symmetry.
**This reading is NOT proved here.** What is proved-by-measurement is the Betti-table identity of §2.2 at
`m = 3`. Establishing `ω_{C_a} ≅ C_b(−s) ⊗ ε` for all `m`, and pinning `ε` against `ω_R = R(−2m) ⊗ sgn_a ⊗ sgn_b`,
would upgrade the law from measured to proved and is the natural next target.

---

## 5. SCOPE

| statement | grade | scope |
|---|---|---|
| no linear character satisfies the duality | **MEASURED, decisive** | `m = 3`, char 0, all 9 classes |
| `E_{s−j}(α,β) = (−1)^c E_j(β,α)` | **MEASURED** | `m = 3`, char 0, 63 identities |
| the equivariant Betti table of §3 | **MEASURED** (with `β_{2,2}` from the proved linear strand) | `m = 3` |
| `ω_{C_a} ≅ C_b(−s) ⊗ ε` | **READING, not proved** | — |
| the law for all `m` | **NOT ESTABLISHED** | `m = 4` cross-check pending |

**Nothing here proves `C` Cohen–Macaulay for all `m`, and nothing here closes `GAP 1`.** What it does is
finish the *identification* half of the step at `m = 3`: the complex's terms are now known as
representations, which is the input the Schur argument for the differentials needs.

**Reproduction:** `chaise_chi_v1.m2` (Macaulay2 ≥ 1.22), log `out_chi_m3.log`.

— Orfila, Chaise Longue campaign
