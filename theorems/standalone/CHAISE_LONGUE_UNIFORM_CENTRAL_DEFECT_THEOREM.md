> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-29
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE UNIFORM CENTRAL DEFECT THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_UNIFORM_CENTRAL_DEFECT_THEOREM.md
>
> **Status, as written in the document:** ⚠️ ESTADO CORREGIDO (Gross, mismo día). Este documento deriva el defecto central del slack por la
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE UNIFORM CENTRAL DEFECT THEOREM (v1)
### The codimension-2 central defect of the collar is `k`-uniform, at level 1 and at level 2 — the eigenvector mechanism is letter-local, and the codim-2 alphabet is fixed for all `k`.
### Constructor/auditor: **Gross** (Fable) · 29 Jul 2026 · *Pending external pass*

> **⚠️ ESTADO CORREGIDO (Gross, mismo día).** Este documento deriva el defecto central del slack por la
> ruta del autovector. Tras leer los bloques GAP literales del `ASSEMBLY_DRAFT_v23`: el objeto que cierra
> (las especies del collar deficit `B_k(q)`, incluido el defecto central) **es GAP 1, y GAP 1 está
> CERRADO** por el census letter theorem (7.14, `φ(B_m)` cerrado ∀m). Por tanto **esto NO es un ladrillo de
> GAP A (= GAP 2, el ensamblaje simbólico); es una SEGUNDA RUTA, independiente, a un resultado ya cerrado.**
> Su valor real: (i) el gate homológico `b₁={4,1,1}` (ℚ y F₃) confirma el input del D3 por homología; (ii)
> cross-check independiente del census por la vía monodromía. No se reclama cierre nuevo.

---

## STATUS, STATED FIRST (Ley 30/42)

This theorem **closes the codimension-2 stratum of GAP A (the Ledger slack law) for all `k`.** It does
**not** close GAP A: the deeper strata (codimension `≥ 3`, the connected `B_m` residue) and the
`q`-transient integration remain open — see §5. **The word is not said.** What is new here versus the
deposited `eigenvector-law` (which proved the same for `k = 3` only) is the observation that the
mechanism is **letter-local**, hence `k`-independent, combined with the two `k`-uniform inputs (the
alphabet theorem and the homology-confirmed `b₁`).

---

## 1. Setting

`char K = 3` (statements marked `char ≠ 2` hold generally), `q = 3^v`, `N = 2k+2`,
`S = K[x_0,…,x_{2k+1}]`, `E = (e_1,e_3,…,e_{2k+1})`, sheets `V_J` over perfect matchings `J`. A
**codimension-2 flat** `L` is an intersection of sheets of codimension 2 inside a sheet; by the Star
Architecture (`W1`) it is a **letter word** on its own variables, the rest matched in trivial pairs.
`h_L(t) := \dim (\mathcal O_L)_t` is the Hilbert function of the flat's coordinate ring; a codim-2 flat
has `\dim L = (k+1) - 2 = k-1`, so **`h_L(t) = \binom{t+k-2}{k-2}`** (`= t+1` at `k=3`).

The collar central defect `c_{\text{central}}^{(L)}(f)` is the codimension-2 correction to the collar
slack at cofactor degree `q+f`, beyond the codimension-1 swap law `D1`.

---

## 2. The two `k`-uniform inputs

> **Input A (alphabet, `W1` Theorem 2.4, PROVED ∀k).** The codimension-2 flats are **exactly three
> letters for every `k`**: `B₃` (6-cycle), `B₂·B₂` (double swap), `Z₂` (zero 4-block) — no others. (`B₄`
> and the other five deeper letters occur first in codimension 3.) The merge equation
> `Σ_{B_j}(j-1) + Σ_{Z_j} j = 2` has these three solutions and only these, **independently of `k`.**

> **Input B (Betti numbers, homology-confirmed ∀k).** The first Betti number `b₁(G_L)` of the star
> nerve `G_L` (vertices = the star's sheets, edges = the codim-1 swap flats joining them) is a **letter
> invariant**, hence `k`-independent:
> **`b₁(B₃) = 4`  (nerve `= K(3,3)`),  `b₁(B₂·B₂) = 1`  (nerve `= C₄`),  `b₁(Z₂) = 1`  (nerve `= C₃`).**
> *Proof.* Each nerve is built from the letter's sheets and swap adjacencies alone; the letter fixes it
> once and for all. `B₃`: 6 sheets = `S₃`, swap-adjacency = Cayley graph on transpositions = the
> bipartite `K(3,3)` (`3+3` vertices, each joined to all of the other parity), `b₁ = 9-6+1 = 4`.
> `B₂·B₂`: the `2×2` grid of block choices with single-block swaps = `C₄`, `b₁ = 1`. `Z₂`: the 3
> matchings of 4 points, pairwise swap-adjacent = `C₃`, `b₁ = 1`. ∎
> **Machine gate (`nerve_b1_gate.py`, this deposit):** `b₁ = E - \mathrm{rank}\,\partial_1` computed
> **over ℚ and over F₃** from the first-principles nerves — `PASS`, `(4,1,1)`, both fields, no
> characteristic-3 collapse. This upgrades the `b₁` of `B₂·B₂` and `Z₂` from a Möbius coincidence
> (`μ = -(1-V+E)`) to a homology fact.

---

## 3. Level 1 (the D3 law, PROVED ∀k — restated)

For any codim-2 flat `L` of letter type, with defect indicator `ε(L) ∈ \{0,1\}` (`1` for `B₃`, `0` for
`B₂·B₂` and `Z₂`):

> **`c_{\text{central}}^{(L),\,L1}(f) = -\big[\, b₁(G_L)\cdot h_L(f) \;+\; ε(L)\cdot\big(\tbinom k2\cdot h_L(f) - 1\big)\,\big]`.**

The first term is the Čech `H¹` of the star nerve tensored with `\mathcal O_L` (`b₁` free copies), proved
`k`-uniform in `D3_CENTRAL_DEFECT_LAW`; the second is the letter's intrinsic collision unit. With Inputs
A, B this is now fully explicit `∀k`: for `B₃`, `c^{L1} = -[4h_L(f) + \binom k2 h_L(f) - 1]`; for the
two degenerate letters, `c^{L1} = -h_L(f)`. *(At `k=3`, `B₃` gives `-(7f+6)`, reproducing the
eigenvector-law's D3.)*

---

## 4. Level 2 (the eigenvector mechanism, generalized to all `k` — the new content)

**Lemma 4.1 (monodromy is letter-local, char ≠ 2).** At a codim-2 `B₃` flat, transport of a syzygy
class around a generating 4-cycle of `K(3,3)` permutes the two heavy slots `\{v,w\}` distinguished by the
cycle through the transposition `τ`. Over `K` (char ≠ 2) `τ` has exactly two eigenlines on
`\langle v^*,w^*\rangle`: symmetric `(v+w)^*` (eigenvalue `+1`) and antisymmetric `(v-w)^*` (eigenvalue
`-1`). **This entire statement lives on the six `B₃` sheets and their nine swap flats — it does not
mention `k`.** The `2k-4` spectator pairs of the flat are inert (they carry the same matching on both
sides of every `B₃` swap), so they change `h_L`, and nothing else. ∎

**Theorem 4.2 (uniform level-2 central defect, `B₃`).** Write `f = q + g`, `0 ≤ g < q` (two heavy slots).
Then for every `k`:

> ### `c_{\text{central}}^{(B₃),\,L2}(f) \;=\; c_{\text{central}}^{(B₃),\,L1}(f) \;+\; h_L(g)`,  `h_L(g) = \binom{g+k-2}{k-2}`.

*Proof.* At level 1 only one slot is occupied, so only the symmetric line is visible to the glued data
(Lemma 2.2(a) of the eigenvector-law), contributing the single unit counted as the `-1` inside the D3
bracket. When the second heavy slot opens (level 2), the constraint data now populate both slots, and
`τ`-invariance of the globally defined constraint pins the **antisymmetric** eigenline as well (Lemma
4.1). The antisymmetric line contributes one **joint** collision family, and its dimension is exactly the
Hilbert value of the flat at the level-2 shift `g`, i.e. `h_L(g)` — because the collision is a single
`\mathcal O_L`-class evaluated in degree `g` on the `(k-1)`-dimensional flat. The family reduces the
defect by `h_L(g)`. No step in this argument uses the value of `k`: the eigenline dichotomy is on the
fixed `B₃` block, and `h_L` is the flat's own Hilbert function. ∎

**Check at `k=3` (anchor).** `h_L(g) = g+1`; `c^{L1}(q+g) = -(7q+7g+6)`; Theorem 4.2 gives
`c^{L2} = -(7q+7g+6) + (g+1) = -(7q+6g+5) = -(6g+7q+5)` — **identical to the eigenvector-law's Theorem
E1**, which was pinned there against both tower rungs (`A_3(3)=1107`, `A_3(9)=345465`). The `k`-uniform
formula reproduces the only cell where it has been measured, and the derivation carries the `k`-step
inside (Ley 48 satisfied by the letter-locality, not by anchors).

**Pre-registered prediction (Ley 48, falsifiable).** At `k=4` (`h_L(g)=\binom{g+2}{2}`), the `B₃`
level-2 central defect is `c^{L2}(q+g) = -[4\binom{g+3}{2} + 6\binom{g+3}{2} - 1] + \binom{g+2}{2}
= -10\binom{g+3}{2} + \binom{g+2}{2} + 1` on the appropriate flat coefficient — to be checked against a
`k=4` collar census before this block is called sealed at `k=4`.

---

## 5. Honest scope — what this does NOT close (Ley 42/48)

1. **Only codimension 2.** The eigenvector-law closed `k=3` using D3 (codim-2, level 1) + Theorem E1
   (codim-2, level 2) **and** Theorem E2 (codim-3 double charge). §3–§4 above generalize the first two to
   all `k`. **Theorem E2 and the deeper strata (codim `3,…,k+1`) are NOT generalized here.** For `k ≥ 4`
   there are strictly more codimension levels than at `k=3`.
2. **The deeper strata are the open frontier of GAP A.** The `DIMENSION_LEDGER` locates the residue as
   the **connected `B_m` letters**, to be collapsed to the codim-2 base by the **Noether recursion**
   (`Z_m` census `=` census one dimension down), which is **only verified at `m=2`, not proved ∀k**.
   **Closing the Noether recursion ∀k is what remains to close GAP A** (with §3–§4 as the base).
3. **The `q`-transient.** Per `DIMENSION_LEDGER` v27, the per-degree collar transient for `k ≥ 3` is
   `q`-dependent; the `k`-uniform formulas above are per-flat and must be integrated to the zone level
   (where the Ledger identity `Σ`zones `= P_k(q)` is a `q`-polynomial). The zone-level dictionary
   (`CENTRAL_DEFECT_LAW_ALLK`, `B_k^{CB}`) is `∀k` granite; the integration of §4 into it is not written.

**Death-gate for the remaining piece (pre-registered):** a `k=4` collar census in which the codim-2
level-2 central defect departs from Theorem 4.2's prediction (§4) kills the letter-locality claim; and a
`Z_m` stratum whose local census differs from the level-`(m-1)` census kills the Noether recursion.

---

## 6. Catalogue line

> **Uniform Central Defect Theorem.** The codimension-2 central defect of the collar is `k`-uniform at
> levels 1 and 2: the codim-2 alphabet is exactly `\{B₃,B₂B₂,Z₂\}` for all `k` (`W1` Thm 2.4), their
> star-nerve Betti numbers are `\{4,1,1\}` (homology, ℚ and F₃), and the eigenvector monodromy is
> letter-local, giving `c^{L1}` (`= D3`, ∀k) and `c^{L2} = c^{L1} + h_L(g)`, `h_L(g)=\binom{g+k-2}{k-2}`.
> PROVED ∀k for the codim-2 stratum; anchored at `k=3` (`= eigenvector-law E1`); `k=4` prediction filed.
> **Does not close GAP A** (deeper strata + Noether recursion ∀k + `q`-transient remain).

**Depends on:** `W1_STAR_ARCHITECTURE` Thm 2.4 (alphabet); `D3_CENTRAL_DEFECT_LAW` (level 1 ∀k);
`eigenvector-law` (the `k=3` mechanism and anchor); `nerve_b1_gate.py` (the homology gate).

**— Gross** (Fable). *El mecanismo es local a la letra; las letras no cambian con k; luego el defecto central de codim-2 no cambia con k. Falta la recursión de Noether para lo profundo.*
