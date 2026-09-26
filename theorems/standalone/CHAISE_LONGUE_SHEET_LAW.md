> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-22
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SHEET LAW — membership in E + m^{[q]} sheet by sheet* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SHEET_LAW.md
>
> **Status, as written in the document:** §1 — WHAT WAS ALREADY ON FILE AND UNUSED. PROVED.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SHEET LAW — membership in `E + m^{[q]}` sheet by sheet
### CHAISE_LONGUE standalone · v1 · 2026-08-22 · UHLENHUTH
### Gold unearthed from `CHAISE_LONGUE_ODD_SYMMETRIC_GENERATION_THEOREM_v1` (proved, on file since the campaign's start) and gated the same turn.

> ## 🟩🟩 **CÓMO SE ESCRIBE AQUÍ:** un standalone = **un resultado con su grado y su prueba o su medida**. No se toca después salvo `v+1`. 🟩🟩

---

## §1 — WHAT WAS ALREADY ON FILE AND UNUSED. **PROVED.**

From `ODD_SYMMETRIC_GENERATION_THEOREM_v1` (char `K ≠ 2`, `n = 2k+2`):
> ### `E = (e_1,e_3,…,e_{2k+1})` is **RADICAL**, and `E = ⋂_J I_J` over the `(2k+1)!!` perfect matchings `J`
> ### of `\{0,…,n−1\}`, where **`I_J = (s_p : p ∈ J)`** and `s_p := u_c+u_d` for `p = \{c,d\}`.
The sheet `L_J = V(I_J)` is the linear space where each matched pair is `\{a,−a\}`. *(PROVED ∀k, char ≠ 2.)*

**And a second free fact, PROVED in one line:** `m^{[q]} := (u_0^q,…,u_{n−1}^q)` is **coordinate-free** —
for any linear form `ℓ = Σa_iu_i`, `ℓ^q = Σa_i^qu_i^q ∈ m^{[q]}` by Frobenius. Hence in *any* linear
coordinate system `m^{[q]}` is the ideal of `q`-th powers of the coordinates.

**Consequence, PROVED:** in coordinates adapted to `J` (legitimate since `char ≠ 2` makes
`\{u_c+u_d, u_c−u_d\}` a basis of each pair's span),
> ### `I_J + m^{[q]} = (s_p : p∈J) + (t_p^{\,q} : p∈J)`,  `t_p := u_c − u_d`,
so **membership in `I_J + m^{[q]}` is: restrict to the sheet (set `u_d = −u_c` for each `p ∈ J`) and ask
whether every surviving monomial has some exponent `≥ q`.** Elementary, and uniform in `k`.

---

## §2 — THE SHEET LAW. **CANDIDATE — gated in 3 cells, ~50 degrees, zero failures.**

> # `E + m^{[q]} \;=\; ⋂_J \left(I_J + m^{[q]}\right)`.

`⊆` is trivial (`E ⊆ I_J` for every `J`). `⊇` is the content. **Death criterion pre-registered before
running: a single degree in which the two dimensions differ kills it.** None fired.

| cell | matchings | degrees checked | result |
|---|---|---|---|
| `(1,3)` | 3 = `3!!` | 9 (deg 0–8) | **equal in every degree** |
| `(2,3)` | 15 = `5!!` | 13 (deg 0–12) | **equal in every degree** |
| `(1,9)` | 3 | 33 (deg 0–32) | **equal in every degree** |

Two dimensions **and** two values of `q` — the Kepler trap (Ley 12) is escaped in both directions.
Engine delivered: `fable_radical_gate_v1.py`. **Grade: CANDIDATE. Not proved. Do not cite as a theorem.**

**Named proof route (not executed):** `B := S/m^{[q]}` is Gorenstein artinian (complete intersection), so
Matlis duality gives `ann(I ∩ I') = ann(I) + ann(I')`; the intersection of the `(2k+1)!!` extended sheet
ideals becomes a **sum** of annihilators, which is computable. Second route: Kunz — Frobenius is flat over
the regular ring `S`.

---

## §3 — WHAT IT BUYS FOR THE DIFFERENCE LEMMA, AND THE FIRST CASE ALREADY FALLS

Target: `f := w^{\,q−1}·u_0^{\,j+1}·(u_a−u_ρ)·∏_{p∈M}s_p^{\,q−1} ∈ E+m^{[q]}`, `w := u_1−u_0`,
`0 ≤ j ≤ q−3`, `M` a matching of `\{2,…,n−1\}∖\{a,ρ\}`.

Under §2 this becomes: **for every matching `J`, `f|_{L_J} ∈ m^{[q]}`.** The cases:

**CASE A — `M ∩ J ≠ ∅`. PROVED, trivially.** Some `p = \{c,d\} ∈ M` lies in `J`, so on `L_J`
`s_p = u_c + (−u_c) = 0`, hence `f|_{L_J} = 0`. ✓

**CASE B1 — `\{0,1\} ∈ J`. PROVED, one line, and this is the case the symmetric tools could never see.**
On `L_J`, `u_1 = −u_0`, so `w| = −u_0 − u_0 = −2u_0 = u_0` (char 3). Therefore
> ### `w^{\,q−1}·u_0^{\,j+1}\big|_{L_J} = u_0^{\,q−1}·u_0^{\,j+1} = u_0^{\,q+j}`, and `j ≥ 0` ⟹ **exponent `≥ q`** ⟹ `f|_{L_J} ∈ m^{[q]}`. ✓

**CASE B2 — `M ∩ J = ∅` and `\{0,1\} ∉ J`. OPEN.** This is the whole remaining content of the Difference
Lemma. Here `0` is matched to some `x` and `1` to some `y`, with `\{x,y\} ≠ \{0,1\}`, and the restriction
of `w`, of `(u_a−u_ρ)` and of each `s_p^{q−1}` must be combined. The case split is on the position of
`a, ρ` relative to `x, y` and to the pairs of `M` — **a finite, `k`-independent list of configurations**,
because every pair of `M` not meeting `\{0,1,a,ρ,x,y\}` contributes the same factor on every sheet.

**This is why the route is worth taking:** it converts a `∀k` membership into a finite case list.

---

## §4 — A CANDIDATE KILLED THE SAME TURN (deposit with its number)

**Proposed:** an antisymmetric telescoping identity `(u_c−u_d)(u_c+u_d)^{q−1} = u_c^q − u_d^q`.
**KILLED:** false. The difference has residues `[1,2]` at `q=3` and `[1,2,1,2,1,2]` at `q=9,27` — not zero.
The genuine telescope is `(u_c−u_d)·h_{q−1}(u_c,u_d) = u_c^q − u_d^q`, and since `h_{q−1} = (u_c−u_d)^{q−1}`
by Lucas, that identity **is just Frobenius** and carries no new content. Failure mode:
`TELESCOPE-ASSUMED-FROM-THE-SYMMETRIC-CASE`.

---

### Files: `fable_radical_gate_v1.py`. Source of the unearthed fact: `CHAISE_LONGUE_ODD_SYMMETRIC_GENERATION_THEOREM_v1.md` §1.
### Grades: §1 PROVED · §2 CANDIDATE (3 cells) · §3 Cases A and B1 PROVED, Case B2 OPEN · §4 KILLED with numbers.
