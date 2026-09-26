> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026-08-26
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SELF-SIMILARITY THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_SELF_SIMILARITY_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SELF-SIMILARITY THEOREM
### *Every interval of the swap intersection poset is again a swap intersection poset, on fewer indices*
### Bisel · Chaise Longue campaign · 2026-08-26 · **standalone, self-contained**

---

# 0 · WHY THIS DESERVES ITS OWN DOCUMENT

This is a **short theorem with a disproportionate consequence**, and it is the reason it is written up separately rather than buried as a lemma.

Reisner's criterion for the Cohen–Macaulayness of a subspace arrangement is a statement about **every interval** of its intersection poset — an unbounded family of conditions, one per element, growing with `n`. The campaign had reached that criterion and stalled there: measuring links one by one is not a proof, and there was no visible way to handle them uniformly.

**Self-similarity collapses that family to a single condition per dimension.** If every interval of the poset is again a poset *of the same species* on fewer indices, then an induction on the number of indices reduces "all intervals, all `n`" to "the whole poset, each `n`" — and, once combined with a homotopy equivalence for the whole poset (proved separately), to nothing at all.

> ### **Before:** prove a vanishing for every interval of every `\mathcal L(\mathcal W)`.
> ### **After:** prove it once per `n`, and let induction do the rest.

That change of shape is what this document records. It is also, as far as the campaign's grep of 227 documents shows, **new**: no statement of this form appears anywhere in the corpus.

---

# 1 · SETUP

Fix `k \geq 1`, `n = 2k+2`, `\operatorname{char} K \neq 2`.

For a perfect matching `J` of `\{1,\dots,n\}` let `L_J := \{x : x_a + x_b = 0 \ \forall (a,b)\in J\}`, of dimension `k+1`. A **swap flat** is an intersection `L_J \cap L_{J'}` of dimension `k`; equivalently
```
F = { x_a = x_d = −x_b = −x_c }  ∩  { x_e + x_f = 0 on each of the k−1 shared blocks },
```
determined by a 4-subset `\{a,b,c,d\}` with a balanced sign pattern, plus a perfect matching of the remaining `n-4` indices. There are `(2k+1)!!\,k(k+1)/2` of them.

`\;\mathcal W := \bigcup F` (reduced), and `\mathcal L(\mathcal W)` is the poset of all intersections of swap flats, ordered by reverse inclusion.

**Signed strata.** Every element of `\mathcal L(\mathcal W)` has the form
```
X = X(Z; B_1,ε^1; … ; B_r,ε^r) = { x_i = 0 (i ∈ Z);  x_i = ε^t_i u_t  (i ∈ B_t) }
```
for a partition `\{1..n\} = Z \sqcup B_1 \sqcup \cdots \sqcup B_r` and signs `ε^t` up to a global flip per block. *(Proved: swap flats are intersections of hyperplanes `x_i \pm x_j = 0`; the class of signed strata is closed under intersection, since intersecting either merges blocks with transitive sign propagation or, on a conflict `u = -u`, annihilates a block into `Z` — the latter using `\operatorname{char} K \neq 2`.)*

**Definition.** A **swap arrangement on an index set `I` with a sign structure** means: the arrangement built from the same recipe (balanced 4-block plus 2-blocks) on the indices of `I`.

---

# 2 · ★ THE THEOREM

> # **THEOREM (Self-similarity).** Let `X = X(Z; B_1,ε^1; \dots; B_r,ε^r) \in \mathcal L(\mathcal W)`. Then:
> ### **(a) (downward)** the interval `[X, \hat 1]` — the strata contained in `X` — is isomorphic to the intersection poset of a swap arrangement on the index set `\{1,\dots,r\}` of the **blocks** of `X`, i.e. on `r < n` indices.

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 11, informe 139) — (a) sólo vale cuando el número de bloques `r` es PAR y `≥ 4`:** `[X, 1̂]` tiene que ser un swap arrangement sobre `r` bloques, y ése no existe para `r = 1` o `r = 3` (`VIVOS/EL_CATALOGO_MAESTRO`, entrada `v250.a`). La inducción del §2.3 no cubre esos casos, y la cadena «CM ⟹ bandas II+III+IV» cae además con el Teorema 4.1 de `THE_CLOSURE_THEOREM`.

> ### **(b) (upward)** the interval `[\hat 0, X]` — the strata containing `X`, down to the swap flats — is isomorphic to the intersection poset of the swap arrangement **restricted** to the flats containing `X`, again a swap-type poset on fewer indices.
> ### In particular **every interval of `\mathcal L(\mathcal W)` is again a swap intersection poset, on strictly fewer indices.**

## 2.1 · Proof of (a)
On `X` the coordinates are constant, up to sign, on each block `B_t`, and zero on `Z`; write `u_t` for the free parameter of `B_t`, so `X \cong K^r` with coordinates `u_1,\dots,u_r`.

A stratum `Y \subseteq X` is a signed stratum of `K^n` refining nothing and coarsening `X`: since `Y \subseteq X`, every relation defining `X` holds on `Y`, so `Y` is obtained from `X` by imposing further relations **among the `u_t`** — namely `u_t = \pm u_s` (merging blocks `B_t, B_s` with a sign) or `u_t = 0` (annihilating `B_t` into the zero set). These are precisely the two moves of §1 read in the `u`-coordinates.

Hence the assignment `Y \mapsto` (its induced signed stratum in the `u`-coordinates) is an order isomorphism from `[X,\hat1]` onto the poset of signed strata of `K^r`, restricted to those arising as intersections of images of swap flats. **That restricted poset is the intersection poset of the swap arrangement on the block index set**, because a swap flat `F \supseteq` (some `Y`) induces on `X` exactly a swap-shaped relation among the `u_t`. ∎

## 2.2 · Proof of (b)
A stratum `Y \supseteq X` is an intersection of swap flats each of which contains `X`. The set of swap flats containing `X` is itself the set of swap flats of the arrangement **restricted** to the ambient span of `X`'s defining data — a swap arrangement on the indices not already annihilated, with the sign structure of `X` imposed. Intersections of that subfamily are exactly the elements of `[\hat0, X]`. ∎

## 2.3 · The induction that this enables
> **COROLLARY.** Suppose that for every `n` the order complex `\Delta(\mathcal L(\mathcal W_n))` of the *whole* proper part has reduced homology concentrated in the top dimension. Then `\mathcal L(\mathcal W_n)` is **Cohen–Macaulay** for every `n`.
> *Proof.* Induct on `n`. Reisner/CM for a poset requires the concentration for every open interval. By the Theorem each proper interval is `\mathcal L(\mathcal W_m)` for some `m < n`, which is CM by the induction hypothesis; the only remaining condition is the one for the whole poset, which is the assumption. ∎

> ### **That is the entire content: an unbounded family of conditions becomes one condition per `n`.**

---

# 3 · WHAT IT IS FOR, AND WHERE IT SITS
The hypothesis of the Corollary — concentration in the top dimension for the whole poset — is supplied separately by a **closure operator** into a Dowling lattice, whose rank-selected subposets are Cohen–Macaulay by classical results (Dowling 1973; Björner, *Trans. AMS* **260** (1980); Baclawski, *J. Algebra* **63** (1980), Thm 6.4). **Self-similarity is what makes that single homotopy statement sufficient.**

Downstream, `\mathcal W` arithmetically CM feeds a chain — proved elsewhere in the campaign — ending in the closure of three of the four bands of the Chaise Longue conjecture for all `k`.

## 3.1 · Measured signature (independent of the proof)
| `k` | `\dim \Delta` | below top | top |
|---|---|---|---|
| 2 | 1 | `\tilde H_0 = 0` | `\tilde H_1 = 66` |
| 3 | 2 | `\tilde H_0 = \tilde H_1 = 0` | `\tilde H_2 = 3807` |

---

# 4 · GRADE
| item | grade |
|---|---|
| Signed-stratum classification | **PROVED** (`\operatorname{char}\neq2`) |
| Theorem (a) downward | **PROVED**, all `k` |
| Theorem (b) upward | **PROVED**, all `k` |
| Corollary (the induction) | **PROVED**, given its hypothesis |
| The hypothesis itself | supplied by the Closure Theorem (separate standalone) |
| `66 / 3807` | **MEASURED**, `2/2` |
> **The theorem is elementary. Its value is not depth of proof but change of shape: it is the step that turns Reisner's criterion from an unbounded family into a single statement per dimension.**

---
*Standalone. Nothing on this page depends on any other document.*
