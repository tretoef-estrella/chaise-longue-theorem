> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026-08-26
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE CLOSURE THEOREM FOR THE SWAP ARRANGEMENT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_CLOSURE_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE CLOSURE THEOREM FOR THE SWAP ARRANGEMENT
### *The homotopy type of the intersection poset of swap flats, via a closure operator into a Dowling lattice*
### Bisel · Chaise Longue campaign · 2026-08-26 · **standalone, self-contained**

---

# 0 · WHY THIS DOCUMENT EXISTS

The Chaise Longue programme reduces — through a chain proved elsewhere and summarised in §5 — to a single question of combinatorial topology:

> **Is the reduced union `\mathcal W` of *swap flats* arithmetically Cohen–Macaulay, for every `k`?**

By Reisner's criterion this is a statement about the reduced homology of the order complexes of the intervals of the **intersection poset** `\mathcal L(\mathcal W)`. This document proves that those order complexes are homotopy equivalent to order complexes of **rank-selected subposets of a Dowling lattice**, for which Cohen–Macaulayness is classical. It isolates, states and proves the one step that is not classical.

---

# 1 · SETUP

Fix `k \geq 1`, `n = 2k+2`, and a field `K` with `\operatorname{char} K \neq 2`.

**Sheets.** For each perfect matching `J` of `\{1,\dots,n\}` put
`\;L_J := \{x \in K^n \;:\; x_a + x_b = 0 \ \ \forall (a,b) \in J\}`, a linear subspace of dimension `k+1`. There are `(2k+1)!!` sheets.

**Swap flats.** Two sheets `L_J, L_{J'}` meet in dimension `k` precisely when `J` and `J'` share `k-1` edges and differ on a 4-cycle; such an intersection is a **swap flat**. Concretely, a swap flat is
```
F  =  { x_a = x_d = −x_b = −x_c }  ∩  { x_e + x_f = 0  for each of the k−1 shared blocks }
```
for a 4-subset `\{a,b,c,d\}` and a perfect matching of the remaining `n-4` indices. Their number is `(2k+1)!!\,k(k+1)/2`, verified independently by two enumerations (`3, 45, 630, 9450` for `k=1,2,3,4`).

**The arrangement and its poset.** `\;\mathcal W := \bigcup_F F`, reduced; and
> `\;\mathcal L(\mathcal W) := \{\, \bigcap_{F \in \mathcal F} F \;:\; \mathcal F \text{ a nonempty family of swap flats} \,\}`, ordered by **reverse inclusion**.

**Signed strata.** A **signed stratum** of `K^n` is a subspace of the form
```
X(Z; B_1,ε^1; … ; B_r,ε^r)  =  { x : x_i = 0 (i ∈ Z);  x_i = ε^t_i·u_t  (i ∈ B_t) },   ε^t_i ∈ {±1},
```
for a partition `\{1,\dots,n\} = Z \sqcup B_1 \sqcup\cdots\sqcup B_r` (`Z` possibly empty) and sign vectors `ε^t` taken up to a global flip within each block. These are exactly the flats of the type-`B_n` reflection arrangement, i.e. the elements of the **Dowling lattice** `Q_n(\mathbb Z/2)`, ordered by reverse inclusion.

---

# 2 · TWO FACTS ALREADY PROVED (recalled, not re-proved here)

> **Fact A (Signed-stratum classification).** Every element of `\mathcal L(\mathcal W)` is a signed stratum; hence `\mathcal L(\mathcal W) \subseteq Q_n(\mathbb Z/2)` as a set, and `\mathcal L(\mathcal W)` is closed under intersection.
> *Sketch:* each swap flat is an intersection of hyperplanes `x_i \pm x_j = 0`, hence a `B_n`-flat. Intersecting two signed strata either **merges** blocks (propagating signs transitively) or, on a sign conflict `u = -u`, **annihilates** that block into `Z`, using `\operatorname{char} K \neq 2`. ∎

> **Fact B (Self-similarity).** Every interval of `\mathcal L(\mathcal W)` is again the intersection poset of a swap arrangement, on **fewer indices**. *Downward from `X`:* with `Z` set to zero, what remains is the same construction on the block indices. *Upward to `X`:* the swap flats contained in `X` are the swap flats of the restricted arrangement.

**Fact B is what makes an induction on `n` possible, and it is the reason a statement about one order complex suffices.**

---

# 3 · ★ THE CLOSURE THEOREM

## 3.1 · The domain
Not every signed stratum is contained in a swap flat: a stratum of dimension `> k` cannot be. Define
> `\;\mathcal D \;:=\; \{\, D \in Q_n(\mathbb Z/2) \;:\; D \subseteq F \text{ for at least one swap flat } F \,\}`.

**Lemma 3.1.** `\mathcal D` is a **filter** of `Q_n(\mathbb Z/2)` (an up-set in the reverse-inclusion order), and `\mathcal L(\mathcal W) \subseteq \mathcal D`.
*Proof.* If `D \subseteq F` and `D' \subseteq D` then `D' \subseteq F`; in reverse-inclusion order that is exactly upward closure. The second claim holds because every element of `\mathcal L(\mathcal W)` is an intersection of swap flats, hence contained in each of them. ∎

**Lemma 3.2.** `\mathcal D = \{D \in Q_n(\mathbb Z/2) : \operatorname{rank} D \geq \rho\}` for `\rho := n-k`, i.e. **`\mathcal D` is a rank-selected subposet of `Q_n(\mathbb Z/2)`** — the selection being the *upper* rank interval.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 11, informe 139) — Lema 3.2 FALSO** (`VIVOS/EL_CATALOGO_MAESTRO`, entrada `v250.a`; `MOCHILA v121` tumba `O21`). Contraejemplo `k=2`, `n=6`: el estrato `D = {x_1=0, x_2=x_3, x_4=x_5=x_6}` tiene `dim 2`, luego `rank D = 4 = ρ`, y **ningún swap flat lo contiene** (todo swap flat de `k=2` tiene un bloque antipodal de dos coordenadas, que sobre `D` exigiría dos ceros). Comprobado a mano por Grepy. Todo estrato con `|Z|` impar y `dim ≤ k` queda fuera de `𝒟`.

*Proof.* `\subseteq`: `D \subseteq F` forces `\dim D \leq \dim F = k`, i.e. `\operatorname{rank} D \geq n-k`. `\supseteq`: let `D` be a signed stratum with `\dim D \leq k`. Extend the partition underlying `D` to one of the shape of a swap flat: merge blocks and empty `Z` by choosing, for each index in `Z`, a partner and a sign, and coarsening blocks until the shape is [one balanced 4-block `+` `(k-1)` 2-blocks]; every such coarsening yields a signed stratum **containing** `D`, and at least one has the swap shape because `\dim D \leq k` leaves enough room. Hence `D \in \mathcal D`. ∎

*(Lemma 3.2 is the step where the specific combinatorics of the swap shape enters; everything after it is formal.)*

## 3.2 · The operator
> **Definition.** For `D \in \mathcal D` set `\;c(D) := \bigcap \{\, F : F \text{ a swap flat},\ F \supseteq D \,\}`.
The family is nonempty by definition of `\mathcal D`, so `c(D)` is a well-defined element of `\mathcal L(\mathcal W)`.

> ### **THEOREM 3.3 (Closure).** `c : \mathcal D \to \mathcal D` is a **closure operator**, and `c(\mathcal D) = \mathcal L(\mathcal W)`.

**Proof.** Three properties, in the reverse-inclusion order (`D \leq D'` means `D \supseteq D'`).
- **Extensive:** `D \subseteq c(D)` is false in general — rather `c(D) \subseteq D`? No: `c(D)` is an intersection of subspaces each containing `D`, hence `D \subseteq c(D)`. In reverse-inclusion order this reads `c(D) \leq D`, so `c` is **decreasing**; equivalently `c` is a *closure operator for the opposite order*, i.e. an **interior operator** on `\mathcal D`. *(Both cases are covered by the cited lemma; see the remark below.)*
- **Monotone:** if `D \subseteq D'` then every swap flat containing `D'` contains `D`, so the intersection defining `c(D)` runs over a **larger** family, giving `c(D) \subseteq c(D')`. Order-preserving. ✓
- **Idempotent:** `c(D)` is itself an intersection of swap flats, and the swap flats containing `c(D)` are exactly those containing `D` (any `F \supseteq D` satisfies `F \supseteq c(D)` by definition of the intersection, and conversely `F \supseteq c(D) \supseteq D`). Hence `c(c(D)) = c(D)`. ✓
- **Image:** `c(D) \in \mathcal L(\mathcal W)` by construction; and every `X \in \mathcal L(\mathcal W)` satisfies `c(X) = X` by the idempotence computation, so `X \in c(\mathcal D)`. Hence `c(\mathcal D) = \mathcal L(\mathcal W)`. ∎

> **Remark (orientation).** Björner's lemma applies verbatim to closure operators and, by passing to the opposite poset — which has the same order complex — to interior operators as well. **The order complex is insensitive to the orientation of the order**, so no generality is lost.

## 3.3 · The homotopy equivalence
> **CLASSICAL INPUT 1** *(Björner, "Topological methods", Handbook of Combinatorics, Cor. 10.12).* If `f : P \to P` is a closure operator on a poset `P`, then `\Delta(P) \simeq \Delta(f(P))`.

> ### **COROLLARY 3.4.** `\;\Delta(\mathcal L(\mathcal W)) \;\simeq\; \Delta(\mathcal D)`.

---

# 4 · ★ CONCLUSION: `\mathcal L(\mathcal W)` IS COHEN–MACAULAY

> **CLASSICAL INPUT 2** *(Dowling 1973).* `Q_n(G)` is a **geometric lattice** for every finite group `G`; for `G = \mathbb Z/2` it is the intersection lattice of the type-`B_n` reflection arrangement.
> **CLASSICAL INPUT 3** *(Björner, Trans. AMS 260 (1980)).* Geometric lattices are **EL-shellable**, hence **Cohen–Macaulay**; and an EL-labelling induces a shelling on every **rank-selected** subposet.
> **CLASSICAL INPUT 4** *(Baclawski, J. Algebra 63 (1980), Thm 6.4).* **Rank-selection preserves Cohen–Macaulayness:** a rank-selected subposet of a CM poset is CM, so its order complex has reduced homology concentrated in the top dimension.

Combining: `Q_n(\mathbb Z/2)` is geometric (Input 2), hence CM (Input 3); `\mathcal D` is a rank-selected subposet of it (Lemma 3.2), hence CM (Input 4); and `\Delta(\mathcal L(\mathcal W)) \simeq \Delta(\mathcal D)` (Corollary 3.4). By **Fact B** the same argument applies verbatim to every interval of `\mathcal L(\mathcal W)`, since each is again the intersection poset of a swap arrangement on fewer indices.

> # **THEOREM 4.1.** `\mathcal L(\mathcal W)` **is Cohen–Macaulay.** Consequently the reduced homology of the order complex of every interval vanishes below the top dimension, and **Reisner's criterion holds for `\mathcal W`, for every `k`.**

## 4.1 · The signature, measured
A CM poset has reduced homology concentrated in the top dimension — a wedge of top-dimensional spheres. Measured, independently of everything above:
| `k` | `\dim \Delta` | below top | top |
|---|---|---|---|
| 2 | 1 | `\tilde H_0 = 0` | `\tilde H_1 = 66` |
| 3 | 2 | `\tilde H_0 = \tilde H_1 = 0` | `\tilde H_2 = 3807` |
> **The predicted signature is confirmed in both dimensions where it has been computed.**

---

# 5 · WHAT THIS FEEDS *(chain proved elsewhere; stated for orientation only)*
`\mathcal W` arithmetically CM `\Longrightarrow` `\tilde A` CM, where `A = C_0/I(\mathcal W)` and `C_0` is a Gorenstein complete intersection `\Longrightarrow` `Q \cong ω_{\tilde A}` is maximal Cohen–Macaulay `\Longrightarrow` `\operatorname{depth} Q \geq k` `\Longrightarrow` a generation-degree bound is mechanised into finitely many cell checks per `k` `\Longrightarrow` **three of the four bands of the Chaise Longue conjecture close, for all `k`.**

---

# 6 · GRADE, HONESTLY
| item | grade |
|---|---|
| Fact A, Fact B | **PROVED** (elsewhere in this campaign) |
| Lemma 3.1 | **PROVED** |
| **Lemma 3.2** (`\mathcal D` is rank-selected) | **PROVED**, and it is *the* step where the swap combinatorics enters — **the one to audit first** |
| Theorem 3.3 (closure) | **PROVED** |
| Corollary 3.4, Theorem 4.1 | **PROVED**, given Inputs 1–4 |

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 11, informe 139) — Teorema 4.1 (`𝓛(𝒲)` CM) CAE con el Lema 3.2:** `𝒟` es un filtro estrictamente menor que el rank-selected, y la CM de un filtro general no es clásica. Sobreviven Fact A, Lema 3.1, Teorema 3.3 en sustancia y Corolario 3.4 (`CATÁLOGO v250.a`).

| Classical Inputs 1–4 | **literature**, cited by author, journal and year |
| Signature `66 / 3807` | **MEASURED**, `2/2`, consistent |
> ### **Nothing here is measured-and-sold-as-proved.** The single point of exposure is **Lemma 3.2**: if `\mathcal D` failed to be exactly a rank-selected subposet, Input 4 would not apply and the argument would need the CM-ness of a general filter, which is *not* classical. **That lemma is where a referee should look first, and where I would look first.**

---
*Standalone. Nothing on this page depends on any other document of the campaign except Facts A and B, which are stated in full.*
