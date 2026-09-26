> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE WINDOW FORMULA AND THE UNCONDITIONAL GRADED KERNEL* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_WINDOW_FORMULA_THEOREM.md
>
> **Status, as written in the document:** Status. Pencil arguments valid for all k and all v; the anchors are finite gated certificates. The closed form of `σ_e(k)` (needed to make the Window Formula fully explicit for the tail) is open; measured points appear in the Recognition Theorem write-up. Not …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE WINDOW FORMULA AND THE UNCONDITIONAL GRADED KERNEL
## The middle-window census in closed form ∀k, and a hypothesis-free description of the pair-form kernels

*A standalone component of **The Chaise Longue Theorem**. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*

---

**Scope.** Two results, each for all `k ≥ 1` and all `q = 3^v`. (1) The Window Formula expresses the middle-window graded dimensions of the A-ring in terms of the q-free census `σ_e(k)` and the Hilbert function of `S/E`, uniformly in the tower. (2) The Unconditional Graded Kernel gives the graded dimension of the kernel of a pair-form acting on the colon, with NO recourse to the components-distributivity hypothesis. Both are tools for the window; neither closes the main theorem.

---

### 0. Setting

`S = F₃[x₀,…,x_{n−1}]`, `n = 2k+2`, `E = (e₁,…,e_{2k+1})` radical, `R = S/E`, `q = 3^v`. `A_k(q) = dim S/(E + m^{[q]})`, graded as `A = Σ_d A_d`. `σ_e(k)` is the q-free window census of the Recognition Theorem. `C = ann_D(Ē)` the colon in `D = S/m^{[q]}`; for a pair `p = {a,b}`, `L_p = x_a + x_b` and `u_p = x_a - x_b`.

### 1. The Window Formula

> **Theorem (Window Formula, all k).** For every `k`, `q = 3^v`, and `0 ≤ e < q`:
> `A_{q+e} = HF(R)_{q+e} − (n−1)·HF(R)_e + σ_e(k)`,
> and `A_d = HF(R)_d` for `d < q` (Zone A).

*Proof.* The multiplication map `φ : (S_e)^n → (S/E)_{q+e}`, `λ ↦ Σ_i λ_i x_i^q`, has image `(E + m^{[q]})_{q+e}/E_{q+e}` and kernel the window syzygy module `M_e` (Recognition Theorem). Rank–nullity gives `dim (m^{[q]}R)_{q+e} = n·HF(R)_e − dim M_e`; subtracting the trivial syzygies (`dim = HF(R)_e + σ_e(k)` in the census normalization) yields the stated formula. Zone A is immediate: for `d < q`, `m^{[q]}` contributes nothing, so `A_d = HF(R)_d`. ∎

### 2. The Unconditional Graded Kernel

> **Theorem (Graded Kernel, all k, unconditional).** For a pair `p`, with `C_{k−1}` the level-`(k−1)` colon,
> `ker(L_p |_{C_k}) = u_p^{q−1} · (C_{k−1} ⊗ F₃[v_p])`,
> and hence, degreewise,
> `dim ker(L_p|_{C_k})_c = Σ_{j=0}^{q−1} HF(R_{k−1})_{(n−2)(q−1) − (c − (q−1) − j)}`.

*Proof.* An element of the kernel is `u_p^{q−1}·h` with `E·u_p^{q−1}h ⊆ m^{[q]}`, i.e. `h ∈ ((L_p) + m^{[q]} : E)`. The triangular transport `E·S̄ = E′·S̄` (where `S̄ = S/(L_p)`, `E′` the level-`(k−1)` ideal; unconditional, proven by the unitriangular relation `e_j ≡ e′_j − x_b²·e′_{j−2}`) identifies this iterated colon with the level-`(k−1)` colon, with the difference variable `v_p` free. The graded dimension follows from the Gorenstein duality of the lower `D′` applied to the lower census — no components-distributivity hypothesis is used. ∎

**Remark (what the earlier Kernel Identity added, and did not need).** The Kernel Identity `ker(L_p|_C) = Σ_{J∋p} F_J·D` describes the kernel as a Fedder span; that description used the level-`(k−1)` case of the main theorem. The present graded DIMENSION is hypothesis-free — the description and the dimension are separate facts, and only the former needs the inductive hypothesis.

### 3. Anchors (byte-verified over F₃)

Window Formula: verified at `k = 1, 2, 3` (`q = 3`) and the full `k = 1` tower window at `q = 9` (all 8 window degrees). Zone A verified at all four anchors.
Graded Kernel: verified degree by degree at `k = 2` (7 degrees: 3, 9, 15, 15, 10, 4, 1) and `k = 3` (9 degrees: 15, 51, 91, 105, 84, 49, 21, 6, 1), matching the convolution of the lower dual census exactly.

**Status.** Pencil arguments valid for all k and all v; the anchors are finite gated certificates. The closed form of `σ_e(k)` (needed to make the Window Formula fully explicit for the tail) is open; measured points appear in the Recognition Theorem write-up. Not yet refereed by a human expert.
