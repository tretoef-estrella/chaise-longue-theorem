> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-05
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE BLOCK-NERVE CENSUS THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BLOCK_NERVE_CENSUS_THEOREM.md
>
> **Status, as written in the document:** This standalone supplies the combinatorial and representation-theoretic inputs for the collar slack law of the Chaise Longue program, uniform in `k`. It does not close any GAP by itself: it delivers the nerve invariants (`b₁` and `mult(sgn)`) that the deeper-s…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE BLOCK-NERVE CENSUS THEOREM (v1)

### The star nerves of the matching arrangement are Cartesian products of single-letter nerves; their cycle rank and their sign-multiplicity are closed and uniform in `k`.

**Constructor:** Frescales 12 (Fable) · **Auditor (independent re-verification in code):** Nash (Fable) · **Architect:** Rafa · 5 Aug 2026 · *Pending external cold-gate (P0).*

---

## STATUS, STATED FIRST (Ley 30/42)

This standalone supplies the **combinatorial and representation-theoretic inputs** for the collar slack law of the Chaise Longue program, uniform in `k`. It **does not** close any GAP by itself: it delivers the nerve invariants (`b₁` and `mult(sgn)`) that the deeper-stratum defect assembly (codim `≥ 3`, GAP A) must consume. What is new versus the deposited `eigenvector-law`/`UNIFORM_CENTRAL_DEFECT` (codim-2 only) is that **every letter of every codimension** now has its nerve homology determined by one closed formula. The word is not said.

**Grades:** the product law and the `b₁` forms are **PROVED ∀k** (elementary graph identities on the `W1` block model). `mult(sgn) = m−2` is **PROVED ∀m over ℚ** (pencil, three lemmas), and **verified over F₃ for `m ≤ 5`** (`F₃ = ℚ` at each), **CONJECTURE over F₃ for general `m`** (a small remaining brick; Lemma 1 makes the mod-3 argument clean since the edge character is an honest permutation character).

---

## 1. Setting

`char K = 3` (statements marked `char ≠ 2` hold generally), `q = 3^v`, `N = 2k+2`, `E = (e_1,e_3,…,e_{2k+1})`, sheets `V_J` over the perfect matchings `J` of `{0,…,2k+1}` with `I_J = (x_a+x_b : {a,b}∈J)`. By the Star Architecture (`W1`) every flat `L` of the arrangement is a **word of letters**: a partition of its support into **signed `2m`-blocks** (a connected 2-colored pair-graph, the two color classes of size `m`) and **zero `2z`-blocks** (`2z ≥ 4`, an odd-cycle component forcing all coordinates to `0`), the remaining points matched in trivial pairs.

For a flat `L`, its **star** `st(L)` is the set of sheets `V_J ⊇ L`, and its **nerve** `N(L)` is the graph on `st(L)` with an edge for each codimension-1 (single `2↔2` swap) meet. `h_L(t) = \dim(\mathcal O_L)_t` is the flat's Hilbert function.

## 2. The single-letter nerves

**Proposition 2.1 (single-block nerves — COMPUTED/PROVED).**
- A **signed `2m`-block**'s star is the `m!` sign-consistent matchings `= S_m`; two adjacent iff they differ by one transposition. Its nerve is the **Cayley graph `Cay(S_m, T)`**, `T` = all transpositions: `|V| = m!`, `|E| = m!\binom{m}{2}/2`.
- A **zero `2z`-block**'s star is the `(2z-1)!!` perfect matchings of `K_{2z}`, adjacent iff sharing all but one pair: the **matching graph `M(K_{2z})`**, `z(z-1)`-regular.

## 3. The product law (level-1 machinery)

**Theorem 3.1 (Product Law — PROVED ∀k).** For a flat with letters `B^{(1)},…,B^{(r)}`, the nerve is the **Cartesian graph product** of the single-letter nerves:
> `N(L) = N^{(1)} \,\square\, N^{(2)} \,\square\, \cdots \,\square\, N^{(r)}`.

*Proof.* A sheet through `L` is an independent choice of a compatible sheet on each block (matching pairs never cross blocks); a single `2↔2` swap re-pairs 4 points inside one block, so adjacent sheets differ in exactly one factor by a nerve edge of that factor — the definition of the Cartesian product. ∎

**Corollary 3.2 (cycle rank, closed and uniform — PROVED ∀k).** With `V_i = |V(N^{(i)})|`, `E_i = |E(N^{(i)})|` and each factor connected (`T` generates `S_m`; `M(K_{2z})` connected for `z ≥ 2`):
> `b₁(N) = \big(\prod_i V_i\big)\big(\sum_i E_i/V_i - 1\big) + 1`,
and per single letter:
> `b₁(Cay(S_m,T)) = m!\cdot\dfrac{m(m-1)-4}{4} + 1` (values `m=2..6`: `0,4,49,481,4681`);
> `b₁(M(K_{2z})) = (2z-1)!!\cdot\dfrac{z(z-1)-2}{2} + 1` (values `z=2..4`: `1,31,526`).

*Gate (re-verified independently in code):* the six anchors `b₁ = 4, 1, 1, 13, 49, 31` for `B₃, B₂², Z₂, K(3,3)\square K_2, Cay(S_4,T), M(K_6)` are reproduced exactly.

## 4. The sign multiplicity (level-2 machinery)

Fix `t₀ = (0\,1)` and the **parity-twisted left-translation** `S_m`-action `π·σ = π∘σ∘t₀^{ε(π)}` on `Cay(S_m,T)` (`ε` = parity). This is the action pinned by the deposited `k=3` datum: it realizes `H₁(K(3,3)) = triv ⊕ sgn ⊕ std`, cross-gated by the filed collar constant `−26`. (Plain conjugation gives `0` and is **not** the theorem's action.)

**Theorem 4.1 (`mult(sgn) = m−2` — PROVED ∀m over ℚ).** `mult(sgn, H₁(Cay(S_m,T))) = m-2` for all `m ≥ 2`.

*Proof (three lemmas; every step re-verified in code, `m ≤ 6`).*
- **L1 (orientation is vacuous).** The action preserves vertex parity (`ε(π·σ) = ε(σ)`), and `Cay(S_m,T)` is bipartite by parity, so no edge is ever reversed: `χ_{C_1}(g) = \#\{\text{edges fixed pointwise}\}`, an honest permutation character.
- **L2 (who fixes edges).** Only `e` (fixes all `m!` vertices) and transpositions `g = στ₀σ^{-1}` (fixing `|C(t₀)| = 2(m-2)!` vertices) fix any vertex; an edge is fixed iff both ends are fixed and its transposition lies in `C(t₀)∩T` (size `1+\binom{m-2}{2}`). Hence `χ_{C_1}(\text{transp}) = (m-2)!\,(1+\binom{m-2}{2})`, `χ_{C_1}(e)=|E|`, else `0`.
- **L3 (the sum collapses).** With `[H_1]=[C_1]-[C_0]+[H_0]`, `⟨sgn,C_0⟩=0`, `⟨sgn,H_0⟩=0` (banked), `⟨sgn,H_1⟩ = ⟨sgn,C_1⟩ = \tfrac{m(m-1)}{4} - \tfrac12 - \tfrac{(m-2)(m-3)}{4} = m-2`. ∎

*Gate (re-verified in code, `m=2..6`):* `|F_g| = 2,2,4,12,48`; `χ_{C_1}(\text{transp}) = 1,1,4,24,168`; value `= 0,1,2,3,4`.

**Theorem 4.2 (composition — the sign lives on single letters; PROVED).** Under the pinned action the vertex module of every signed block contains no `sgn` (`⟨sgn,C_0⟩=0`, Lemma L2), so by the Künneth splitting for the Cartesian product,
> `mult(sgn, H₁(N^{(1)}\square N^{(2)})) = m_1 s_0(N_2) + s_0(N_1) m_2 + t(N_1)t(N_2)` with `s_0 = t = 0` for signed blocks,

hence **any flat with two or more nontrivial signed letters has `mult(sgn) = 0`**: the `sgn` weight is carried by **single-letter flats only**, with weight `m-2` for a signed-`2m` letter. *(Gate: `K(3,3)\square K_2` gives `b₁=13`, `mult(sgn)=0`, re-verified in code.)*

*Note on graph Künneth (correction banked):* for connected `G,H`, `H₁(G\square H) = (H₁G\otimes ℚ^{V_H}) ⊕ (ℚ^{V_G}\otimes H₁H) ⊕ (\tilde H_0 G\otimes \tilde H_0 H)`; the third (product-square) summand is required — omitting it undercounts (`8` vs the true `13` for `K(3,3)\square K_2`).

## 5. What this feeds, and what remains

For the collar slack law, a signed-`2m` letter contributes, per the deposited codim-2 mechanism (`UNIFORM_CENTRAL_DEFECT`, `eigenvector-law`): a **level-1** central term `b₁(nerve)·h_L` and a **level-2** correction weighted by `mult(sgn) = m-2`. This standalone makes **both weights closed and uniform in `k` for every letter of every codimension**. Two things remain, both named and open:
1. **The consumption at codim `≥ 3` (GAP A deeper strata):** proving the deeper-stratum defect is assembled from these nerve invariants exactly as codim-2 is (the `UNIFORM_CENTRAL_DEFECT` mechanism lifted one codimension down). Inputs now all in hand.
2. **`mult(sgn) = m-2` over F₃ for general `m`** (verified `m ≤ 5`): a small brick, expected clean from L1's permutation-character structure.

**Anchors.** `BLOCK_NERVE_SM_REP_REPORT_v1`, `SGN_EDGE_REP_ALLM_REPORT_v1` (constructor); independent code re-verification (auditor, `m ≤ 6`); consumes `W1` (Star Architecture), banked against `UNIFORM_CENTRAL_DEFECT_v1`, `eigenvector-law`, Hammock §4.2′. github.com/tretoef-estrella.
