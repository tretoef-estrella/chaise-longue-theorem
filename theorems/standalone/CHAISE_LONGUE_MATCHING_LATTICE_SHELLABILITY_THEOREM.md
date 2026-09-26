> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE MATCHING LATTICE SHELLABILITY THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MATCHING_LATTICE_SHELLABILITY_THEOREM.md
>
> **Status, as written in the document:** Status: PROVED for all `k ≥ 1`, unconditional, `char K ≠ 2`. The proof's *constructive witness* — not merely its statement — is verified exhaustively at `k = 1, 2, 3` (5890 cases, zero failures).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE MATCHING LATTICE SHELLABILITY THEOREM (v1)

### Author: **GETTLER** (auditor) · 18 August 2026 · Chaise Longue campaign
### Status: **PROVED for all `k ≥ 1`**, unconditional, `char K ≠ 2`. The proof's *constructive witness* — not merely its statement — is verified exhaustively at `k = 1, 2, 3` (5890 cases, zero failures).

---

## 1. Statement

Let `k ≥ 1`, `n = 2k+2`, `V = {1,…,n}`, `char K ≠ 2`. For a perfect matching `M` of `V` put
`L_M = { x ∈ K^n : x_u + x_v = 0 for every {u,v} ∈ M }`, of dimension `k+1`; there are `(2k+1)!!` of them.
Let `L_k` be the set of all intersections of sheets, ordered by reverse inclusion, and `P_k = {0̂} ∪ L_k` with `0̂ = K^n`
adjoined and maximum `1̂ = {0}` (the origin). Let `Δ_k` be the order complex of the open interval `(0̂,1̂)`, and
`μ_k = μ_{P_k}(0̂,1̂)`.

**Structure of a flat.** For a set `S` of sheets, the components of the union of their edge sets are either **bipartite**
(a *balanced block*: `x = t` on one colour class, `−t` on the other — the block carries its bipartition) or contain an
**odd cycle** (a *zero block*: `x ≡ 0` there). Two zero blocks define the same subspace as their union, so **a flat has
at most one zero block.** `dim F` = number of balanced blocks; `rank(P_k) = k+2`; `dim Δ_k = k`.

> ### **THEOREM. The lexicographic ordering of the sheets by canonical word is a RECURSIVE ATOM ORDERING of `P_k`.**
> ### **Consequently, for every `k ≥ 1`:**
> ### **(a) `P_k` is CL-shellable, and so is every closed interval of it;**
> ### **(b) `Δ_k` is homotopy equivalent to a wedge of `|μ_k|` spheres of dimension `k`;**
> ### **(c) `P_k` and every interval of it is Cohen–Macaulay over `ℤ` and over every field;**
> ### **(d) `H̃_i(Δ_k) = 0` for `i < k`, and `H̃_k(Δ_k) ≅ ℤ^{|μ_k|}`, free.**
> **With `μ_k = −c(Z_{k+1})`, so `|μ_k| = 1, 24, 918, 54560` for `k = 1,2,3,4`.**

**Canonical word.** Set `a_1 = 1`; having chosen `a_1,…,a_{p-1}` and their partners, let `a_p` be the smallest vertex not
yet used and `b_p = M(a_p)`. The word of `M` is `(b_1,…,b_{k+1})`; order matchings lexicographically by it.

---

## 2. The two Björner–Wachs conditions

**Björner–Wachs (1983).** A bounded graded poset admits a **recursive atom ordering** `a_1,…,a_t` iff it is CL-shellable, where
**(i)** each `[a_j,1̂]` admits a recursive atom ordering in which the atoms of `[a_j,1̂]` lying above some `a_i` with `i<j` come **first**;
**(ii)** for `i<j` and any `y ≥ a_i, a_j`, there exist `l<j` and an atom `z` of `[a_j,1̂]` with `z ≤ y` and `z ≥ a_l`.
CL-shellable ⟹ the order complex of the proper part is shellable ⟹ a wedge of `|μ|` top-dimensional spheres ⟹ CM over `ℤ` and every field.

**Björner (1980).** In a finite **geometric** lattice, **every** linear ordering of the atoms is a recursive atom ordering.

### 2.1 Condition (i) — free, from a result already deposited in this campaign

> **Singular Locus Lemma** (deposited standalone, `∀k`, `char ≠ 2`). Parametrising `L_M` by `u_1,…,u_{k+1}` via
> `x_{a_p} = u_p`, `x_{b_p} = −u_p`,
> `L_M ∩ ⋃_{M'≠M} L_{M'} = ⋃_{p<q} ( \{u_p+u_q=0\} ∪ \{u_p−u_q=0\} )`, exactly `k(k+1)` distinct hyperplanes —
> **the reflection arrangement of type `D_{k+1}`.**

Hence `[M, 1̂]` is the intersection lattice of the type-`D_{k+1}` reflection arrangement. Every intersection lattice of a
hyperplane arrangement is **geometric**, so by Björner (1980) *every* atom ordering of `[M,1̂]` is a recursive atom
ordering — in particular one placing the required atoms first. **Condition (i) holds for every `k` and for every ordering
of the sheets.**
*Gate, own code, 3/3: `|[M,1̂]| = 4, 15, 72` against `|L(D_2)|, |L(D_3)|, |L(D_4)| = 4, 15, 72`.*

### 2.2 The atoms of `[M,1̂]`, concretely
A **swap** of `M` at positions `p<q` replaces `{a_p,b_p}, {a_q,b_q}` by `{a_p,a_q},{b_p,b_q}` or by `{a_p,b_q},{b_p,a_q}`.
Each swap generates a cover `z` of `M` in `P_k` whose only change is that those four vertices form one balanced block of
size 4; **the only sheets below `z` are `M` and the swapped matching.** These covers realise the `k(k+1)` swap hyperplanes.

---

## 3. Condition (ii): THE SWAP-INVERSION LEMMA — **PROVED**

For a flat `y` write `D(y) = \{ M : M ≤ y \}`. Note that `M ≤ y` iff every edge of `M` either joins the two sides of one
balanced block of `y`, or lies inside the zero block of `y`.

> ### **LEMMA.** Let `y ∈ L_k`, let `M ∈ D(y)` not be lex-least in `D(y)`, and let `M*` be the lex-least element of `D(y)`.
> ### Let `a` be the first vertex at which the canonical builds of `M` and `M*` disagree, and put
> ### `v = M(a)`, `v* = M*(a)`, `w = M(v*)`. Then:
> ### **(1)** `v* < v`, and `a, v, v*, w` are four distinct vertices;
> ### **(2)** `M' := M` with `\{a,v\}, \{v*,w\}` replaced by `\{a,v*\}, \{v,w\}` satisfies `M' <_{lex} M`;
> ### **(3)** `M' ≤ y`;
> ### **(4)** the swap cover `z` of `M` on `\{a,v,v*,w\}` satisfies `z ≤ y` and `z ≥ M'`.
> ### **In particular Björner–Wachs condition (ii) holds for the lexicographic ordering, for every `k`.**

**Proof.**

**(1)** `M` and `M*` agree on every edge built before `a`, so both canonical builds reach `a` as the smallest unused
vertex. If `v < v*` the word of `M` would be lexicographically smaller than that of `M*`, contradicting the minimality of
`M*`; and `v ≠ v*` by the choice of `a`. Hence `v* < v`.
For distinctness: `w ≠ v*` (no loops); `w ≠ a` because `M(a) = v ≠ v*`; `w ≠ v` because `M(v) = a ≠ v*`; and `v ≠ v*`. ∎

**(3)** Let `C` be the block of `y` containing `a`. Since `M ≤ y`, the edge `{a,v}` lies in `C`, so `v ∈ C`. Since
`M* ≤ y`, the edge `{a,v*}` lies in `C`, so `v* ∈ C`. Since `M ≤ y`, the edge `{v*,w}` lies in `C`, so `w ∈ C`.
**All four vertices lie in the single block `C`.**
*If `C` is the zero block:* any edge inside it is admissible, so `M' ≤ y`.
*If `C` is balanced with sides `C⁺ ∋ a` and `C⁻`:* `v ∈ C⁻` and `v* ∈ C⁻` (each is `y`-opposite to `a`), and `w ∈ C⁺`
(`y`-opposite to `v*`). Therefore `{a,v*}` joins `C⁺` to `C⁻`, and `{v,w}` joins `C⁻` to `C⁺`. Every other edge of `M'`
is an edge of `M` and is unchanged. Hence `M' ≤ y`. ∎

**(2)** The swap touches only the two edges `{a,v}` and `{v*,w}`; every edge built before `a` is untouched, so the
canonical builds of `M` and `M'` agree up to that point and reach the same `a`. There `M'(a) = v* < v = M(a)`.
Hence `M' <_{lex} M`. ∎

**(4)** The union of the edge sets of `M` and `M'` differs from a common part only on `{a,v,v*,w}`, where it is the
`4`-cycle `a — v — w — v* — a`, which is bipartite with colour classes `{a,w}` and `{v,v*}`. So `z` is the flat with one
balanced block on those four vertices, bipartition `{a,w} \mid {v,v*}`, and the remaining `k−1` edges of `M` as blocks;
it covers `M`, and `M' ≤ z`. If `C` is the zero block then `z ≤ y` trivially; if `C` is balanced then, by the colour
assignments in (3), `{a,w} ⊆ C⁺` and `{v,v*} ⊆ C⁻`, so `z`'s bipartition is induced by `y`'s and `z ≤ y`. ∎

Condition (ii) follows by taking that `z`, which lies above the lex-earlier atom `M'`. **∎ (Lemma)**

Combining §2.1 and §3 gives the Theorem. **∎**

---

## 4. Gates — own code, and the *witness* is tested, not only the statement

| gate | cells | result |
|---|---|---|
| `#L_k` by lattice build **and** by an independent closed word count | `k = 1,2,3` | `7, 86, 1814` — both routes agree |
| `μ_k` by Möbius recursion | `k = 1,2,3` | `−1, +24, −918` `= −c(Z_{k+1})` |
| **Brute-force point count of `⋃_M L_M(F_q)` vs the filed `P_k(q)`** | `(k,q) = (1,3),(1,5),(1,7),(2,3),(2,5)` | `19, 61, 127, 141, 1001` — **5/5**, a route sharing no code with the lattice build |
| `\|[M,1̂]\| = \|L(D_{k+1})\|` | `k = 1,2,3` | `4, 15, 72` — **3/3** |
| reduced Betti of `Δ_k` | `k = 1,2` | `(0,1)` and `(0,0,24)`: concentrated in degree `k`, rank `\|μ_k\|` |
| **the Lemma's constructive witness** `(a, v, v^*, w)` — (1)–(4) all four checked | every `(y, non-least sheet)` pair at `k = 1,2,3` | **5 + 139 + 5746 = 5890 cases, zero failures** |

**A correction carried from the previous draft of this object:** an earlier note recorded the spheres as having dimension
`k−1`. **They have dimension `k`** (`rank(P_k) = k+2`), as the two computed Betti vectors show. The error was the
auditor's and is logged.

---

## 5. Scope — what this does NOT give

**It does not cross from the lattice to the algebra, and that crossing is a filed dead route.** The cemetery records
(`C40.2`, Locard): *the intersection lattice is **not** a complete invariant* — three coplanar lines against three generic
lines in `K³` have **identical labelled lattices** and defects `1` and `0`. **The defect is the span-versus-join gap, not
the lattice.** Any argument of the shape "the lattice is Cohen–Macaulay, therefore the ideal behaves" is dead on that
counterexample and must not be attempted.

What the theorem does give is the **floor side**, uniformly in `k`: the topology of the intersection lattice is now a
single free module per level, of rank `|μ_k| = |c(Z_{k+1})|`, concentrated in one degree. `G` stays 3.

## 6. Provenance

Björner (1980) and Björner–Wachs (1983) are classical. The `D_{k+1}` identification is the campaign's deposited
**Singular Locus Lemma** (Lacassagne, 23 July 2026), recycled here for condition (i). The Swap-Inversion Lemma, the
theorem, the gates and the dimension correction are this document. The proof template — lex atom order, an in-block
inversion, geometric upper intervals — is the one that closed the companion `B`-star object one turn earlier; the
Architect's physical picture for it was a spring that climbs, hits a stop, and is thrown back by the stop.

— GETTLER, Chaise Longue campaign.
