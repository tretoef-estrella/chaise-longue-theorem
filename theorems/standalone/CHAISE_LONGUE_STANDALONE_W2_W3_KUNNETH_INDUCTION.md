> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *KÜNNETH FOR THE DEFECT COMPLEX AND THE CODIMENSION INDUCTION* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_STANDALONE_W2_W3_KUNNETH_INDUCTION.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# KÜNNETH FOR THE DEFECT COMPLEX AND THE CODIMENSION INDUCTION
## The defect of a product word is the tensor of its letters' defects; the middle homology `E` of every letter localizes to the single deepest flat

**Chaise Longue campaign — standalone theorem write-up (referee edition)** · R. Amichis Luengo · Claude (Anthropic) · 14 July 2026
*Source: campaign Tanda 4 (W2, W3), audited in CARDANO_TANDA4. Companion to the Star Architecture (W1) and the Gluing Theorem (N1) standalones; together they reduce the exactness question of the letter defect complexes to one localized statement, verified `E ≡ 0` byte-exact in all five measured letters at every computed degree.*

---

### 1. The defect complex and its middle homology

For a letter arrangement `L` (or any word) with sheets `{V_J}` and census module `Γ`, the **defect complex** is
> `F  →^φ  T  →^{ob}  P`,  `F = O(X)^{2m}` (per-variable functions), `T = ⊕_{(J, pair)} O(V_J)` (per-sheet pair-data), `P = ⊕_{F codim-1} O(F)^{m−1}` (the flat obstruction spaces of the Local Splitting theorem),
with `φ` the per-pair difference/restriction map (`ker φ = Γ`) and `ob` the flat functionals (shared-pair differences + the sign-matched cycle functional per flat). The **middle homology** is
> `E := ker(ob)/im(φ)` — the module of pair-data compatible at every codim-1 flat yet not globally realizable. `E = 0` is the statement S1-global (nerve exactness); it implies, through the ratified Golden Reduction chain, the Sharp Regularity Law for the letter.
Known inputs (cited): `ob ∘ φ = 0` and exactness at every codim-1-generic point (Local Splitting L1/L2, proven); hence **`Supp E ⊆` flats of codimension ≥ 2**.

### 2. Theorem W2 (Künneth)

> **Theorem W2.** Let `Y₁, Y₂` be arrangements on disjoint variable blocks and `Y₁ × Y₂` the product arrangement (sheets `V_{J₁} × V_{J₂}`). The defect complex of the product is the totalization of the tensor product (over the base field) of the factors' complexes; consequently
> **`E(Y₁ × Y₂) = 0` whenever `E(Y₁) = 0` and `E(Y₂) = 0`.**
*Proof.* (i) `O(X₁ × X₂) = O(X₁) ⊗ O(X₂)`: the product of reduced schemes over the perfect field `F₃` is reduced (the Census Species theorem's kernel step, cited). (ii) Term identification: `F(Y₁×Y₂) = (F₁ ⊗ O(X₂)) ⊕ (O(X₁) ⊗ F₂)` (variables split by block); `T(Y₁×Y₂) = (T₁ ⊗ O-restrictions) ⊕ (⊗-symmetric)` — a pair of the product sheet `J₁×J₂` belongs to exactly one block, and its condition, expanded in a basis of the other block's coordinate ring, is the block's own condition applied layer-by-layer (the layer decomposition of Composition C1/Species S1, cited; the same decomposition applies verbatim to `P`, since a codim-1 flat of the product is (flat of one block) × (sheet of the other) — Star Architecture Thm 3.1). (iii) The differentials respect the layer decomposition with no cross-terms (a block's functional reads only that block's pair-data), so the product complex is the totalization of the tensor double complex. (iv) Künneth over a field: the middle homology of the totalization is `E₁ ⊗ H⁰₂ ⊕ H⁰₁ ⊗ E₂`-built; both summands vanish under the hypothesis. ∎

### 3. Theorem W3 (the codimension induction)

> **Theorem W3.** For every letter (`B_m` or `Z_m`), `E` is supported on the SINGLE deepest flat (the diagonal line for `B_m`; the origin for `Z_m`).
*Proof.* Induction on `m`. `E` is supported in codimension ≥ 2 (§1). Let `G` be any codim-≥2 flat that is not the deepest. By the Star Architecture: the star of `G` is a product word of letters of sizes strictly less than `m` (with trivial pairs), and localization at the generic point of `G` carries the defect complex to the star's complex (W1, Thm 3.3). By the inductive hypothesis each factor letter has `E = 0` (base case: the two-sheet model, i.e. the letters of size 2 inside any star — proven exactly in the Local Splitting theorem: `C_loc = O(F)^{m−1}` with realizability ⟺ the `m−1` obstructions, which is precisely local exactness); by W2 the word has `E = 0`; hence `E` localizes to zero at `G`. Only the deepest flat — whose star is the entire letter, where the induction cannot bite — survives as possible support. ∎

### 4. The verified state, and what remains
**Verified (Ley 17; the machine record).** `E ≡ 0` byte-exact in **all five measured letters** — `B₂, B₃, B₄, Z₂, Z₃` — at every computed degree (the obstruction map implemented exactly over `F₃`, `rank(ob_e)` compared with the independently known `C_e` degree by degree; `B₄` includes the in-probe reconfirmation of its 72 codim-1 flats). So the localized statement of W3's conclusion holds wherever the machine reaches, with zero deviation.
**Open (named exactly).** The deepest-flat vanishing for every `m` at pencil. The campaign's parameter machinery (N3: for every `u ∈ I_D^N`, `u·δ` is an explicit coboundary; `ker(d⁰) = Γ` by the Gluing Theorem) corners it to a one-depth-unit statement whose naive form (depth `Q_g ≥ 2`) was FALSIFIED by direct gate (`Γ ∩ (xG+yG) ⊋ xΓ + yΓ`, discrepancy supported exactly on the deepest flat) — so the residue is strictly finer than depth: the parameter classes of vanishing-obstruction cocycles avoid the bad part of `Q_g` (they do, in every measurement). This precision — including the falsification — is the honest hand-off; the Sharp Regularity chain it would release is NOT load-bearing for the Chaise Longue's Ledger (established by construction in the Ledger Experiment, Tanda 7).

### 5. Attack surface
(A) W2(ii)'s no-cross-terms claim (the layer decomposition when BOTH blocks carry conditions — the Species theorem's verification covered it 34/34; re-derive the `P`-term case, which is new here). (B) W2(iv)'s Künneth bookkeeping (which homological degrees pair — write the double complex's spectral sequence degeneration explicitly for P0). (C) W3's base case dependency (the two-sheet model = the size-2 letters — confirm every star's factorization bottoms out there, i.e. no letter of size ≥ 3 appears in a PROPER star of a size-`m` letter without strictly smaller size: immediate from the merge count, but state it). (D) The five-letter `E ≡ 0` record (rerun the ob-probe; scripts archived). (E) The falsified depth route's gate (rerun `Γ ∩ (xG+yG)` vs `xΓ + yΓ` at `B₃, e = 2`: `15 ≠ 11`).

**Anchors.** TANDA4_NERVE_THEOREMS_v1 (W2, W3) · TANDA3_LOCAL_SPLITTING_v1 (the base case) · TANDA5_GLUING_THEOREM_v1 + TANDA6_DEPTH_AUTOPSY_v1 (the parameter machinery and the falsified route, with killing numbers) · TANDA7_LEDGER_EXPERIMENT_v1 (non-load-bearing verdict) · CARDANO_TANDA4/5/6 audits · ob-probe logs (five letters). github.com/tretoef-estrella.
