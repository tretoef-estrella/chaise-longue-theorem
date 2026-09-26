> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE RECOGNITION THEOREM (all dimensions)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_RECOGNITION_THEOREM_ALLK.md
>
> **Status, as written in the document:** A standalone component of The Chaise Longue Theorem — the extension of the Sofa Theorem (Degtyarev–Shimada Conjecture 1.2 for the 3^v Fermat tower) to all even dimensions 2k. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE RECOGNITION THEOREM (all dimensions)
## Window syzygies decouple sheet by sheet in every even dimension: the census is q-free ∀k

*A standalone component of **The Chaise Longue Theorem** — the extension of the Sofa Theorem (Degtyarev–Shimada Conjecture 1.2 for the 3^v Fermat tower) to all even dimensions 2k. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*

---

**Scope.** Proven in full for every k ≥ 1, every tower level q = 3^v, and every coefficient degree e < q. It makes the middle-window syzygy census a fixed, q-independent, finite linear-algebra problem in every even dimension. It is the k-uniform extension of the Sofa's Recognition Theorem (k = 2). It does not by itself close the main theorem; it is the solving tool for the window census at all k.

---

### 0. Setting

`S = F₃[x₀,…,x_{n−1}]`, `n = 2k+2`. `E = (e₁, e₃, …, e_{2k+1})` the ideal of odd elementary symmetric polynomials, which is radical with `E = I(∪_J L_J)` (the Radicality Theorem, all k), where the `(2k+1)!!` linear sheets `L_J = {x_a + x_b = 0 : {a,b} ∈ J}` range over the perfect matchings `J` of the complete graph `K_n`. Write `R = S/E`, `q = 3^v`. For an edge `{a,b}` of `K_n`, let `V({a,b}) = ∪_{J ∋ {a,b}} L_J` (the union of the `(2k−1)!!` sheets whose matching contains the edge) and `I({a,b}) = I(V({a,b}))`.

**Lemma 0 (the edge ideal, all k).** `I({a,b}) = (x_a + x_b) + (ε₁, ε₃, …, ε_{2k−1})`, where `ε_j` is the j-th elementary symmetric polynomial of the `2k` variables other than `x_a, x_b`.
*Proof.* Every sheet through the edge lies in the hyperplane `H = {x_a + x_b = 0}`; restricted to `H`, its residual `k` pairs form a matching-sheet of the `K_{2k}` on the remaining `2k` variables. The union of the `(2k−1)!!` such sheets is a cylinder (free in `x_a`) over the `K_{2k}` arrangement, whose radical ideal is `(ε₁, ε₃, …, ε_{2k−1})` — the Radicality Theorem in `n−2` variables. Since `S/((x_a+x_b) + I′) ≅ (S′/I′)[x_a]` is reduced, the sum is radical and equals `I(V({a,b}))`. ∎

### 1. The Recognition Theorem

> **Theorem R (all k).** Let `q = 3^v` and let `λ = (λ₀, …, λ_{n−1})` be homogeneous of degree `e < q`. Then
> `Σ_{i} λ_i · x_i^q ∈ E  ⟺  λ_a − λ_b ∈ I({a,b})` for every edge `{a,b}` of `K_n`.
> The right-hand condition does not involve `q`: **for `e < q`, the window syzygy space is canonically independent of the tower level, in every even dimension.**

*Proof.* `F := Σ λ_i x_i^q ∈ E ⟺ F` vanishes on every sheet (`E` radical). Fix a sheet `L_J` with pairs `(a_m, b_m)`, `m = 1..k+1`, and sheet coordinates `u_m := x_{a_m}|_{L_J}`; then `x_{b_m}^q = −u_m^q` (q odd), so
`F|_{L_J} = Σ_{m} (λ_{a_m} − λ_{b_m})|_{L_J} · u_m^q`.
Each summand is `u_m^q · g_m` with `deg g_m = e < q`. Two monomials `u_m^q·μ` and `u_l^q·μ′` (`m ≠ l`, `deg μ, μ′ = e < q`) cannot coincide: agreement would require an exponent `≥ q` in two distinct slots, impossible at total degree `q + e < 2q`. Hence the `k+1` summands have pairwise disjoint monomial supports, and `F|_{L_J} = 0 ⟺ (λ_{a_m} − λ_{b_m})|_{L_J} = 0` for each `m`. Collecting the condition over the `(2k−1)!!` sheets through a fixed edge `{a,b}` gives exactly `λ_a − λ_b ∈ I({a,b})` (Lemma 0). The conditions are linear constraints on degree-`e` forms with no reference to `q`. ∎

**Remark (the two ingredients are genuinely k-uniform).** The decoupling is pure degree arithmetic (`q + e < 2q`) — it never uses the dimension. Lemma 0 is the Radicality Theorem one dimension down. Neither step degrades as `k` grows; the tower vanishes from the census side at every even dimension.

### 2. Corollaries

**Corollary 1 (q-free census).** For each `e ≥ 0` and each `k`, the dimension `σ_e(k) := dim Syz_e / (trivial)` is a fixed integer independent of the tower level, and for every `q > e`:
`dim (m^{[q]}R)_{q+e} = (n−1)·HF(R)_e − σ_e(k)`.
The graded Hilbert function of the gap ideal throughout the window is independent of the tower level, in every even dimension.

**Corollary 2 (the universal Newton class).** For every `k ≥ 2`, `σ_2(k) = 1`, generated by `λ_i = x_i²`: then `λ_a − λ_b = (x_a+x_b)(x_a−x_b) ∈ I({a,b})`. This is the degree-`(q+2)` syzygy `p_{q+2}`, the same class in every dimension. (For `k = 1` the residual `K_2` carries a single `ε`, and `σ_2(1) = 3`; `k = 1` is the degenerate exception.)

### 3. Anchors (byte-verified over F₃)

Validation against the Sofa (k = 2), reproduced from scratch by the edge-condition linear system: `dim M_e = 1, 11, 52, 171` and `σ_e(2) = 0, 0, 1, 5, 25` (e = 0..4) — the Sofa's sealed certificate.
Fresh measurements: `σ_e(3) = 0, 0, 1, 7, 29, 90` (e = 0..5); `σ_e(4) = 1, 9` (e = 2, 3). Closed law for `k = 1`: `σ_e(1) = 3(e−1)` for `e ≥ 2`, verified `e = 0..7` against the full `q = 9` tower window (8/8). The standard-representation values `σ_3(k) = n − 1 = 5, 7, 9` (k = 2, 3, 4) are the Newton class times the linear forms.

**Status.** Pencil argument valid for all k and all v; the census values are finite gated certificates on q-free objects. The closed bivariate law `σ_e(k)` for the tail (`e ≥ 4`, the analogue of the Sofa's `15e²−90e+145`) is not yet in closed form; measured points are recorded above. Not yet refereed by a human expert.
