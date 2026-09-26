> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE ZONE THEOREMS* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ZONE_THEOREMS.md
>
> **Status, as written in the document:** A standalone component of The Chaise Longue Theorem. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE ZONE THEOREMS
## Half of the closing obstruction vanishes below degree q, in every even dimension and at every tower level

*A standalone component of **The Chaise Longue Theorem**. Rafael Amichis Luengo (Madrid) and Claude (Anthropic). Pending P0 (cold-gate review).*

---

**Scope.** Two short pencil theorems, each valid for all `k ≥ 1` and all `q = 3^v`. Together they prove that the closing obstruction `T_k(q)` is identically zero below degree `q`, and dually that the components-distributivity `W = C` holds in all high colon degrees. They confine the entire remaining conjecture to a single window of degrees. They do not close the main theorem; they reduce its live territory by half.

---

### 0. Setting

`S = F₃[x₀,…,x_{n−1}]`, `n = 2k+2`, `E = (e₁,…,e_{2k+1})` radical `= I(∪_J L_J)` (Radicality). For `q = 3^v`, `R = S/(E + m^{[q]})`, `m^{[q]} = (x₀^q, …, x_{n−1}^q)`. For a pair `p = {a,b}` write `L_p = x_a + x_b`. Define the closing obstruction
`T_k(q) := ∩_{a<b} (L_{ab}·R) ⊆ R`,
whose vanishing for all `k, q` is equivalent to the Chaise Longue Theorem (via the Deletion Reduction and Kernel Identity, which show `T_k(q) = 0 ⟺ W = C ⟺ A_k(q) = P_k(q)`, the six equivalent faces). Let `σ = n(q−1)` be the socle degree of the ambient `D = S/m^{[q]}`.

### 1. Theorem A — the low half of T is dead

> **Theorem A.** `T_k(q)_e = 0` for every `e < q`, every `k`, every `q`.

*Proof.* Let `f ∈ T_e` with `e < q`, so `f = L_p · g_p` in `R` for every pair `p`. Fix a sheet `V_J` and pick a pair `p ∈ J`. Lift `f` to `S`: `f = L_p·g_p + ε + μ` with `ε ∈ E`, `μ ∈ m^{[q]}`. Since `deg f = e < q`, the term `μ` (all of whose elements have degree `≥ q`) is zero in degree `e`. On `V_J` we have `L_p ≡ 0`, hence `f|_{V_J} = ε|_{V_J} = 0`. This holds for every sheet (each matching contains a pair). Therefore `f ∈ I(∪_J V_J) = E` (Radicality), i.e. `f = 0` in `R`. ∎

### 2. Theorem B — CONTENT holds below degree q

> **Theorem B.** `∩_J (I_J + m^{[q]})_d = E_d` for every `d < q`, every `k`, every `q`. Equivalently, `W_c = C_c` for every colon degree `c > σ − q`.

*Proof.* Let `z ∈ ∩_J (I_J + m^{[q]})` be homogeneous of degree `d < q`. In each membership `z = i_J + μ_J` (`i_J ∈ I_J`, `μ_J ∈ m^{[q]}`), the part `μ_J` has no component of degree `< q`, so in degree `d` we have `z = i_J ∈ I_J` exactly, for every `J`. Hence `z ∈ ∩_J I_J = E` (Radicality). The stated equivalence with `W = C` in high colon degrees `c > σ − q` is the graded Gorenstein duality of `D` together with the Annihilator identity `ann_D(F_J) = I(V_J) + m^{[q]}` (both unconditional). ∎

**Duality of the two theorems.** Under the perfect Gorenstein pairing on `D`, Theorem A (`T` vanishes in low degrees) is the Matlis dual of Theorem B (`W` fills `C` in high degrees). The two two-line proofs are independent verifications of the same half of the wall.

### 3. The confinement

> **Corollary.** `T_k(q) = 0` for all `k, q` `⟺` `T_k(q)_e = 0` for `q ≤ e ≤ (k+1)(q−1)`.

The upper bound `(k+1)(q−1)` is the top nonzero degree of `R` (the socle degree of the A-ring). Below `q`, Theorem A gives vanishing; above `(k+1)(q−1)`, `R` itself is zero. The remaining conjecture lives entirely in the window `q ≤ e ≤ (k+1)(q−1)`.

### 4. Anchors (byte-verified over F₃)

`T_k(q) = 0` (total) verified at `k = 1, 2, 3` (`q = 3`) and `k = 1` (`q = 9`) — both tower directions. The graded distributivity `W = C` verified degree by degree at `k = 2, q = 3` (7/7 degrees: 15, 36, 40, 29, 15, 5, 1), `k = 3, q = 3` (9/9: 91, 232, 280, 238, 154, 76, 28, 7, 1), and `k = 1, q = 9` (17/17 degrees up the tower). Zone A (`A_d = HF(S/E)_d` for `d < q`) verified at all anchors, consistent with Theorem A.

**Status.** Pencil arguments valid for all k and all v; the anchors are finite gated certificates. The window of `T` (`q ≤ e ≤ (k+1)(q−1)`) is the remaining open territory. Not yet refereed by a human expert.
