> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_FIRST_MIDDLE_RUNG_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FIRST_MIDDLE_RUNG_THEOREM.md
>
> **Status, as written in the document:** Author: Marsh (Auditor). Grade: PROVED ∀k, char ≠ 2, gated byte-exact. Supersedes the *conditional* status of CATÁLOGO v130/v131.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_FIRST_MIDDLE_RUNG_THEOREM_v1
### The first middle-zone socle rung, made unconditional: `soc(A)_{q−1}=0` for all `k`, char-free.
### Author: Marsh (Auditor). Grade: **PROVED ∀k, char ≠ 2**, gated byte-exact. Supersedes the *conditional* status of CATÁLOGO v130/v131.

---

## 0. Setup and standing facts (all cited, none re-derived here)

`K` a field, `char K ≠ 2`. `S = K[x_1,…,x_n]`, `n = 2k+2`. `E = (e_1,e_3,…,e_{2k+1})` the odd elementary
symmetric polynomials; `R = S/E`; `A = S/(E + m^{[q]})` with `m^{[q]} = (x_1^q,…,x_n^q)`, `q` odd,
`q ≥ k+1`; `T = (k+1)(q−1)`.

Standing PROVED-∀k inputs used below:
- **(S1)** `E` is a complete intersection of codimension `k+1`; `R = S/E` is **radical**, and its zero locus
  is the union `⋃_J L_J` of the `(2k+1)!!` matching sheets `L_J` (`ODD_SYMMETRIC_GENERATION_THEOREM_v1`,
  `DEFORMATION_REDUCEDNESS_THEOREM_v1`; char ≠ 2). Each `L_J` is the linear subspace where the `n`
  coordinates pair off as `x_{a_p} + x_{b_p} = 0`, `p = 1,…,k+1`.
- **(S2)** `p_m := Σ_i x_i^m = 0` in `R` for every **odd** `m` (char-free). *Proof: in `R` the generating
  series `E(t) := ∏_i(1 − x_i t) = Σ_m (−1)^m e_m t^m` has only even-degree terms (odd `e_m` vanish), hence
  `E(t)=E(−t)`; then `P(t) := −E'(t)/E(t) = Σ_m p_m t^{m−1}` satisfies `P(−t) = −P(t)`, so `p_m = 0` for odd
  `m`.* In particular `p_q = 0` (`q` odd).
- **(S3)** `depth R = dim R = k+1 ≥ 2`, so `soc(R) = 0` (positive depth ⇒ no socle).

No use is made of the conjectural `s=0` minimal-generator description `minbase(in E) = {x_1}∪{m(V)}`
(that set-identity is CONJECTURE ∀k, gated `k ≤ 4` only). The argument below is **initial-ideal-free**.

---

## 1. Lemma L (PROVED ∀k, char ≠ 2)

Consider the `K`-linear map
> `μ : K^{n×n} → R_{q+1}`, `μ(c) = Σ_{i,l} c_{il}\, x_i x_l^q`.

Two families of genuine relations lie in `ker μ`:
- **rows** `x_i · p_q = 0` (each `i`); i.e. the matrices constant along a row are in `ker μ`;
- **cols** `e_1 · x_l^q = Σ_i x_i x_l^q = 0` (each `l`); i.e. matrices constant along a column are in `ker μ`.
Together they span the space `D` of **sum-decomposable** matrices `{c_{il} = r_i + s_l}`, `dim D = 2n−1`.

> **Lemma L.** `ker μ = D` exactly. Equivalently `dim\,\mathrm{im}\,μ = \dim\mathrm{span}\{x_i x_l^q\}_R = (n−1)^2`,
> i.e. the induced map `μ_L : R_1 ⊗ V' → R_{q+1}` (`R_1 = S_1/(e_1)`, `V' = ⟨x_l^q⟩/(p_q)`) is **injective**.

**Proof.**

*Step 1 — vanishing on sheets.* By (S1), `R` is radical, so `μ(c) = 0` in `R` iff the polynomial
`Σ c_{il} x_i x_l^q` vanishes on `⋃_J L_J` (over `K̄`; the statement is field-independent since `μ`, the
sheets and `E` are defined over the prime field). Equivalently it vanishes on every sheet `L_J`.

*Step 2 — sheet coordinates.* Fix a matching `J` with blocks `{a_p,b_p}`, `p=1,…,k+1`, and parametrise
`L_J` by `u_p := x_{a_p} = −x_{b_p}`. Then `x_i|_{L_J} = ε_i u_{π(i)}` with `ε_{a_p}=+1`, `ε_{b_p}=−1`,
`π(i)` = the block of `i`. Because `q` is **odd**, `ε_i^q = ε_i`, so
`x_i x_l^q|_{L_J} = ε_i ε_l\, u_{π(i)} u_{π(l)}^q`. The monomials `u_α u_β^q` (`α,β ∈ {1,…,k+1}`) are pairwise
distinct for `q ≥ 2`, hence linearly independent. Extracting the coefficient of `u_α u_β^q` gives, for every
ordered pair of blocks `(α,β)`,
> `(★_{J,α,β})`  `c_{a_α a_β} − c_{b_α a_β} − c_{a_α b_β} + c_{b_α b_β} = 0`
(a `2×2` alternating sum over `{a_α,b_α} × {a_β,b_β}`).

*Step 3 — which alternating sums appear.* As `J` ranges over all matchings and `(α,β)` over its blocks,
the `2×2` alternating sums that occur are exactly:
- **(D)** over a single pair `{a,b}` (case `α=β`): every `2`-subset occurs as a block of some matching (`k≥1`);
- **(O)** over two **disjoint** pairs `{a,b},{a',b'}` (case `α≠β`, `4` distinct indices): every pair of
  disjoint `2`-subsets occurs together in some matching (extend to a perfect matching of the remaining
  `2k−2` tokens).
No sheet ever produces the "shared-index" alternating sum (row-pair and col-pair sharing one index), because
two distinct blocks of a matching are disjoint.

*Step 4 — sum-decomposability lemma.* We claim `(D)+(O) ⇒ c ∈ D` for all `n ≥ 4`. It suffices to force **all**
`2×2` alternating sums to vanish (then `c` has vanishing mixed second differences, so `c_{il} = r_i + s_l` by
the standard reference construction). The only case not directly supplied by `(D)/(O)` is the shared-index
sum `X = c_{aa'} − c_{ba'} − c_{ab'} + c_{bb'}` with `|{a,b}∩{a',b'}| = 1`. Pick a spare index `e` (exists,
`n ≥ 4`). Writing the active indices as `{a₀,a₁,a₂}` (the three distinct entries) and `e` the spare, one has
the **uniform identity**, verified exactly over `ℚ`:
> `X = −½·O(a₀,a₁,a₂,e) + ½·O(a₀,a₂,a₁,e) − ½·O(a₁,a₂,a₀,e) + ½·D(a₀,a₁) + ½·D(a₀,a₂) − ½·D(a₁,a₂)`,
where `O(a,b,a',b') = c_{aa'}−c_{ba'}−c_{ab'}+c_{bb'}` and `D(a,b) = c_{aa}−c_{ab}−c_{ba}+c_{bb}`. The
coefficients `±½` are the only place `char ≠ 2` is used in this step. Hence `X = 0`, all `2×2` alternating
sums vanish, and `c ∈ D`.

Therefore `ker μ = D`, `dim\,\mathrm{im}\,μ = n^2 − (2n−1) = (n−1)^2`, and `μ_L` is injective. ∎

**Remarks.** (i) The proof is **char-free** except for `char ≠ 2` (already forced by (S1) and the `½`
certificate). Frobenius is not used; `q` enters only as an odd exponent. (ii) It uses **no** description of
`in(E)`, avoiding the conjectural `s=0` set-identity. (iii) It subsumes the previously-open "three
non-vanishings" (`x_a^{q+1} ≠ x_b^{q+1}`, `x_a x_b^q ≠ x_b x_a^q`, and the symmetric-traceless image `≠ 0`),
which are the three non-trivial `S_n`-isotypic pieces of `μ_L`; injectivity of `μ_L` gives all three at once
and sidesteps the `1/n` trace subtlety of the symmetric piece.

---

## 2. Corollary: `soc(A)_{q−1} = 0` (PROVED ∀k, char ≠ 2)

> **Theorem.** For all `k ≥ 1`, all odd `q ≥ k+1`, `char K ≠ 2`: `soc(A)_{q−1} = 0`.

**Proof.** Since `m^{[q]}` first appears in degree `q`, `A_{q−1} = R_{q−1}` and `A_q = R_q/V`,
`V = span\{x_l^q\}`. Let `a ∈ soc(A)_{q−1}`. Then `x_i a ∈ V` in `R` for each `i`, say
`x_i a = Σ_l c_{il} x_l^q`. Commutation `x_j(x_i a) = x_i(x_j a)` gives the relation
`Σ_l c_{il}\,x_j x_l^q − Σ_l c_{jl}\,x_i x_l^q = 0` in `R`. Its coefficient matrix
`d_{αβ} = δ_{αj}c_{iβ} − δ_{αi}c_{jβ}` lies in `ker μ`, hence in `D` (Lemma L): `d_{αβ} = r_α + s_β`. Reading
off `α ∉ {i,j}` forces `s_β = −γ` constant and `r_α = γ`; then `α = j` gives `c_{iβ} = r_j − γ`, **constant
in `β`**. So each row `c_{i·}` is constant, `c_{iβ} = t_i`, and `x_i a = t_i Σ_β x_β^q = t_i\, p_q = 0` by
(S2). Thus `x_i a = 0` for all `i`, i.e. `a ∈ soc(R) = 0` by (S3), so `a = 0`. ∎

**Scope.** `A_{q−1} = R_{q−1}` throughout, so this rung of levelness lives entirely in the complete
intersection `R`; the box `m^{[q]}` enters only as the target `V` and never mixes degrees. The **next** rung
`soc(A)_q = 0` is genuinely different — there `A_q = R_q/V` already, so the box acts within the source — and
is not covered here.

---

## 3. Gates (byte-exact; scripts delivered)

Two independent computational shadows, plus the endpoint.

**G1 — Lemma L directly** (`gate_lemmaL.py`): `dim\,\mathrm{span}\{x_i x_l^q\}_R = (n−1)^2`, over prime field
`GF(p)`, integer exponent `q`, with positive controls (`e_1=0`, `p_q=0`, each row/col relation `=0`, a
genuine relation reduces to `0`) and `p_2 ≠ 0` (nontriviality):

| `(k,q)` | field | pred `(n−1)^2` | measured | `#1 ≠0` | `#2 ≠0` |
|---|---|---|---|---|---|
| `(1,3)` | `GF(3)` | 9 | 9 ✓ | ✓ | ✓ |
| `(1,3)` | `GF(7)` | 9 | 9 ✓ | ✓ | ✓ |
| `(1,5)` | `GF(3)` | 9 | 9 ✓ | ✓ | ✓ |
| `(2,3)` | `GF(3)` | 25 | 25 ✓ | ✓ | ✓ |
| `(2,3)` | `GF(7)` | 25 | 25 ✓ | ✓ | ✓ |

**G2 — the `k`-uniform core** (`gate_kernel.py`): building the sheet constraints `(★)` over **all** matchings,
the solution space equals `2n−1` and the rank equals `(n−1)^2` (char-free rational linear algebra):

| `k` | `n` | #constraints | rank | soln dim | pred `2n−1` |
|---|---|---|---|---|---|
| 1 | 4 | 12 | 9 | 7 | 7 ✓ |
| 2 | 6 | 105 | 25 | 11 | 11 ✓ |
| 3 | 8 | 448 | 49 | 15 | 15 ✓ |
| 4 | 10 | 1305 | 81 | 19 | 19 ✓ |

The `½`-certificate of Step 4 is verified exactly over `ℚ` (`cert.py`) and independently over `GF(7)`
(`cert2.py`: every sum-decomposable matrix has vanishing shared-index sums).

**G3 — the endpoint** (`gate_soc.py`): `soc(A)_{q−1} = 0` directly, with positive control
`dim\,soc(A)_T = (2k+1)!!`, `T=(k+1)(q−1)`:

| `(k,q)` | field | `soc(A)_{q−1}` (pred 0) | `soc(A)_T` (pred `(2k+1)!!`) |
|---|---|---|---|
| `(1,3)` | `GF(3)` | 0 ✓ | 3 ✓ |
| `(2,3)` | `GF(3)` | 0 ✓ | 15 ✓ |
| `(1,3)` | `GF(7)` | 0 ✓ | 3 ✓ |

All gates carry pre-registered predictions and positive/negative controls (Ley 6). `char = q` (`GF(3)`,
campaign) and `char ≠ q` (`GF(7)`) both pass, confirming char-independence of the mechanism.

---

## 4. What this does and does not close

- **Closes** the first middle-zone socle rung `soc(A)_{q−1} = 0` **unconditionally ∀k** (was CONDITIONAL on
  Lemma L in CATÁLOGO v130/v131). Lemma L itself is now a **theorem** ∀k, not a reduction to `4` (or `3`)
  non-vanishings.
- **Does not close GAP 3.** GAP 3 is `dim A_T ≤ (2k+1)!!`, equivalently `soc(A)_d = 0` for **all**
  `q−1 ≤ d < T`. Only the single rung `d = q−1` is settled here. The bulk `q ≤ d < T` remains open, and the
  degree-`q` rung is where the box first acts within the source (a new ingredient). **`G` stays `3`.**

— Marsh, Chaise Longue campaign.
