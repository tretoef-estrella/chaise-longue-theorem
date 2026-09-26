> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE LINEAR STRAND THEOREM — CHAISE_LONGUE_LINEAR_STRAND_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_LINEAR_STRAND_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE LINEAR STRAND THEOREM — `CHAISE_LONGUE_LINEAR_STRAND_THEOREM_v1`
### The multiplicity space `W` of the defect module `C(B_m)`, fixed for all `m`
**Chaise Longue campaign · 23 Jul 2026 · Orfila (auditor), on a target set by Lacassagne (constructor)**

> **Summary.** The bottom of the minimal free resolution of the defect module is determined outright,
> for every `m`, with no measurement: `W` is the permutation representation of the `a`-side symmetric
> group on `m` letters, with the `b`-side acting trivially. Three consequences follow. The programme of
> fixing `W` by two traces is impossible, and impossible in the cheapest possible way — the traces of the
> actual `W`, fed into the ansatz, demand a multiplicity of `1/2`. The two one-sided defect modules
> `C_a` and `C_b` are **not** isomorphic as representations, so there is no equivariant swap symmetry of
> `C_a`; the involution carries `C_a` to `ι^* C_b`. And the scalar by which that involution squares is
> measured to be `+1`, so the `Z/2` extension acts honestly and Schur's lemma may be used over the
> ordinary group algebra.

---

## 0. SETUP AND NOTATION

`k` a field, `R = k[a_1,…,a_m, b_1,…,b_m]` with the standard grading. Write

- `I_B = ( e_j(a) − (−1)^j e_j(b) )_{j=1..m}`, a complete intersection of degrees `1,…,m`;
- `X = V(I_B)`, `O(X) = R/I_B`;
- for each `σ ∈ S_m` (a *sheet*), `I_σ = ( a_i + b_{σ(i)} : i = 1..m )`;
- `Γ = ker( O(X)^{2m} → ⊕_{σ,i} O(X)/I_σ )`, `λ ↦ ( λ_{a_i} − λ_{b_{σ(i)}} )` read on sheet `σ`;
- `C_a = coker( Γ →^{π_a} O(X)^m )`, `π_a` the projection onto the `a`-coordinates;
- `C_b = coker( Γ →^{π_b} O(X)^m )`, `π_b` the projection onto the `b`-coordinates.

`C_a` is the defect module of the campaign, `Hilb(C_a) = h_m(t)/(1−t)^{m−1}`; the realisation and its
gates are recorded in `CHAISE_LONGUE_REFEREE_EVIDENCE_DOSSIER`.

The group `G = S_m^{(a)} × S_m^{(b)}` acts on `R` by permuting the two blocks of variables. It fixes
each generator of `I_B` (the `e_j` are symmetric), hence acts on `O(X)`; it permutes the sheets by
`σ ↦ βσα^{−1}`, hence acts on `Γ`; and it permutes the `m` coordinates of `O(X)^m` through its `a`-factor
alone. So `G` acts on `C_a`, and `W` below is a `G`-representation.

`W` denotes the multiplicity space of `O(X)` inside `O(X)^m`: the `m`-dimensional space spanned by the
`m` projection coordinates. The **linear strand** of `C_a` is the exact sequence
`0 → triv → W → W/triv → 0`.

---

## 1. THEOREM 1 — THE DEGREE-ZERO PART OF `Γ` *(PROVED, all `m ≥ 2`)*

> **`Γ_0 = k · (1,1,…,1)`**, the line spanned by the all-ones vector of `O(X)^{2m}`.

**Proof.** Each `I_σ` is generated in degree 1, so `(O(X)/I_σ)_0 = k` and the degree-0 component of the
defining map sends a constant vector `λ` to the family `( λ_{a_i} − λ_{b_{σ(i)}} )_{σ,i}` of scalars.
Thus `λ ∈ Γ_0` if and only if `λ_{a_i} = λ_{b_{σ(i)}}` for every sheet `σ` and every `i`. Since `σ` runs
over **all** of `S_m`, for `m ≥ 2` every pair `(i,j)` occurs as `(i, σ(i))`, so all `2m` coordinates are
equal. Conversely the all-ones vector clearly lies in the kernel. ∎

**Machine corroboration (byte-exact).** The minimal generators of `Γ` have degrees `{0,1,2,2,2,2,2}` at
`m = 3` and `{0,1,2,3,3,3,3,3,3,3,3,3,3}` at `m = 4`; in each case exactly one generator has degree `0`
and it is printed as the all-ones column. `HF(Γ) = 1,6,24,60,…` (`m=3`) and `1,8,35,120,…` (`m=4`).

---

## 2. THEOREM 2 — `W` IS FIXED *(PROVED, all `m ≥ 2`, no measurement)*

> **As a representation of `G = S_m^{(a)} × S_m^{(b)}`,**
> **`W = ( triv ⊕ std )_a ⊗ triv_b`** — the permutation representation of `S_m^{(a)}` on `m` letters,
> with `S_m^{(b)}` acting trivially. Consequently
> **`β_{0,0}(C_a) = (C_a)_0 = W/triv = std_a ⊗ triv_b`, of dimension `m−1`.**

**Proof.** The `m` coordinates of `O(X)^m` are indexed by the `a`-vertices. `S_m^{(a)}` permutes that
index set; `S_m^{(b)}` fixes each index. In degree `0` we have `O(X)_0 = k`, so `G` acts on
`(O(X)^m)_0 = k^m` **only** through the index permutation: that is the permutation representation of
`S_m^{(a)}`, with `b` trivial, which is `W`. By Theorem 1, `π_a(Γ_0)` is the diagonal line, so
`(C_a)_0 = k^m / \text{diagonal} = std_a ⊗ triv_b`. Since `C_a` is generated in degree `0` and
`β_{0,0} = \dim (C_a)_0`, the last claim follows. ∎

**Machine corroboration.** `\dim (C_a)_0 = 2` at `m=3` and `3` at `m=4`, matching `β_{0,0} = m−1` in the
sealed Betti tables (`2,10,16,10,2` and `3,21,48,48,21,3`).

---

## 3. COROLLARY 3 — `W` IS NOT A SUM OF LINEAR CHARACTERS, AND THE TWO-TRACE PROGRAMME IS IMPOSSIBLE
*(PROVED, all `m ≥ 3`)*

The campaign carried an ansatz

>  `W = a'(triv⊗triv) ⊕ b'(sgn⊗sgn) ⊕ c'( triv_a⊗sgn_b ⊕ sgn_a⊗triv_b )`, with `a'+b'+2c' = m`,

to be solved for `(a',b',c')` from the two traces `tr_W(α,1) = a'−b'` and `tr_W(α,β) = a'+b'−2c'`
(`α, β` transpositions). Those three equations are correct for that ansatz. The ansatz is not.

**First kill (structural).** By Theorem 2, `W` contains `std_a`, irreducible of dimension `m−1 ≥ 2`.
A sum of linear characters contains none. ∎

**Second kill (the inverse test, independent of any hypothesis).** The true traces are
`tr_W(α,1) = m−2` (fixed points of a transposition acting on `m` letters) and `tr_W(α,β) = m−2`
(the `b`-factor acts trivially). Substituting:

```
   a' − b'        = m − 2
   a' + b' − 2c'  = m − 2
   a' + b' + 2c'  = m
```

Subtracting the second from the third gives `4c' = 2`, so **`c' = 1/2`**, and then `a' = m − 3/2`.
Fractional multiplicities: no representation has them. The ansatz is impossible on its own arithmetic,
without appeal to Theorem 2. ∎

*Note on the failed hypothesis behind the ansatz.* It descended from the claim "if `C` is swap-symmetric
then `W` is a sum of `m` linear characters, since every swap-stable non-linear representation has
dimension at least `min(4, 2(m−1)) > m−1`". The conclusion is false by Theorem 2, so the hypothesis is
false: see Theorem 4.

---

## 4. THEOREM 4 — THE TWO SIDES ARE NOT EQUIVARIANTLY ISOMORPHIC *(PROVED, all `m ≥ 3`)*

> **`C_a ≇ C_b` as `G`-modules.** In particular there is no equivariant swap symmetry of `C_a`; the
> involution `ι` exchanges the two sides, carrying `C_a` to `ι^* C_b`.

**Proof.** By Theorem 2 applied on each side, `(C_a)_0 = std_a ⊗ triv_b` and `(C_b)_0 = triv_a ⊗ std_b`.
For `m ≥ 3` these are distinct irreducible representations of `G` (a non-trivial irreducible in the
`a`-factor against a trivial one). An isomorphism of graded `G`-modules would restrict to an isomorphism
in degree `0`. ∎

**Machine corroboration, stronger than the statement.** `\dim_k Hom(C_a, C_b)_0 = 0` at `m = 3` (char 3
and char 0) and `m = 4` (char 3): there is not even a non-zero degree-preserving map, let alone an
isomorphism.

**What survives, and it is not nothing.** `ι : a_i ↔ b_i` is a ring involution of `R` with
`ι( e_j(a) − (−1)^j e_j(b) ) = −(−1)^j ( e_j(a) − (−1)^j e_j(b) )`, so `ι(I_B) = I_B` and `ι` descends to
`O(X)`; it carries `I_σ` to `I_{σ^{−1}}`, hence permutes the sheets and acts on `Γ` by exchanging the two
blocks of coordinates. It therefore carries `C_a` to `ι^* C_b`, and **`C_a ≅ ι^* C_b`** — measured below.

---

## 5. THEOREM 5 — THE SWAP SCALAR `λ` *(MEASURED, `m = 3, 4`; gated)*

Since `End(C_a)_0 = k` (recorded in the evidence dossier), an isomorphism `φ : C_a → ι^* C_b` is unique
up to a scalar, and the composite of `φ` with its own `ι`-image is a scalar `λ` on `C_a`. Rescaling `φ`
by `μ` replaces `λ` by `μ²λ`, so in general `λ` is well defined only modulo squares — **but over `F_3`
every square is `1`, so there `λ` is an outright invariant.** `λ = 1` means the `Z/2` extension acts
honestly; `λ = −1` would mean it acts only projectively, and Schur's lemma would have to be applied over
a twisted group algebra.

> **Measured: `\dim_k Hom(C_a, ι^* C_b)_0 = 1`, the generator is an isomorphism, and `λ = +1`.**
> `m = 3` in characteristic 3 and in characteristic 0, and `m = 4` in characteristic 3. Both composites
> `ι(φ)∘φ` and `φ∘ι(φ)` return the identity exactly.

**Consequence.** The differentials of the resolution may be constrained by Schur's lemma over the
**ordinary** group algebra of `S_m^{(a)} × S_m^{(b)} ⋊ Z/2` acting on `C_a ⊕ C_b`. No twisted algebra is
needed.

---

## 6. MEASURED REMARK — `End(C)` IS A LINE BUNDLE'S WORTH OF ENDOMORPHISMS

> `\dim Hom(C,C) = \dim C` and `\deg Hom(C,C) = \deg C`: `2` and `9` at `m = 3`, `3` and `72` at `m = 4`
> (characteristic 3, and characteristic 0 at `m = 3`).

Together with `\dim_k End(C)_0 = 1` this says that `C` is generically of rank one on its support, and
that `End(C)` is a module of the same dimension and the same degree as `C` itself. **Grade: MEASURED at
`m = 3, 4`.**

---

## 7. WHAT THIS DOES **NOT** SETTLE — THE TWIST CHARACTER `χ`

`χ` is defined by the self-duality of the Betti table, `β_{c−i, s−j} = β_{i,j} ⊗ χ`, with `c = m+1` and
`s = m + C(m,2)`.

1. **The argument that `χ` is `ι`-stable does not stand.** It required the swap to act on `C_a`, which
   Theorem 4 refutes. Applying `ι^*` to `ω_{C_a} ≅ C_a(s) ⊗ χ` yields `ω_{C_b} ≅ C_b(s) ⊗ ι^*χ`: a
   statement about the *other* side, which puts no constraint on `χ` itself. The restriction to the two
   `ι`-stable linear characters `{ triv, sgn_a⊗sgn_b }` is therefore withdrawn.
2. **`χ` is a single Betti cell.** Granting the recorded cell `β_{2,2} = triv`, the duality gives
   `β_{c−2, s−2} = triv ⊗ χ = χ`, a one-dimensional cell (`β_{2,4} = 1` at `m=3`, `β_{3,8} = 1` at
   `m=4`, both in the sealed tables). **So `χ` is the character of one one-dimensional cell of the
   minimal resolution, and one trace computation settles it.**
3. **It must be done at `m = 4` or higher.** In `S_3`, `std ⊗ sgn = std`, so `m = 3` cannot distinguish a
   twist by `sgn_a`. At `m = 4` the two candidates have transposition traces `+1` and `−1`.

**Grade of `χ` after this deposit: CANDIDATE.** Not proved trivial, not proved anything.

---

## 8. SCOPE — WHAT IS PROVED AND WHAT IS MEASURED

| statement | grade | scope |
|---|---|---|
| `Γ_0 = k·(1,…,1)` | **PROVED** | all `m ≥ 2`, any field |
| `W = (triv ⊕ std)_a ⊗ triv_b`, `β_{0,0} = std_a ⊗ triv_b` | **PROVED** | all `m ≥ 2`, any field |
| the linear-characters ansatz for `W` is impossible (`c' = 1/2`) | **PROVED** | all `m ≥ 3` |
| `C_a ≇ C_b` as `G`-modules | **PROVED** | all `m ≥ 3` |
| `ι(I_B) = I_B`, `ι` permutes sheets, `C_a ≅ ι^*C_b` | PROVED / **MEASURED** | descent proved; the isomorphism measured at `m=3,4` |
| `λ = +1` | **MEASURED** | `m=3` (char 3, char 0), `m=4` (char 3) |
| `\dim End(C)_0 = 1`, `\deg End(C) = \deg C` | **MEASURED** | `m=3,4` |
| `χ` | **CANDIDATE** | not fixed by anything in this deposit |

**Nothing here proves `C` Cohen–Macaulay for all `m`, and nothing here closes `GAP 1`.** What it does is
remove the first of the two open pieces of that step: `W` no longer has to be found, and the route that
was going to find it could not have worked.

**Reproduction:** `chaise_W_lambda_v1.m2` (Macaulay2 ≥ 1.22), with the logs
`out_Wlambda_m3_char3.log`, `out_Wlambda_m3_char0.log`, `out_Wlambda_m4.log`.

— Orfila, Chaise Longue campaign
