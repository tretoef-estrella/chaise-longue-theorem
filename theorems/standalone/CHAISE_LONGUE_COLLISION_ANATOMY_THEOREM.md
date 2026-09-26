> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — COLLISION ANATOMY THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_COLLISION_ANATOMY_THEOREM.md
>
> **Status, as written in the document:** Status: PROVED (pencil, four steps) + gated 6/6 at `(2,5)`. Char `p≠2`, `q` odd. Does NOT close GAP 3 — it concentrates it at the last collision.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — COLLISION ANATOMY THEOREM (v1)
### Author: Apolo (architecture: Lacassagne's collision ladder; gates by Apolo). Auditor: Balthazard.
### Status: PROVED (pencil, four steps) + gated 6/6 at `(2,5)`. Char `p≠2`, `q` odd. **Does NOT close GAP 3** — it concentrates it at the last collision.

## Statement
Let `n=2k+2`, `E=(e_1,e_3,…,e_{2k+1})`, and let `ψ(T)=T^{q_0}\prod_{p=1}^{r}(T^2−a_p)` with `q_0` odd, `a_p` distinct nonzero (a collision stratum of the monic odd family; `q=q_0+2r`). Set `A(ψ)=S/(E+(ψ(x_i))_i)`. Then:

1. **(CRT split)** `A(ψ)=⊕_{(S,ε)} A_{S,ε}`, over subsets `S⊆\{0,…,n−1\}` ("fat" coordinates, local factor `T^{q_0}`) and assignments `ε` of the remaining coordinates to the `2r` live roots `±\sqrt{a_p}`.
2. **(Unbalanced vanishing)** If the pinned multiset `ε` is **not** negation-closed, then `A_{S,ε}=0`.
   *Proof:* the fat variables are nilpotent (`z_i^{q_0}=0`-type), so every symmetric function of them is nilpotent; if some odd `e_d` of the pinned values is a nonzero constant `c`, the corresponding generator is `(\text{nilpotent})+c` = **unit** ⟹ ideal `=(1)`. ∎
3. **(Balanced identification)** If `ε` is negation-closed (`|S|=2m` necessarily even), then
   $$A_{S,ε}\ \cong\ A_{m−1}(q_0).$$
   *Proof:* the pinned generating function is even, `G(t^2)=\prod(1−a_p t^2)^{(\cdot)}`, so the odd-degree coefficients of `\prod_{i∈S}(1+z_it)\cdot G(t^2)` are triangular combinations `∑_j g_j\,e_{d−2j}(z)`, generating exactly `(e_1(z),e_3(z),…,e_{2m−1}(z))`; adding the fat local equations gives precisely the cell `A_{m−1}(q_0)` in `2m=2(m−1)+2` variables. ∎
4. **(Convolution)** Hence
   $$\dim A(ψ)=\sum_{m=0}^{k+1}\binom{n}{2m}\,N_{\mathrm{bal}}(n−2m;r)\cdot A_{m−1}(q_0),\qquad A_{−1}:=1,$$
   with `N_bal` = number of negation-closed assignments of `n−2m` coordinates to the `r` live pairs. If the lower tower is clean (`A_j(q_0)=P_j(q_0)` for `j≤k`), the grid recursion of `P` gives
   $$\dim A(ψ)=P_k(q).$$

**Corollary (stratification flatness).** Given lower-tower cleanliness at `q_0`, **every collision stratum with at least one live pair has dimension exactly `P_k(q)`** — unconditionally, without measuring the box. The entire monic family is flat except possibly at the single deepest point `ψ=T^q`. **GAP 3 concentrates at the last collision `±a→0`.** (Consistent with the three-line meta-obstruction: the final step cannot follow from this generic machinery.)

## Gates (`(2,5)`, `ψ=T^3(T^2−1)`, all predictions pre-stated)
```
|S|=6 fat all:        141 = A_2(3) ✓      |S|=4 balanced:  19 = A_1(3) ✓
|S|=4 UNbalanced:       0 ✓               |S|=2 balanced:   3 = A_0(3) ✓
|S|=2 UNbalanced:       0 ✓               |S|=0 balanced:   1 ✓
Sum: 141+15·2·19+15·6·3+20·1 = 1001 = P_2(5) ✓   (independent stratum gate: dims 1001, a=1..4, 4/4)
```

## Honest scope
Proves the full intermediate stratification and localizes the conjecture at one point per cell. Does **not** prove the last collision (the box), which remains GAP 3. `G=3`.

— Apolo, Chaise Longue.
