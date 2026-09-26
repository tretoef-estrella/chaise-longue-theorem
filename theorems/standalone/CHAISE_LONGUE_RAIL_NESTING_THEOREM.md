> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE RAIL-NESTING THEOREM (the k→k+1 staircase step, PENCIL)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_RAIL_NESTING_THEOREM.md
>
> **Status, as written in the document:** CHAISE_LONGUE_RAIL_NESTING_THEOREM_v1 · standalone · PROVED forall k, forall q, char ≠ 2
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE RAIL-NESTING THEOREM (the k→k+1 staircase step, PENCIL)
### CHAISE_LONGUE_RAIL_NESTING_THEOREM_v1 · standalone · PROVED forall k, forall q, char ≠ 2

Notation: `N = 2k+2`; `S_k = κ[x_1,…,x_N]`, grevlex `x_1 > … > x_N`; `e_j^{(N)}` = j-th elementary
symmetric in `x_1,…,x_N`; `E_k = (e_1,e_3,…,e_{2k+1})`; `I_k = E_k + m^{[q]} = E_k+(x_1^q,…,x_N^q)`.
Add the pair `y_1=x_{N+1}, y_2=x_{N+2}` (the two SMALLEST grevlex variables of `S_{k+1}`);
`π : S_{k+1} → S_k` sets `y_1=y_2=0`.

## THEOREM (RAIL-NESTING).
> The minimal leaders of `in(I_k)` are **exactly** the `y`-free minimal leaders of `in(I_{k+1})`:
> `{ μ ∈ in(I_{k+1}) : μ involves no y } = in(I_k)` as monomial ideals in `x_1,…,x_N`, and the minimal
> generators correspond. Hence the frozen staircase **nests**, `∀k`, forced by the rails — the measured
> `6 ⊂ 20 ⊂ 111` is now a theorem, not data.

## Proof (uniform in k).

**(0) Rail identity `π(I_{k+1}) = I_k`.** For `j ≤ N`, `π(e_j^{(N+2)}) = e_j^{(N)}` (drop the monomials
using `y`). The one new odd generator restricts to zero: `π(e_{2k+3}^{(N+2)}) = e_{2k+3}^{(N)} = 0` (no
`2k+3` distinct indices among `N=2k+2`). And `π(x_i^q)=x_i^q` for `i≤N`, `π(y_a^q)=0`. So
`π(E_{k+1}) = (e_1,…,e_{2k+1}) = E_k` and `π(m^{[q]}_{k+1}) = m^{[q]}_k`, giving `π(I_{k+1}) = I_k`. ∎₀

**(grevlex lemma).** For monomials of equal total degree, a `y`-free one is grevlex-LARGER than any
`y`-involving one: grevlex breaks a degree tie by the last nonzero coordinate of the difference; the two
disagree at a `y`-slot (the `y`-free one has 0 there, the other is positive), and that slot is late
(smallest variables), so the difference is negative there ⟹ the `y`-free monomial wins. ∎_L

**(1) `y`-free `μ ∈ in(I_{k+1}) ⟹ μ ∈ in(I_k)`.** Let `μ = lm(f)`, `f ∈ I_{k+1}`, `μ` `y`-free. Since `μ`
is `y`-free it survives `π` and, being the grevlex-top of `f`, stays the top of the sub-sum `π(f)` (whose
terms are a subset of `f`'s): `lm(π(f)) = μ`. As `π(f) ∈ π(I_{k+1}) = I_k`, `μ ∈ in(I_k)`. ∎₁

**(2) `μ ∈ in(I_k) ⟹ μ ∈ in(I_{k+1})` (and `μ` is `y`-free).** Write `μ = lm(g)`, `g ∈ I_k`, so
`g = Σ_j h_j e_j^{(N)} + Σ_{i≤N} c_i x_i^q` with `h_j, c_i ∈ S_k` (`y`-free). **Lift with the SAME
cofactors:** `F := Σ_j h_j e_j^{(N+2)} + Σ_{i≤N} c_i x_i^q ∈ I_{k+1}` (each `e_j^{(N+2)}`, odd `j≤2k+1`, is
a generator of `E_{k+1}`). Then `π(F) = g`, and `F − g = Σ_j h_j (e_j^{(N+2)} − e_j^{(N)})`, a sum of terms
that ALL involve `y`, each of the SAME total degree as the matching term of `g`. Grevlex prioritizes total
degree, so `deg μ` is the maximal degree in `g`, hence also `≥` every degree in `F−g`; and at each degree
the `y`-free terms of `g` beat the `y`-terms of `F−g` (grevlex lemma). Therefore `lm(F) = lm(g) = μ`. Since
`F ∈ I_{k+1}`, `μ ∈ in(I_{k+1})`; and `μ` is `y`-free. ∎₂

**(3) Minimal generators.** (1)+(2) give `{ y-free monomials of in(I_{k+1}) } = in(I_k)` as ideals in
`x_1,…,x_N`. A `y`-free monomial `μ` is a minimal generator of `in(I_k)` iff it is a minimal generator of
`in(I_{k+1})`: any divisor of `μ` in `in(I_{k+1})` is `y`-free (μ is), hence lies in `in(I_k)`, so
minimality transfers both ways. ∎₃

Thus the minimal leaders of `in(I_k)` are exactly the `y`-free minimal leaders of `in(I_{k+1})`. ∎

## Consequence & scope (honest)
- **PROVED forall k, forall q, char ≠ 2:** the old staircase persists intact under `k→k+1`; the level-k
  leaders are precisely the level-(k+1) leaders that avoid the new pair. The nesting `6 ⊂ 20 ⊂ 111`
  (k=1,2,3) is now a theorem. Control (q=7): the 20 y-free minimal leaders of the k=3 staircase equal the
  20 k=2 leaders, byte-exact — consistent (this control supported, did not constitute, the proof).
- **NOT proved here (the remaining half of the transfer step): the INCREMENT** — the new leaders that
  involve `x_{2k+3},x_{2k+4}` (measured 91 for k=2→3). RAIL-NESTING says the old leaders are rigid; the
  increment law (governed by the first-return split on the added pair + the single new generator
  `e_{2k+3}`) is the next pencil. Does NOT close GAP 3 or move G by itself.

**Grade: RAIL-NESTING PROVED forall k (pencil, rails + grevlex). INCREMENT: open.**
