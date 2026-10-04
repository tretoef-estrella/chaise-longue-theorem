# q_even_blocks.md — piece E16: the colour reduction for every degree (paper v11 §9.3, Lemmas 9.4 and 9.5)

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/EvenBlocks/`, namespace `EvenBlocks`.

## What this piece is

In the odd case (pieces 20–24: `ColSplit`, `ColSurv`, `ColComp`, `ColTensor`, `ColDecomp`) the colour reduction splits the ideal `I = (ψ_J : J)` of the group algebra into blocks, one per colour class, assuming that the only colour equal to its own inverse is `1` (`ColComp.IsReps`, which needs `r` odd). For an even degree `m = q·r'` with `p | m` and `p ∤ r'`, the cofactor `r'` may be even; then (and only then, for `p` odd) the colour `−1` is also its own inverse, and its class carries perfect matchings, like the class of `1`. This piece generalises Lemma 6.3 and Proposition 6.5 to an arbitrary set of self-inverse colours, with no hypothesis on the parity of `p`, `q` or `r`.

The splitting and survival lemmas themselves (Lemma 9.4 = Lemmas 6.1, 6.2 for every prime) need no new proof: `ColSplit.lemma61_0_surjective`, `lemma61_i`, `lemma61_ii`, `lemma61_iii` and `ColSurv.lemma62_i`, `lemma62_ii`, `lemma62_iii` are stated for an arbitrary `S : ColSplit.ColSetting F`, which carries no parity hypothesis on `p` or `r`. Part 0 records this and supplies the settings needed later.

## Setting (reuse unchanged)

- `S : ColSplit.ColSetting F` (a field `F` of characteristic `p` prime, `p = 2` allowed, `q = p^v`, `v ≥ 1`, `r ≥ 1`, `μ ⊆ F` with `|μ| = r` and `X^r − 1 = Π_{ζ∈μ}(X − ζ)`), `S.m = q·r`.
- `ColSurv`: `cExt c`, `tR`, `phi`, `psi S k J`, `S.piC c`, `Rc`.
- `ColComp`: `cls`, `Compatible`, `PerfMatch`, `CompMatching`, `IsReps`, `restrict`.
- `ColDecomp`: `boxS`, `idealI`, `varSet`, `tB`, `pairF`, `gP`, `gσ`, `Ic1`, `Icz`, `W1`, `Wz`, `rcEquiv`, `prop65_i`, `prop65_ii`, `prop65_iii`, `piC_psi_eq_unit_mul_prod`.
- `ColTensor`: `BoxSetting`, `iota`, `lemma64_iv`.

## Part 0 — Lemma 9.4, and settings for every prime

**(01)** For every `S : ColSetting F`, `(S.r : F) ≠ 0`. (From the setting: `X^r − 1` is the product of the `r` distinct linear factors `X − ζ`, `ζ ∈ μ`, so it is squarefree; if `p ∣ r` then `X^r − 1 = (X^{r/p} − 1)^p` and `1` would be a multiple root. Use whichever proof is shortest.)

**(02)** For every prime `p`, every `v ≥ 1` and every `r ≥ 1` with `¬ p ∣ r`, there is `S : ColSetting K` with `K = AlgebraicClosure (ZMod p)`, `S.p = p`, `S.v = v`, `S.r = r`, `S.μ = nthRootsFinset r (1 : K)`; hence `S.m = p^v·r`. (Model: the `let S` inside `ColAssembly.finrank_IK_of_isAlgClosed_of_dvd`, with `prod_nthRootsFinset_of_isAlgClosed`; there `r` is odd, here it is not needed.)

**(03) Lemma 9.4.** A theorem `lemma94` that restates `ColSplit.ColSetting.lemma61_ii` and `ColSurv.lemma62_iii` (with `ColComp.lemma63_v_cExt` if convenient) for an arbitrary `S`, with a docstring saying that no parity of `p`, `q`, `r` is assumed. This is bookkeeping, not new mathematics.

## Part A — self-inverse colours and compatible matchings (generalising Lemma 6.3)

Definitions:
- `SInv S : Finset F := S.μ.filter (fun ζ => ζ⁻¹ = ζ)` (the self-inverse colours).
- `IsReps2 S R : Prop := R ⊆ S.μ \ SInv S ∧ ∀ ζ ∈ S.μ \ SInv S, Xor' (ζ ∈ R) (ζ⁻¹ ∈ R)`.

**(A1)** `1 ∈ SInv S`; `ζ ∈ SInv S ↔ ζ ∈ S.μ ∧ ζ ^ 2 = 1`; `SInv S ⊆ {1, −1}`.

**(A2)** (a) If `Odd S.r` or `S.p = 2`, then `SInv S = {1}`. (b) If `Even S.r`, then `S.p ≠ 2`, `(−1 : F) ≠ 1`, `−1 ∈ S.μ` and `SInv S = {1, −1}`.

**(A3)** For every `S` there is `R` with `IsReps2 S R` (every `r`, every `p`).

**(A4)** If `SInv S = {1}`, then `IsReps2 S R ↔ ColComp.IsReps S R`.

**(A5)** For `c : Fin (2k+2) → F` with values in `S.μ` and `IsReps2 S R`: the classes `cls c ζ` (`ζ ∈ SInv S`) and the sets `cls c ζ ∪ cls c ζ⁻¹` (`ζ ∈ R`) are pairwise disjoint and their union is `Finset.univ`.

**(A6)** Under the same hypotheses, for `a, b`: `c a * c b = 1 ↔ (∃ ζ ∈ SInv S, a ∈ cls c ζ ∧ b ∈ cls c ζ) ∨ ∃ ζ ∈ R, (a ∈ cls c ζ ∧ b ∈ cls c ζ⁻¹) ∨ (b ∈ cls c ζ ∧ a ∈ cls c ζ⁻¹)`.

**(A7)** `Compatible c J ↔ (∀ ζ ∈ SInv S, (cls c ζ).image J.1 = cls c ζ) ∧ ∀ ζ ∈ R, (cls c ζ).image J.1 = cls c ζ⁻¹`.

**(A8)** Restriction is a bijection `CompMatching c ≃ ((ζ : SInv S) → PerfMatch (cls c ζ)) × ((ζ : R) → (cls c ζ ≃ cls c ζ⁻¹))` (with the explicit inverse, as `ColComp.compEquiv`).

**(A9)** `(∃ J, Compatible c J) ↔ (∀ ζ ∈ SInv S, Even (cls c ζ).card) ∧ ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card`; and under these conditions `Nat.card {J // Compatible c J} = (∏ ζ ∈ SInv S, ((cls c ζ).card − 1)‼) * ∏ ζ ∈ R, ((cls c ζ).card)!`.

## Part B — Lemma 9.5, the tensor decomposition

Definitions, for `c : Fin (2k+1) → S.μ` and `ζ ∈ SInv S`:
- `WS S c ζ := varSet (cls (cExt c) ζ)` (so `W1 S c = WS S c 1`, by `rfl`);
- `gPS S c ζ (P : PerfMatch (cls (cExt c) ζ)) : (boxS S c).Box (WS S c ζ)`, the product of `pairF S.q (tB S c (WS S c ζ)) x (P x)` over the `x` with `x < P x` — exactly `gP` with the class `ζ` in place of the class `1` (so `gP S c = gPS S c 1`, by `rfl` or a one-line proof);
- `IcS S c ζ := Ideal.span (Set.range (gPS S c ζ))` (so `Ic1 S c = IcS S c 1`).

Let `R` satisfy `IsReps2 S R`.

**(B1)** For a compatible matching `J`, `rcEquiv (boxS S c) (S.piC c (psi S k J))` is a unit times `∏_{ζ : SInv S} ι(gPS S c ζ P_ζ) · ∏_{ζ : R} ι(gσ S c ζ σ_ζ)`, where `(P, σ)` is the image of `J` under (A8) and `ι` is `(boxS S c).iota _ Finset.univ (Finset.subset_univ _)`. (Model: `ColDecomp.piC_psi_eq_unit_mul`, from `piC_psi_eq_unit_mul_prod` and a split of the product over the pairs of `J` along the blocks, as `prod_pairs_split`.)

**(B2)** If some matching is compatible with `cExt c`, then `((idealI S k).map (S.piC c)).map (rcEquiv (boxS S c))` is the ideal generated by those products, over all `(P, σ)`. (Model: `ColDecomp.map_idealI_eq_span`.) If none is compatible, the map is `⊥` (`ColDecomp.prop65_i`, which needs no representatives: cite it).

**(B3) Lemma 9.5.** `((∃ J, Compatible (cExt c) J) → finrank F ((idealI S k).map (S.piC c)) = (∏ ζ ∈ SInv S, finrank F (IcS S c ζ)) * ∏ ζ ∈ R, finrank F (Icz S c ζ)) ∧ ((¬ ∃ J, …) → finrank … = 0)`. (Model: `ColDecomp.prop65_iii`, with the blocks indexed by `SInv S ⊕ R` instead of `Option R`, and `ColTensor.lemma64_iv`.)

**(B4)** Consistency: if `SInv S = {1}` then the product over `SInv S` in (B3) is `finrank F (Ic1 S c)`, so (B3) is `prop65_iii` again.

## Remarks for the proofs

- Nothing about the generator `pairF` changes: for a pair inside the class `−1`, `t_b − 1` is a unit of `R_c` and `(t_a t_b − 1)^{q−1}` is what it is; the block generator is still the product of the factors of (6.2) over the pairs of the block. Identifying the block of colour `−1` with the ideal of Theorem O (Lemma 9.9) is a later piece (E18); here the block is only defined and the decomposition proved.
- The index `0` of `V = Fin (2k+2)` has no variable; `varSet` already removes it, as in `W1`.
- The case `p = 2` is included: then `−1 = 1` in `F` and `SInv S = {1}` (A2a), and everything reduces to the old statements (A4, B4).

## Checks done before sending (`chkE16.py`, `chkE16.log`)

Seven cells, computed directly in the rings `R_c = F[t]/((t_i − c_i)^q)` over `F_3`, `F_4`, `F_5`, `F_9`: `(k, m, p) = (1,6,3), (1,6,2), (1,10,5), (1,12,3), (1,12,2), (1,20,5), (2,6,3)`. They cover the three kinds of block: self-inverse `1`, self-inverse `−1` (r' = 2, 4 with p odd), and pairs (`(1,6,2)`, `(1,12,3)`, `(1,12,2)`, `(1,20,5)`). Checked: (A1), (A2) shape of `SInv`, (A6), (A7) for every matching, (A9) existence and count for every colouring, (B1)/(B3) `dim π_c(I) = Π` block dimensions for every compatible colouring and `0` otherwise, and `Σ_c dim π_c(I) = Q_k(m)` (61, 61, 217, 331, 331, 1027, 1001). 3 399 checks, 0 failures. Controls (each must fire, and does): dropping a self-inverse block from the product (96 times), the count without the factor of the class `−1` (20), and a wrong compatibility rule for the class `−1` (210).
