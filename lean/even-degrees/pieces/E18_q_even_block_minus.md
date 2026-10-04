# q_even_block_minus.md — piece E18: the blocks at every prime, and the block of colour −1 (paper v11 §9.4, Lemmas 9.7, 9.8, 9.9)

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/EvenMinus/`, namespace `EvenMinus`.

## What this piece is

Pieces E16 (`EvenBlocks`) and E17 (`EvenColours`) split the ideal and the count along the blocks `SInv S ⊕ R` of a colouring, for every prime and every cofactor. This piece proves the lower bound block by block (Lemmas 9.7–9.9 of the paper), except the block of colour `1` at the prime `2` (Lemma 9.10, piece E19):

- **pair blocks** (`ζ ∈ R`), every prime, `2` included: `Bip.Nbal |𝒞_ζ| q ≤ dim I_{c,ζ}` (Lemma 9.7) — Lemma 6.7 (`ColPairs`) without `p ≠ 2`, with `BipAny.theoremC_prime_pow` (piece E1) in place of `Bip.theoremC`;
- **colour `1` at an odd prime**: `NS S 1 |𝒞_1| ≤ dim I_{c,1}` (Lemma 9.8) — Lemma 6.6 (`ColOne.lemma66_ii`, `lemma66_iii`) read with `EvenColours.NS`;
- **colour `−1`** (`p` odd, `r` even): `NS S (−1) |𝒞_{−1}| ≤ dim I_{c,−1}` (Lemma 9.9) — new: with `u := −t` the block is the odd box `r = q`, and Theorem O (`OddTheorem.theoremO`) and Theorem 8.11 (`OddTheorem.theorem811`) give the bound.

## Setting (reuse unchanged)

- `S : ColSplit.ColSetting F`, `c : Fin (2k+1) → S.μ`, `cExt`, `cls`, `boxS S c`, `pairF`, `tB`.
- `EvenBlocks`: `SInv`, `IsReps2`, `WS`, `gPS`, `IcS`, `even_r_facts`, `not_p_dvd_r`; `ColDecomp`: `Wz`, `Icz`, `gσ`, `Ic1`, `W1`; `ColPairs`: `lemma67_i`, `lemma67_iii_*`, `lemma67_iv`, `lemma67_vi` (as models); `ColOne`: `lemma23_i`, `lemma23_ii_one`, `lemma24_i`, `lemma66_ii`, `lemma66_iii`, `Psi`, `yW`, `DP`, `one_le_h`, `odd_q`; `BipAny.theoremC_prime_pow`, `BipAny.choose_pred_prime_pow`; `Bip.Nbal`, `Bip.Nph`, `Bip.lemma72_iii`; `ColCount.Nbal_eq_Nz` (model).
- `EvenColours.NS`, `C3_a`, `C3_c`, `C3_d`, `p_ne_two_of_neg_one_ne_one`.
- `OddTheorem.theoremO`, `OddTheorem.theorem811`, `OddTheorem.stdOddSetting`; `OddLayers.card_ZS_root_even`; `OddShapes.isInterlaced_root_even`; `OddPatterns.VSAll`, `B5_no_marked`; `Tight.VLam`, tight patterns of the empty partition; `TheoremB.DIdeal`, `TheoremB.card_closedTuples`, `TheoremB.Qk`; `EvenCount.QkEven`.

## Part P — pair blocks at every prime (Lemma 9.7)

**(P1)** Re-prove `ColPairs.lemma67_i`, `lemma67_iii_bal`, `lemma67_iii_ph`, `lemma67_iii_ph'`, `lemma67_iii_ne`, `lemma67_iv` under the hypotheses `IsReps2 S R` and `ζ ∈ R` in place of `IsReps S R` (if the old proofs only use that the classes `𝒞_ζ`, `𝒞_{ζ⁻¹}` are disjoint and that `ζ, ζ⁻¹ ≠ 1`, state the new versions under exactly those hypotheses and say so; if the old statements already apply, cite them).

**(P2)** For every prime `p` (`2` included), `ζ ∈ R` (`IsReps2 S R`) and `|𝒞_ζ| = |𝒞_{ζ⁻¹}|`: if `0 ∉ 𝒞_ζ ∪ 𝒞_{ζ⁻¹}`, `Bip.Nbal |𝒞_ζ ∖ 0| q ≤ dim Icz`; otherwise `Bip.Nph (min …) q ≤ dim Icz` (as `lemma67_vi`, without `hp : S.p ≠ 2`, using `BipAny.theoremC_prime_pow`).

**(P3) Lemma 9.7.** For every prime `p`, `ζ ∈ R` and `|𝒞_ζ| = |𝒞_{ζ⁻¹}|`: `Bip.Nbal (cls (cExt c) ζ).card S.q ≤ Module.finrank F (Icz S c ζ)` (the index `0` as an ordinary coordinate, as in `EvenColours.C2`; use `Bip.lemma72_iii` as in `ColCount.Nbal_eq_Nz`).

## Part Q — colour 1 at an odd prime (Lemma 9.8)

**(Q1) Lemma 9.8.** If `S.p ≠ 2`: `EvenColours.NS S 1 (cls (cExt c) 1).card ≤ Module.finrank F (EvenBlocks.IcS S c 1)`. (From `ColOne.lemma66_ii` when `0 ∈ 𝒞_1` with `|𝒞_1| = 2j + 2`, via `EvenColours.C3_a` and `TheoremB.card_closedTuples`; from `ColOne.lemma66_iii` when `0 ∉ 𝒞_1` with `|𝒞_1| = 2j`; and `EvenColours.C3_d` when `|𝒞_1|` is odd. `IcS S c 1 = Ic1 S c` by `rfl`.)

## Part M — the block of colour −1 (Lemma 9.9)

Throughout Part M, `(−1 : F) ≠ 1` (equivalently `Even S.r`; then `S.p ≠ 2` and `q` is odd), and `W := EvenBlocks.WS S c (−1)` (the indices of `𝒞_{−1}` other than `0`); on the factor `B(W)` every `t_s` satisfies `(t_s + 1)^q = 0`.

**(M1) Coordinates.** There is an `F`-algebra isomorphism `Ψ : Peel.C F (S.q + 1) W.card ≃ₐ[F] (boxS S c).Box W` with `Ψ(y_i) = u − u⁻¹` where `u = −t_{e(i)}` (`e` an order bijection `Fin W.card ≃ W`). (Model: `ColOne.lemma23_i` at the point `1`; for instance compose it with the automorphism `t ↦ −t` that takes the point `−1` to the point `1`.)

**(M2) Units and the pair factor.** For `s ∈ W`, `t_s − 1` is a unit of `B(W)`; for `i ≠ l` in `W`, `t_i t_l − 1 = (unit) · (y_i + y_l)` with `y = Ψ(y)`. (Model: `ColOne.lemma23_ii_one`; `t_i t_l = u_i u_l`.)

**(M3) The binomial identity.** In characteristic `p` with `q = p^v`: `(a + b)^{q−1} = Σ_{u=0}^{q−1} (−1)^u a^u b^{q−1−u}` in every commutative `F`-algebra; this is `Tight.D F (q + 1) a b` (or `ColOne.Dab`, or `OddShapes`'s `Dab (q+1)` — use whichever is the polynomial of the ideals `TheoremB.DIdeal F (q+1)` and `Tight.VLam F (q+1)`, and say which). (From `BipAny.choose_pred_prime_pow`.)

**(M4) The generators.** For a perfect matching `P` of `𝒞_{−1}`: `gPS S c (−1) P = (unit) · Ψ(Π D(y_i, y_l))`, the product over the pairs `{i < l}` of `P` with `i ≠ 0` (the pair `{0, k_0}`, if any, contributes a unit).

**(M5) `0 ∈ 𝒞_{−1}`.** If `0 ∈ 𝒞_{−1}` and `|𝒞_{−1}| = 2j + 2`: `finrank F (IcS S c (−1)) = finrank F (TheoremB.DIdeal F (S.q + 1) j)`, hence `EvenCount.QkEven j (S.q + 1) ≤ finrank F (IcS S c (−1))` (Theorem O, `OddTheorem.theoremO` with `h = (q − 1)/2`, `2h + 2 = q + 1`, `1 ≤ h`). (Model: `ColOne.lemma66_ii`: after the increasing relabelling of `𝒞_{−1} ∖ {0}` as `{1, …, 2j + 1}`, the perfect matchings of `𝒞_{−1}` are the matchings of `BallotBound.Matching j` and the generators are the `DJ`.)

**(M6) `0 ∉ 𝒞_{−1}`.** If `0 ∉ 𝒞_{−1}` and `|𝒞_{−1}| = 2j + 2`: `finrank F (IcS S c (−1))` is the dimension of the ideal of `Peel.C F (S.q + 1) (2j + 2)` generated by the products `Π_{{i,l} ∈ P} D(y_i, y_l)` over the perfect matchings `P` of `Fin (2j + 2)`, which is `OddPatterns.VSAll F h (2j + 2) {(emptyPart, false)}` (`B5_no_marked`, tight patterns of `∅` = perfect matchings), hence `EvenCount.QkEven j (S.q + 1) ≤ finrank F (IcS S c (−1))` (by `OddTheorem.theorem811` with `isInterlaced_root_even` and `OddLayers.card_ZS_root_even` for `stdOddSetting h`).

**(M7) Lemma 9.9.** `EvenColours.NS S (−1) (cls (cExt c) (−1)).card ≤ Module.finrank F (EvenBlocks.IcS S c (−1))` (with `EvenColours.C3_c` for even sizes, `C3_d` for odd sizes, and size `0`: both sides `1`).

## Part S — summary

**(S1)** For every prime, every `R` with `IsReps2 S R` and every compatible `c`, every factor of the product of `EvenColours.C2` is at most the corresponding factor of `EvenBlocks.lemma95`, except possibly the factor of colour `1` when `S.p = 2`: i.e. `(S.p ≠ 2 → NS S 1 |𝒞_1| ≤ dim IcS S c 1)`, `(−1 ≠ 1 → NS S (−1) |𝒞_{−1}| ≤ dim IcS S c (−1))`, `(∀ ζ ∈ R, Nbal |𝒞_ζ| q ≤ dim Icz S c ζ)`.

## Remarks

- No hypothesis on `p` or `r` except where written. `p = 2` appears only in Part P.
- If a statement is easier in a slightly different but equivalent form, use it and say so.

## Checks done before sending (`chkE18.py`, `chkE18.log`)

The block of colour `−1` computed in the LITERAL ring `F_p[t_s]/((t_s + 1)^q)` with the literal generators of (6.2) (pair `{0, k_0}`: `t_{k_0} − 1`; pair `{i < l}`, `i ≠ 0`: `(t_l − 1)(t_i t_l − 1)^{q−1}`), for `(p, q) = (3, 3), (5, 5), (7, 7), (3, 9)` and `|𝒞_{−1}| = 2, 4, 6`, with and without the index `0` (16 cells): its dimension equals the dimension of the odd-box ideal `(Π (y_i + y_l)^{q−1})` in `F_p[y]/(y^q)` and equals `N_q(|𝒞_{−1}|) = QkEven (a − 1) (q + 1)` exactly (`3, 19, 141, 5, 61, 7, 127, 9, 217`). The binomial identity (M3) for `q = 3, 9, 27, 5, 7`. 84 checks, 0 failures. Controls (each must fire, and does): the same block at the point `t = 1` (colour `1`; 16 cells differ) and the count at the wrong box `QkEven (a − 1) q` (16 cells differ).
