# q_oddbox_equality.md — piece E15: the equality at the odd box (paper v11 Lemma 8.12, Corollary 8.13), every field and freeness over ℤ

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/OddEquality/`, namespace `OddEquality`.

## What this piece is

`OddTheorem.theoremO` (piece E14) gives, for every field `F`, `h ≥ 1` and `k`, the inequality `QkEven k (2h+2) ≤ finrank F (TheoremB.DIdeal F (2h+2) k)`: the count at the odd box `r = 2h + 1` (the ring `Peel.C F (2h+2) m = F[y_1, …, y_m]/(y_i^r)`). This piece proves the reverse inequality, hence Theorem O with equality for every field, the freeness of the integral quotient, and the same for the companion ideal `ℳ = Σ_P D_P·C_N` of Lemma 8.12.

**The route is NOT the paper's.** The paper bounds `dim ℳ` through Proposition 10.5(ii) (a Macaulay duality, which is not in the project). Here only a perfect pairing of the box ring is used: the annihilator of `ℳ` contains the intersection of the ideals `I_P C_N`, and the intersection is bounded by a degeneration to points, exactly as in `q_degeneration.md` but with a set `T` of `r` points that contains `0`. As in Lemma 9.10, the injectivity of the map `θ` of Lemma 8.12 is not needed for the inequality.

## Setting (reuse unchanged)

- `Peel.C F q m` (the box ring `F[y]/(y_i^{q−1})`), `Tight.y`, `Tight.D F q` (the polynomial `D_r(a,b) = Σ_{u<r} (−1)^u a^u b^{r−1−u}` for `q = r + 1`), `TheoremB.DJ`, `TheoremB.DIdeal`; `OddTheorem.theoremO`, `theorem811`, `stdOddSetting`; `OddShapes.isInterlaced_root_even`, `emptyPart`; `OddLayers.card_ZS_root_even`; `OddPatterns.VSAll`, `B5_no_marked`; `EvenMinus.lemmaM6` (a model of how `ℳ` is identified with `VSAll F h (2j+2) {(emptyPart, false)}`).
- `Degeneration` (`q_degeneration.md`: gr of an ideal, top forms, the support bound), `EveryField.rankOver`, `rankOver_le_rankOver_rat`, `EveryField.Integral` (integer vectors of box monomials), `FreeZ.quotient_free_of_finrank_image`.
- `EvenCount.QkEven`, `PointedSetting`, `closedPointed`, `card_closedPointed` (`|closedPointed S (2k+2)| = QkEven k (2h+2)` for any pointed set with `h` classes).

Throughout, `r = 2h + 1 ≥ 3`, `q := r + 1 = 2h + 2` (so `Peel.C F q m` has the box `r`), `N := 2k + 2`.

## Part A — the ideal `ℳ` and the map `θ` (Lemma 8.12, one direction)

**(A1)** `ℳ := Σ_P D_P·C_N ⊆ Peel.C F q N`, the ideal spanned by the products `D_P := Π_{\{a,b\} ∈ P} D(y_a, y_b)` over the perfect matchings `P` of `Fin N`. It equals `OddPatterns.VSAll F h N {(OddShapes.emptyPart, false)}` (the patterns of the empty unmarked shape are the perfect matchings; `B5_no_marked`). Say if the identification is easier in another form.

**(A2)** `QkEven k q ≤ finrank F ℳ` for every field (`theorem811` with `isInterlaced_root_even` and `card_ZS_root_even`, as in `EvenMinus.lemmaM6`).

**(A3) θ.** `θ : Peel.C F q N →ₗ[F] Peel.C F q (2k+1)`, «the coefficient of `y_0^{r−1}`», with the variables `y_1, …, y_{2k+1}` of the target being `y_{i.succ}` of the source. (As `EvenOne.theta`, with the exponent `r − 1` in place of `0`.) It is `Peel.C F q (2k+1)`-linear through the inclusion `ι : y_i ↦ y_{i.succ}`: `θ (ι g · f) = g · θ f`.

**(A4)** For every matching `J ∈ BallotBound.Matching k` (vertex `0` paired with `J 0`): `θ (D_{P_J}) = D_J` (= `TheoremB.DJ F q J`), where `P_J` is `J` read as a perfect matching of `Fin N`. (The coefficient of `y_0^{r−1}` in `D(y_0, y_b)` is `(−1)^{r−1} = 1` because `r` is odd; the other factors do not contain `y_0`.)

**(A5)** `finrank F (DIdeal F q k) ≤ finrank F ℳ`. (`θ(ℳ)` is a `Peel.C F q (2k+1)`-submodule by (A3) and contains every `D_J` by (A4), so `DIdeal ⊆ θ(ℳ)`; and `dim θ(ℳ) ≤ dim ℳ`.)

## Part B — the pairing bound

**(B1) The pairing of the box ring.** On `C := Peel.C F q N`, `⟨f, g⟩ :=` the coefficient of the top monomial `Π_i y_i^{r−1}` in `f·g` is a perfect pairing (the monomial `y^α` pairs to `1` exactly with `y^{(r−1) − α}`). Hence for every subspace `V ⊆ C`: `finrank V + finrank V^⊥ = finrank C`, and for an ideal `V`, `Ann(V) := {g : g·V = 0} ⊆ V^⊥`. So `finrank V ≤ finrank C − finrank Ann(V)`.

**(B2)** `(y_a + y_b)·D(y_a, y_b) = y_a^r + y_b^r = 0` in `C` (Tight/OddShapes `A0`, `A3_D`). Hence for every perfect matching `P`, `I_P·C := (y_a + y_b : {a,b} ∈ P)·C ⊆ Ann(D_P)`, and `⋂_P I_P·C ⊆ Ann(ℳ)`.

**(B3)** `finrank F ℳ ≤ finrank F (C ⧸ ⋂_P I_P·C)` (from (B1), (B2)).

## Part C — the degeneration bound over `ℚ`

**(C1) Degeneration with a zero.** Generalize `q_degeneration.md` to any finite set `T ⊆ F` with `|T| = r` (no condition `Π(y − u) = y^{r} − 1`): with `g(y) := Π_{u∈T}(y − u)` (monic of degree `r`, top form `y^r`), `F[y_1, …, y_n]/(g(y_i))` is the ring of functions on `T^n` (distinct roots), and for every ideal `I ⊇ (g(y_i))`, `dim F[y]/I = dim F[y]/gr(I)` and `gr(I) ⊇ (y_i^r) + (top forms of generators)`. State it in the form you need; the existing proof should go through unchanged.

**(C2) The points.** Over `ℚ`, `T := {−h, …, h}`, a pointed set with the involution `u ↦ −u` and the fixed point `0` (`EvenCount.PointedSetting`). `Γ := closedPointed T N`, the tuples that split into pairs `{u, −u}`; `|Γ| = QkEven k q` (`card_closedPointed`).

**(C3) The ideal of one matching.** For a perfect matching `P` of `Fin N`: the ideal of the finite set `V(I_P) ∩ T^N` in `ℚ[y]` is `I_P + (g(y_i))`, and its ideal of top forms is `I_P + (y_i^r)`. (Both quotients have dimension `r^{k+1}`: eliminating `y_b = −y_a` for each pair, and `g` is odd, so `g(−y) = −g(y)`; `I_P + (y_i^r) ⊆ gr(I_P + (g(y_i)))` and equal dimensions.)

**(C4)** `gr(I(Γ)) ⊆ ⋂_P (I_P + (y_i^r))`, because `Γ ⊇ V(I_P) ∩ T^N` for every `P` (a point of `V(I_P)` with coordinates in `T` splits into the pairs of `P`), so `I(Γ) ⊆ I(V(I_P) ∩ T^N) = I_P + (g(y_i))`, and gr is monotone. Hence `dim ℚ[y]/⋂_P(I_P + (y_i^r)) ≤ dim ℚ[y]/gr(I(Γ)) = dim ℚ[y]/I(Γ) = |Γ|`.

**(C5)** `finrank ℚ (C_ℚ ⧸ ⋂_P I_P·C_ℚ) = dim ℚ[y]/⋂_P(I_P + (y_i^r))` (the box ideal `(y_i^r)` lies in every `I_P + (y_i^r)`), hence `≤ QkEven k q`.

## Part D — the theorem

**(D1) Equality over every field (Corollary 8.13).** For every field `F`, every `h ≥ 1` and every `k`:
`finrank F ((TheoremB.DIdeal F (2h+2) k).restrictScalars F) = QkEven k (2h+2)` and `finrank F ℳ = QkEven k (2h+2)`.
(Over `ℚ`: (A5), (B3), (C5) give `≤`, and `theoremO`, (A2) give `≥`. Over any `F`: both ideals are spanned by the images of integer vectors (the products times box monomials; as in `EveryField.Integral`), so `finrank_F = rankOver F A ≤ rankOver ℚ A = finrank_ℚ`; with `theoremO` and (A2), equality.)

**(D2) Freeness over `ℤ` (Theorem O, second sentence).** The quotient of `ℤ[y_1, …, y_{2k+1}]/(y_i^r)` (written as `Fin r^{2k+1}`-indexed integer vectors, or as `Peel.C ℤ (2h+2) (2k+1)`, whichever is easier) by the subgroup generated by the `D_J·y^α` is a free `ℤ`-module of rank `r^{2k+1} − QkEven k (2h+2)`; the same for `ℳ` in `N` variables, with rank `r^N − QkEven k (2h+2)`. (`FreeZ.quotient_free_of_finrank_image`: the dimension over `ZMod p` equals the dimension over `ℚ` by (D1).)

**(D3) (optional)** The dimension of each graded piece of `DIdeal F (2h+2) k` does not depend on `F`. Prove it only if it is convenient; otherwise say so.

## Remarks

- No hypothesis on the characteristic of `F`. `h ≥ 1` (so `r ≥ 3`); the case `k = 0` is included.
- If a statement is easier in a slightly different but equivalent form, use it and say so. More general statements are fine if noted (for instance (C1) for any finite `T`, or (B1) for any box).
- This piece is not on the path of Main Theorem′ (which uses only `≥`); it completes Theorem O as printed.

## Checks done before sending (`chkE15.py`, `chkE15.log`)

- `dim_F (D_J)·C_{2k+1} = N_r(2k+2)` over `F_2, F_3, F_5, F_7` and over `ℚ` (proxied by the prime `32003`) for `(r, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,0), (7,1), (9,1), (11,1), (13,1)`: `3, 19, 141, 5, 61, 7, 127, 217, 331, 469`.
- `dim ℳ = N_r(2k+2)` and `dim C_N/⋂_P I_P C_N = N_r(2k+2)` (so the bound of Part B is attained) at `(3,0), (3,1), (3,2), (5,0), (5,1), (7,0)`; `dim ℳ` also over `F_2, F_3`.
- `N_r(2k+2) = |Γ| = QkEven k (r+1)` for `T = {−h, …, h}`; the coefficient of `y_0^{r−1}` in `D(y_0, y_1)` is `1`.
- 111 checks, 0 failures. Controls (each fires): `D^−` (degree `r − 2`) in place of `D` changes the dimension (7 cells), the count at `r + 2` differs (10 cells), a point set without the zero gives another count (2 cells).
