# q_even_block_one.md — piece E19: the block of colour 1 at the prime 2, and the lower bound for every even degree (paper v11 §9.4 Lemma 9.10, §9.5)

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/EvenOne/`, namespace `EvenOne`.

## What this piece is

Pieces E16–E18 (`EvenBlocks`, `EvenColours`, `EvenMinus`) give the colour reduction for every prime and the lower bound for every block except one: the block of colour `1` at the prime `2`. This piece proves that block (Lemma 9.10 of the paper) and then puts the blocks together: for every `ColSetting S` (every prime, `2` included, every cofactor), `card (closedT negT (2k+2)) ≤ dim_F I` — that is, `Q_k(m) ≤ dim_F I` for every even `m` (and for every odd `m`). Piece E20 will add the equality and the transfer to every field and to `ℤ`.

At the prime `2` the block of colour `1` lives in a group algebra `F[t_i]/(t_i^q − 1)` with `q = 2^v`: there is no coordinate `y = t − t⁻¹`. If `0 ∈ 𝒞_1`, the block IS the ideal `(ψ_J)` of degree `q` (`ColUpper.IK F q j`), and `Pow2.prop92_ge` with Theorem O bounds it. If `0 ∉ 𝒞_1`, a linear map `θ` (the coefficient of `t_{i_1}^0`, `i_1 = min 𝒞_1`) sends the generators to those of the first case.

## Setting (reuse unchanged)

- `S : ColSplit.ColSetting F` with `S.p = 2` in Parts A–D (then `CharP F 2` from `S.charP`, `S.q = 2 ^ S.v`, `S.v ≥ 1`); `c`, `cExt`, `cls`, `ColDecomp.boxS`, `tB`, `pairF`; `ColTensor.BoxSetting.Box`, `t`, `boxLift`.
- `EvenBlocks`: `SInv`, `SInv_subset`, `IsReps2`, `exists_isReps2`, `existsA9`, `WS`, `gPS`, `IcS`, `lemma95`; `EvenColours`: `NS`, `C2`, `C3_b`, `C3_d`, `C4`, `C4_even`, `C4_odd`, `closedT`, `negT`.
- `EvenMinus`: `lemma97`, `lemma98`, `lemma99`, `ebarS` (model of the relabelling), `lemmaM5` (model of the case `0 ∈ 𝒞`), `finrank_IcS_of_card_eq_zero` (model for size `0`).
- `ColSplit.GA`, `gaIdeal`, `ColSplit.ColSetting.lemma61_ii`; `ColUpper.IK`, `psiG`, `tU`; `ColSurv.phi`.
- `Pow2.phi_two_pow`, `Pow2.prop92_ge`, `Pow2.pow2_of_oddbox`, `Pow2.q_two`; `OddTheorem.theoremO`; `EvenCount.QkEven`.

## Part A — the box at the point 1 at the prime 2 is a group algebra

**(A1)** In every commutative ring of characteristic `2` and for `q = 2^v`, `v ≥ 1`: `(u − 1)^{q−1} = ColSurv.phi q u` and `(u − 1)^q = u^q − 1`. (From `Pow2.phi_two_pow`.)

**(A2)** If `S.p = 2` and `W := WS S c 1`, then for every bijection `e : Fin n ≃ W` there is an `F`-algebra isomorphism `Φ_e : ColSplit.GA F n S.q ≃ₐ[F] (boxS S c).Box W` with `Φ_e (mk (X i)) = t_{e i}`. (On `W` every `c_s = 1`, and `(t − 1)^q = t^q − 1` by (A1); use `boxLift` and the universal property of `GA`.)

## Part B — `0 ∈ 𝒞_1`

**(B1)** If `S.p = 2`, `0 ∈ 𝒞_1` and `|𝒞_1| = 2j + 2`: `finrank F (IcS S c 1) = finrank F ((ColUpper.IK F S.q j).restrictScalars F)`. (After the increasing relabelling `ē : Fin (2j+2) ≃o 𝒞_1`, `ē 0 = 0`, as in `EvenMinus.lemmaM5` / `ColOne.lemma66_ii`, the perfect matchings of `𝒞_1` are the `BallotBound.Matching j`, and `Φ_e` (with `e` the increasing bijection of `W`) sends `psiG F S.q J` to `gPS S c 1 P` EXACTLY, no unit: `pairF` gives `t_b − 1` for the pair `{0, b}` and `(t_b − 1)(t_a t_b − 1)^{q−1} = (t_b − 1)·phi q (t_a t_b)` by (A1) for the others — the two factors of `psiG`.)

**(B2)** If `S.p = 2`: `EvenCount.QkEven j S.q ≤ finrank F ((ColUpper.IK F S.q j).restrictScalars F)` for every `j`. (If `S.v ≥ 2`: `OddTheorem.theoremO` with `h = (S.q − 2)/2 ≥ 1`, `2h + 2 = S.q`, then `Pow2.prop92_ge` (or `Pow2.pow2_of_oddbox`, which gives the equality). If `S.v = 1`: `Pow2.q_two`.)

**(B3)** Hence, under (B1): `EvenCount.QkEven j S.q ≤ finrank F (IcS S c 1)`.

## Part C — `0 ∉ 𝒞_1` (the map θ)

**(C1) θ.** For `n` and `q ≥ 1` let `ι : GA F n q →ₐ[F] GA F (n+1) q` be induced by `X i ↦ X i.succ`, and let `θ : GA F (n+1) q →ₗ[F] GA F n q` be «the coefficient of `X 0 ^ 0`»: every `f` is uniquely `Σ_{u < q} X 0^u · ι(f_u)`, and `θ f = f_0`. (One implementation: `θ (mk p) := mk (Σ_{d ∈ p.support, q ∣ d 0} coeff d p • monomial (d ∘ Fin.succ) 1)`; it is well defined because it sends `p·(X 0^q − 1)` to `0` and `p·(X i.succ^q − 1)` to `θ(p)·(X i^q − 1)`. Any other definition is fine; say which.)

**(C2)** `θ (ι h · f) = h · θ f` for all `h`, `f` (θ is `GA F n q`-linear through `ι`), and `θ (X 0^u · ι h) = if u = 0 then h else 0` for `u < q`.

**(C3)** For `q = 2^v`, `v ≥ 1`, in characteristic `2` and `b : Fin n`: `θ ((ι (X b) − 1) · phi q (X 0 · ι (X b)) · ι h) = (X b − 1) · h`. (The coefficient of `X 0^0` in `phi q (X 0 · ι X b) = Σ_{u<q} X 0^u ι(X b)^u` is `1`.)

**(C4)** If `S.p = 2`, `0 ∉ 𝒞_1` and `|𝒞_1| = 2j + 2`: with `ē : Fin (2j+2) ≃o 𝒞_1` increasing (so `ē 0 = i_1 := min 𝒞_1`) and the increasing bijection `e : Fin (2j+2) ≃ W` (here `W = 𝒞_1 ∖ {0}` has `2j + 2` elements, `e 0 ↔ i_1`): for every perfect matching `P` of `𝒞_1`, `θ (Φ_e⁻¹ (gPS S c 1 P)) = psiG F S.q J` with `J := ē⁻¹ ∘ P ∘ ē ∈ BallotBound.Matching j` (vertex `0` of `J` is `i_1`; the variable `X i` of `GA F (2j+1) q` is vertex `i.succ`). (The pair `{i_1, l}` gives `(t_l − 1)·phi q (t_{i_1} t_l)` by (A1), and (C3) leaves `t_l − 1`, the factor of the pair `{0, J 0}` of `psiG`; the other pairs do not contain `i_1` and pass through by (C2).)

**(C5)** Hence `finrank F (IcS S c 1) ≥ finrank F ((ColUpper.IK F S.q j).restrictScalars F)` and, with (B2), `EvenCount.QkEven j S.q ≤ finrank F (IcS S c 1)`. (`ℳ := Φ_e⁻¹(IcS S c 1)`; `θ(ℳ)` is a `GA F (2j+1) q`-submodule by (C2), contains every `psiG F S.q J` by (C4) (every `J` comes from some `P`), so `θ(ℳ) ⊇ IK F S.q j` and `dim ℳ ≥ dim θ(ℳ) ≥ dim IK`.) **Note:** the paper also proves that `θ` is injective on `ℳ` (by the invariance under `g = Π t_i`); that gives the equality and is NOT needed for the inequality — prove it only if it is convenient.

## Part D — Lemma 9.10

**(D1) Lemma 9.10.** If `S.p = 2`: `EvenColours.NS S 1 (cls (cExt c) 1).card ≤ Module.finrank F (EvenBlocks.IcS S c 1)`. (Size `0`: both sides `1` — `C3_b` and the analogue of `EvenMinus.finrank_IcS_of_card_eq_zero` for the colour `1`; size `2j + 2`: `C3_b` with (B3) or (C5); odd size: `C3_d`.)

## Part E — the lower bound for every even degree

**(E1)** For every `ColSetting S` (every prime), every `R` with `IsReps2 S R` and every `c` with a compatible matching: `(∏ ζ ∈ SInv S, NS S ζ |𝒞_ζ|) · ∏ ζ ∈ R, Bip.Nbal |𝒞_ζ| S.q ≤ (∏ ζ ∈ SInv S, finrank (IcS S c ζ)) · ∏ ζ ∈ R, finrank (Icz S c ζ)`. (Factor by factor: `ζ ∈ SInv S` is `1` or `−1` (`SInv_subset`); colour `1`: `EvenMinus.lemma98` if `S.p ≠ 2`, (D1) if `S.p = 2`; colour `−1 ≠ 1`: `EvenMinus.lemma99`; `ζ ∈ R`: `EvenMinus.lemma97` with `|𝒞_ζ| = |𝒞_{ζ⁻¹}|` from `existsA9`.)

**(E2)** For every `c` (compatible or not): the term of `EvenColours.C2` (`if ∃ J, Compatible (cExt c) J then … else 0`) is `≤ finrank F ((idealI S k).map (S.piC c))`. (`lemma95` and (E1).)

**(E3) Theorem 9.11, `≥`, over `F`.** For every `ColSetting S` and every `k`: `(closedT negT (2k+2)).card ≤ finrank F ((idealI S k).restrictScalars F)`; hence `EvenCount.QkEven k S.m ≤ finrank F (idealI S k)` if `Even S.m`, and `TheoremB.Qk k S.m ≤ finrank F (idealI S k)` if `Odd S.m`. (`lemma61_ii` writes `dim I` as the sum over `c` of `dim π_c(I)`; (E2) and `EvenColours.C4`, `C4_even`, `C4_odd`.)

## Remarks

- Parts A–D assume only `S.p = 2`; Part E no hypothesis on `p`, `q`, `r`.
- If a statement is easier in a slightly different but equivalent form, use it and say so.

## Checks done before sending (`chkE19.py`, `chkE19.log`)

In the LITERAL ring `F_2[t_s]/(t_s^q − 1)` with the literal generators of (6.2) at the point `1`, for `q = 2, 4, 8`: case `0 ∈ 𝒞_1` (`2j + 1` variables) and case `0 ∉ 𝒞_1` (`2j + 2` variables), `j = 0, 1, 2` where `q^n ≤ 4096`. The block generators equal the `ψ_J` of degree `q` exactly (no unit); the dimension equals `QkEven j q` in both cases (`1, 1, 1, 3, 19, 141, 7, 127`); `θ(g_P)` equals the case-`0 ∈ 𝒞_1` generator of the relabelled matching for every `P`; and `θ` restricted to `ℳ` has rank `dim ℳ`. The colour-reduction sum `dim_{F_p} (ψ_J) F_p[G] = Q_k(m)` for `(m, k, p) = (4,1,2), (4,2,2), (6,1,2), (6,1,3), (8,1,2), (10,1,2), (10,1,5), (12,1,2), (12,1,3)` (`19, 141, 61, 61, 127, 217, 217, 331, 331`). 118 checks, 0 failures. Controls (each must fire, and does): the count at the wrong box `QkEven j (2q)` (8 cells), `θ` with the coefficient of `t_{i_1}^1` (23 matchings), and the exponent `q − 2` instead of `q − 1` (3 cells).
