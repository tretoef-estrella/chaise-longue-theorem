# q_even_count_colours.md — piece E17: the count factors over the blocks, for every degree (paper v11 §9.3, Lemma 9.6)

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/EvenColours/`, namespace `EvenColours`.

## What this piece is

Piece E16 (`EvenBlocks`) split the ideal along the blocks of a colouring, for every prime and every cofactor: the classes of the self-inverse colours `SInv S` (`{1}`, or `{1, −1}` when `r` is even) and the pairs `𝒞_ζ ∪ 𝒞_{ζ⁻¹}`, `ζ ∈ R` (`IsReps2 S R`). This piece splits the COUNT in the same way (Lemma 9.6 of the paper): the number `Q_k(m)` of closed tuples is the sum over the compatible colourings of a product of block counts. It is the analogue of `ColCount.lemma68_i/ii/iii` (piece 27, odd degrees), with three differences: no hypothesis on the parity of `p` or `r`; the self-inverse colours are indexed by `SInv S`; and **the index `0` is an ordinary coordinate of the count**, so every pair block contributes `Bip.Nbal (|𝒞_ζ|) q` (no phantom count, unlike `ColCount.Nz`).

## Setting (reuse unchanged)

- `S : ColSplit.ColSetting F` (any field, `p` any prime, `p = 2` allowed, `q = S.q = p^v`, `v ≥ 1`, `r ≥ 1`, `μ = S.μ`), `S.m = q·r`.
- `ColSurv.cExt`, `ColComp.cls`, `ColComp.Compatible`, `BallotBound.Matching`.
- `EvenBlocks.SInv`, `EvenBlocks.IsReps2`, `EvenBlocks.exists_isReps2`, `EvenBlocks.existsA9`, `EvenBlocks.SInv_eq_singleton`, `EvenBlocks.even_r_facts`, `EvenBlocks.r_ne_zero`.
- `Fibres.cnt`; `Bip.Nbal`, `Bip.lemma72_iii`; `TheoremB.FibreSetting`, `closedTuples`, `stdSetting`, `Qk`, `card_closedTuples`; `EvenCount.PointedSetting`, `closedPointed`, `QkEven`, `card_closedPointed`, `stdPointed`.
- Models for the proofs: `ColCount.Defs`, `ColCount.Colours`, `ColCount.Blocks` (`Good`, `card_good_eq_prod`, `blk`, `card_good_one`, `card_good_pair`), `ColCount.Main`.

## Definitions

- `Om S := ZMod S.q` (a model of the `q`-th roots of unity: `0` plays `1`, negation plays inversion; `S.q ≥ 2`). Use `Fin S.q` with its negation instead if it is easier, and say so.
- `T2 S := {x : Om S × S.μ // x ≠ (0, ⟨1, _⟩)}` with `negT (w, ζ) := (−w, ζ⁻¹)` (it maps `T2 S` to itself).
- For a finite type `X` with `neg : X → X`: `closedT neg n : Finset (Fin n → X) := univ.filter (fun g => (∀ u, cnt g u = cnt g (neg u)) ∧ ∀ u, neg u = u → Even (cnt g u))` (the tuples that split into pairs `{u, neg u}`).
- For a colour `ζ : F` and `a : ℕ`: `NS S ζ a := if ζ = 1 then (closedT (fun w => −w) a : Finset (Fin a → {w : Om S // w ≠ 0})).card else (closedT (fun w => −w) a : Finset (Fin a → Om S)).card` (on `𝒞_1` the entries avoid the point `1`; on `𝒞_{−1}` they do not, because `−w ≠ 1` there).

## (C0) The model point set

(i) `negT` is an involution of `T2 S`. (ii) `Fintype.card (T2 S) = S.m − 1`. (iii) If `Even S.m`, `negT` has exactly one fixed point; if `Odd S.m`, it has none. (The fixed point is `(q/2, 1)` when `p = 2`, and `(0, −1)` when `r` is even; exactly one of the two happens.) (iv) If `Even S.m`, there is `P : EvenCount.PointedSetting (T2 S) ((S.m − 2)/2)` with `P.neg = negT`, and `(closedT negT (2k+2)).card = EvenCount.QkEven k S.m`. (v) If `Odd S.m`, there is `Q : TheoremB.FibreSetting (T2 S) ((S.m − 1)/2)` with `Q.neg = negT`, and `(closedT negT (2k+2)).card = TheoremB.Qk k S.m`.

## (C1) The colour of the index `0` is determined

For `g ∈ closedT negT n`, `∏ i, ((g i).1.2 : F) = 1`. Hence for `g ∈ closedT negT (2k+2)`, `((g 0).1.2 : F) = cExt (fun j => (g j.succ).1.2) 0`.

## (C2) The factorization (Lemma 9.6, one colouring)

For every `k`, every `c : Fin (2k+1) → S.μ` and every `R` with `IsReps2 S R`:
`((closedT negT (2k+2)).filter fun g => ∀ i, ((g i).1.2 : F) = cExt c i).card = if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) * ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q else 0`.
(The splitting of a closed tuple restricts to each block, because a splitting matching is compatible with the colours; on `𝒞_1` the entries are `(w, 1)` with `w ≠ 0`; on `𝒞_{−1}` they are `(w, −1)` with `w` arbitrary; on `𝒞_ζ ∪ 𝒞_{ζ⁻¹}` the multiset of the `w` on `𝒞_ζ` equals the multiset of the `−w` on `𝒞_{ζ⁻¹}`, which is `Nbal` after `w ↦ −w`. The conditions concern disjoint coordinates, so the count is a product.)

## (C3) The closed forms of the block counts

(a) If `S.p ≠ 2`: `NS S 1 a = (TheoremB.closedTuples (TheoremB.stdSetting ((S.q − 1)/2) _) a).card` (the count `N_1` of `ColCount`; no fixed point).
(b) If `S.p = 2`: `NS S 1 0 = 1` and `NS S 1 (2k' + 2) = EvenCount.QkEven k' S.q` (the point set `Om ∖ {0}` has the one fixed point `q/2` and `q − 1` elements).
(c) If `(−1 : F) ≠ 1`: `NS S (−1) 0 = 1` and `NS S (−1) (2k' + 2) = EvenCount.QkEven k' (S.q + 1)` (here `q` is odd and the one fixed point is `0`).
(d) For `ζ ∈ SInv S` and `a` odd, `NS S ζ a = 0`.

## (C4) Lemma 9.6 (the sum)

For every `k` and every `R` with `IsReps2 S R`:
`∑ c : Fin (2k+1) → S.μ, (if ∃ J, Compatible (cExt c) J then (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) * ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q else 0) = (closedT negT (2k+2)).card`;
hence `= EvenCount.QkEven k S.m` if `Even S.m`, and `= TheoremB.Qk k S.m` if `Odd S.m`.

## Remarks for the proofs

- Follow `ColCount.lemma68_iii`: partition the closed tuples by their colours at the indices `j.succ` and use (C1) for the index `0`.
- Follow `ColCount.card_good_eq_prod` for (C2), with the blocks indexed by `SInv S ⊕ R` (as `EvenBlocks.blocks2`) instead of `Option R`.
- For (C0)(iii): `w = −w` in `ZMod q` iff `w = 0` or (`q` even and `w = q/2`); `ζ⁻¹ = ζ` iff `ζ ∈ SInv S`; `p = 2` and `Even r` cannot both hold (`EvenBlocks.not_p_dvd_r`); `Even S.m ↔ (S.p = 2 ∨ Even S.r)`.
- No hypothesis on the parity of `p`, `q`, `r` anywhere except where written (`Even S.m`, `Odd S.m`, `S.p ≠ 2`, `S.p = 2`, `(−1 : F) ≠ 1`).

## Checks done before sending (`chkE17.py`, `chkE17.log`)

Fourteen cells `(p, v, r, k)`, with `μ_r` and `Om` modelled as `Z/r`, `Z/q` (negation for inversion): even `m` at the prime `2` (`(2,1,3,1)`, `(2,1,3,2)`, `(2,2,3,1)`, `(2,1,5,1)`, `(2,3,3,1)`, i.e. `m = 6, 6, 12, 10, 24`) and at an odd prime with an even cofactor (`(3,1,2,1)`, `(3,1,2,2)`, `(3,1,4,1)`, `(5,1,2,1)`, `(5,1,4,1)`, `(3,2,2,1)`, `(3,1,2,3)`, i.e. `m = 6, 6, 12, 10, 20, 18, 6`), and odd `m = 15` at `p = 3` and `p = 5`. Checked: (C0)(ii)–(iii) (card and the number of fixed points), (C1), (C2) for every colouring against a direct count of the closed tuples with that colour tuple, (C3)(a)–(c) for every block met, (C4) the sum against the direct total and against `QkEven k m` for even `m` (`61, 1001, 331, 217, 1519, 61, 1001, 331, 217, 1027, 817, 18733`) and `3m² − 9m + 6 = 546` for `m = 15`. 1 869 checks, 0 failures. Controls (each must fire, and does): dropping the factor of the class `−1` (7 cells), treating the index `0` as a phantom in the pair blocks (9 cells), and counting the class `−1` over `Om ∖ {0}` (7 cells).
