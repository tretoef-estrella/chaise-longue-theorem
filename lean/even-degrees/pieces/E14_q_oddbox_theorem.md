# q_oddbox_theorem.md — the assembly of the odd box: Proposition 8.10, Theorem 8.11, Theorem O (`≥`)

Piece E14 of the Lean plan for the even degrees of the Chaise Longue paper (v11, §8.6–§8.7).
Written by Grepy Mandalay, 3 October 2026. Everything here uses, unchanged, the folders
`OddShapes`, `OddLayers`, `OddPatterns`, `OddLifts`, `OddLifts2`, `Lifts`, `Peel`, `Tight`,
`ChainLemma`, `Membership`, `TheoremB`, `EvenCount` of the project.

## Setting

`F` is a field, `h ≥ 1`, `r = 2h + 1`, `q = 2h + 2`. The box ring of level `m` is
`Peel.C F (2*h+2) m` (exponents below `r`), with variables `Tight.y F (2*h+2)`. Shapes are
`OddShapes.Shape = Partition × Bool` (`true` = marked), `OddShapes.Sh h m` is the set of shapes of
level `m`, `OddShapes.optS h s p` (`p = 1, …, 2h+1`) is the list of options of a shape,
`OddShapes.FS h Λ s` is `F_Λ(s)`, `OddShapes.IsInterlaced h m Λ` is Definition 8.2,
`OddLayers.layerS h m Λ i = {σ ∈ Sh h (m−1) : i < FS h Λ σ}` is `Λ_i`, and
`OddPatterns.VSAll F h m Λ` is `V_Λ`. The slices are `Peel.W (m := n+1) _ V d`; the slice `r − 1 − i`
of the paper is `d = 2h − i`.

For a shape `(μ, δ)` with `ℓ = μ.len`, the list `optS h (μ, δ) p` is: removals of the rows
`p = 1, …, ℓ`; the zero option `(μ, !δ)` at `p = ℓ + 1`; the middle option `(μ.addOne, δ)` for
`ℓ + 1 < p ≤ 2h + 1 − ℓ`; the additions `(μ.addE (2h + 2 − p), δ)` for `p > 2h + 1 − ℓ`.
`OddShapes.optS_filter_eq_Icc` (already proved) says: for `Λ` interlaced of level `m ≥ 1` and
`(μ, δ) ∈ Sh h (m − 1)`, the `p ∈ [1, 2h+1]` with `optS h (μ, δ) p ∈ Λ` are exactly `[1, Φ]`,
`Φ := FS h Λ (μ, δ)`.

## Part K — the case lemma (the analogue of `Lifts.cases_of_FLam`)

**Lemma K.** Let `h ≥ 1`, `Λ` interlaced of level `n + 1`, `(μ, δ) ∈ Sh h n`, and
`Φ := FS h Λ (μ, δ) ≥ 1`. Write `low := if δ then 2 else 1`. Then at least one of:

- **(A)** there are `lam` with `(lam, δ) ∈ Λ` and `cs ≥ low` with
  `colLen lam c = colLen μ c + [c = cs]` for every `c ≥ 1`, and `colLen μ cs + Φ = 2h + 1`;
- **(M)** `δ = true`, `(μ.addOne, true) ∈ Λ`, `(μ, false) ∈ Λ`, `μ.len < h`, and `Φ = 2h + 1 − μ.len`;
- **(Z)** `(μ, !δ) ∈ Λ` and `Φ = μ.len + 1`;
- **(R)** there are `lam` with `(lam, δ) ∈ Λ` and `c0 ≥ low` with
  `colLen lam c + [c = c0] = colLen μ c` for every `c ≥ 1`, and `colLen μ c0 = Φ`;
- **(R1)** `δ = true`, `1 ≤ μ.len`, `μ.row μ.len = 1`, `(μ.subE μ.len, true) ∈ Λ`, and `Φ = μ.len`.

*Proof (paper, proof of Proposition 8.10).* By `optS_filter_eq_Icc`, `optS h (μ, δ) Φ ∈ Λ` and
`optS h (μ, δ) (Φ + 1) ∉ Λ` (or `Φ = 2h + 1`). Split by the position of `p = Φ`.
- `p > 2h + 1 − ℓ` (an addition): `j0 := 2h + 2 − Φ ∈ [1, ℓ]`, the option is `(μ.addE j0, δ)`.
  `j0` is the first row of its length: if `j0 ≥ 2` and `μ.row (j0 − 1) = μ.row j0`, then
  `μ.addE (j0 − 1)` and `μ.addE j0` are equal-up-to-`≼` both ways (`Lifts.addE_le_of_row_eq`), so the
  option at `p = Φ + 1` (row `j0 − 1`) is in `Λ` by (D1), a contradiction. Then with `lam = μ.addE j0`
  and `cs = μ.row j0 + 1 ≥ 2`, `Lifts.colLen_addE` gives the column relation and
  `Lifts.colLen_row_succ` gives `colLen μ cs = j0 − 1 = 2h + 1 − Φ`. This is (A).
- `ℓ + 1 < p ≤ 2h + 1 − ℓ` (the middle option, so `ℓ < h`): all the middle options are the same shape,
  so `Φ = 2h + 1 − ℓ`. If `δ = false`: (A) with `lam = μ.addOne`, `cs = 1`, `colLen μ 1 = ℓ`
  (`Lifts.colLen_addOne`, `Lifts.colLen_one`). If `δ = true`: (M); `(μ, false) ∈ Λ` because the zero
  option `p = ℓ + 1 < Φ` is in `Λ`.
- `p = ℓ + 1` (the zero option): (Z).
- `p ≤ ℓ` (a removal): `ρ := Φ`, the option is `(μ.subE ρ, δ)`. `ρ` is the last row of its length:
  if `ρ < ℓ` and `μ.row (ρ + 1) = μ.row ρ`, then by `Lifts.subE_le_of_row_eq` (both ways) and (D1)
  the option at `p = Φ + 1` is in `Λ`, a contradiction. Put `c0 := μ.row ρ`; then `colLen μ c0 = ρ`
  (`Lifts.colLen_row`) and `Lifts.colLen_subE` gives the column relation. If `δ = false` or `c0 ≥ 2`
  this is (R). If `δ = true` and `c0 = 1`: the last row of length `1` is the row `ℓ`, so `ρ = ℓ` and
  `μ.row ℓ = 1`: this is (R1).

## Part P — Proposition 8.10 (`V_{Λ_i} ⊆ W_{r−1−i}(V_Λ)`)

**(P0)** Let `h ≥ 1`, `Λ` interlaced of level `n + 1`, `(μ, false) ∈ Sh h n`, `i < FS h Λ (μ, false)`,
and `T : Tight.TightPattern μ (Finset.univ : Finset (Fin n))`. Then
`T.prod F (2*h+2) ∈ Peel.W (m := n+1) _ (OddPatterns.VSAll F h (n+1) Λ) (2*h - i)`.

**(P1)** The same for `(μ, true) ∈ Sh h n`, `i < FS h Λ (μ, true)`, and
`T : OddPatterns.MarkedPattern μ (Finset.univ : Finset (Fin n))`: `T.prod F h ∈ … (2*h - i)`.

*Proof.* `Φ := FS ≥ i + 1`. By Lemma K, the product lies in the slice `2h + 1 − Φ`:
- (A): `OddLifts.T1` (δ = false) or `OddLifts.T3` (δ = true, `cs ≥ 2`); slice `colLen μ cs = 2h + 1 − Φ`,
  and `colLen μ cs ≤ 2h` since `Φ ≥ 1`.
- (M): `OddLifts2.T7`; slice `μ.len = 2h + 1 − Φ`.
- (Z): `OddLifts.T5` (δ = false; `μ.len ≤ h` from `Sh`) or `OddLifts2.T6` (δ = true; uses `1 ≤ h`);
  slice `2h − μ.len = 2h + 1 − Φ`.
- (R): `OddLifts.T2` (δ = false) or `OddLifts.T4` (δ = true, `c0 ≥ 2`); slice `2h + 1 − colLen μ c0
  = 2h + 1 − Φ`, with `1 ≤ colLen μ c0 = Φ ≤ 2h + 1` (`FS ≤ 2h + 1` follows from `OddShapes.FS_eq_card`).
- (R1): `OddLifts2.T8`; slice `2h + 1 − μ.len = 2h + 1 − Φ`.
Then `Lifts.W_mono_le` (with `q = 2h + 2`, so `3 ≤ q`) from `2h + 1 − Φ` to `2h − i` (`≤ 2h = q − 2`).

**(P) Proposition 8.10.** Let `h ≥ 1`, `m ≥ 1`, `Λ` interlaced of level `m`, `i ≤ 2h`. Then
`(OddPatterns.VSAll F h (m - 1) (OddLayers.layerS h m Λ i) : Set _) ⊆ Peel.W hm (OddPatterns.VSAll F h m Λ) (2*h - i)`.

*Proof.* As `Lifts.layer_subset_W`: write `m = n + 1`; the slice is an ideal (`Peel.W_isIdeal`,
`3 ≤ q`, `2h − i ≤ q − 2`); `VSAll` is the sup of the span of the tight products of
`comp _ false` and the span of the marked products of `comp _ true`, and every generator of either
lies in the slice by (P0), (P1) (a shape of `layerS` lies in `Sh h n` and has `i < FS`).

## Part T — Theorem 8.11 (interlaced down-set theorem)

**(T) Theorem 8.11.** For every field `F`, every finite type `T` with `[DecidableEq T]`, every
`S : OddShapes.OddSetting T h`, every `m` and every `Λ` with `OddShapes.IsInterlaced h m Λ`:
`(OddShapes.ZS S m Λ).card ≤ Module.finrank F ((OddPatterns.VSAll F h m Λ).restrictScalars F)`.

*Proof.* Induction on `m` (generalizing `Λ`), as `Induction.finrank_VLamAll_ge_card_ZLam`.
- `m = 0`: `Sh h 0 = {(∅, false)}` (a marked shape needs `|λ| + 1 ≤ 0`), so `|Z_Λ| ≤ 1`; if `Z_Λ` is
  non-empty, the shape of the empty tuple is `(∅, false) ∈ Λ`, the empty tight pattern has product
  `1`, so `1 ∈ VSAll` and the dimension is `≥ 1` (the box ring is non-trivial, `q ≥ 2`).
- `m ≥ 1`: `OddLayers.card_ZS_eq_sum` (`|Z_Λ| = Σ_{i < 2h+1} |Z_{Λ_i}|`), `Peel.finrank_eq_sum`
  with `q = 2h + 2` (`dim V_Λ = Σ_{j < 2h+1} dim W_j`), reflect the sum (`j = 2h − i`), the induction
  hypothesis on `layerS h m Λ i` (interlaced by `OddLayers.isInterlaced_layerS`, needs `1 ≤ h`,
  which is `S.one_le`), and `Submodule.finrank_mono` with (P).

## Part O — Theorem O, the inequality `≥`

**(O) Theorem O (`≥`).** For every field `F`, every `h ≥ 1` and every `k`:
`EvenCount.QkEven k (2*h+2) ≤ Module.finrank F ((TheoremB.DIdeal F (2*h+2) k).restrictScalars F)`.

*Proof.* `Λroot := {(onePart, false), (emptyPart, true)}` is interlaced of level `2k + 1`
(`OddShapes.isInterlaced_root_odd`), and `|Z_{Λroot}| = QkEven k (2h+2)`
(`OddLayers.card_ZS_root_odd`, for any `OddSetting`; build one, e.g. `T = Option (Fin h × Bool)`
with `none` the zero and `(u, ε) ↦ (u, !ε)`). By (T), `QkEven k (2h+2) ≤ dim VSAll F h (2k+1) Λroot`.
It remains `VSAll F h (2k+1) Λroot ≤ TheoremB.DIdeal F (2h+2) k`:
- the tight part is `Tight.VLamAll F (2h+2) (2k+1) {TheoremB.one} = TheoremB.DIdeal F (2h+2) k`
  (`TheoremB.VLamAll_one_eq`; `comp Λroot false = {onePart}` and `onePart = TheoremB.one`);
- a marked pattern of `emptyPart` on `Fin (2k+1)`: `ℓ = 0`, no blocks, marked block `B0` with
  `|B0| = 1 + 2t`, pairs `P` covering the rest; its product is `D_P · markedPf F h 0 B0`. By
  `OddPatterns.D3` (with `l = 0`, needs `1 ≤ h`), `markedPf F h 0 B0 ∈ Membership.UB (2h+1) 1 y B0`,
  spanned by `Tight.vand y {s} · DPy (2h+1) y Q` with `Q` a perfect matching of `B0 ∖ {s}`;
  `vand y {s} = 1`, and `D_Q · D_P` is the product of the tight pattern of `onePart` with pairs
  `Q ∪ P` and first block `{s}`, hence lies in `DIdeal`.

At `h = 1` this is `Odd3.O_ge_three` (consistency, not a dependency).

## Checks done before sending (Grepy Mandalay, `chkE14.py`, `chkE14.log`)

Part K was checked in the Lean convention of `optS` for every interlaced pair of the levels
`m ≤ 8` (`h = 1`), `m ≤ 6` (`h = 2`), `m ≤ 5` (`h = 3`): 154 interlaced pairs, 948 tails with
`Φ ≥ 1`; in each, the disjunct predicted from `Φ` holds with its numbers (column relations,
`colLen μ cs + Φ = 2h + 1`, `colLen μ c0 = Φ`, `cs, c0 ≥ low`), the side conditions of the lifts
hold, `FS ≤ 2h + 1`, and the options in `Λ` form `[1, Φ]`: 8 743 checks, 0 failures. Controls
fire: for pairs of down-sets that fail (D2) the initial segment breaks (379 times), the middle
option of a marked shape can lack `(μ, false)` (45), and taking the first row instead of the row
`ρ` breaks `colLen μ c0 = Φ` (17). Parts P, T, O are Proposition 8.10, Theorem 8.11 and
Theorem O of the paper, already checked by the auditors with their own engines (12 530 slice
memberships of Proposition 8.10, 0 failures; `dim V_Λ ≥ |Z_Λ|` on 163 interlaced pairs, with
equality; Theorem O on 18 cells over `F_2, F_3, F_5, F_7`).
