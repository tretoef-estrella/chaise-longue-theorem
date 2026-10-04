# q_even_assembly.md — piece E20: Main Theorem′ for every even degree, every field and freeness over ℤ (paper v11 §9.5: Theorem 9.11, Corollary 9.12), and the Main Theorem′ for every m ≥ 1

Grepy Mandalay, 3 Oct 2026. New folder `RequestProject/EvenAll/`, namespace `EvenAll`.

## What this piece is

`EvenOne.E3` (piece E19) gives, for every `ColSetting S` over a field `F` (every prime, `2` included, every cofactor) and every `k`, the lower bound `card (closedT negT (2k+2)) ≤ finrank F (idealI S k)`, hence `QkEven k S.m ≤ dim` for even `S.m` and `TheoremB.Qk k S.m ≤ dim` for odd `S.m`. `EvenCount.finrank_IK_le_even` (piece E2) and `ColUpper.finrank_IK_le` give the upper bounds. `EvenAssembly.theorem_ii` and `theorem_iii` (piece E5) turn the hypothesis `HypH m k` into «every field» and «free over `ℤ`». This piece proves `HypH m k` for every even `m ≥ 2` and every `k`, states Main Theorem′ for every even `m` and for every `m ≥ 1`, and proves Corollary 9.12 of the paper (every block has exactly the dimension of its count; the bipartite ideals at `q = 2^v` over `F̄_2`), and its odd analogue Corollary 7.8.

## Setting (reuse unchanged)

- `EvenOne.E3`; `EvenBlocks.exists_setting`, `algClosureSetting`, `exists_isReps2`, `lemma95`, `SInv`, `IsReps2`, `IcS`; `EvenColours.C2`, `C4`, `C4_even`, `C4_odd`, `NS`, `C3_a`, `C3_b`, `C3_c`, `C3_d`, `closedT`, `negT`; `EvenMinus.lemma67_iv_reps2`.
- `ColDecomp.idealI`, `Icz`; `ColSplit.ColSetting.lemma61_ii`; `ColUpper.IK`, `psi_eq_psiG` (`ColSurv.psi S k J = psiG F S.m J`, by `rfl`), `finrank_IK_eq_rankOver`, `finrank_IK_le`; `ColAssembly.rank_map_algebraMap`, `mainTheorem'_Z`, `mainTheorem'_field`; `EveryField.rankOver`.
- `EvenCount.QkEven`, `finrank_IK_le_even`; `EvenAssembly.HypH`, `theorem_ii`, `theorem_iii`, `mainTheorem'_Z_even`, `mainTheorem'_field_even`; `TheoremB.Qk`; `Bip.Ibal`, `Iph`, `Nbal`, `Nph`.

## Part A — the hypothesis `H(m, k)` for every even `m`

**(A1)** For every `ColSetting S` over `F` and every `k`: `ColDecomp.idealI S k = ColUpper.IK F S.m k` (both are the span of the same family: `psi_eq_psiG`).

**(A2) Equality for every `ColSetting`.** For every `ColSetting S` over `F` and every `k`:
`finrank F ((idealI S k).restrictScalars F) = card (closedT (negT S) (2k+2))`; hence `= QkEven k S.m` if `Even S.m` and `= TheoremB.Qk k S.m` if `Odd S.m`. (`≥` is `EvenOne.E3`; `≤` is `EvenCount.finrank_IK_le_even` for even `S.m` (with `2 ≤ S.m`, since `S.m = p^v r ≥ 2`) and `ColUpper.finrank_IK_le` for odd `S.m`, with (A1) and `EvenColours.C4_even`, `C4_odd`.)

**(A3) `H(m, k)`.** For every even `m ≥ 2` and every `k`: `EvenAssembly.HypH m k`. (Let `p` be a prime dividing `m`; write `m = p^v·r` with `v ≥ 1` and `p ∤ r` (`Nat.exists_eq_pow_mul_and_not_dvd` or `Nat.factorization`); take `S := algClosureSetting p v _ r _ _` over `K := AlgebraicClosure (ZMod p)`, so `S.m = m`. By (A2), `finrank K (IK K m k) = QkEven k m`; by `finrank_IK_eq_rankOver` this is `rankOver K (intMatU m k)`; and `rankOver K A = rankOver (ZMod p) A` because the rank of a matrix does not change under the field extension `ZMod p → K` (`ColAssembly.rank_map_algebraMap`).)

## Part B — Theorem 9.11 (Main Theorem′ for every even `m`)

**(B1) Every field.** For every even `m ≥ 2`, every `k` and every field `F` (any universe): `rankOver F (intMatU m k) = QkEven k m` and `finrank F ((IK F m k).restrictScalars F) = QkEven k m`. (`EvenAssembly.theorem_ii` with (A3).)

**(B2) Main Theorem′, even `m`.** For every even `m ≥ 2` and every `k`: `RZ (2k+1) m ⧸ IZ m k` is a free `ℤ`-module of rank `m^{2k+1} − QkEven k m`, and for every field `F`, `finrank F (GA F (2k+1) m ⧸ IK F m k) = m^{2k+1} − QkEven k m`. (`EvenAssembly.theorem_iii` with (A3).)

## Part C — Main Theorem′ for every `m ≥ 1`

**(C1)** Define `Qall m k := if Even m then EvenCount.QkEven k m else TheoremB.Qk k m`.

**(C2) Main Theorem′.** For every `m ≥ 1` and every `k`: `RZ (2k+1) m ⧸ IZ m k` is a free `ℤ`-module of rank `m^{2k+1} − Qall m k`, and for every field `F`, `finrank F (GA F (2k+1) m ⧸ IK F m k) = m^{2k+1} − Qall m k` and `finrank F (IK F m k) = Qall m k`. (Odd `m`: `ColAssembly.mainTheorem'_Z`, `mainTheorem'_field`; even `m`: (B2), (B1).) This is the statement of v11 for every degree, with no topology.

## Part D — Corollary 9.12 (i): every block has exactly the dimension of its count

**(D1) Positivity.** For every `ColSetting S`: `NS S ζ (2j) ≥ 1` for every `ζ ∈ SInv S` and every `j`, and `Bip.Nbal a S.q ≥ 1` for every `a`. (A closed tuple exists: pair the coordinates; for `Nbal`, `(ξ, ξ)`.)

**(D2) Corollary 9.12 (i).** For every `ColSetting S`, every `R` with `IsReps2 S R`, every `k` and every `c : Fin (2k+1) → S.μ` with a compatible matching:
- `finrank F (IcS S c ζ) = NS S ζ |𝒞_ζ|` for every `ζ ∈ SInv S`, and
- `finrank F (Icz S c ζ) = Bip.Nbal |𝒞_ζ| S.q` for every `ζ ∈ R`.
(Sandwich. By `lemma61_ii`, `dim I = Σ_c dim π_c(I)`; by (A2) and `C4`, `dim I = Σ_c (term of C2)`; each term of `C2` is `≤ dim π_c(I)` (`EvenOne.E2`), so every term is an equality. For a compatible `c`, `dim π_c(I)` is the product of the block dimensions (`lemma95`), the term of `C2` is the product of the counts, each count is `≤` its dimension (`EvenOne.NS_le_finrank_IcS`, `EvenMinus.lemma97` with `existsA9`) and every count is `≥ 1` (D1); a product of naturals that equals a product of smaller-or-equal positive naturals forces each factor to be equal.)

## Part E — Corollary 9.12 (ii): the bipartite ideals at `q = 2^v`

**(E1)** For every `v ≥ 1`, `q = 2^v` and every `a`:
`finrank K ((Bip.Ibal K q a).restrictScalars K) = Bip.Nbal a q` and `finrank K ((Bip.Iph K q a).restrictScalars K) = Bip.Nph a q`, with `K = AlgebraicClosure (ZMod 2)`. (`a = 0`: `Ibal K q 0 = ⊤` in `R K q 0 0 ≅ K`, dimension `1 = Nbal 0 q`; `Iph K q 0 = ⊤` in `R K q 1 0`, dimension `q = Nph 0 q`. `a ≥ 1`: take `S := algClosureSetting 2 v _ 3 _ _` (`m = 3q`), `k := a`, and `ζ ∈ S.μ` with `ζ ≠ 1` (a primitive cube root of unity; `ζ⁻¹ ≠ ζ`), `R` with `IsReps2 S R` and `ζ ∈ R` (choose `R = {ζ}`: `SInv S = {1}` since `p = 2`). For `Ibal`: colour `a` coordinates of `Fin (2a+1)` by `ζ`, `a` by `ζ⁻¹` and the last one by `1`; then `cExt c 0 = 1`, `𝒞_1` has two elements, `0 ∉ 𝒞_ζ ∪ 𝒞_{ζ⁻¹}`, and by `EvenMinus.lemma67_iv_reps2` (first case) and (D2) `dim Ibal a = dim Icz = Nbal a q`. For `Iph`: colour `a + 1` coordinates by `ζ` and `a` by `ζ⁻¹`; then `cExt c 0 = ζ⁻¹`, `𝒞_1 = ∅`, `0 ∈ 𝒞_{ζ⁻¹}`, and `lemma67_iv_reps2` (second case, `β = a`) and (D2) give `dim Iph a = Nbal (a+1) q = Nph a q` (`Bip.lemma72_iii`). A compatible matching exists by `existsA9`.)

**(E2) Corollary 7.8 (odd `p`, the same argument).** For every odd prime `p`, `v ≥ 1`, `q = p^v` and every `a`: the same two equalities over `AlgebraicClosure (ZMod p)`. (Take `r := 3` if `p ≠ 3` and `r := 5` if `p = 3`, `S := algClosureSetting p v _ r _ _`, `ζ` a non-trivial `r`-th root of unity, `R` with `IsReps2 S R` and `ζ ∈ R` (exists: `ζ ≠ ζ⁻¹` because `r` is odd); the colourings and the citations are those of (E1), with `𝒞_1` now of size `1` resp. `0` among the non-zero indices. Say if a different choice is easier.)

## Remarks

- No hypothesis on `p`, `q` or `r` except where written.
- If a statement is easier in a slightly different but equivalent form, use it and say so. More general statements are fine if noted (for instance (E1) for every field of characteristic `2`).
- What is NOT in Lean after this piece, and must not be claimed: the topology (Pham's theorem and [DS, Thm 2.2], cited), i.e. the passage from Main Theorem′ to the homology of the Fermat variety.

## Checks done before sending (`chkE20.py`, `chkE20.log`)

- `dim_{F_p} (ψ_J) F_p[G] = QkEven k m` and the quotient `m^{2k+1} − QkEven k m`, for `(m, k) = (4,1), (4,2), (6,1), (8,1), (10,1), (12,1)` at the primes `2, 3, 5` (dividing `m` or not): `19, 141, 61, 127, 217, 331`, 30 checks.
- The unified count (tuples in `{1, …, m−1}^{2k+2}` that pair `a` with `−a mod m`) equals `QkEven k m` for even `m`; for odd `m` it gives `6, 36, 90, 168, 20` at `(3,1), (5,1), (7,1), (9,1), (3,2)`.
- Corollary 9.12 (ii) over `F_2`: `dim Ibal a = Nbal(a, q)` and `dim Iph a = Nph(a, q) = Nbal(a+1, q)` for `q = 2, 4`, `a = 0, 1, 2, 3` (`1, 2, 6, 20` and `2, 6, 20, 70` at `q = 2`; `1, 4, 28, 256` and `4, 28, 256, 2716` at `q = 4`).
- 59 checks, 0 failures. Controls (each fires): the odd formula at `m ± 1` differs from `QkEven k m` (6 cells), `Ibal` with exponent `q − 2` changes the dimension (3 cells), `Nbal` at the wrong `q` differs (6 cells).
