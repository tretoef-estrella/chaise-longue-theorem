# The assembly for an even degree, and Main Theorem′ for the degree `4`

This file uses, unchanged:
- `q_col_upper.md`: for any field `K`, any `m ≥ 1` and `k ≥ 0`, with `d = 2k + 1`: the group algebra `K[G] = K[t_1, …, t_d]/(t_i^m − 1)`, the elements `ψ_J`, the ideal `I_K = (ψ_J : J a matching) ⊆ K[G]`, the integer matrix `A` (rows indexed by the pairs `(ν, J)`, columns by the exponents `μ`), and its parts (0) `dim_K K[G] = m^d`; (i) `dim_K I_K = rank_K(A)`; (ii) if `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)` in `K[X]`, then `dim_K I_K = |Γ|`.
- `q_every_field.md`: for an integer matrix `A`, `rank_F(A) ≤ rank_ℚ(A)`, with equality if `char F = 0`.
- `q_free_Z.md`, the Lemma (integer matrices): for a subgroup `L ⊆ Z^n`, if for every prime `p` the image of `L` in `F_p^n` has dimension `r = dim_ℚ (ℚ-span of L)`, then `Z^n/L` is free of rank `n − r`.
- `q_col_assembly.md`: the invariance of the rank of a matrix under extension of the field (so `rank_F(A) = rank_{F_p}(A)` for a field `F` of characteristic `p`); the fact that in an algebraically closed field `K` with `n ≠ 0` in `K`, `X^n − 1 = Π_{ξ∈μ_n}(X − ξ)` with `|μ_n| = n`; the ring `R = Z[t_1, …, t_d]/(t_i^m − 1)` with its monomial basis, the ideal `I_Z = (ψ_J : J) ⊆ R`, and the fact that the coordinate map `R ≅ Z^n` (`n = m^d`) carries `I_Z` onto the `Z`-span `L` of the rows of `A`; and the fact that, for every field `F`, the image of `L` in `F^n` spans a space of dimension `rank_F(A)`.
- `q_even_count.md`: the number `Q^e_k(m)`; its part (v): for even `m` with `m ≠ 0` in `K` and `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)`, `|Γ| = Q^e_k(m)`; and its part (vi): for even `m ≥ 2`, `rank_ℚ(A) = Q^e_k(m)` and `dim_F I_F ≤ Q^e_k(m)` for every field `F`.
- `q_pow2_leading.md`, part (vii): for every field `F` of characteristic `2` and every `k`, with `m = 4`: `dim_F I_F = Q^e_k(4)`.

## Setting

`m ≥ 2` is even, `k ≥ 0`, `d = 2k + 1`, `n = m^d`. `A` is the integer matrix of `q_col_upper.md` for `(m, k)`. For a field `F`, `I_F ⊆ F[G]` is the ideal of the `ψ_J`. `R = Z[t_1, …, t_d]/(t_i^m − 1)` and `I_Z ⊆ R` is the ideal of the `ψ_J`.

**Hypothesis `H(m, k)`.** For every prime `p` dividing `m`: `rank_{F_p}(A) = Q^e_k(m)`.

(Equivalently, by (i) of `q_col_upper.md`: `dim_{F_p} I_{F_p} = Q^e_k(m)` for every prime `p | m`.)

## Theorem

**(i) (away from the primes of `m`)** Let `m ≥ 2` be even and `F` a field in which `m ≠ 0` (that is, of characteristic `0`, or of characteristic `p` with `p ∤ m`). Then `rank_F(A) = Q^e_k(m)` and `dim_F I_F = Q^e_k(m)`.

**(ii) (every field, under `H`)** Let `m ≥ 2` be even and assume `H(m, k)`. Then for every field `F`: `rank_F(A) = Q^e_k(m)` and `dim_F I_F = Q^e_k(m)`.

**(iii) (Main Theorem′ for an even degree, under `H`)** Let `m ≥ 2` be even and assume `H(m, k)`. Then `R/I_Z` is a free `Z`-module of rank `m^{2k+1} − Q^e_k(m)`, and for every field `F`, `dim_F F[G]/I_F = m^{2k+1} − Q^e_k(m)`.

**(iv) (`H` for the degree `4`)** `H(4, k)` holds for every `k ≥ 0`: `rank_{F_2}(A) = Q^e_k(4)`.

**(v) (Main Theorem′ for the degree `4`)** For `m = 4` and every `k ≥ 0`: `R/I_Z` is a free `Z`-module of rank `4^{2k+1} − Q^e_k(4)`; and for every field `F`, `rank_F(A) = Q^e_k(4)`, `dim_F I_F = Q^e_k(4)` and `dim_F F[G]/I_F = 4^{2k+1} − Q^e_k(4)`.

(For `k ≥ 1` this is Main Theorem′ of the paper at the degree `4`: the algebraic core of Conjecture 1.2 for the Fermat quartics of every even dimension. The topological translation is not formalized.)

## Proofs

(i) By (i) of `q_col_upper.md`, `dim_F I_F = rank_F(A)`, so it is enough to compute the rank.
- *Characteristic `0`.* `rank_F(A) = rank_ℚ(A) = Q^e_k(m)`, by `q_every_field.md` and (vi) of `q_even_count.md`.
- *Characteristic `p > 0`, `p ∤ m`.* Let `K` be an algebraic closure of `F_p`. By the invariance of the rank under field extension, `rank_F(A) = rank_{F_p}(A) = rank_K(A)`. In `K`, `m ≠ 0`, so `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)` with `μ_m` the set of the `m`-th roots of unity. By (i) and (ii) of `q_col_upper.md`, `rank_K(A) = dim_K I_K = |Γ|`, and by (v) of `q_even_count.md` (`m` even, `m ≠ 0` in `K`), `|Γ| = Q^e_k(m)`.

(ii) Let `F` be a field. If `m ≠ 0` in `F`, this is (i). Otherwise `F` has characteristic `p` with `p | m`, and `rank_F(A) = rank_{F_p}(A) = Q^e_k(m)` by the invariance of the rank and by `H(m, k)`. Then `dim_F I_F = rank_F(A)`.

(iii) As in `q_col_assembly.md`: `R/I_Z ≅ Z^n/L`, with `L` the `Z`-span of the rows of `A`. For every prime `p`, the image of `L` in `F_p^n` spans a space of dimension `rank_{F_p}(A) = Q^e_k(m)` by (ii), and the `ℚ`-span of `L` has dimension `rank_ℚ(A) = Q^e_k(m)`. By the Lemma of `q_free_Z.md`, `Z^n/L` is free of rank `n − Q^e_k(m) = m^{2k+1} − Q^e_k(m)`. For a field `F`: `dim_F F[G]/I_F = m^d − dim_F I_F = m^{2k+1} − Q^e_k(m)`, by (0) of `q_col_upper.md` and (ii).

(iv) The only prime dividing `4` is `2`. `F_2` is a field of characteristic `2`, so by (vii) of `q_pow2_leading.md`, `dim_{F_2} I_{F_2} = Q^e_k(4)`, and by (i) of `q_col_upper.md` this is `rank_{F_2}(A)`.

(v) By (iv), (ii) and (iii) with `m = 4`.

## Remarks

1. Parts (i), (ii), (iii) are stated for every even `m` so that later pieces (the other even degrees) only have to prove `H(m, k)`.
2. For odd `m` the same three statements, with `Q_k(m)` in place of `Q^e_k(m)`, are the Theorem (every field) and Main Theorem′ of `q_col_assembly.md`; there `H` is Proposition 6.9.
3. Checked by brute force before this file was written (`chkE5.py`): the rank of the ideal over `F_2`, `F_3`, `F_5`, `F_7` and a large prime for `m = 4`, `k = 1, 2`; and for `m = 6, 8` at `k = 1`, over primes that divide `m` and primes that do not.
