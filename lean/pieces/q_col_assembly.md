# The colour reduction and the assembly (§6.7 of the paper, Proposition 6.9, and the proof of Main Theorem′ in §7)

This file uses, unchanged:
- `q_col_splitting.md` (Lemma 6.1), `q_col_survivors.md` (`ψ_J`, the extended colouring), `q_col_compatible.md` (Lemma 6.3), `q_col_decomp.md` (Proposition 6.5: `I = (ψ_J : J)`, `I_{c,1}`, `I_{c,ζ}`), `q_col_one.md` (Lemma 6.6), `q_col_pairs.md` (Lemma 6.7), `q_col_count.md` (Lemma 6.8: the counts `N_1(c)`, `N_ζ(c)` and `Σ_c [comp(c)]·N_1(c)·Π_ζ N_ζ(c) = Q_k(m)`);
- `q_theorem_B_lower.md` (closed tuples, `Q_k`, and its Theorem (ii): `#closed tuples in T^{2j+2} = Q_j(q)` for `|T| = 2·(q−1)/2`);
- `q_col_upper.md`: for any field `K` and `m ≥ 1`, the ideal `I_K = (ψ_J : J) ⊆ K[G]`, the monomial basis (0), the integer matrix `A = A_{m,k}` of (i) with `dim_K I_K = rank_K(A)`, the count (ii)–(iii), and (iv): `dim_F I_F ≤ Q_k(m)` for every field `F` and odd `m`, and `rank_ℚ(A) = Q_k(m)`; also the compatibility `ψ_J` of `q_col_survivors.md` `= ψ_J` of `q_col_upper.md` (for `m := q·r`);
- `q_every_field.md` (the rank `rank_K(A)` of an integer matrix over a field, part (ii));
- `q_free_Z.md`: its Lemma (integer matrices): for a subgroup `L ⊆ Z^n`, if for every prime `p` the image of `L` in `F_p^n` spans a subspace of dimension `r := dim_ℚ(ℚ-span of L)`, then `Z^n/L` is free of rank `n − r`.

## Setting

`k ≥ 0`, `d = 2k + 1`. For a field `K` and `m ≥ 1`, `K[G]` and `I_K` are as in `q_col_upper.md`. Over the integers put

`R := Z[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)`,   `I_Z := (ψ_J : J a matching) ⊆ R`,

with `ψ_J` given by the same formula (its image in `K[G]` is the `ψ_J` of `K[G]`).

## Proposition 6.9 (the colour reduction)

Let `F` be a field with the Setting of `q_col_splitting.md` (characteristic `p`, `q = p^v`, `r`, `μ`, `m = q·r`), with **`p ≠ 2`** and **`r` odd**. Then

`dim_F I_F = Q_k(m)`.

## Theorem (every field)

Let `m ≥ 1` be odd. For every field `F`, `dim_F I_F = Q_k(m)`; equivalently, `rank_F(A) = Q_k(m)`.

## Main Theorem′

Let `m ≥ 1` be odd. Then `R/I_Z` is a free `Z`-module of rank `m^{2k+1} − Q_k(m)`. Moreover, for every field `F`, `dim_F F[G]/I_F = m^{2k+1} − Q_k(m)`.

(For `m ≥ 3` and `k ≥ 1` this is Main Theorem′ of the paper, the algebraic core of the Main Theorem; the topological translation, Theorem 0(a), is not formalized.)

## Proofs

**Proposition 6.9.** *Lower bound.* `I_F` is the ideal `I` of `q_col_decomp.md` (by the compatibility of the two `ψ_J`). By Lemma 6.1, `dim_F I = Σ_{c ∈ μ^d} dim_F π_c(I)`. Fix `c`, and a set `ℛ` of representatives (it exists as `r` is odd, Lemma 6.3 (i)).
- If no matching is compatible with `c`, the term is `≥ 0`, and the corresponding term of Lemma 6.8 is `0`.
- Otherwise, by Proposition 6.5 (iii), `dim_F π_c(I) = dim I_{c,1} · Π_{ζ∈ℛ} dim I_{c,ζ}`, and by Lemma 6.3 (iv), `|𝒞_1|` is even and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`.
  - `dim I_{c,1} ≥ N_1(c)`: if `0 ∈ 𝒞_1`, then `|𝒞_1| = 2j + 2` for some `j`, and Lemma 6.6 (ii) gives `dim I_{c,1} ≥ Q_j(q)`, which is `N_1(c)` by Theorem (ii) of `q_theorem_B_lower.md`; if `0 ∉ 𝒞_1`, then `|𝒞_1| = 2j`, and Lemma 6.6 (iii) gives `dim I_{c,1} ≥ N_1(c)`.
  - `dim I_{c,ζ} ≥ N_ζ(c)` for every `ζ ∈ ℛ`, by Lemma 6.7 (vi).

  So `dim_F π_c(I) ≥ N_1(c)·Π_ζ N_ζ(c)`.

Summing and using Lemma 6.8, `dim_F I ≥ Q_k(m)`. *Upper bound.* `m = q·r` is odd (`q` is a power of the odd prime `p`), so Theorem (iv) of `q_col_upper.md` gives `dim_F I ≤ Q_k(m)`. ∎

**Theorem (every field).** By (i) of `q_col_upper.md`, `dim_F I_F = rank_F(A)`.
- *(a) Field extensions.* For fields `F ⊆ F'` and an integer matrix `A`, `rank_F(A) = rank_{F'}(A)`: the rank of a matrix over a field does not change under extension of scalars (e.g. it is the largest size of a non-vanishing minor, and the minors are the same elements). So `rank_F(A)` depends only on the prime field of `F`.
- *(b) Characteristic `0`.* `rank_F(A) = rank_ℚ(A) = Q_k(m)` (part (ii) of `q_every_field.md` and (iv) of `q_col_upper.md`).
- *(c) Characteristic `p > 0`.* Let `K` be an algebraic closure of `F_p`; by (a), `rank_F(A) = rank_{F_p}(A) = rank_K(A)`.
  - If `p ∤ m`, then `m ≠ 0` in `K`, so `X^m − 1` is separable and has `m` distinct roots in `K` (the set `μ_m` of its roots, `X^m − 1 = Π_{ξ∈μ_m}(X − ξ)`). By (ii) and (iii) of `q_col_upper.md`, `rank_K(A) = dim_K I_K = |Γ| = Q_k(m)`.
  - If `p | m`, then `p` is odd, as `m` is. Write `m = p^v·r` with `v ≥ 1` and `p ∤ r`; `r` is odd. `X^r − 1` is separable over `K`, so it has a set `μ` of `r` distinct roots with `X^r − 1 = Π_{ζ∈μ}(X − ζ)`. So `K` with `(p, v, r, μ)` satisfies the Setting of `q_col_splitting.md`, with `q·r = m`, `p ≠ 2` and `r` odd. By Proposition 6.9, `rank_K(A) = dim_K I_K = Q_k(m)`. ∎

**Main Theorem′.**
- *The basis.* As in (0) of `q_col_upper.md` (the same proof works over `Z`), `R` is a free `Z`-module with basis the monomials `t^ν`, `0 ≤ ν_i < m`; write `e : R ≅ Z^n`, `n = m^d`, for the coordinate map. `I_Z` is the `Z`-span of the elements `t^ν ψ_J`, and by the construction in (i) of `q_col_upper.md` their coordinate vectors are the rows of `A`. So `e(I_Z) = L :=` the `Z`-span of the rows of `A`, and `R/I_Z ≅ Z^n/L`.
- *The ranks.* For every field `F`, the image of `L` in `F^n` spans the row space of `A` read in `F`, of dimension `rank_F(A)`. By the Theorem (every field), `rank_{F_p}(A) = Q_k(m) = rank_ℚ(A)` for every prime `p`.
- *Freeness.* By the Lemma of `q_free_Z.md`, `Z^n/L` is free of rank `n − Q_k(m) = m^{2k+1} − Q_k(m)`.
- *Every field.* By (0) of `q_col_upper.md`, `dim_F F[G]/I_F = m^d − dim_F I_F = m^{2k+1} − Q_k(m)`. ∎

## Checks

- Exact ranks of the matrix `A` (all `t^ν ψ_J` in the monomial basis) over `F_p` for `p = 2, 3, 5, 7, 11, 13` and over `F_{1000003}` (as a stand-in for `ℚ`), at `(m, k) = (3, 1), (5, 1), (7, 1), (9, 1), (3, 2)`: every rank equals `Q_k(m) = 6, 36, 90, 168, 20`, so `R/I_Z` has rank `21, 89, 253, 561, 223` and no torsion. At the composite degree `(m, k) = (15, 1)` (the case of §6: two primes, `q·r = 3·5` and `5·3`), the rank over `F_2`, `F_3`, `F_5` is `546 = Q_1(15)` (and `|Γ| = 546` by evaluation over `F_31`, in the checks of `q_col_upper.md`). 0 failures.
- Negative control (from `q_col_upper.md`): with `t_b + 1` in place of `t_b − 1` in `ψ_J`, the ranks are `19, 61, 127, 217, 141`, not `Q_k(m)`.
- Remark on subfamilies: removing one matching at `(m, k) = (9, 1)` or `(3, 2)` still gives no torsion; the first subfamily with `3`-torsion is at `(q, k) = (9, 2)` (paper, §9), beyond these checks. This does not affect the statements above, which are about the full family.
