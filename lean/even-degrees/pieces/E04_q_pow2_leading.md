# Degree `2^v`: leading forms (Proposition 9.2 of the paper)

This file uses, unchanged:
- `q_col_splitting.md`: for a field `F` and `d, m ≥ 0`, the group algebra `F[G] := F[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)`.
- `q_col_survivors.md`: `φ_m(u) := u^{m−1} + ⋯ + u + 1`, for `u` in any ring.
- `q_col_upper.md`: for any field `F`, any `m` and `k ≥ 0`, with `d = 2k + 1` and the matchings `J` of `V = {0, 1, …, 2k+1}` (fixed-point-free involutions), the element `ψ_J := Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} φ_m(t_a t_{J(a)}) ∈ F[G]` and the ideal `I_F := (ψ_J : J a matching of V) ⊆ F[G]`.
- `q_peeling_lemma.md`: the ring `C_d` with parameter `q` is `F[y_1, …, y_d]/(y_1^{q−1}, …, y_d^{q−1})`. Here it is used with two parameters: with the parameter `q + 1` it is `B := F[s_1, …, s_d]/(s_1^q, …, s_d^q)`; with the parameter `q` it is `C := F[y_1, …, y_d]/(y_1^{q−1}, …, y_d^{q−1})`.
- `q_P3_identities.md`: `D(a, b) := Σ_{w=0}^{q−2} (−1)^w a^w b^{q−2−w}`.
- `q_theorem_B_lower.md`, with its parameter `q` (any `q`; here `q` is even): `D_J := Π D(y_a, y_{J(a)})` over the `k` pairs `{a < J(a)}` of `J` that avoid `0`, and the ideal `(D_J : J ∈ 𝒥) ⊆ C`, `C` in the `2k + 1` variables `y_1, …, y_{2k+1}`.
- `q_col_one.md`, Proposition 2.5 (which holds for every `q`): `Y_d := y_1 ⋯ y_d ∈ B`; the kernel of the multiplication by `Y_d` on `B` is `(y_i^{q−1})`; `f ↦ Y_d·f̃` is a well-defined injective `F`-linear map `μ_Y : C → B`; and for every family `(f_α)` of polynomials, `dim_F (Y_d f_α : α)·B = dim_F (f_α : α)·C`.
- `q_even_count.md`: the number `Q^e_k(m)` and its part (vi): for every field `F` and every even `m ≥ 2`, `dim_F I_F ≤ Q^e_k(m)`.
- `q_odd3.md`, part (vi): for every field `F` and every `k`, `Q^e_k(4) ≤ dim_F (D_J : J ∈ 𝒥)·C` at the parameter `q = 4`.

## Setting

`v ≥ 1`, `q := 2^v`, `k ≥ 0`, `d := 2k + 1`, and `F` is a field of characteristic `2`. `F[G]` is the group algebra with `m = q` and `d` variables, and `I_F ⊆ F[G]` is the ideal of the `ψ_J` (with `φ = φ_q`). `B := F[s_1, …, s_d]/(s_i^q)` and `C := F[y_1, …, y_d]/(y_i^{q−1})`. The vertex `a ∈ {1, …, 2k+1}` of a matching carries the variable `t_a`, `s_a`, `y_a`.

For a matching `J` define the polynomials in `F[s_1, …, s_d]`

`P_J := Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} (s_a + s_{J(a)} + s_a s_{J(a)})^{q−1}`,

`L_J := Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} (s_a + s_{J(a)})^{q−1}`,

`E_J := Π_{0 < a < J(a)} D(s_a, s_{J(a)})`.

`L_J` is homogeneous of degree `δ := (k + 1) + k(q − 1)`. The class of `E_J` in `C` (reading `s` as `y`) is `D_J`.

## Theorem

**(i) (`φ` in characteristic `2`)** For every commutative ring `A` of characteristic `2`, every `u ∈ A` and `q = 2^v` (`v ≥ 0`): `φ_q(u) = (u + 1)^{q−1}`.

**(ii) (the ring)** There is an isomorphism of `F`-algebras `Θ : F[G] → B` with `Θ(t_i) = 1 + s_i` for `i = 1, …, d`.

**(iii) (the generators)** For every matching `J`: `Θ(ψ_J)` is the class of `P_J` in `B`.

**(iv) (Lemma, lowest forms)** Let `F` be any field (any characteristic), `e ≥ 1`, `d ≥ 0`, `B_e := F[s_1, …, s_d]/(s_1^e, …, s_d^e)`, and let `I` be an ideal of `B_e`. Let `(f_α)_α` and `(g_α)_α` be two families of polynomials in `F[s_1, …, s_d]` and `(δ_α)_α` natural numbers such that, for every `α`: the class of `f_α` lies in `I`; `g_α` is homogeneous of degree `δ_α`; and every monomial of `f_α − g_α` has total degree greater than `δ_α`. Then

`dim_F (ḡ_α : α)·B_e ≤ dim_F I`,

where `ḡ_α` is the class of `g_α`.

**(v) (the leading forms)** (a) For every commutative ring `A` of characteristic `2`, `q = 2^v` with `v ≥ 1`, and `a, b ∈ A` with `b^q = 0`: `b·(a + b)^{q−1} = a·b·D(a, b)`. (b) For every matching `J`, the class of `L_J` in `B` is `Y_d · Ē_J`, where `Ē_J` is the class of `E_J` in `B`.

**(vi) (Proposition 9.2, the inequality)** `dim_F (D_J : J ∈ 𝒥)·C ≤ dim_F I_F`.

**(vii) (the quartic, at the prime `2`)** For every field `F` of characteristic `2` and every `k ≥ 0`, with `m = q = 4`: `dim_F I_F = Q^e_k(4)`.

**(viii) (the conditional form)** For `v ≥ 1`, `q = 2^v`, a field `F` of characteristic `2` and `k ≥ 0`: if `Q^e_k(q) ≤ dim_F (D_J : J ∈ 𝒥)·C`, then `dim_F I_F = Q^e_k(q)`.

**(ix) (`q = 2`)** For every field `F` of characteristic `2` and every `k ≥ 0`, with `m = q = 2`: `dim_F (D_J : J ∈ 𝒥)·C = 1`, `Q^e_k(2) = 1` and `dim_F I_F = 1`.

## Proof

(i) In `F_2[u]`: `(u + 1)·φ_q(u) = u^q + 1` (the sum telescopes, and `−1 = 1`), and `(u + 1)^q = u^q + 1` because `q` is a power of the characteristic. So `(u + 1)·φ_q(u) = (u + 1)·(u + 1)^{q−1}`. `F_2[u]` is a domain and `u + 1 ≠ 0`, hence `φ_q(u) = (u + 1)^{q−1}` in `F_2[u]`. A commutative ring `A` of characteristic `2` is an `F_2`-algebra; apply the homomorphism `F_2[u] → A` that sends `u` to the given element. (For `v = 0`: `φ_1(u) = 1 = (u + 1)^0`.)

(ii) In `F[x_1, …, x_d]`, `(x_i + 1)^q = x_i^q + 1 = x_i^q − 1`. Let `τ` be the `F`-algebra endomorphism of `F[x_1, …, x_d]` with `τ(x_i) = x_i + 1`; `τ∘τ` is the identity (characteristic `2`), so `τ` is an automorphism. `τ(x_i^q) = (x_i + 1)^q = x_i^q − 1` and `τ(x_i^q − 1) = x_i^q`, so `τ` maps the ideal `(x_i^q − 1 : i)` onto the ideal `(x_i^q : i)`. Hence `τ` induces an isomorphism `Θ : F[G] = F[x]/(x_i^q − 1) → F[x]/(x_i^q) = B` with `Θ(t_i) = s_i + 1`.

(iii) `Θ(t_b − 1) = s_b`. By (i) in `B`, `Θ(φ_q(t_a t_b)) = φ_q((1 + s_a)(1 + s_b)) = ((1 + s_a)(1 + s_b) + 1)^{q−1} = (s_a + s_b + s_a s_b)^{q−1}`. Multiply over the pairs.

(iv) Grade `B_e` by the total degree: the classes of the monomials with all exponents `< e` are a basis of `B_e`; let `(B_e)_n` be the span of those of degree `n` (zero for `n > N := d(e − 1)`), `π_n : B_e → (B_e)_n` the projection, and `(B_e)_{≥n} := ⊕_{j ≥ n} (B_e)_j`. The class of a polynomial all of whose monomials have degree `≥ n` lies in `(B_e)_{≥n}`, and its image under `π_n` is the class of its homogeneous component of degree `n` (the class of a monomial is a basis element of the same degree, or `0`).

For a subspace `V ⊆ B_e` put `V_{≥n} := V ∩ (B_e)_{≥n}` and `gr_n(V) := π_n(V_{≥n}) ⊆ (B_e)_n`, and `in(V) := Σ_n gr_n(V)`.

(a) `dim in(V) = dim V`. The restriction of `π_n` to `V_{≥n}` has kernel `V_{≥n+1}`, so `dim gr_n(V) = dim V_{≥n} − dim V_{≥n+1}`. The sum `Σ_n gr_n(V)` is direct, because the `gr_n(V)` lie in the different summands `(B_e)_n`. So `dim in(V) = Σ_{n=0}^{N} (dim V_{≥n} − dim V_{≥n+1}) = dim V_{≥0} − dim V_{≥N+1} = dim V`.

(b) Let `H := (ḡ_α : α)·B_e`. As an `F`-space `H` is spanned by the elements `x̄·ḡ_α`, `x` a monomial, because the classes of the monomials span `B_e`. Fix `α` and a monomial `x` of degree `j`. The class of `x f_α` lies in `I`. Every monomial of `x f_α = x g_α + x(f_α − g_α)` has degree `≥ δ_α + j`, and its component of degree `δ_α + j` is `x g_α`. So the class of `x f_α` lies in `I_{≥ δ_α + j}` and its image under `π_{δ_α + j}` is `x̄·ḡ_α`. Hence `x̄·ḡ_α ∈ gr_{δ_α + j}(I) ⊆ in(I)`. So `H ⊆ in(I)` and `dim H ≤ dim in(I) = dim I` by (a).

(v) (a) In `F_2[a, b]`: `(a + b)·Σ_{u=0}^{q−1} a^u b^{q−1−u} = a^q + b^q = (a + b)^q`, the first equality by telescoping (with `−1 = 1`) and the second because `q` is a power of `2`. `F_2[a, b]` is a domain and `a + b ≠ 0`, so `(a + b)^{q−1} = Σ_{u=0}^{q−1} a^u b^{q−1−u}`. Multiply by `b`:

`b(a + b)^{q−1} = Σ_{u=0}^{q−1} a^u b^{q−u} = b^q + Σ_{u=1}^{q−1} a^u b^{q−u} = b^q + a b·Σ_{w=0}^{q−2} a^w b^{q−2−w} = b^q + a b·D(a, b)`,

since in characteristic `2` the signs of `D` are `1` (here `q ≥ 2` is used). Map to `A` and use `b^q = 0`.

(b) Let `J` be a matching. Its `k + 1` pairs are `{a < J(a)}`; one of them is `{0, J(0)}`. The larger elements of the `k + 1` pairs together with the smaller elements of the `k` pairs that avoid `0` are exactly `1, …, 2k+1`, each once. So `Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} s_a = s_1 ⋯ s_d = Y_d`. In `B`, by (a) with `b = s_{J(a)}` (`b^q = 0`):

`L̄_J = s_{J(0)} · Π_{0 < a < J(a)} s_{J(a)}(s_a + s_{J(a)})^{q−1} = s_{J(0)} · Π_{0 < a < J(a)} s_a s_{J(a)} D(s_a, s_{J(a)}) = Y_d · Ē_J`.

(vi) By (ii), `dim_F I_F = dim_F Θ(I_F)`, and by (iii) `Θ(I_F) = (P̄_J : J)·B`. For a pair `0 < a < J(a)`, `(s_a + s_{J(a)} + s_a s_{J(a)})^{q−1} = (s_a + s_{J(a)})^{q−1} + (terms of degree ≥ q)`: every other term of the expansion contains the factor `s_a s_{J(a)}` at least once instead of a linear form. So `P_J = L_J + (terms of degree > δ)`, and `L_J` is homogeneous of degree `δ`. By (iv) with `e = q`, `I = Θ(I_F)`, `f_J = P_J`, `g_J = L_J`:

`dim_F (L̄_J : J)·B ≤ dim_F Θ(I_F) = dim_F I_F`.

By (v)(b), `(L̄_J : J)·B = (Y_d Ē_J : J)·B`, and by Proposition 2.5 (ii) of `q_col_one.md` (with the polynomials `E_J`) its dimension is `dim_F (Ē_J : J)·C = dim_F (D_J : J ∈ 𝒥)·C`.

(vii) `q = 4 = 2^2`. By `q_odd3.md` (vi) and by (vi): `Q^e_k(4) ≤ dim_F (D_J : J)·C ≤ dim_F I_F`. By `q_even_count.md` (vi) with `m = 4`: `dim_F I_F ≤ Q^e_k(4)`.

(viii) The same, with the hypothesis in place of `q_odd3.md` (vi), and `q_even_count.md` (vi) with the even number `m = q ≥ 2`.

(ix) For `q = 2`: `C = F[y_1, …, y_d]/(y_1, …, y_d) = F`; `D(a, b) = Σ_{w=0}^{0} a^0 b^0 = 1`, so `D_J = 1` for every `J`, there is at least one matching, and `(D_J : J)·C = C` has dimension `1`. `Q^e_k(2)`: here `(m − 2)/2 = 0`, the only term has `2c = 2k + 2`, and it is `(2k+2)!/(2k+2)! = 1`. Then (viii) gives `dim_F I_F = 1`.

## Remarks

1. Part (iv) does not say that `in(I)` is an ideal (it is, but this is not needed), and it does not need `ḡ_α ≠ 0`.
2. Parts (i), (ii), (iii), (v) and (vi) are the three steps of the proof of Proposition 9.2 of the paper; (vii) is the statement of that proposition for the degree `4` at the prime `2`, with equality; (viii) is its statement for every `2^v`, given Theorem O at the odd box `2^v − 1`.
3. Checked by brute force over `F_2` before this file was written (`chkE4.py`): (i) for `q ≤ 64`; (ii), (iii), (v), (vi) and the dimensions at `(k, q) = (0,2), (0,4), (0,8), (1,2), (1,4), (1,8), (1,16), (2,2), (2,4), (3,2)`; (iv) on random ideals.
