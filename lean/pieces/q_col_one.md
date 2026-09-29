# The block of colour 1: the coordinate y = t − t^{−1} and the sum form, in local form (§2.3–§2.4 and §6.4 of the paper: Lemmas 2.3, 2.4, Proposition 2.5, Lemma 6.6)

This file uses, unchanged:
- `q_col_splitting.md`: the Setting (`F` of characteristic `p`, `q = p^v`, `r`, `μ`);
- `q_col_survivors.md`: `k`, `d = 2k + 1`, `V = {0, …, 2k+1}`, matchings, the extended colouring `c_0`;
- `q_col_compatible.md`: the classes `𝒞_ζ` and perfect matchings of a finite set;
- `q_col_tensor.md`: the box rings `B(W)`;
- `q_col_decomp.md`: `W_1 = 𝒞_1 ∖ {0}`, the pair factors `f_{a,b}`, the generators `g_P` and the ideal `I_{c,1} = (g_P : P) ⊆ B(W_1)`;
- `q_peeling_lemma.md`: the ring `C_m = F[y_1, …, y_m]/(y_i^{q−1})` (and `C_m` with `q + 1` in place of `q`, which is `F[y_1, …, y_m]/(y_i^q)`);
- `q_P3_identities.md`: the divided difference `D(y_a, y_b) = Σ_{u=0}^{q−2} (−1)^u y_a^u y_b^{q−2−u}`;
- `q_theorem_B_lower.md`: matchings `J` of `{0, …, 2j+1}`, `D_J`, the ideal `(D_J : J) ⊆ C_{2j+1}`, `Q_j(q)`, the point set `T = {1, …, h} × {±1}`, closed tuples, and its Theorem (iv): `dim (D_J : J) ≥ Q_j(q)`;
- `q_P3_lifts.md`, `q_P3_identities.md`, `q_induction.md`: `Par_m`, down-sets, tight patterns, `V_Λ`, `Z_Λ`, and the Theorem of `q_induction.md`: `dim V_Λ ≥ |Z_Λ|` for every down-set `Λ` of `Par_m`.

## Setting

In addition, **`p ≠ 2`**, so `q` is odd and `q ≥ 3`. Write `B_m := F[y_1, …, y_m]/(y_1^q, …, y_m^q)` (the ring `C_m` of `q_peeling_lemma.md` with `q + 1` in place of `q`) and `C_m := F[y_1, …, y_m]/(y_1^{q−1}, …, y_m^{q−1})`, and `Y_m := y_1 y_2 ⋯ y_m ∈ B_m` (`Y_0 = 1`).

**Box rings at the point 1.** Let `W` be a finite set of indices and consider the box ring `B(W)` of `q_col_tensor.md` at a point `c` with `c_s = 1` for every `s ∈ W` (so `B(W) = F[t_s : s ∈ W]/((t_s − 1)^q)`). Every `t_s` is a unit of `B(W)` (it is `1` plus a nilpotent). Put

`y_s := t_s − t_s^{−1} ∈ B(W)`.

## Lemma 2.3 (local form)

**(i)** Let `n := |W|` and `e : [n] → W` a bijection. There is an `F`-algebra isomorphism `Ψ_e : B_n → B(W)` with `Ψ_e(y_i) = y_{e(i)}`.

**(ii)** For `s ∈ W`, `t_s − 1 = u_s·y_s` with `u_s` a unit of `B(W)`. For `s ≠ l` in `W`, `t_s t_l − 1 = u_{s,l}·(y_s + y_l)` with `u_{s,l}` a unit.

## Lemma 2.4 (local form)

**(i)** In every commutative `F`-algebra `A`, if `b ∈ A` has `b^q = 0`, then for every `a ∈ A`

`(a + b)^{q−1}·b = −a·b·D(a, b)`,   `D(a, b) := Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}`.

**(ii)** Suppose the point `c` has `c_s = 1` on `W = 𝒞_1 ∖ {0}` (as for `W_1` in `q_col_decomp.md`), and let `P` be a perfect matching of `𝒞_1`. Then in `B(W_1)`

`g_P = u·Y_{W_1}·D_P`,

with `u` a unit, `Y_{W_1} := Π_{s ∈ W_1} y_s`, and `D_P := Π D(y_a, y_b)` over the pairs `{a < b}` of `P` with `a ≠ 0` (the pairs avoiding `0`; the empty product is `1`).

## Proposition 2.5 (local form: the sum form)

Let `m ≥ 0`.

**(i)** Multiplication by `Y_m` on `B_m` has kernel exactly `(y_1^{q−1}, …, y_m^{q−1})·B_m`; hence `f ↦ Y_m·f̃` (`f̃` any lift of `f` from `C_m` to `B_m`, e.g. through `F[y_1, …, y_m]`) is a well-defined injective `F`-linear map `μ_Y : C_m → B_m`.

**(ii)** For every family `(f_α)` of polynomials in `F[y_1, …, y_m]`, the ideal `(Y_m f_α : α)·B_m` is the image under `μ_Y` of the ideal `(f_α : α)·C_m`; in particular

`dim_F (Y_m f_α : α)·B_m = dim_F (f_α : α)·C_m`.

## Lemma 6.6 (the block of colour 1)

Fix `c ∈ μ^d` (extended by `c_0`), let `𝒞_1 = {v ∈ V : c_v = 1}` and `s := |𝒞_1|`, and let `I_{c,1} ⊆ B(W_1)` be the ideal of `q_col_decomp.md`.

**(i)** If `s` is odd, then `I_{c,1} = 0`.

**(ii)** If `0 ∈ 𝒞_1` and `s = 2j + 2` (`j ≥ 0`), then `dim_F I_{c,1} = dim_F (D_J : J a matching of {0, …, 2j+1}) ⊆ C_{2j+1}`, and hence `dim_F I_{c,1} ≥ Q_j(q)`.

**(iii)** If `0 ∉ 𝒞_1` and `s = 2j` (`j ≥ 0`), then `dim_F I_{c,1} ≥` the number of closed tuples in `T^{2j}` (`T = {1, …, h} × {±1}`, `h = (q−1)/2`, the point set of `q_theorem_B_lower.md`), i.e. the number of `2j`-tuples in `T` whose multiset is closed under the involution.

## Proofs

**Lemma 2.3.** (i) In `B(W)`, `(t_s − 1)^q = 0`, so `F[t_s]/((t_s − 1)^q)` is local with maximal ideal `(t_s − 1)`; `t_s` and `t_s + 1 = 2 + (t_s − 1)` are units (`2 ≠ 0` as `p ≠ 2`). So `y_s = t_s^{−1}(t_s − 1)(t_s + 1)` is a unit times `t_s − 1`. Hence `y_s^q = 0`, and `1, y_s, …, y_s^{q−1}` is a basis of `F[t_s]/((t_s − 1)^q)` (they lie in successive powers of the maximal ideal and not in the next; the dimension is `q`). So `F[y]/(y^q) → F[t_s]/((t_s−1)^q)`, `y ↦ y_s`, is an isomorphism for each `s`, and `Ψ_e` is their tensor product (the box ring splits over the variables, `q_col_tensor.md` Lemma 6.4 (ii), or directly: `Ψ_e` is well defined since `y_s^q = 0`, and bijective since it maps the monomial basis `Π y_i^{a_i}`, `0 ≤ a_i ≤ q−1`, of `B_n` onto a basis of `B(W)`). (ii) The first claim is the unit statement just proved. For the second: `y_s + y_l = t_s + t_l − t_s^{−1} − t_l^{−1} = (t_s + t_l)(t_s t_l)^{−1}(t_s t_l − 1)`, and `t_s + t_l = 2 + (t_s − 1) + (t_l − 1)` is a unit.

**Lemma 2.4.** (i) In `ℤ[a, b]` (or `F[a, b]`), `(a + b)·Σ_{s=0}^{q−1} (−1)^s a^s b^{q−1−s} = a^q + b^q` (telescoping; `q` odd). In characteristic `p`, `a^q + b^q = (a + b)^q`, and cancelling `a + b` in the domain `F[a, b]` gives `(a + b)^{q−1} = Σ_{s=0}^{q−1} (−1)^s a^s b^{q−1−s}`, an identity of polynomials, hence valid in every commutative `F`-algebra. Multiply by `b` and use `b^q = 0`: `Σ_{s=1}^{q−1} (−1)^s a^s b^{q−s} = −a b Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}`. (ii) `g_P = Π f_{a,b}` over the pairs `{a < b}` of `P`. For the pair `{0, b}` (if `0 ∈ 𝒞_1`), `f_{0,b} = t_b − 1 = u_b y_b` by Lemma 2.3 (ii). For a pair `{a < b}` with `a ≠ 0`: `f_{a,b} = (t_b − 1)(t_a t_b − 1)^{q−1} = (unit)·y_b·(y_a + y_b)^{q−1} = (unit)·(−y_a y_b D(y_a, y_b))` by Lemma 2.3 (ii) and (i) (with `b := y_b`, `y_b^q = 0`). The indices occurring in these monomial factors are the elements of `𝒞_1 ∖ {0} = W_1`, each exactly once (the pairs of `P` partition `𝒞_1`). Multiply.

**Proposition 2.5.** (i) Multiplication by `Y_m` sends a monomial `Π y_i^{a_i}` (`0 ≤ a_i ≤ q−1`) of the monomial basis of `B_m` to `Π y_i^{a_i+1}`, which is `0` if some `a_i = q − 1` and is again a distinct basis monomial otherwise. So the kernel is spanned by the basis monomials with some `a_i = q − 1`, which is `(y_1^{q−1}, …, y_m^{q−1})B_m`, and this ideal is the kernel of `B_m → C_m`. Hence `μ_Y` is well defined and injective. (ii) `(Y_m f_α)B_m` consists of the `Σ Y_m f_α g_α` (`g_α ∈ B_m`), which is `μ_Y(Σ f_α ḡ_α)`; and every element of `(f_α)C_m` is such a `Σ f_α ḡ_α`. An injective linear map preserves dimension.

**Lemma 6.6.** (i) A set of odd size has no perfect matching, so `I_{c,1}` is generated by the empty set. (ii) Let `n := s − 1 = 2j + 1 = |W_1|` and `e : [n] → W_1` the increasing enumeration; extend it by `e(0) := 0` to an increasing bijection `ē : {0, …, 2j+1} → 𝒞_1`. The perfect matchings `P` of `𝒞_1` are exactly the `ē ∘ J ∘ ē^{−1}` for the matchings `J` of `{0, …, 2j+1}`, and since `ē` is increasing, `D_P = Ψ_e(D_J)` (the pair `{a < b}` of `J` goes to the pair `{ē(a) < ē(b)}` of `P`, and `a ≠ 0` iff `ē(a) ≠ 0`). By Lemma 2.4 (ii), `I_{c,1} = (Y_{W_1} D_P : P) = Ψ_e((Y_n D_J : J)B_n)` (units do not change the ideal, `q_col_tensor.md` Lemma 6.4 (v)). `Ψ_e` is an `F`-algebra isomorphism, so `dim I_{c,1} = dim (Y_n D_J : J)B_n = dim (D_J : J)C_n` by Proposition 2.5 (ii), and this is `≥ Q_j(q)` by the Theorem (iv) of `q_theorem_B_lower.md`. (iii) Let `n := s = 2j = |W_1|` and `e : [n] → W_1 = 𝒞_1` the increasing enumeration. As in (ii), `I_{c,1} = Ψ_e((Y_n D_P : P)B_n)`, now over the perfect matchings `P` of `[n]` and with every pair avoiding `0`, so `dim I_{c,1} = dim (D_P : P)C_n`. The set `{∅}` is a down-set of `Par_n` (`λ ≼ ∅` forces `λ = ∅`; `∅ ∈ Par_n` as `n` is even), and a tight pattern of `∅` on `[n]` has `n/2` pairs and no blocks: it is a perfect matching `P`, with product `D_P`. So `(D_P : P)C_n = V_{{∅}}`, and the Theorem of `q_induction.md` gives `dim V_{{∅}} ≥ |Z_{{∅}}|`. Finally `Z_{{∅}}` is the set of tuples in `T^n` whose residue partition is empty, i.e. with `#{i : M_i = u} = #{i : M_i = −u}` for every `u`: the closed tuples. (For `j = 0`, `W_1 = ∅`, `I_{c,1} = (1) = B(∅) = F` has dimension `1`, and there is one closed tuple of length `0`.) ∎

## Checks

- Lemma 2.4 (i) as an identity in `F_p[a, b]/(b^q)`, `p = q ∈ {3, 5, 7, 11, 13}`: 5 of 5. Negative control (the divided difference without the signs `(−1)^u`): fails 5 of 5.
- Lemma 6.6 together with Lemmas 2.3, 2.4 and Proposition 2.5, by exact linear algebra over `F_p` (`q = p`): `dim I_{c,1}` computed from the `g_P` inside `R_c` equals `dim (D_J)C` (resp. `dim (D_P)C`) computed in the `y`-coordinates, and is `≥ Q_j(q)` (resp. `≥` the number of closed tuples), and `I_{c,1} = 0` for odd `|𝒞_1|`: every colouring for `(p, q, r, k) ∈ {(3,3,1,1), (5,5,1,1), (3,3,1,2), (7,7,3,1)}` and 14 random colourings for `(13, 13, 3, 1)`; 44 colourings, 0 failures (both `0 ∈ 𝒞_1` and `0 ∉ 𝒞_1` occur).
