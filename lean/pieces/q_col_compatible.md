# Colour classes and compatible matchings (§6.3 of the paper, Lemma 6.3)

This file uses, unchanged, `q_col_splitting.md` (the Setting: `F`, `p`, `q`, `r`, the set `μ ⊆ F` of the `r`-th roots of unity with `X^r − 1 = Π_{ζ∈μ}(X − ζ)`) and `q_col_survivors.md` (matchings of `{0, …, 2k+1}` as fixed-point-free involutions `J`, the colouring `c ∈ μ^{2k+1}` extended by `c_0 := (c_1 ⋯ c_{2k+1})^{−1}`, and its elementary facts: `1 ∈ μ`, `μ` closed under products and inverses).

## Setting

In addition, **`r` is odd**. Let `k ≥ 0`, `V := {0, 1, …, 2k+1}`, and let `c : V → μ` be a colouring of `V` (in the paper `c_0` is determined by `c_1, …, c_{2k+1}`; parts (i)–(iv) below hold for every `c : V → μ`, and part (v) uses `Π_{v∈V} c_v = 1`).

**Colour classes.** For `ζ ∈ μ` put `𝒞_ζ := {v ∈ V : c_v = ζ}`.

**Representatives.** A set `ℛ ⊆ μ ∖ {1}` of **representatives** is a set containing exactly one of `ζ, ζ^{−1}` for every `ζ ∈ μ ∖ {1}`.

**Compatibility.** A matching `J` of `V` is **compatible** with `c` if `c_a c_{J(a)} = 1` for every `a ∈ V`.

## Lemma 6.3

**(i) (no self-inverse colour)** If `ζ ∈ μ` and `ζ^{−1} = ζ`, then `ζ = 1`. Consequently a set `ℛ` of representatives exists, and for `ζ ∈ ℛ` the classes `𝒞_ζ`, `𝒞_{ζ^{−1}}` are disjoint from each other and from `𝒞_1`; the sets `𝒞_1` and `𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`) partition `V`.

**(ii) (compatible pairs)** For `a ≠ b` in `V`: `c_a c_b = 1` iff either `a, b ∈ 𝒞_1`, or there is `ζ ∈ ℛ` with one of `a, b` in `𝒞_ζ` and the other in `𝒞_{ζ^{−1}}`.

**(iii) (compatible matchings are product choices)** A matching `J` is compatible with `c` iff `J(𝒞_1) = 𝒞_1` and `J(𝒞_ζ) = 𝒞_{ζ^{−1}}` for every `ζ ∈ ℛ`. The map

`J ↦ (J|_{𝒞_1}, (J|_{𝒞_ζ})_{ζ ∈ ℛ})`

is a bijection from the set of matchings of `V` compatible with `c` onto the set of tuples `(P, (σ_ζ)_{ζ∈ℛ})` with `P` a perfect matching of `𝒞_1` (a fixed-point-free involution of `𝒞_1`) and `σ_ζ : 𝒞_ζ → 𝒞_{ζ^{−1}}` a bijection for each `ζ ∈ ℛ`. Its inverse sends `(P, (σ_ζ))` to the involution of `V` that is `P` on `𝒞_1`, `σ_ζ` on `𝒞_ζ` and `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}`.

**(iv) (existence)** A matching compatible with `c` exists iff `|𝒞_1|` is even and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`; in that case the number of compatible matchings is `(|𝒞_1| − 1)!!·Π_{ζ∈ℛ} |𝒞_ζ|!` (with `(−1)!! := 1`).

**(v) (the pair of `0`)** If `Π_{v∈V} c_v = 1`, then `J` is compatible with `c` iff `c_a c_{J(a)} = 1` for every `a` with `a ≠ 0` and `J(a) ≠ 0`.

## Proof

(i) If `ζ^{−1} = ζ` then `ζ^2 = 1`; also `ζ^r = 1` (every element of `μ` is a root of `X^r − 1`). As `r` is odd, `ζ = ζ^{r+1}·ζ^{−r} = (ζ^2)^{(r+1)/2}·(ζ^r)^{−1} = 1`. So inversion is a fixed-point-free involution of `μ ∖ {1}`, whose orbits are the pairs `{ζ, ζ^{−1}}`; choosing one element in each orbit gives `ℛ`. Distinct colours give disjoint classes, and every colour is `1`, or `ζ`, or `ζ^{−1}` for exactly one `ζ ∈ ℛ`.

(ii) `c_a c_b = 1` iff `c_b = c_a^{−1}`. If `c_a = 1`, this says `c_b = 1`. If `c_a ≠ 1`, then `c_a ∈ ℛ` or `c_a^{−1} ∈ ℛ`, and the condition says that `a` and `b` lie in the two classes `𝒞_ζ`, `𝒞_{ζ^{−1}}` of the pair `{ζ, ζ^{−1}} = {c_a, c_a^{−1}}`.

(iii) If `J` is compatible, then `c_{J(a)} = c_a^{−1}` for every `a`, so `J` maps `𝒞_ζ` into `𝒞_{ζ^{−1}}` for every `ζ ∈ μ`; as `J` is an involution, `J(𝒞_ζ) = 𝒞_{ζ^{−1}}`, and in particular `J(𝒞_1) = 𝒞_1`. The converse is (ii). For a compatible `J`, the restriction `J|_{𝒞_1}` is a fixed-point-free involution of `𝒞_1`, and `J|_{𝒞_ζ} : 𝒞_ζ → 𝒞_{ζ^{−1}}` is a bijection (with inverse `J|_{𝒞_{ζ^{−1}}}`). The map of the statement is injective because the classes `𝒞_1`, `𝒞_ζ`, `𝒞_{ζ^{−1}}` cover `V` (i) and `J` on `𝒞_{ζ^{−1}}` is the inverse of `J` on `𝒞_ζ`. It is surjective: the involution assembled from `(P, (σ_ζ))` is well defined on the partition of (i), is fixed-point-free (`P` is, and `σ_ζ` maps `𝒞_ζ` to the disjoint set `𝒞_{ζ^{−1}}`), is an involution, and is compatible by (ii); its restrictions are `P` and the `σ_ζ`.

(iv) By (iii), compatible matchings exist iff fixed-point-free involutions of `𝒞_1` and bijections `𝒞_ζ → 𝒞_{ζ^{−1}}` exist, i.e. iff `|𝒞_1|` is even and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`. The number of fixed-point-free involutions of a set of even size `2s` is `(2s − 1)!!`, and the number of bijections between two sets of size `t` is `t!`.

(v) The condition for `a = 0` and for `a = J(0)` is the same equation `c_0 c_{J(0)} = 1`. The pairs of `J` partition `V`, so `1 = Π_v c_v = c_0 c_{J(0)}·Π c_a c_{J(a)}`, the last product over the pairs `{a, J(a)}` not containing `0`; if those factors are `1`, so is `c_0 c_{J(0)}`. ∎

## Checks

- Enumeration with `μ` modelled as `ℤ/r` (additively; `c_a c_b = 1` means `c_a + c_b ≡ 0`), `ℛ = {z : 0 < z < r − z}`, for every colouring `c : V → ℤ/r` and every matching, `r ∈ {3, 5, 7}`, `|V| ∈ {2, 4, 6}`: (ii) for every pair, the count formula of (iv) and the characterization of (iii) for every compatible matching, the existence criterion (iv), and (v) for the colourings with `Σ c_v ≡ 0`: 4 643 740 checks, 0 failures.
- Negative control (`r` even): for `r = 4` the colour `2` is its own inverse, and (ii) fails for `c_a = c_b = 2` (`c_a c_b = 1`, but `a, b ∉ 𝒞_1` and `2` is in no pair `{ζ, ζ^{−1}}` with `ζ ≠ ζ^{−1}`).
