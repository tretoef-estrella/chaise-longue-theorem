# Part 4: §9 — header (reader notes 3, 4), blocks (note 12), Lemma 9.8 (note 2),
# Lemma 9.10 short route (D3, pending 412), Remark 9.15(2) (note 7).
import pathlib
SRC = (pathlib.Path(__file__).parent / "v11_source.md").read_text(encoding="utf-8")
def block(start, end):
    assert SRC.count(start) == 1, start
    assert SRC.count(end) == 1, end
    i = SRC.index(start); j = SRC.index(end, i)
    return SRC[i:j]

OLD_910 = block("*`0 ∉ 𝒞_1`.* Now `g_P = ", "### 9.5 The theorem")
NEW_910 = """*`0 ∉ 𝒞_1`.* Now `g_P = Π_{{i<l} ∈ P} (t_l − 1)φ_q(t_it_l)`, over the perfect matchings `P` of the `2k' ≥ 2` indices of `𝒞_1`; let `ℳ` be the ideal they generate. Let `i_1 := min 𝒞_1`, let `H'` be the group on the other indices, and write each `f ∈ R_{c,1}` as `f = Σ_{j ∈ Z/q} t_{i_1}^j f_j` with `f_j ∈ F[H']`. The map `θ : ℳ → F[H']`, `f ↦ f_0`, is `F[H']`-linear. If `{i_1, l} ∈ P`, the coefficient of `t_{i_1}^0` in `φ_q(t_{i_1}t_l)` is `1`, and no other factor of `g_P` contains `t_{i_1}`; so `θ(g_P) = (t_l − 1)·Π (t_{l'} − 1)φ_q(t_{i'}t_{l'})`, the product over the other pairs: the generator of the previous case, with `i_1` in the role of `0`. So `θ(ℳ)` contains the ideal of the previous case in `2k' − 1` variables, and `dim ℳ ≥ dim θ(ℳ) ≥ N_{q−1}(2k')`. ∎

(Version 11 proved in addition that `θ` is injective on `ℳ`. No conclusion uses it: the equality block by block is Corollary 9.12(i), which follows from the inequalities alone. The proof printed here is the one that was formalized, §14.8.)

"""

EDITS = [
    ("9 header (reader note 3)",
     "In this section `m ≥ 4` is even, `k ≥ 1`, `n = 2k` and `N = n + 2`. Nothing in §2.1",
     "In this section `m ≥ 4` is even, `k ≥ 1`, `n = 2k` and `N = n + 2`, except in §9.2, which also allows the degree `2` and `k ≥ 0` (Lemma 9.10 uses it in that generality). Nothing in §2.1"),
    ("9 N_1 (reader note 4)",
     "In this section the letter `r` is the odd box of §8, and the cofactor of a prime power in `m`, which §6 calls `r`, is written `r'`.",
     "In this section the letter `r` is the odd box of §8, and the cofactor of a prime power in `m`, which §6 calls `r`, is written `r'`. The count `N_r(n)` of §8 makes sense for `r = 1` (`h = 0`): `N_1(n) = 1`, the only tuple being `(0, …, 0)`; it is used in that sense in §9.2 and §9.4."),
    ("9.3 blocks (reader note 12)",
     "**Blocks.** Fix a colouring `c ∈ μ_{r'}^{n+1}`,",
     "**Blocks** (this replaces Lemma 6.3, which uses that the cofactor is odd). Fix a colouring `c ∈ μ_{r'}^{n+1}`,"),
    ("9.8 N_1 (reader note 2)",
     "*Proof.* This is Lemma 6.6: §6.4 uses only `(t_i − 1)^q = 0`, `q = p^v` and `2 ∈ F^×`. ∎",
     "*Proof.* This is Lemma 6.6: §6.4 uses only `(t_i − 1)^q = 0`, `q = p^v` and `2 ∈ F^×`. The number `N_1(c)` of §6.4 is the one of Lemma 9.6: if `0 ∉ 𝒞_1` the two definitions coincide, and if `0 ∈ 𝒞_1` a tuple `(w_i)_{i ∈ 𝒞_1}` that splits into inverse pairs has product `1`, so its entry `w_0` is the one that §6.4 computes from the others, and deleting it is a bijection between the two sets of tuples. ∎"),
    ("9.10 short route (D3)", OLD_910, NEW_910),
    ("9.15(2) (reader note 7)",
     "(2) *The list of boxes.* Theorem 9.11 uses Theorem O exactly at the boxes",
     "(2) *The list of boxes.* Theorem 9.11 uses Theorem O — or, in Lemma 9.9 when `0 ∉ 𝒞_{−1}`, Theorem 8.11 at the second root `{(∅, 0)}` — exactly at the boxes"),
]
