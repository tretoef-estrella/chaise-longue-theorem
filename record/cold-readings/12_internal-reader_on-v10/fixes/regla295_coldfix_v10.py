# -*- coding: utf-8 -*-
# Second stage of PAPER_OFICIAL_v10: the findings of the cold reading of 1 October 2026
# (VIVOS/ATAQUES_Y_REPORTES/COLD_V10/COLD_REPORT_V10.md: G1, E1, E2, P1-P11) applied to the output of
# regla293_build_v10.py.  Run:  python3 regla293_build_v10.py && python3 regla295_coldfix_v10.py
# Grepy, 2026-10-01. Every replacement asserts its anchor.
import os, re
os.chdir('/Users/rafa/Desktop/ARBOLYAML/VIVOS/MISIONES_TRAS_BARRIDO')
t = open('PAPER_OFICIAL_v10.md', encoding='utf-8').read()
assert '### A.9 Equality for every partition' not in t, 'already applied'

def rep(old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (n, count, old[:110])
    t = t.replace(old, new)

def block(start, end):
    """(i, j) of the text from `start` (inclusive) to `end` (exclusive); both anchors unique"""
    assert t.count(start) == 1, (t.count(start), start[:80])
    i = t.index(start); j = t.index(end, i)
    return i, j

def rep_in(start, end, pairs):
    """replacements restricted to one block; each pair is (old, new, count)"""
    global t
    i, j = block(start, end)
    s = t[i:j]
    for old, new, count in pairs:
        n = s.count(old)
        assert n == count, (n, count, old[:110])
        s = s.replace(old, new)
    t = t[:i] + s + t[j:]

# ---------------------------------------------------------------- P4: abstract
rep("As a count, Theorem A is not new: the ring is the space of coinvariants of the centralizer of a regular unipotent element of `SO_q` in a tensor power of the vector representation,",
    "As a count, Theorem A is not new: over an infinite field the ring is the space of coinvariants of the centralizer of a regular unipotent element of `SO_q` in a tensor power of the vector representation,")

# ---------------------------------------------------------------- P3: section 1.8, the tenses; and two stale «previous version»
rep("The previous version of this paper proved the Main Theorem for odd prime powers and stated the colour reduction for the degrees that are not prime powers as an open problem; the reduction and the bipartite count (§6–§7) complete it.",
    "Versions 4 and 5 of this paper proved the Main Theorem for odd prime powers and stated the colour reduction for the degrees that are not prime powers as an open problem; the reduction and the bipartite count (§6–§7), added in version 6, complete it.")
rep("The present version (v8) adds the machine-checked proof of Main Theorem′ (§12.8), records that the repository [Rep] is public, states the status of the *Double Ladder* theorem more precisely (Remark 10.2), and adds one clause to the proof of Lemma 6.8; no statement and no proof of the previous version changes.",
    "Version 8 added the machine-checked proof of Main Theorem′ (§12.8), recorded that the repository [Rep] is public, stated the status of the *Double Ladder* theorem more precisely (Remark 10.2), and added one clause to the proof of Lemma 6.8; no statement and no proof of version 7 changed.")
rep("Version 9 (the present one) corrects the attribution of Theorem A: in characteristic `0` it follows from a theorem of Kostant, which the earlier versions did not cite (Remark 8.4). It also records that the *Watermark* and *Double Ladder* theorems are now proved for every prime and verified in Lean [WDL] (Remark 10.2). Again no statement and no proof changes.",
    "Version 9 corrected the attribution of Theorem A: in characteristic `0` it follows from a theorem of Kostant, which the earlier versions did not cite (Remark 8.4). It also recorded that the *Watermark* and *Double Ladder* theorems are now proved for every prime and verified in Lean [WDL] (Remark 10.2). Again no statement and no proof changed.")
rep("It also adds the reading of Theorem B in the same language (Proposition 8.5, Corollary 8.6, Remark 8.7), restates problem 6 of §13 and adds problem 7. No statement and no proof of the earlier versions changes.",
    "It also adds the reading of Theorem B in the same language (Proposition 8.5, Corollary 8.6, Remark 8.7) and the equality for the ideals of Appendix A (Corollary A.17), restates problem 6 of §13 and adds problem 7. A supplementary note [Note], deposited with this version, presents the dictionary on its own, with a statistic on walks that gives the Hilbert series of the ring of Theorem A. No statement and no proof of the earlier versions changes.")
rep("The previous version of this paper wrote «initial ideal» for `gr` in the proofs of Theorem 5.9 and Proposition 9.1.)",
    "Version 4 of this paper wrote «initial ideal» for `gr` in the proofs of Theorem 5.9 and Proposition 9.1.)")

# ---------------------------------------------------------------- Remark 8.4: symbols (P8), P9, E2, P5, P1, P4, P11(d)
R84 = "**Remark 8.4 (the centralizer of a regular unipotent element; as a count, Theorem A is not new).**"
P85 = "**Proposition 8.5 (the invariant copairing).**"
rep(R84 + " Let `q = 2m + 1 ≥ 3`.",
    R84 + " Let `q = 2h + 1 ≥ 3`, so that `h = (q−1)/2` as in §1.9. In this remark and in Remark 8.7 the letters `G`, `T`, `W`, `K`, `ℓ` and `u` have the meaning that they have in the sources quoted, not that of §2 and §9; `𝒵` is the centralizer defined in (1).")
rep_in("(1) *A dictionary.*", "(2) *Characteristic `0`: Kostant's theorem.*", [
    ("and `f(e)` preserves the form exactly when `f(e)f(−e) = 1`; its determinant is `f(0)^q = f(0)`. So the centralizer of `e` in `SO(V) ≅ SO_{2m+1}` is the commutative unipotent group",
     "and `f(e)` preserves the form exactly when `f(e)f(−e) = 1`; the constant term of this identity gives `f(0) = ±1`, so the determinant of `f(e)` is `f(0)^q = f(0)`. So the centralizer of `e` in `SO(V) ≅ SO_{2h+1}` is the commutative unipotent group", 1),
    ("`Z := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`.", "`𝒵 := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`.", 1),
    ("lies in `Z`, and for `t ≠ 0` it has a single Jordan block: it is a regular unipotent element of `SO(V)`, and `Z` is its centralizer.",
     "lies in `𝒵`, and for `t ≠ 0` it has a single Jordan block: it is a regular unipotent element of `SO(V)`, and `𝒵` is its centralizer.", 1),
    ("and `f(e) ∈ Z` acts on it as multiplication by", "and `f(e) ∈ 𝒵` acts on it as multiplication by", 1),
    ("For a general `f(e) ∈ Z` put `h := 1 + f`; then `h(0) = 2` is a unit, `f(x) = h(x)/h(−x)`, and `Π_x f(x) − 1 = (H − H^−)/H^−` with `H := Π_x h(x)` and `H^− := Π_x h(−x)`.",
     "For a general `f(e) ∈ 𝒵` put `φ := 1 + f`; then `φ(0) = 2` is a unit, `f(x) = φ(x)/φ(−x)`, and `Π_x f(x) − 1 = (H − H^−)/H^−` with `H := Π_x φ(x)` and `H^− := Π_x φ(−x)`.", 1),
    ("`F[L]/I_q(L) = V^{⊗n} / ⟨(g − 1)v : g ∈ Z, v ∈ V^{⊗n}⟩`,", "`F[L]/I_q(L) = V^{⊗n} / ⟨(g − 1)v : g ∈ 𝒵, v ∈ V^{⊗n}⟩`,", 1),
    ("the coinvariants of the centralizer of a regular unipotent element on the `n`-th tensor power of the vector representation of `SO_{2m+1}`. Since `V^{⊗n}` is isomorphic to its dual as a representation of `Z`, this space has the dimension of the invariants `(V^{⊗n})^Z`. In characteristic `0` the invariants of `Z` are those of its Lie algebra, which has basis `e, e^3, …, e^{2m−1}`;",
     "the coinvariants of the centralizer of a regular unipotent element on the `n`-th tensor power of the vector representation of `SO_{2h+1}`. The hypothesis that `F` is infinite cannot be dropped: over `F_3` the coinvariants of the finite group `𝒵` have dimension `9`, `27` and `19` at `(q, n) = (3, 3), (3, 4)` and `(5, 3)`, against `7`, `19` and `13` for the ring (§12.5). Over a finite field the statement holds for the centralizer as an algebraic group, that is, after extension of scalars to an infinite field. Since `V^{⊗n}` is isomorphic to its dual as a representation of `𝒵`, the space of coinvariants has the dimension of the invariants `(V^{⊗n})^𝒵`. In characteristic `0` the invariants of `𝒵` are those of its Lie algebra, which has basis `e, e^3, …, e^{2h−1}`;", 1),
])
rep_in("(2) *Characteristic `0`: Kostant's theorem.*", "(3) *Odd characteristic: a proposition of Bezrukavnikov, Riche and Rider.*", [
    ("Let `G` be a connected reductive group over `C` and `W`", "Let `G` be a connected semisimple group over `C` and `W`", 1),
    ("The weights of `V` are `0, ±ε_1, …, ±ε_m`, which span the root lattice of `so_{2m+1}`.", "The weights of `V` are `0, ±ε_1, …, ±ε_h`, which span the root lattice of `so_{2h+1}`.", 1),
    ("the number of closed walks of length `n` on `Z^m` with steps `0, ±ε_i`, which is `N_q(n)`.", "the number of closed walks of length `n` on the lattice `Z^h` with steps `0, ±ε_i`, which is `N_q(n)`.", 1),
])
rep_in("(3) *Odd characteristic: a proposition of Bezrukavnikov, Riche and Rider.*", "(4) *What Appendix A contributes.*", [
    ("Take `G = Spin_{2m+1}` and `ℓ` odd. The only bad prime of type `B_m` is `2`, and `X^*(T)/ZR ≅ Z/2`, so the hypotheses hold.",
     "Take `G = Spin_{2h+1}` and `ℓ` odd. Then `ℓ` is good for `G` (the only bad prime of type `B_h`, `h ≥ 2`, is `2`, and type `A_1` has none), and `X^*(T)/ZR ≅ Z/2`, so the hypotheses hold.", 1),
    ("([BRR, proof of Lemma 2.13] for `m ≥ 2`; for `m = 1`, `G = SL_2` and `V` is the Weyl module of highest weight `2`)",
     "([BRR, proof of Lemma 2.13] for `h ≥ 2`; for `h = 1`, `G = SL_2` and `V` is the Weyl module of highest weight `2`)", 1),
    ("`dim F[L]/I_q(L) = dim (V^{⊗n})^Z = N_q(n)`", "`dim F[L]/I_q(L) = dim (V^{⊗n})^𝒵 = N_q(n)`", 1),
    ("The count of Theorem A should be credited to Kostant in characteristic `0` and to [BRR] in odd characteristic.",
     "The count of Theorem A should be credited to Kostant in characteristic `0` and to [BRR] in odd characteristic. (Logically, the case of characteristic `0` also follows from the case of one odd prime `p`: the ring over `Q` is `M ⊗ Q` for the abelian group `M` of Corollary 8.2, so its dimension is at most that of `M ⊗ F_p`, and Proposition A.5 gives the lower bound. We keep the reference to Kostant, whose theorem is the origin of the statement.)", 1),
    ("it describes the centralizer group scheme and does not contain the count.",
     "it describes the centralizer group scheme, and we did not find the count in it (we read its introduction and §2.2, and searched its source).", 1),
])
rep_in("(4) *What Appendix A contributes.*", "(5) *Computed, not claimed.*", [
    ("to every partition `μ` with at most `m` parts,", "to every partition `μ` with at most `h` parts,", 1),
    ("such that `dim F[L]/K_μ(L)` is at most the multiplicity `N_μ(n)` of the weight `μ` in `V^{⊗n}` (Theorem A.15; equality is proved for `μ = ∅` and computed at `178` cells, §12.5), and each row of `K_μ(L ∪ z)` contains the ideal of the corresponding neighbouring weight (Theorem A.12).",
     "such that `dim F[L]/K_μ(L)` is the multiplicity `N_μ(n)` of the weight `μ` in `V^{⊗n}` (Theorem A.15 and Corollary A.17; computed independently at `178` cells, §12.5), and each row of `K_μ(L ∪ z)` is the ideal of the corresponding neighbouring weight (Theorem A.12 and Corollary A.17).", 1),
])
rep_in("(6) *Even `q`.*", P85, [
    ("For even `q = 2m` the form of (1) is alternating, and the same dictionary holds with `Sp(V) ≅ Sp_{2m}`: the centralizer of the regular unipotent element `g_1` is `{±1} × Z`, and `−1` acts on `V^{⊗n}` as `(−1)^n`. The group `Sp_{2m}` is simply connected, its only bad prime is `2`, `X^*(T)/ZR ≅ Z/2`, and `V` is a simple Weyl module in every characteristic.",
     "For even `q` the form of (1) is alternating, and the same dictionary holds with `Sp(V) ≅ Sp_q`: the centralizer of the regular unipotent element `g_1` is `{±1} × 𝒵`, and `−1` acts on `V^{⊗n}` as `(−1)^n`. The group `Sp_q` is simply connected, every odd prime is good for it, `X^*(T)/ZR ≅ Z/2`, and `V` is a simple Weyl module in every characteristic.", 1),
    ("`dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q) = n!·[y^n] I_0(2y)^m`,", "`dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q) = n!·[y^n] I_0(2y)^{q/2}`,", 1),
    ("the number of closed walks of length `n` on `Z^m` with steps `±ε_i`. Version 9 listed this as an open problem; for even `n` it is a consequence of the literature.",
     "the number of closed walks of length `n` on the lattice `Z^{q/2}` with steps `±ε_i`. (In characteristic `0` the reference to [Kos] can again be avoided: the dimension over `Q` is at most the dimension over `F_3`, and Proposition 8.5(iii) with Corollary 8.6(i), applied to the odd number `q + 1`, gives the lower bound.) Version 9 listed this as an open problem; for even `n` it is a consequence of the literature.", 1),
    ("and the proposition says nothing about the invariants of `Z` alone.", "and the proposition says nothing about the invariants of `𝒵` alone.", 1),
])

# ---------------------------------------------------------------- Corollary 8.6: P5, P8
R87 = "*Remark 8.7 (what this says).*"
rep_in("**Corollary 8.6 (Theorem B at `2k + 2` variables; both ends of the sandwich).**", R87, [
    ("Every element `f` of `M := Σ_J D_{q−1,J}C_{q−1}` is killed by", "Every element `f` of `ℳ := Σ_J D_{q−1,J}C_{q−1}` is killed by", 1),
    ("and the linear map `θ : M → C`,", "and the linear map `θ : ℳ → C`,", 1),
    ("so `M = Σ_J D_{q−1,J}C`. Hence `θ(M) = (D_J : J ∈ 𝒥)C`, and `dim M = Q_k(q)` by Theorem B.",
     "so `ℳ = Σ_J D_{q−1,J}C`. Hence `θ(ℳ) = (D_J : J ∈ 𝒥)C`, and `dim ℳ = Q_k(q)` by Theorem B.", 1),
    ("(ii) By Remark 8.4(6), which rests on [BRR, Proposition 2.12] (on [Kos] in characteristic `0`), `dim F[x]/((e_j : j odd) + (x_i^{q−1})) = N!·[y^N] I_0(2y)^{(q−1)/2} = Q_k(q)`. By Proposition 8.5(iii) and (i), `M` is a subspace of `ann(e_j : j odd)` of the same dimension, so they are equal.",
     "(ii) By Proposition 8.5(iii) and (i), `ℳ` is a subspace of `ann(e_j : j odd)`, of dimension `Q_k(q)`; so `dim F[x]/((e_j : j odd) + (x_i^{q−1})) ≥ Q_k(q)` over every field. If `char F` is odd, this dimension is `N!·[y^N] I_0(2y)^{(q−1)/2} = Q_k(q)` by Remark 8.4(6), which rests on [BRR, Proposition 2.12]. If `char F = 0`, the ring is obtained by extension of scalars from the finitely generated abelian group `Z[x]/((e_j : j odd) + (x_i^{q−1}))`, so its dimension is the rank of this group, which is at most the dimension of its reduction modulo `3`, that is, `Q_k(q)`; so [Kos] is not needed. In both cases `ℳ` and `ann(e_j : j odd)` have the same dimension, so they are equal.", 1),
])

# ---------------------------------------------------------------- Remark 8.7: P4, P7, P8, E1, P10, G1, P6
rep_in(R87, "## 9.", [
    ("so every `D_{r,J}` is a tensor of `V_r^{⊗N}` invariant under the whole group `G` of isometries (`Sp_r` for even `r`, `O_r` for odd `r`).",
     "so every `D_{r,J}` is a tensor of `V_r^{⊗N}` invariant under the whole group of isometries (`Sp_r` for even `r`, `O_r` for odd `r`).", 1),
    ("over every field; in characteristic `≠ 2` that space is the whole space of invariants of the centralizer of a regular unipotent element.** By Proposition 2.5, for `m = p^v` Conjecture 1.2 of [DS] is equivalent to this statement over `F_p` for `Sp_{m−1}`.",
     "over every field; in characteristic `≠ 2`, and modulo [BRR, Proposition 2.12], that space is the whole space of invariants of the centralizer of a regular unipotent element** (of the centralizer as an algebraic group; equivalently, over an infinite field). By Proposition 2.5 and Theorem 0, for degree `p^v` and `k ≥ 1`, Conjecture 1.2 of [DS] is equivalent to the first half of this statement (the dimension count) over `F_p`, for `Sp_{p^v−1}`.", 1),
    ("By Kostant's theorem the evaluation at a regular nilpotent `e` maps the `G`-equivariant polynomial maps `𝔤 → W` onto `W^{𝔤^e}` [Kos]. By the first fundamental theorem, the equivariant maps `𝔤 → V_r^{⊗N}` of degree `d` are spanned by the complete contractions of `V_r^{⊗N} ⊗ 𝔤^{⊗d}` with the form (for odd `r` the group is `SO_r`; an invariant involving the determinant would leave an odd number `N + 2d − r` of factors to be paired, so none occurs).",
     "Let `G` be `SO_r` for odd `r` and `Sp_r` for even `r`, with Lie algebra `𝔤`, and let `W := V_r^{⊗N}`. By Kostant's theorem the evaluation at a regular nilpotent `e` maps the `G`-equivariant polynomial maps `𝔤 → W` onto the invariants `W^{G^e}` of the centralizer of `e` in `G` [Kos]. These are the invariants of `𝔤^e`: for `SO_r` the group `G^e` is connected, and for `Sp_r` it is the product of `{±1}` and a connected group, and `−1` acts trivially on `W` because `N` is even. By the first fundamental theorem, the equivariant maps `𝔤 → W` of degree `d` are spanned by the complete contractions of `V_r^{⊗N} ⊗ 𝔤^{⊗d}` with the form (for odd `r`, `O_r = {±1} × SO_r`, and `−1` acts trivially on this tensor power, whose degree `N + 2d` is even; so the invariants of `SO_r` in it are those of `O_r`).", 1),
    ("For odd `r = q` the same statement would read `dim_F Σ_J D_{q,J} C_q = N_q(N)`, that is, `⋂_J (I_J + (x_i^q)) = (e_j : j odd) + (x_i^q)` by Theorem A.",
     "For odd `r = q` the same statement would read `dim_F Σ_J D_{q,J} C_q = N_q(N)`; for `char F ≠ 2` this is `⋂_J (I_J + (x_i^q)) = (e_j : j odd) + (x_i^q)`, by Proposition 8.5 and Theorem A.", 1),
    ("The inequality `≤` holds over every field, by the argument of Proposition 9.1, and by (2) there is equality in characteristic `0`.",
     "The inequality `≤` holds over every field. In characteristic `≠ 2` it is Proposition 8.5(iii) together with Theorem A. In characteristic `2` the two ideals differ (their colengths are `19` and `21` at `(q, N) = (3, 4)`), and the argument of Proposition 9.1 does not apply, because it needs a set of `q` values on which `v ↦ −v` has a single fixed point; but `Σ_J D_{q,J}C_q` is spanned by vectors with integer coordinates, so its dimension over any field is at most its dimension over `Q`. By the sketch (2) there is equality in characteristic `0`.", 1),
])

# ---------------------------------------------------------------- section 12.5: the finite-field check; section 12.6: sources read
rep("One run of the first engine was stopped by the memory guard at the cell `(5, 6)` and rerun with a corrected engine.",
    "One run of the first engine was stopped by the memory guard at the cell `(5, 6)` and rerun with a corrected engine. For the last sentences of Remark 8.4(1): the coinvariants of the group of `F_p`-points of the centralizer at `(p, q, n) = (3, 3, 3), (3, 3, 4), (3, 5, 3)` (`9, 27, 19` against `7, 19, 13`), computed by the cold reader and again by the author with separate code; at `(5, 3, 3)` and `(5, 5, 3)` the two numbers agree.")
rep("[BRR, §2] and the introduction of [Ric] were read in the arXiv sources;", "[BRR, §2.1–§2.6] and the introduction and §2.2 of [Ric] were read in the arXiv sources;")

# ---------------------------------------------------------------- section 13, problem 6 (P8)
rep("every even `q = 2m` and every odd `n`, `dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q)` is the number of walks of length `n` on `Z^m` with steps `±ε_i` from `0` to `ε_1`.",
    "every even `q` and every odd `n`, `dim F[x_1, …, x_n]/(e_1, e_3, …; x_1^q, …, x_n^q)` is the number of walks of length `n` on the lattice `Z^{q/2}` with steps `±ε_i` from `0` to `ε_1`.")
rep("For even `n` the corresponding statement (closed walks) follows from [Kos] and [BRR, Proposition 2.12] (Remark 8.4(6));",
    "For even `n` the corresponding statement (closed walks) follows from [BRR, Proposition 2.12] (Remark 8.4(6));")

# ---------------------------------------------------------------- section 14 (P1)
rep("What this paper adds is that dictionary and the elementary proof of Appendix A, with its ideals `K_μ`.",
    "What this paper adds is that dictionary and the elementary proof of Appendix A, with its ideals `K_μ` and the equality `dim F[L]/K_μ(L) = N_μ(n)` for every `μ` (Corollary A.17).")

# ---------------------------------------------------------------- Appendix A: Corollary A.17 (P1)
A16 = "*Remark A.16.* In characteristic `2` the statement fails, and the proof uses `½` in exactly one place (Lemma A.10). The measured dimensions at `n = 4` are `21, 65, 133, 225` for `q = 3, 5, 7, 9`, against `N_q(4) = 19, 61, 127, 217`."
rep(A16, A16 + """


### A.9 Equality for every partition

**Corollary A.17.** *For every partition `μ` with `ℓ(μ) ≤ h`, every finite set `L` and every `z ∉ L`:*
- *`dim_F F[L]/K_μ(L) = N_{μ}(|L|)`;*
- *`R_a(K_μ(L ∪ z)) = K_{child_a(μ)}(L)` for every `a ∈ {0, …, q−1}`.*

*Proof.* Let `P(μ)` be the statement «`dim_F F[L]/K_μ(L) = N_μ(|L|)` for every finite set `L`». `P(∅)` is Theorem A. Suppose `P(μ)`, and let `|L| = n` and `z ∉ L`. In the chain of the proof of Theorem A.15,

`dim F[L∪z]/K_μ(L∪z) = Σ_a dim F[L]/R_a(K_μ(L∪z)) ≤ Σ_a dim F[L]/K_{child_a(μ)}(L) ≤ Σ_a N_{child_a(μ)}(n) = N_μ(n+1)`,

the two ends are equal by `P(μ)`, and all the numbers are finite. The first inequality is a sum of the inequalities `dim F[L]/R_a ≤ dim F[L]/K_{child_a(μ)}(L)` given by the inclusions of Theorem A.12, and the second is a sum of the inequalities of Theorem A.15; so each of them is an equality. Hence `dim F[L]/K_{child_a(μ)}(L) = N_{child_a(μ)}(n)` for every `a` and every `L`, which is `P(child_a(μ))`, and `R_a(K_μ(L∪z)) = K_{child_a(μ)}(L)`, because one ideal contains the other and they have the same finite codimension. So `P(μ)` implies `P(ν)` for every child `ν` of `μ`, and the second claim for `μ`.

It remains to see that every partition `ν ≠ ∅` with `ℓ(ν) ≤ h` is a child of a partition `μ` with `ℓ(μ) ≤ h` and `|μ| = |ν| − 1`; then `P(ν)` follows by induction on `|ν|`. Let `μ` be `ν` with its smallest part lowered by `1` (and deleted if it becomes `0`). If the smallest part of `ν` is `1`, then `ν = μ ∪ (1)` and `ℓ(μ) + 1 = ℓ(ν) ≤ h`, so `ν` is a new-class child of `μ` (Definition A.2). Otherwise `ℓ(μ) = ℓ(ν) =: ℓ` and `ν` is `μ` with `μ_ℓ` replaced by `μ_ℓ + 1`: the raise child `a = q − ℓ`. ∎

So the ideals `K_μ(L)` are graded models of all the weight spaces of `V^{⊗n}`, and the `q` rows of `K_μ(L ∪ z)` are exactly the ideals of the `q` neighbouring weights. We proved Theorem A.15 as an upper bound, which is all that Theorem A needs; that the bound is an equality was pointed out by the cold reader of this version (§12.6).""")

# ---------------------------------------------------------------- references (P11) and the note
rep("- **[BRR]** R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer, I*, arXiv:2005.05583 (v2, 4 July 2024). (Remark 8.4, Corollary 8.6; §2.2–§2.6 were read in the arXiv source, in particular Proposition 2.12 and the proof of Lemma 2.13.)",
    "- **[BRR]** R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583 (v2, 4 July 2024; the first version carried «, I» in the title). (§1.6, §1.8, §8, §9.1, §12.6, §13 and §14; §2.1–§2.6 were read in the arXiv source, in particular Proposition 2.12 and the proof of Lemma 2.13.)")
rep("(Remarks 8.4 and 8.7 only; quoted through [Gin]; not read in the original.)\n- **[LC]**",
    "(§1.6, §8, §12.6 and §14; quoted through [Gin]; not read in the original.)\n- **[LC]**")
RIC = "- **[Ric]** S. Riche, *Kostant section, universal centralizer, and a modular derived Satake equivalence*, arXiv:1411.3112. (Remark 8.4(3) only; the introduction and §2.2 were read in the arXiv source.)\n"
rep(RIC, "")
rep("- **[Shi79]** T. Shioda,",
    "- **[Ric]** S. Riche, *Kostant section, universal centralizer, and a modular derived Satake equivalence*, arXiv:1411.3112 (v4, 19 May 2015). (Remark 8.4(3) only; the introduction and §2.2 were read in the arXiv source.)\n"
    "- **[Shi79]** T. Shioda,")
rep("- **[Mlib]** The mathlib Community,",
    "- **[Note]** R. Amichis Luengo, *The Chaise Longue Theorem and the centralizer of a regular unipotent element* (supplementary note, version 1, 1 October 2026), deposited with this version of the paper in the same Zenodo record, and in [Rep], `paper/`. (§1.8 and §12.6 only; not refereed.)\n"
    "- **[Mlib]** The mathlib Community,")

# ---------------------------------------------------------------- notation table (P8)
rep("| `C_r`, `D_r(a,b)`, `D_{r,J}` | the box ring `(x_i^r)` in `2s` variables; the copairing and its products over a matching (Proposition 8.5) | §8 |",
    "| `C_r`, `D_r(a,b)`, `D_{r,J}` | the box ring `(x_i^r)` in `2s` variables; the copairing and its products over a matching (Proposition 8.5) | §8 |\n"
    "| `V`, `e`, `𝒵`, `g_t` | `F[x]/(x^q)` with its form; multiplication by `x`; the centralizer of `e` in `SO(V)`; the Cayley transform (Remark 8.4) | §8 |")

# ---------------------------------------------------------------- final checks
i, j = block(R84, "## 9.")
s = t[i:j]
assert not re.search(r'`Z`|\^Z\b|∈ Z\b|× Z\b', s), 'centralizer still written Z in section 8'
assert not re.search(r'2m|_m\b|\^m\b|`m`', s), 'rank still written m in section 8'
assert 'PLACEHOLDER' not in t and 'not yet been read cold' not in t
open('PAPER_OFICIAL_v10.md', 'w', encoding='utf-8').write(t)
print('cold fixes applied: PAPER_OFICIAL_v10.md', len(t), 'chars;', t.count('\n'), 'lines')
