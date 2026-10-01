# -*- coding: utf-8 -*-
# The findings of the cold reading of 1 October 2026 (COLD_REPORT_V10.md: G1, E1, E2, E3, P1, P4, P9-P13)
# applied to THE_REGULAR_CENTRALIZER_NOTE_v1.md. Input: the copy kept in corpus4/regla295_v10_fixes/ (the text the reader read).
# Grepy, 2026-10-01. Every replacement asserts its anchor.
import re
SRC = '/Users/rafa/Desktop/ARBOLYAML/corpus4/regla295_v10_fixes/THE_REGULAR_CENTRALIZER_NOTE_v1_before_cold_fixes.md'
OUT = '/Users/rafa/Desktop/ARBOLYAML/VIVOS/MISIONES_TRAS_BARRIDO/THE_REGULAR_CENTRALIZER_NOTE_v1.md'
t = open(SRC, encoding='utf-8').read()
def rep(old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (n, count, old[:110])
    t = t.replace(old, new)

# ---- P8: the centralizer is written 𝒵 (Z is kept for the integers)
rep("is `Z` for odd `r` and `{±1} × Z` for even `r`, where*", "is `𝒵` for odd `r` and `{±1} × 𝒵` for even `r`, where*")
rep("`Z := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`,", "`𝒵 := { f(e) : f(e)f(−e) = 1, f(0) = 1 }`,")
rep("is an element of `Z` with a single Jordan block", "is an element of `𝒵` with a single Jordan block")
rep("with `g ∈ Z` is the ideal", "with `g ∈ 𝒵` is the ideal")
rep("= (V^{⊗n})_Z`,", "= (V^{⊗n})_𝒵`,")
rep("*the space of coinvariants of `Z`, and its dimension is `dim (V^{⊗n})^Z`.*", "*the space of coinvariants of `𝒵`, and its dimension is `dim (V^{⊗n})^𝒵`.*")
rep("For a general `f(e) ∈ Z` put", "For a general `f(e) ∈ 𝒵` put")
rep("as a `Z`-module, through the form", "as a `𝒵`-module, through the form")
rep("(1) In characteristic `0` the invariants of `Z` are", "(1) In characteristic `0` the invariants of `𝒵` are")
rep("is a walk of length `n` on `Z^m`, with a loop", "is a walk of length `n` on the lattice `Z^m`, with a loop")
rep("this says: `dim (V^{⊗n})^Z = dim (V^{⊗n})^T`", "this says: `dim (V^{⊗n})^𝒵 = dim (V^{⊗n})^T`")
rep("So `dim (V^{⊗n})^Z = dim (V^{⊗n})^T = N_q(n)` over `K`", "So `dim (V^{⊗n})^𝒵 = dim (V^{⊗n})^T = N_q(n)` over `K`")
rep("The centralizer of `g_1` is `{±1} × Z`,", "The centralizer of `g_1` is `{±1} × 𝒵`,")
rep("the ring is the space of coinvariants of `Z` alone.", "the ring is the space of coinvariants of `𝒵` alone.")

# ---- header and summary (P4, E3)
rep("A supplement to *The Chaise Longue Theorem*, version 10 (doi:10.5281/zenodo.22961150), cited below as [CL].",
    "A supplement to *The Chaise Longue Theorem*, version 10 (doi:10.5281/zenodo.22961150), cited below as [CL]. In this note `Z` is the ring of integers and `𝒵` is a centralizer.")
rep("The ring of Theorem A of [CL] is the space of coinvariants of the centralizer of a regular unipotent element in `V^{⊗n}`.",
    "Over an infinite field, the ring of Theorem A of [CL] is the space of coinvariants of the centralizer of a regular unipotent element in `V^{⊗n}`.")
rep("Theorem B of [CL], which is the algebraic form of Conjecture 1.2 of Degtyarev and Shimada, says:",
    "Theorem B of [CL], which for degree `p^v` is the algebraic form of Conjecture 1.2 of Degtyarev and Shimada, says:")
rep("With the proposition of Bezrukavnikov–Riche–Rider, that subspace is, in characteristic `≠ 2`, the whole space of invariants of the centralizer. In characteristic `0` this also follows from Kostant's theorem and the first fundamental theorem of invariant theory (§4.3, a sketch).",
    "With the proposition of Bezrukavnikov–Riche–Rider, that subspace is, in characteristic `≠ 2`, the whole space of invariants of the centralizer (as an algebraic group). In characteristic `0` there is also a derivation from Kostant's theorem and the first fundamental theorem of invariant theory (§4.3, a sketch).")
rep("A statistic on lattice walks whose generating function is the Hilbert series of the ring of Theorem A (a theorem, given Appendix A of [CL]);",
    "A statistic on lattice walks whose generating function is the Hilbert series of the ring of Theorem A (a theorem, given Appendix A of [CL]; that appendix also gives, for every weight `μ`, an ideal whose colength is the multiplicity of `μ`);")

# ---- section 1: the finite-field caveat (P4)
rep("The zero weight space has dimension the number of closed walks: `N_r(n) := n!·[y^n] e^y I_0(2y)^m` for odd `r`, and `n!·[y^n] I_0(2y)^m` for even `r`.",
    "The zero weight space has dimension the number of closed walks: `N_r(n) := n!·[y^n] e^y I_0(2y)^m` for odd `r`, and `n!·[y^n] I_0(2y)^m` for even `r`. (3) The hypothesis that `F` is infinite cannot be dropped. Over `F_3` the group `𝒵` is finite, and its coinvariants have dimension `9`, `27` and `19` at `(r, n) = (3, 3), (3, 4)` and `(5, 3)`, against `7`, `19` and `13` for the ring (computed; at `(3, 3)` and `(5, 3)` over `F_5` the two numbers agree). Over a finite field the proposition holds for the centralizer as an algebraic group, that is, after extension of scalars to an infinite field; the dimension of the ring does not change under such an extension.")

# ---- section 2 (E2, P9, P5, P1)
rep("**2.1 Characteristic `0`: Kostant.** For a connected reductive group `G` over `C`", "**2.1 Characteristic `0`: Kostant.** For a connected semisimple group `G` over `C`")
rep("Take `G = Spin_{2m+1}` and `ℓ` odd. The only bad prime of type `B_m` is `2`, and `X^*(T)/ZR ≅ Z/2`.",
    "Take `G = Spin_{2m+1}` and `ℓ` odd. Then `ℓ` is good for `G` (the only bad prime of type `B_m`, `m ≥ 2`, is `2`, and type `A_1` has none), and `X^*(T)/ZR ≅ Z/2`.")
rep("follows from Theorem A over the fields `Q` and `F_p`, so it follows too.",
    "follows from Theorem A over the fields `Q` and `F_p`, so it follows too. (Logically, characteristic `0` follows from one odd prime `p`: the dimension over `Q` is the rank of that group, which is at most the dimension over `F_p`, and the lower bound of [CL, Proposition A.5] is elementary. Kostant's theorem is the origin of the statement, and we keep the reference.)")
rep("such that `dim F[L]/K_μ(L)` is at most the multiplicity of the weight `Σμ_iε_i` in `V^{⊗n}`, with equality for `μ = ∅` (proved) and at `178` cells (computed).",
    "such that `dim F[L]/K_μ(L)` is the multiplicity of the weight `Σμ_iε_i` in `V^{⊗n}`, and such that the rows of `K_μ` in a new variable are the ideals of the `q` neighbouring weights ([CL, Theorem A.15 and Corollary A.17]; computed independently at `178` cells).")

# ---- section 3 (P9, P5, P13(a))
rep("For even `q = 2m` the group is `Sp_{2m}`: simply connected, with `2` as the only bad prime, `X^*(T)/ZR ≅ Z/2`,",
    "For even `q = 2m` the group is `Sp_{2m}`: simply connected, with every odd prime good, `X^*(T)/ZR ≅ Z/2`,")
rep("**Proposition 3.1** (modulo [BRR, Proposition 2.12]; [Kos] in characteristic `0`).", "**Proposition 3.1** (modulo [BRR, Proposition 2.12]).")
rep("[CL] v9 listed this as an open problem. For even `n` it is a consequence of the literature.",
    "In odd characteristic this is [BRR, Proposition 2.12] with Proposition 1.2. In characteristic `0` it is a case of Kostant's theorem; it also follows from the case of one odd prime, because the dimension over `Q` is at most the dimension over `F_p`, and Proposition 4.1(iii) with Theorem 4.2(i) below gives the lower bound. [CL] v9 listed this as an open problem. For even `n` it is a consequence of the literature.")
rep("In `8` cells (`q ∈ {2, 4, 6, 8}`) the dimension, in characteristics `0, 3, 5, 7`, is the number of walks from `0` to `ε_1`, which is the multiplicity of the minuscule weight.",
    "In the cells with odd `n` that we computed — `(q, n) = (2, 3), (2, 5), (2, 7), (4, 3), (4, 5), (6, 3), (6, 5), (8, 3)` in characteristic `0`, and `(2, 5), (4, 3)` in characteristics `3, 5, 7` — the dimension is the number of walks from `0` to `ε_1`, which is the multiplicity of the minuscule weight; the cold reader of this note found the same at `(2, 3), (2, 5), (4, 3), (4, 5), (6, 3)` in characteristics `3, 5, 7` and `1000003`.")

# ---- section 4 (P13(c), P4, P13(d), E3/P7, E1, P10)
rep("The right-hand side of (iii) is `(V^{⊗N})^Z`, by Proposition 1.2 and duality in the Gorenstein ring `C_r`. So the subspace generated by the invariant tensors under the copies of `e` always lies in the invariants of the centralizer.",
    "For `char F ≠ 2` and `F` infinite, the right-hand side of (iii) is the space of invariants `(V^{⊗N})^𝒵`: a vector is invariant iff it is killed by the elements `Π_x f(x) − 1`, `f(e) ∈ 𝒵`, and by Proposition 1.2 these generate the ideal `(e_j : j odd)`. So the subspace generated by the invariant tensors under the copies of `e` always lies in the invariants of the centralizer.")
rep("in characteristic `≠ 2`, `Σ_J D_{q−1,J}C_{q−1} = (V^{⊗N})^Z`, and", "in characteristic `≠ 2`, `Σ_J D_{q−1,J}C_{q−1} = ann_{C_{q−1}}(e_j : j odd)`, which is `(V^{⊗N})^𝒵` when `F` is infinite, and")
rep("This holds over every field of characteristic `≠ 2`, and the generated space has the right dimension over every field, so the lattice it spans over `Z` is saturated.*",
    "This holds, modulo [BRR, Proposition 2.12], over every infinite field of characteristic `≠ 2` (over a finite field, for the centralizer as an algebraic group); and the generated space has the right dimension over every field, so the lattice it spans over the integers is saturated.*")
rep("By [CL, Proposition 2.5], Conjecture 1.2 of Degtyarev–Shimada for the Fermat variety of degree `m = p^v` and dimension `2k` is equivalent to (i) over `F_p` with `q = m`.",
    "By [CL, Proposition 2.5 and Theorem 0], for `k ≥ 1` Conjecture 1.2 of Degtyarev–Shimada for the Fermat variety of degree `p^v` and dimension `2k` is equivalent to (i) over `F_p` with `q = p^v`. For the odd degrees that are not prime powers the algebraic form of the conjecture is Main Theorem′ of [CL], which needs more than Theorem B.")
rep("Let `W = V^{⊗N}` with `N` even.", "Let `W = V^{⊗N}` with `N` even, and let `G` be `SO_r` (odd `r`) or `Sp_r` (even `r`); the centralizer `G^e` is `𝒵` or `{±1} × 𝒵`, and `−1` acts trivially on `W`.")
rep("(For odd `r` the group is `SO_r`; an invariant containing a determinant would leave `N + 2d − r` factors, an odd number, to be paired, so there is none.)",
    "(For odd `r`, `O_r = {±1} × SO_r`, and `−1` acts trivially on this tensor power, whose degree `N + 2d` is even; so the invariants of `SO_r` in it are those of `O_r`.)")

# ---- section 5 (G1, P13(b))
rep("- `≤` holds over every field (the argument of [CL, Proposition 9.1]).",
    "- `≤` holds over every field. In characteristic `≠ 2` it is Proposition 4.1(iii) with Theorem A. In characteristic `2` the two ideals differ (colengths `19` and `21` at `(q, N) = (3, 4)`), and the point-counting argument of [CL, Proposition 9.1] does not apply; but `Σ_J D_{q,J}C_q` is spanned by vectors with integer coordinates, so its dimension over any field is at most its dimension over `Q`.")
rep("In the working notes of the project this was called «the bone», and for several months it was the target, because the project took it to be equivalent to Conjecture 1.2. It is not: the conjecture is the statement at the even box `q − 1` (§4.2).",
    "In the working notes of the project this was called «the bone». For several months the project took the count of Theorem A to be the algebraic form of Conjecture 1.2 ([CL, §1.8]), and the bone was the statement it tried to prove on the way to that count. Neither is the conjecture: the conjecture is the statement at the even box `q − 1` (§4.2).")

# ---- section 7 (P12, P1)
rep("order the possible last steps `c` by `N_{j−1}(p_j − c)`, decreasing, and let `r_j(w)` be the position of the actual step `s_j` in that order, starting from `0`.",
    "order the possible last steps `c` by `N_{j−1}(p_j − c)`, decreasing, with any fixed rule for ties, and let `r_j(w)` be the position of the actual step `s_j` in that order, starting from `0`.")
rep("**Theorem 7.1** (a consequence of [CL, Theorem A, Theorem A.12 and Theorem A.15]). *For odd `q` and `char F ≠ 2`, the Hilbert series of `F[L]/((e_j : j odd) + (x^q))` is `Σ_w t^{stat(w)}`, the sum over the closed walks of length `n`.*",
    "**Theorem 7.1** (a consequence of [CL, Theorem A, Theorem A.12 and Theorem A.15]; see [CL, Corollary A.17]). *For odd `q` and `char F ≠ 2`, the Hilbert series of `F[L]/((e_j : j odd) + (x^q))` is `Σ_w t^{stat(w)}`, the sum over the closed walks of length `n`. The sum does not depend on the rule for ties.*")
i = t.index("*Proof.* In the proof of [CL, Theorem A.15] there is a chain"); j = t.index("- **Explicit order of the steps**")
t = t[:i] + ("*Proof.* For a partition `μ` with at most `m` parts, `N_μ(n)` is the number of walks of length `n` from `0` to the point `Σμ_iε_i`, and the `q` children of `μ` in [CL, Definition A.2] are the shapes of the `q` points from which that point is reached in one step ([CL, Lemma A.3]). "
    "In the proof of [CL, Theorem A.15] there is a chain `dim F[L∪z]/K_μ(L∪z) = Σ_a dim F[L]/R_a ≤ Σ_a dim F[L]/K_{child_a(μ)}(L) ≤ Σ_a N_{child_a(μ)}(n) = N_μ(n+1)`, where `R_a` is the row of index `a` (the coefficient ideal of `z^a`) and `K_{child_a(μ)}(L) ⊆ R_a`. For `μ = ∅` the two ends are equal for every `n`, by Theorem A. So every inequality is an equality: `R_a = K_{child_a(∅)}(L)` and `dim F[L]/K_{child_a(∅)}(L) = N_{child_a(∅)}(n)`, for every `n`. The same argument then applies to each child, again for every `n`, and so on; every `μ` with at most `m` parts is reached. So for every `μ` equality holds and the rows are the ideals of the children; this is [CL, Corollary A.17]. "
    "The ideals are homogeneous, so `HS(F[L∪z]/K_μ(L∪z)) = Σ_a t^a·HS(F[L]/R_a)`. Rows are nested, `R_0 ⊆ R_1 ⊆ ⋯`, so the numbers `N_{child_a(μ)}(n)` do not increase with `a`, and two rows with the same number are equal ideals. Hence the row of index `a` belongs to a step of rank `a` in the definition, whatever the rule for ties. Induct on `n`. ∎\n\n") + t[j:]
rep("- **Explicit order of the steps** (equal to the definition in `3 605` profiles):", "- **Explicit order of the steps** (it is the order of [CL, Definition A.2], so it is proved by the argument above; it was also compared with the definition in `3 605` profiles):")

# ---- table (E3, P1)
rep("| an elementary proof of Theorem A, with the ideals `K_μ` | this project ([CL, Appendix A]) | proved |",
    "| an elementary proof of Theorem A, with ideals `K_μ` of colength `N_μ(n)` for every weight `μ` | this project ([CL, Appendix A]) | proved |")
rep("| **Theorem B / Conjecture 1.2 of [DS] for odd degree** | **this project ([CL])** | **proved; Lean-checked in its algebraic form** |",
    "| **Theorem B (every field, every odd `q`); Conjecture 1.2 of [DS] for every odd degree** | **this project ([CL])** | **Theorem B and Main Theorem′ proved and Lean-checked; the conjecture proved modulo Pham's theorem and [DS, Theorem 2.2]** |")

# ---- sections 9 and 10, references (P11)
rep("[BRR] §2.2–§2.6 (in particular Propositions 2.2 and 2.12, Lemmas 2.7, 2.8 and 2.13) and the introduction;", "[BRR] §2.1–§2.6 (in particular Propositions 2.2 and 2.12, Lemmas 2.7, 2.8 and 2.13) and the introduction;")
rep("to positive characteristic and to integral coefficients. It does not contain the count.", "to positive characteristic and to integral coefficients. We did not find the count in it (we read its introduction and §2.2, and searched its source).")
rep("- **This note has not been refereed.** It was read cold by an AI system (see [CL, §12.6]).",
    "- **This note has not been refereed.** It was read cold on 1 October 2026, together with the new material of [CL] v10, by a separate instance of the AI system used in this project, working alone and with its own code. Its verdict was «holds», with one gap (the inequality of §5 in characteristic `2`), three errors (a false sentence in the sketch of §4.3, the hypothesis of [Gin, Proposition 4.2], and the row of Theorem B in the table of §8) and thirteen points of presentation, among them the remark (3) after Proposition 1.2 and the equality for every `μ` of §2.3(c). All are incorporated, with the texts and the arguments that the reader proposed. See [CL, §12.6].")
rep("| no odd torsion in `Z[L]/((e_odd) + (x^q))` |", "| no odd torsion in `Z[L]/((e_j : j odd) + (x^q))` |")
rep("- The dictionary: `(e_odd) + box = (p_odd) + box` in characteristic `0` at `6` cells; the coefficients of `E(t)/E(−t) − 1` generate `(e_odd)` in characteristics `3, 5, 7` at `5` cells.",
    "- The dictionary: `(e_j : j odd) + box = (p_j : j odd) + box` in characteristic `0` at `6` cells; the coefficients of `E(t)/E(−t) − 1` generate `(e_j : j odd)` in characteristics `3, 5, 7` at `5` cells. The coinvariants of the points of `𝒵` over `F_3` and `F_5` at `5` cells (remark (3) of §1), by the cold reader and again by the author with separate code.")
rep("*Modular affine Hecke category and regular unipotent centralizer, I*, arXiv:2005.05583 (v2, 4 July 2024).", "*Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583 (v2, 4 July 2024).")
rep("arXiv:math/9803141.", "arXiv:math/9803141 (v2).")
rep("arXiv:1411.3112.", "arXiv:1411.3112 (v4, 19 May 2015).")

left = [t[max(0, m.start()-40):m.end()+25].replace('\n', ' ') for m in re.finditer(r'`Z`|\^Z\b|∈ Z\b|× Z\b|_Z`', t)]
for s in left: print('  Z kept (integers):', s)
assert len(left) == 2 and 'ring of integers' in left[0] and 'semicontinuity over' in left[1], left
assert 'has not been read' not in t and 'PLACEHOLDER' not in t and '_odd' not in t
open(OUT, 'w', encoding='utf-8').write(t)
print('note written', len(t), 'chars;', t.count('\n'), 'lines')
