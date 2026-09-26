> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE PATTERN FLOOR THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_PATTERN_FLOOR_THEOREM.md
>
> **Status, as written in the document:** Status: pencil-proven; every load-bearing number verified byte-exact (exact rational arithmetic, files named, probes attached). Pending the project P0 cold gate (Ley 45).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE PATTERN FLOOR THEOREM
## The bite pattern of a covector determines its W-projection; the price of coverage is a pseudoinverse quadratic form of the chorus-blind Gram, with an exact continuous determinant floor per pattern

**A King Pin structural theorem, built on pillars Star (i), Steel (ii), Spectrum (iv), Coverage⊥Correlation (vi) and on the Graft-Factoring Theorem (v111). It replaces the per-row CVP refinement of v112 with the correct object — a determinant floor over the pattern lattice — and buries the coset-CVP lane with a number.**

**Status: pencil-proven; every load-bearing number verified byte-exact (exact rational arithmetic, files named, probes attached). Pending the project P0 cold gate (Ley 45).**

---

### 0. Why this theorem (Quanta paragraph)
v112 left one "pending refinement": exact CVP in the rank-48 coset `f + K`, `K = ker(M_W)`, to shave the `2^{20.7}` cost of the wall-annihilating cuts. But CVP minimizes the **dual norm per row**, while the price is a **determinant** — the same trace-vs-determinant confusion that v62 killed and v111 re-killed, reincarnated one level down. This theorem shows the refinement is unnecessary and misdirected: because the pairing matrix has full rank on `W`, the bite pattern of a covector *determines* its `W`-component exactly, and the minimum of the joint determinant over the coset is achieved *continuously* by the `D`-orthogonal projection — a closed-form rational number per pattern, no CVP needed. The governing metric turns out to be the pseudoinverse of the Gram matrix of the 162 chorus-blind squirrels themselves: the squirrels price their own coverage. As a corollary the v112 annihilating patterns carry a continuous floor of `2^{13.61}` (in dnorm² units) for their two covering rows alone, against a *total* cut budget of `2^{8.08}`: the coset-CVP lane is dead with a number. The live object it leaves behind is a new, well-posed invariant — the **Pattern Number** of the chorus-blind residual.

### 1. Setting (all objects byte-exact from files)
Canonical frame `L0sat` (`gram_L0sat_141_v1.txt`, `G`, `det = 2^{128}`), dual Gram `D = 32·G^{-1}` (`dualgram_L0sat_xD.txt`, integer). Reference cut `best_cut` (`gabrieloak_best_cut_v1.txt`), price `2^{7.906891}` (re-verified). Wall = the 1935 norm-12 residual squirrels (`pitbull_TRUE_RESIDUAL_1935_v1`); survivors of `best_cut`: 913; chorus-blind survivors of type `(8,4,0,0)`: exactly **162** (re-verified). Let `M_W ∈ ℤ^{162×141}` be their matrix; `rank M_W = 93` (re-verified), `K = ker(M_W) ∩ ℤ^{141}`, rank 48. The **pattern** of a covector `f ∈ ℤ^{141}` is `p(f) = M_W f ∈ ℤ^{162}`; its support is the set of bitten squirrels. The **pattern lattice** is `Λ_W = M_W(ℤ^{141}) ⊂ ℤ^{162}`, free of rank 93.

Define
> **`H := M_W · (G/32) · M_W^T ∈ (1/32)·ℤ^{162×162}`** — one thirty-second of the Gram matrix, in `G`, of the 162 chorus-blind squirrels. `rank H = 93` (verified); `diag H = 3/8` (each squirrel has `G`-norm 12).

### 2. The three propositions

> **Proposition 1 (Injectivity — the pattern is the projection).** Since `rank M_W = 93 = dim W`, the map `W → ℝ^{162}` induced by `M_W` is injective. Hence the pattern `p(f)` determines the `D`-orthogonal projection `π_W f` of `f` onto `span(K)^{⊥_D}` uniquely. Two covectors have the same pattern iff they lie in the same coset `f + span(K)`.
> *Proof.* `p(f) = p(f′)` ⟺ `f−f′ ∈ ker M_W = span(K)`; and `π_W` is constant exactly on those cosets. Injectivity on `W` is `rank M_W = dim W`. ∎

> **Proposition 2 (The metric identity).** For every covector `f` with pattern `p = M_W f`:
> **`dnorm²(π_W f) = p^T H^+ p / 32`,**
> where `H^+` is the Moore–Penrose pseudoinverse (`p ∈ range(H)` always, so any solution `x` of `Hx = p` gives the value `p^T x / 32`). In particular the *continuous* minimum of `dnorm²` over the coset `f + span(K)` equals `p^T H^+ p / 32`, attained at `π_W f`, and every integer representative satisfies `dnorm²(f) ≥ p^T H^+ p / 32`.
> *Proof.* `span(K)^{⊥_D} = D^{-1}·rowspace(M_W)`, so `π_W f = D^{-1} M_W^T α` with `(M_W D^{-1} M_W^T) α = p`; then `‖π_W f‖²_D = α^T (M_W D^{-1} M_W^T) α = p^T (M_W D^{-1} M_W^T)^+ p`. Since `D^{-1} = G/32`, the operator is `M_W (G/32) M_W^T = H`, and `dnorm² = ‖·‖²_D/32`. ∎
> *Verification gate:* for the LLL dual-basis vector `basis[116]` (dnorm² = 2, bites 10/162): `p^T H^+ p = 408339010/206619023 = 63.2413…`, giving `63.2413/32 = 1.976290` — byte-exact equal to the directly computed projection norm (`pattern_metric_identity_probe_v1.py`).

> **Proposition 3 (The determinant floor — volume shrink).** Let `Φ` be any 13-cut and `r_1,…,r_k` any subset of its rows with patterns `p_1,…,p_k`. Then, with `N(p_a,p_b) := p_a^T H^+ p_b / 32` the pattern Gram:
> **`det(Φ D Φ^T)/32^{13} ≥ det( N(p_a,p_b) )_{a,b=1..k} · det_{⊥}(rest)/32^{13-k} ≥ det( N(p_a,p_b) )_{a,b=1..k} · μ_{13-k}`,**
> where the first inequality is the Gram–Schmidt factorization (order the `k` rows first) combined with the fact that `D`-orthogonal projection cannot increase the volume of a parallelepiped, and `μ_{13-k} > 0` is the (currently unproven-in-general, see §5) floor of the complementary block. In particular, for **any** cut two of whose rows carry a covering pair of patterns `(p_a, p_b)`:
> `pr(Φ) ≥ [N(p_a)N(p_b) − N(p_a,p_b)²] · μ_{11}` — the bracketed quantity is the **continuous pair floor**, exact and rational per pattern pair, independent of which integer representatives realize the patterns. ∎

### 3. The theorem

> **Theorem (Pattern Floor).**
> **(i)** The price contribution of coverage is governed entirely by the pattern lattice `Λ_W` (rank 93) equipped with the exact rational quadratic form `N(p) = p^T H^+ p / 32`, `H` = (Gram of the 162 chorus-blind in `G`)/32. Covering the 162 with `k ≤ 13` rows means choosing `p_1,…,p_k ∈ Λ_W` whose supports jointly equal all of `{1..162}`; the coverage block of the price obeys the exact continuous floor `det(N(p_a,p_b))_{k×k}` of Proposition 3, with equality in the continuous relaxation (rows = projections).
> **(ii) [support floor]** For any pattern `p` with support `S`: `N(p) ≥ p_S^T (H_{SS})^{-1} p_S ≥ |S| / (32·λ_max(H))`, where `λ_max(H) ≤ 5` rigorously (Gershgorin, exact integer row sums of `32H`) and `λ_max(H) = 2.35784…` measured. Coverage and cheapness are anticorrelated *inside the metric itself* — Coverage⊥Correlation (pillar vi) is now a property of one quadratic form.
> **(iii) [spectral unification]** `λ_max(H) = λ_max(D^{-1}Q)`, `Q = M_W^T M_W` — the Mordida-Norma constant of v112 (`Λ′ = 32·λ_max = 75.45`) and the Pattern-Floor metric share their full nonzero spectrum (the operators `AB` and `BA` with `A = M_W D^{-1/2}`-type factorizations have identical nonzero eigenvalues). The v112 trace bound (how many a covector *can bite*) and the present determinant floor (what coverage *must cost*) are the two faces of one operator: the chorus-blind Gram.
> *Proof.* (i) is Propositions 1–3. (ii): restriction of a PSD dual form to a coordinate subset dominates the sub-form (`p^T H^+ p ≥ p_S^T (H_{SS})^{-1} p_S` for `p ∈ range(H)`, Schur-complement monotonicity); then integrality (`|p_t| ≥ 1` on `S`) and `x^T (H_{SS})^{-1} x ≥ |x|²/λ_max(H_{SS}) ≥ |S|/λ_max(H)` (eigenvalue interlacing). Gershgorin bound from exact integer row sums of `32H = M_W G M_W^T`: max row sum `160`, so `λ_max ≤ 160/32 = 5`. (iii): `H = (M_W G^{1/2}/√32)(G^{1/2} M_W^T/√32)` and `D^{-1}Q = (G/32)(M_W^T M_W)`; both are products `AB`, `BA` of the same pair up to conjugation, hence equal nonzero spectra. ∎

### 4. Corollaries (all measured byte-exact)

> **Corollary 1 (the coset-CVP lane is dead — a burial with a number).** The v112 "pending refinement" (exact CVP in the rank-48 coset for the constructed covering pairs) cannot help. The continuous floors of those pattern pairs are, exactly:
> pair (1×6, 2×4): `det₂ floor = 12481.1497 = 2^{13.6075}`; pair (1×6, 3×3): `2^{14.1526}`; pair (3×6, 5×4): `2^{13.9305}`; pair (1×6, 4×4): `2^{15.8524}` — in dnorm² units, i.e. the units in which the **total** 13-row budget is `2^{8.08}`. Individual coverer floors: support 152 → `N = 286.91`; support 141 → `N = 43.58`. Any integer CVP representative sits **above** these floors; Babai's `2^{20.7}` was ~7 bits of integrality + complement, not slack CVP can recover. The lane is closed by its own continuous relaxation.

> **Corollary 2 (short ⟺ narrow, measured inside Λ_W).** LLL-reducing `Λ_W` in the exact `N`-metric (93-dim, denominators cleared): the shortest patterns have norms `0.4656, 0.5457, 0.5515, …` and supports `5, 3, 6, 7, 6, 17, 8, 12, …` out of 162. Cheap patterns are support-starved; wide patterns are expensive (support-152 coverer: `N = 286.9`). No covering pair exists among the reduced basis and its small combinations (473 candidates, zero covering pairs).

> **Corollary 3 (the Pattern Number — the new well-posed invariant).** Define
> **`PN(k) := min { det(N(p_a,p_b))_{k×k} : p_1..p_k ∈ Λ_W, supports cover {1..162} }`.**
> The record's coverage face is blocked at the continuous level iff `PN(k)·μ_{13-k} ≥ 2^{8.08}` for every `k ≤ 13`. `PN` lives in one fixed 93-dimensional lattice with one exact rational metric — a finite, sharply-posed minimization, strictly finer than every prior formulation (product seal, greedy pools, per-row CVP). Current measured upper bound: `PN(2) ≤ 2^{13.6075}`. Lower bounds for `PN(2)` from (ii): a covering pair has one support `≥ 81`, so one factor `≥ 81/(32·λ_max)` — `≥ 0.506` rigorous, `≥ 1.073` at measured `λ_max`; a full lower bound for the *determinant* (not the norms) is the open work.

### 5. Scope, and what stays open (stated straight)
- No claim about the section **minimum** is made anywhere; everything lives on the price/coverage (BOX) face. Remark 5.3′ untouched.
- The complement floor `μ_{11}` (the 11 non-covering rows, projected `D`-orthogonally to the coverers) has **no proven positive lower bound yet**; Corollary 1 kills the CVP lane and the constructed patterns because their pair floor alone exceeds the *total* budget by ≥ 5.5 bits, but a formal seal of the whole coverage face requires bounding `PN(k)` below over all of `Λ_W` — the live pencil lane this theorem opens.
- The v112 coverage results remain correct as stated (covering number = 2 as an existence statement; annihilating cuts at `2^{20.7}` as measured objects). What dies is the *refinement lane*, not the measurements.

### 6. Verification record
`pattern_metric_identity_probe_v1.py` (metric identity gate on basis[116], byte-exact); `pattern_floor_probe_v1.py` (continuous pair floors, exact rational determinants); `pattern_lattice_v1.py` (Λ_W basis by HNF: 93 rows; exact Gram in `N`-metric, LLL, supports; gate: basis[116] pattern norm `408339010/206619023`). Frames: `gram_L0sat_141_v1.txt`, `dualgram_L0sat_xD.txt`, `dump_planes_L0sat_960x141_v1.txt`, `pitbull_TRUE_RESIDUAL_1935_v1.txt`, `gabrieloak_best_cut_v1.txt`. Re-verified gates this session: price `2^{7.906891}`, survivors `913/1935`, chorus-blind `162`, `rank M_W = 93`, `rank K = 48`, basis[116] `dnorm² = 2` biting `10/162`.

### 7. Ley 41 certificate
Object: *the exact continuous determinant floor of a bite pattern, given by the pseudoinverse quadratic form of the chorus-blind Gram on the pattern lattice `Λ_W`, and the minimization of coverage cost over patterns (not coset representatives).* Graveyard grep by object: (a) **product seal `2^{18.20}`** (v110) — distinct: that was an AM–GM product heuristic with no lower-bound status; this is a legitimate determinant lower bound via projection volume shrink; (b) **coset reduction / CVP** (v112) — distinct and *buried here*: that lane fixes the pattern and minimizes per-row dual norm (a trace-type objective); this varies the pattern and bounds the joint determinant — buried with `2^{13.6075}`; (c) **Ley Mordida-Norma** (v112) — complementary, now unified: same operator, trace face vs determinant face (Theorem (iii)); (d) **detector cover `2^{25.76}`** — distinct: blind pool search, no floor structure. No collision. Pending P0.

---
*Part of the Operación Glotón / King Pin corpus · github.com/tretoef-estrella · tretoef@gmail.com — Marlowe (Auditor), 10 July 2026.*
