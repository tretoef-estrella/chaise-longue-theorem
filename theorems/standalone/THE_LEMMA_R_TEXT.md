> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Hodge–Fermat campaign* · 2026-06-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *LEMMA R — THE TEXT* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_LEMMA_R_TEXT.md
>
> **Status, as written in the document:** Throughout, m ≥ 5 is an odd prime (the case m = 3 is covered separately in the skeleton's scope line). A = ⊕_{j=1,2,3} Z^{(Z/m)²} is the free module on the three line families, points of each family indexed by (k, l) ∈ (Z/m)². G is the intersection Gram on A, …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# LEMMA R — THE TEXT
### Constructor → Auditor · 4 June 2026 (night) · Prose, not routes
### Companion instrument: BETA1_DISPLAY_PROBE_v1.py (all displayed identities verified entrywise, every t and c, m = 5 and 7: PASS; the three pure generators integral and in K: PASS 3/3 both primes)

Throughout, m ≥ 5 is an odd prime (the case m = 3 is covered separately in the skeleton's scope line). A = ⊕_{j=1,2,3} Z^{(Z/m)²} is the free module on the three line families, points of each family indexed by (k, l) ∈ (Z/m)². G is the intersection Gram on A, K = ker(G) (saturated, rank 9m − 7). For t ∈ Z/m write x_t(k,l) = k + t·l, and x_∞(k,l) = l; the m + 1 **pencils** of a family are the level-set partitions of these forms (t = 0 and t = ∞ are the two **axis** pencils; the others are **live**). For a pencil L, the **fiber-sum operator** E_L : Z^{m²} → Z^{m²} is (E_L u)(p) = Σ_{p′ : x_L(p′) = x_L(p)} u(p′); equivalently E_L u = pb_L(f_{L,u}) where f_{L,u} ∈ Z^m is the vector of fiber sums and pb_L denotes pullback along x_L. Z₀ ⊂ Z^m is the sum-zero sublattice. SAT ⊂ K is the explicit lattice: the six axis blocks pb_{j,axis}(Z₀); the three paired overlap blocks {pb_j(y) + pb_{j′}(y∘τ_{s₀}) : y ∈ Z₀} (τ = cyclic translation; s₀ = 0 for the pairs 12, 23 and s₀ = 1 for 13, in the session's coordinates); and the trivial relations N₁ − N₂, N₂ − N₃ (N_j = all-ones of family j). Membership SAT ⊂ K and rank 38 = 9m − 7 are file-verified (GRANSLAP_PROBE_v2, LEMAR_SHAKE_PROBE_v1). aug(u) = Σ_p u(p).

---

## Lemma R.1 (incidence identity). On each family, Σ_{L over the m+1 pencils} E_L = m·I + J, where J is the all-ones operator.

**Proof.** Evaluate at a point p: (Σ_L E_L u)(p) = Σ_{p′} u(p′) · #{L : x_L(p′) = x_L(p)}. If p′ = p the count is m + 1 (one fiber through p per pencil). If p′ ≠ p, then x_L(p′) = x_L(p) iff the difference p′ − p lies in the kernel line of x_L; a nonzero vector of (Z/m)² lies in exactly one of the m + 1 directions, so the count is 1. Hence the sum equals (m+1)u(p) + Σ_{p′≠p} u(p′) = m·u(p) + (Ju)(p). ∎

## Lemma R.2 (augmentation divisibility). For every x = (x₁, x₂, x₃) ∈ K and every j: m | aug(x_j). Moreover aug(x₁) + aug(x₂) + aug(x₃) = 0 exactly.

**Proof.** We display four identities in A; each is proved by direct incidence counting and each is verified entrywise for every parameter value at m = 5 and 7 in the companion probe.

**(i) G·N_j = m·1_A.** For p′ in family j: the diagonal contributes 2 − m, and p′ meets the m − 1 lines sharing its k and the m − 1 sharing its l, total (2−m) + 2(m−1) = m. For p′ in another family, the incidence condition with family j is a single nondegenerate linear constraint on (k,l), with exactly m solutions. Pairing with x ∈ K: 0 = N_jᵀ G x = m·1_Aᵀx gives **aug(x₁) + aug(x₂) + aug(x₃) = 0** exactly.

For (ii)–(iv), let y = y_{t,c} be the indicator of the family-1 fiber {k + t·l ≡ c}, t ≠ 0. Within family 1: if p′ lies on the fiber, the fiber point sharing its k and the one sharing its l are both p′ itself (for t ≠ 0 the fiber is a graph over k and over l), so the value is 2 − m; if p′ is off the fiber, it shares k with exactly one fiber point and l with exactly one, and these are distinct (a common one would equal p′), value 2. Hence (Gy)|₁ = 2·1₁ − m·y always. Across families: the family-2 condition is k − l ≡ d′; on the fiber, k − l = c − (t+1)l, which is a bijection in l when t ≠ −1 (one fiber point per d′) and is constant ≡ c when t = −1. The family-3 condition is d′ ≡ k + l + 1; on the fiber, k + l = c + (1−t)l, a bijection when t ≠ 1 and constant ≡ c when t = 1. Therefore:

**(ii) t ∉ {0, 1, −1}:** G·y = 2·1₁ + 1₂ + 1₃ − m·y. (Such t exists since m ≥ 5.)
**(iii) t = 1:** G·y = 2·1₁ + 1₂ + m·z₃ − m·y, with z₃ the family-3 fiber indicator {k − l ≡ c + 1}.
**(iv) t = −1:** G·y = 2·1₁ + m·z₂ + 1₃ − m·y, with z₂ the family-2 fiber indicator {k − l ≡ c}.

(For completeness, t = 0 gives G·y = 1_A and carries no new information.) Pairing each with x ∈ K and writing a_j = aug(x_j), the terms m·z and m·y vanish mod m and we obtain, mod m: (ii) 2a₁ + a₂ + a₃ ≡ 0; (iii) 2a₁ + a₂ ≡ 0; (iv) 2a₁ + a₃ ≡ 0. Subtracting (iii) from (ii): a₃ ≡ 0. Subtracting (iv) from (ii): a₂ ≡ 0. Then (iii) gives 2a₁ ≡ 0, and m odd forces a₁ ≡ 0. ∎

## Lemma R.3 (overlap assembly at function level). Let x ∈ K, let (L in family j) ↔ (L′ in family j′) be one of the three overlap pairs with shift s₀, and let f̃_{j,L} ∈ Z^m denote the sum-zero part of the fiber-sum vector of x_j along L (integer by R.2, since the mean is aug(x_j)/m). Then f̃_{j′,L′} = f̃_{j,L} ∘ τ_{s₀}, and consequently pb_j(f̃_{j,L}) + pb_{j′}(f̃_{j′,L′}) lies in the paired overlap block of SAT.

**Proof.** Decompose x_j ⊗ Q into its trivial part and its L-isotypic parts over the m + 1 pencils. For pencils L″ ≠ L, the map p ↦ (x_L(p), x_{L″}(p)) is a bijection of (Z/m)², so each L-fiber meets each L″-fiber exactly once; the L-fiber sums of an L″-isotypic component pb_{L″}(h) (h sum-zero) are therefore Σ_v h(v) = 0. The trivial component contributes only to the mean. Hence f̃_{j,L} = m·g, where pb_L(g) is the L-isotypic component of x_j ⊗ Q. By the kernel character census (Lemma P, Corollary 5), the only live pencils on which a kernel vector has nonzero isotypic mass are the overlap pencils, and on an overlap Γ-character the component of x lies in the one-dimensional null direction of the ratified phase law P3′: the Fourier coefficients on the line satisfy ĝ′(a) = ζ^{a·s₀}·ĝ(a) for every character a of the line. Over Z/m, multiplying the a-th Fourier coefficient by ζ^{a·s₀} for all a is precisely translation by s₀; hence g′ = g ∘ τ_{s₀} and f̃_{j′,L′} = m·g′ = f̃_{j,L} ∘ τ_{s₀}. Since f̃_{j,L} ∈ Z₀ (integer fiber sums minus integer mean), the displayed sum is the paired-block member with y = f̃_{j,L}. ∎

## Theorem R.4 (mK ⊆ SAT). For every x ∈ K: m·x ∈ SAT.

**Proof.** Fix x ∈ K and apply R.1 to each component: m·x_j = Σ_L E_L x_j − J x_j = Σ_L pb_{j,L}(f_{j,L}) − aug(x_j)·1_j. Write each fiber-sum vector as f_{j,L} = f̃_{j,L} + (aug(x_j)/m)·1, with integer mean by R.2 and f̃_{j,L} ∈ Z₀. Substituting, the m + 1 means contribute (m+1)(aug(x_j)/m)·1_j, so

m·x_j = Σ_L pb_{j,L}(f̃_{j,L}) + (aug(x_j)/m)·1_j.

Classify the pencil terms. **Axis pencils:** pb(f̃) ∈ pb_{j,axis}(Z₀) ⊂ SAT. **Live non-overlap pencils:** by the census step inside R.3's proof, f̃_{j,L} = m·g with pb(g) the L-isotypic component of x_j, which is zero for a kernel vector on a non-overlap live pencil; hence f̃ = 0. **Overlap pencils:** summing over the three components of m·x, the six overlap terms group into the three pairs of R.3, each pair equal to a paired-block member of SAT. **Constants:** the leftover Σ_j (aug(x_j)/m)·1_j has integer coefficients summing to zero (R.2), hence equals (aug(x₁)/m)(N₁ − N₃) + (aug(x₂)/m)(N₂ − N₃) ∈ SAT. All terms lie in SAT. ∎

## Corollary R.5. K/SAT is an elementary abelian m-group; in particular [K : SAT] = m^d with d = dim_{F_m} K/SAT = 38 − rank_{F_m}(SAT mod m), and the index has no part at any prime p ≠ m.

**Proof.** R.4 says the finite group K/SAT is annihilated by m. Elementary abelian of exponent m; all p ≠ m parts vanish. The dimension formula: x ↦ m·x identifies K/SAT with the kernel of the reduction SAT/mSAT → A/mA, of dimension 38 − rank_{F_m}(SAT mod m). ∎

*(This kills, as a proof, the entire p ≠ m question that the disc bookkeeping left open: the index is a pure m-power because it is killed by m, not because we measured it so.)*

## The three pure generators (the proven part of the lower bound). For each family j, let y* = 1 − m·e_{m−1} ∈ Z₀ and g_j := ( pb_{j,(1,0)}(y*) − pb_{j,(0,1)}(y*) ) / m. Then g_j ∈ K, and the classes of g₁, g₂, g₃ are F_m-independent in K/SAT.

**Proof.** Entrywise, pb(y*)(p) = 1 − m·[x(p) = m−1], so pb_a(y*) − pb_b(y*) = m·([x_b(p) = m−1] − [x_a(p) = m−1]) entrywise, visibly divisible by m. The numerator is a difference of two axis-block members of SAT ⊂ K, so g_j ∈ (1/m)·K ∩ A; since K is saturated and g_j ∈ Q·K ∩ A, g_j ∈ K. (File verification: integral and G·g_j = 0, 3/3 both primes.) Independence: the SAT-coordinates of g_j are (1/m)(axis combination of family j); the three classes live on disjoint family supports and each is nonzero mod m (the combination pb_a(y*) − pb_b(y*) is not in m·SAT: its axis coordinates are the unit vectors of y*). ∎

---

## The exact final position

With R.4 proven, with the blockwise saturation [SAT : K₀] = m^{9(m−2)} proven, and with the big determinant of §17 proven exactly equal to m^{(9m²−3m−6)/2}, the assembly identity of §18 reads:

> **unified index = m^{(9m²−21m+28)/2 − d}, and THE WATERMARK THEOREM (odd half) ⟺ d = 12.**

The constant d is measured 2/2 (d = 12 at m = 5 and 7, full anatomy, elementary), bounded below by 3 tonight with written proof, and the remaining pencil work is now confined to a single F_m-dimension count, in two halves: **(lower, d ≥ 12)** the nine remaining generators — the affine construction y_lin = X − ((m−1)/2)·1 ∈ Z₀ makes pb_L(y_lin) congruent mod m to an affine function of (k,l), i.e. to an axis-plus-constant combination, producing the family-pair and global generators whose measured mod-m coordinates at m = 5 are the template; **(upper, d ≤ 12)** rank_{F_m}(SAT mod m) ≥ 26, by a structured 26-minor that is a unit mod m, using the disjoint-support decomposition (relations are per family, coupled only through the shared coefficients of overlap columns). Both halves are finite, structured, and aimed at a target that can no longer move.

PMC.
