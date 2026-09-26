> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026-06-16
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE STAR THEOREM (v2, hardened)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_STAR_THEOREM.md
>
> **Status, as written in the document:** Status of this revision. Every numeric claim below is re-verified byte-exact from the project frame files by the auditing engine `audit_star_numbers_v1.py` (companion). The dichotomy (two faces), the block-scalar covariance (Theorem 3.2) and the forced-overlap…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE STAR THEOREM (v2, hardened)
### A two-faced reading of the primitive Fermat lattice V(4,4)-prim, and an honestly-demarcated criterion for the King Pin section

**Operación Glotón / King Pin**
Architect: Rafael Amichis Luengo · Auditor Jefe (this revision): El Tunelero · building on the draft of Auditor Vitor (16 June 2026)
16 June 2026

> **Status of this revision.** Every numeric claim below is re-verified byte-exact from the project frame files by the auditing engine `audit_star_numbers_v1.py` (companion). The dichotomy (two faces), the block-scalar covariance (Theorem 3.2) and the forced-overlap lemma (Proposition 4.2) are **proved**. Three claims of the prior draft are **corrected** (logged in §7, Graveyard). The central criterion (§5) is a **program with one open conjecture**, and — corrected from the prior draft — it finitizes the *price* but **not** the *minimum*; the minimum is archimedean and is the true open core. Nothing here claims the record.

---

## Abstract

Let Λ = V(4,4)-prim be the primitive cohomology lattice of the degree-four Fermat fourfold: positive-definite, even, rank 141, det 2^128. The **King Pin problem** asks whether Λ has a rank-128 primitive sublattice ("section") S with min(S) ≥ 24 and price pr(S) = det(S)/2^128 < 2^8.08; a positive answer gives a dimension-128 packing of centre density δ ≥ 2^98.44, beating the Mordell–Weil record of Elkies (2^97.40, unbeaten since 2001).

We prove a **structural dichotomy**. Every *lattice-theoretic* invariant of Λ is supported at the prime 2 (Theorem 2.1, the **arithmetic face**), while the geometry of its minimal vectors is governed by S₆ acting on K₆ (Theorem 3.2, the **geometric face**), and the two faces are not separate theories but two readings of one object.

We then make the meeting precise — **and here we correct the prior draft**. The two faces do **not** compute one shared invariant; they impose **two independent constraints on one shared object**, the cut Φ: the arithmetic face bounds its *price determinant* (a 2-adic quantity), the geometric face bounds the *minimum and isotypic position* of its kernel (an archimedean-plus-representation quantity). A King Pin section is the joint feasibility of the two constraints. This is the exact content of the Architect's stellar analogy — a star is the balance of **two** opposing forces, not the value of one quantity.

We formulate the **Star Criterion** (Program 5.3) and isolate the single open proposition (5.4) that would close it. We are explicit about a limit the prior draft obscured: the criterion finitizes the *price* side (2-adic Smith data), but the *minimum* side (min ≥ 24, an archimedean short-vector condition) is **not** reducible to 2-adic or representation-theoretic data, and remains the intractable core. We close with the one route that side-steps it: the **MW128-embedding test** (§5.4), which imports a known minimum rather than searching for one.

---

## 1. The object and the problem

Fix Λ = V(4,4)-prim, the primitive part H⁴_prim(X,Z) of the middle cohomology of X = {x₀⁴+···+x₅⁴=0} ⊂ P⁵, with the suitably normalized intersection form. As an abstract lattice Λ is positive-definite, even, rank 141, with

> det Λ = 2^128 (1)

a value of the Watermark/Double-Ladder lineage, **verified byte-exact** in the saturated integral frame G = gram_L0sat (det G = 2^128 = 340282366920938463463374607431768211456).

A **section** is a primitive S ⊆ Λ of rank 128. Its **minimum** min(S) = min_{0≠v∈S} ⟨v,v⟩_G and its **price** pr(S) = det(S)/2^128 obey

> log₂ δ(S) = 64·log₂(min(S)/4) − 64 − ½·log₂ pr(S), (2)

so min(S) ≥ 24 with pr(S) < 2^8.08 yields δ ≥ 2^98.44.

**Definition 1.1 (King Pin section).** A rank-128 primitive S ⊆ Λ with min(S) ≥ 24 and pr(S) < 2^8.08.

The two constraints **oppose**: the price pulls S together (compactness), the minimum pushes its vectors apart (no short vector). A King Pin section is their equilibrium — the Architect's *star*: outward pressure (the minimum barrier) against inward gravitation (the price). The analogy is exact in the variational statement and **breaks at integrality** (§5.1); the place it breaks is the mathematical content.

### 1.1 What is proved, and what is not

- **(A) The arithmetic face is 2-adic (Theorem 2.1).** det, dual ladder, deep block scale, section rank: all powers of 2, no odd prime. *Proved.*
- **(B) The geometric face is S₆-combinatorial (Theorem 3.2).** The kissing covariance **operator** is block-scalar on four S₆-isotypic blocks of dimensions (90, 30, 20, 1); the eigenvalues carry the odd primes 3, 5, 7 of K₆. *Proved, byte-exact.*
- **(C) The two faces meet at the cut Φ — as two independent constraints, not one invariant (§4, corrected).** A King Pin section is the joint feasibility of a 2-adic price bound and an archimedean minimum bound on one Φ. *The reduction of the price side to finite Smith data is plausible (Program 5.3); the minimum side does not so reduce (Remark 5.3'); the joint link is the open Proposition 5.4.*

The value of the dichotomy is methodological: the campaign's eight theorems split, without exception, onto one of the two faces (§6); the long-open **Bridge** is not a missing transfer between faces but the (still open) question of whether the two constraints on Φ are jointly satisfiable.

---

## 2. The arithmetic face

G ∈ Sym₁₄₁(Z), G ≻ 0, even, det G = 2^128. Write L₂ = Λ ⊗ Z₂.

**Theorem 2.1 (pure 2-adicity).** In each item the prime 2 is the only prime that occurs.

- **(i) Determinant.** det Λ = 2^128; no odd prime divides it.
- **(ii) Dual ladder.** den(G⁻¹) = 2^5 (32·G⁻¹ integral, 5 least). On the cheap dual spectrum {c : cᵀG⁻¹c ≤ 3} the squared dual-norm denominators are exactly {2^0, 2^1, 2^4}; no odd prime occurs.
- **(iii) Jordan scales — corrected.** The **deepest non-unimodular Jordan block of L₂ sits at scale 2^5** (= the saturation scale = den(G⁻¹), Steel Lemma A–B). The value **2^4 is the cheap-spectrum ladder cap (the Wild Tooth fold depth)** — a property of the cheap dual functionals, **not** the deepest block. The **unit-scale (scale-0) multiplicity is r₀ = rank_F2(G) = 98**; the **non-unit dimensions total 43** (= corank_F2 G), distributed over scales 1…5 with Σ_{k≥1} k·r_k = 128. *Only r₀ = 98 and the top scale 5 are pinned by current results; the full Jordan profile (the middle multiplicities r₁…r₄) is the explicit decomposition Steel flagged as the next deliverable and is **not yet established.***
- **(iv) Section dimension.** 128 = 2^7 (codim 13); 141 = 3·47. The section rank is a pure 2-power; the descent of §5 operates on it.

*Proof.* (i) is (1). (ii) is the Steel Theorem, read byte-exact from the dual Gram and the cheap pool. (iii): Steel Lemma A pins den(G⁻¹) as 2^(top non-unimodular scale); den = 2^5 ⟹ deepest block at 2^5. The cheap cap 2^4 is Steel Lemma C (the 41/16 steel), the Wild Tooth depth — distinct from the deepest scale. r₀ = rank_F2(G) = 98 and corank = 43 are computed byte-exact (`audit_star_numbers_v1.py`); the radical of (G mod 2) is the non-unit part, of dimension 43, so the **unit-scale** multiplicity is the rank, 98. (iv) is arithmetic. ∎

**Remark 2.2 (the two consumed numbers).** rank_F2(G) = 98 and corank_F2(G) = 43 (byte-exact). The corank fixes the **non-unit** total (43), not the unit-scale multiplicity; the unit-scale multiplicity is the rank, 98. *(This corrects the prior draft, which set r₀ = 43; see §7.)*

---

## 3. The geometric face

The **squirrels** of Λ are the 143 520 norm-12 vectors s = M_i − M_j arising as differences of the 960 plane classes in the saturated frame (gate {12:143520, 14:300960, 18:15840}, byte-exact); they are the minimal vectors (min Λ = 12). S₆ acts through the six coordinates of K₆; the form is S₆-equivariant.

**Definition 3.1 (geometric kissing covariance form).** With {s_t}_{t=1}^{143520} ⊂ Z^141,
> K_geo = Σ_t (G s_t)(G s_t)ᵀ ∈ Sym₁₄₁(Z), so xᵀ K_geo x = Σ_t ⟨x, s_t⟩²_G.

The **covariance operator** of the squirrel distribution on (R^141, ⟨·,·⟩_G) is the G-self-adjoint
> C = G⁻¹ K_geo, equivalently the matrix product K·G where K = Σ_t s_t s_tᵀ (same spectrum).

**Theorem 3.2 (S₆-isotypic block-scalarity).** The spectrum of the covariance operator is exactly four values, with multiplicities equal to the four S₆-isotypic eigenspace dimensions:
> spec(C) = spec(G⁻¹K_geo) = spec(KG) = { 9216^(90), 13440^(30), 23040^(20), 28800^(1) }, (3)

so, with G-orthogonal projectors Π₉₀, Π₃₀, Π₂₀, Π₁,
> K_geo = G·( 9216 Π₉₀ + 13440 Π₃₀ + 23040 Π₂₀ + 28800 Π₁ ). (4)

Trace identity: Σ_t ⟨s_t, s_t⟩_G = 12·143520 = 1 722 240 = 90·9216 + 30·13440 + 20·23040 + 1·28800. The values factor as 9216 = 2^10·3², 13440 = 2^7·3·5·7, 23040 = 2^9·3²·5, 28800 = 2^7·3²·5², carrying the odd primes 3, 5, 7 of K₆.

*Proof.* (3) is computed byte-exact as the spectrum of the symmetric-definite pencil (K_geo, G) (`audit_star_numbers_v1.py`). The multiplicities (90, 30, 20, 1) are the eigenspace dimensions of the intersection form (eigenvalues 32, 48, 96, 240; Spectrum law λ = 16·N_a) on the 141-dimensional Λ, where the 240-eigenspace is one-dimensional (only the impostor χ* survives once h is removed). Both operators are S₆×T-equivariant and multiplicity-one on these types, so the eigenspaces coincide; block-scalarity (4) is Schur's lemma. ∎

**Remark 3.3 (the covariance operator is unique — sharper than the prior draft).** There is **one** covariance operator, C = G⁻¹K_geo = KG (same spectrum), and it **is** block-scalar. "Not block-scalar" arises only from forming a different, frame-dependent object — the pencil (K, G), i.e. spec(G⁻¹K), which is **141 distinct eigenvalues** (byte-exact) and is **not** the covariance operator (it raises the wrong index). The historical "seven-orbit, not block-scalar, no averaged covariance" caveat was about that artifact pencil, not the covariance. The correct axis is **operator vs. artifact**, not "coordinate vs. geometric": from either K or K_geo the *correctly formed* operator (KG, G⁻¹K_geo) is the same block-scalar C. The averaged covariance is therefore exact and usable.

**Proposition 3.4 (no squirrel hides in the refuge).** Let E₉₀ be the lowest (eigenvalue-9216) block. Every squirrel s has 4 ≤ ‖Π₉₀ s‖²_G ≤ 8; in particular the count of squirrels with refuge-energy ≥ 11 is 0 (max 8 on orbit [8,4,0,0], 1440 squirrels; min 4 on orbit [4,3,4,1], 5760). *Byte-exact.*

**Proposition 3.5 (the finite wall does not seal).** The wall W₁₂ — the 1935 norm-12 squirrels that break the budget under the cheapest cut — has **rank W₁₂ = 128** (byte-exact; all 1935 reconstructed as M_i − M_j, all norm 12), equal to the section rank, yet there is a rank-128 section containing none of W₁₂. Rank is span, not membership; a generic 128-subspace avoids any prescribed finite set of lines. The union of plane-difference strata {12, 14, 18} admits a 13-functional kernel avoiding all of it (fractional set-cover ≈ 6.82 < 13). The unbounded strata {16, 20, 22} and arbitrary short vectors (~10^10) are not a finite hitting target, so **no finite covering seals**. *This is a non-sealing fact (an upper-bound/coverage statement), not a seal.*

---

## 4. The two faces meet: at the cut Φ, as two independent constraints

**(Corrected from the prior draft, which asserted a single shared invariant.)**

Let Φ ∈ Z^{13×141} be a cut (13 primitive integral functionals) and S = ker Φ ∩ Λ its section. The price is the oracle determinant
> pr(S) = det(Φ D Φᵀ) / 32^13, D = 32 G⁻¹ ∈ Sym₁₄₁(Z). (5)

**Proposition 4.1 (the price is a 2-adic ladder determinant).** det(Φ D Φᵀ) ∈ Z, pr(S) ∈ Z[1/2] with 2-power denominator bounded by the ladder of Theorem 2.1(ii). Over the cheap pool the price floor is 2^5.585 < 2^8.08, a function of the ladder (Steel Lemma D), not of the search. *This quantity is a function of Φ.*

**Proposition 4.2 (the minimum is constrained by forced isotypic overlap).** By the Grassmann dimension formula, any rank-128 S meets the eigenspaces in dimensions at least
> dim(S ∩ E_d) ≥ 128 + dim E_d − 141 = (77, 17, 7, 0) for E₉₀, E₃₀, E₂₀, E₁.

The minimum captured covariance energy over 128-subspaces is the sum of the 128 smallest eigenvalues,
> min_{dim U=128} tr(Π_U K_geo) = 90·9216 + 30·13440 + 8·23040 = 1 416 960,

attained by dropping the 13 largest directions. *This quantity is a **constant**, independent of Φ; it is a universal lower bound on the energy any section retains against the squirrels.*

**The meeting point — stated correctly.** Propositions 4.1 and 4.2 read the **same cut Φ** through **two different invariants**: the price determinant det(Φ D Φᵀ) (function of Φ, the arithmetic/2-adic face) and the forced-overlap energy 1 416 960 with overlaps (77, 17, 7, 0) (a constant of the geometric/S₆ face). **These are not equal and not the same invariant** — a constant cannot equal a Φ-dependent determinant. The two faces are **two independent constraints on one object**: Φ must (a) keep its price determinant below budget *and* (b) position its kernel so the forced overlap does not force a vector of norm < 24. A King Pin section is the **joint feasibility** of (a) and (b). The hardness of the problem — and the openness of Proposition 5.4 — is exactly that **nothing proven forces (a) and (b) compatible or incompatible**: they are independent. This is the Architect's star read correctly: the equilibrium of **two** forces, not the value of one.

---

## 5. The Star Criterion

### 5.1 The equilibrium, made precise

Lowering the price (4.1) compresses S within the 2-adic ladder; raising the minimum (4.2) forces S across the high-energy blocks E₃₀ ⊕ E₂₀, where Proposition 3.4 forbids hiding the squirrels in E₉₀ alone. A King Pin section is a critical point of log₂ pr − β·log₂(min/24) (β → ∞) subject to integrality.

**Remark 5.1 (the star, exact and broken).** The variational reading is exact: a star is the critical point of (inward pressure + outward gravitation). It breaks at **integrality** — a star equilibrates in a continuum of radii, a section is a point of the integral Grassmannian Gr(128, Λ). The continuous equilibrium is a **phantom**:

**Remark 5.2 (scale homogeneity; the phantom).** The price functional is **homogeneous of degree 26** in Φ: det((cΦ)D(cΦ)ᵀ) = c^26 det(ΦDΦᵀ), since ΦDΦᵀ ↦ c²(ΦDΦᵀ) on a 13×13 determinant. Hence inf_{c>0} pr(cΦ) = 0 for any fixed cut: the continuous infimum carries **no geometric content**; the genuine price lives only at primitive integral Φ. *Verified byte-exact:* scaling the start cut by c = 0.605 reproduces pr = 0.605^26·2^25.76 = 2^6.91; by c = 0.5, 2^{−0.24}. The "continuous price 2^0" of earlier work was this homogeneity, not a property of Λ. The mathematical question is whether an **integral rung** of the 2-adic ladder lands at the equilibrium — invisible to the continuum, visible to the ladder.

### 5.2 The criterion

L₂ = ⊕_k 2^k U_k (U_k unimodular over Z₂), scales in {0, …, 5} with top scale 5, unit-scale multiplicity r₀ = 98 (Remark 2.2). Π₉₀, Π₃₀, Π₂₀, Π₁ the isotypic projectors.

**Program 5.3 (the Star Criterion).** A King Pin section exists iff there is an integral corank-13 sublattice S = ker Φ ∩ Λ such that both hold:

- **(1) Arithmetic / price (2-adic).** The Smith data of Φ against the Jordan splitting {2^k U_k} gives val₂ det(Φ D Φᵀ) − 65 < 8.08; i.e. Φ descends the ladder by at most the budget.
- **(2) Geometric / minimum (archimedean + representation).** The real span of S meets the eigenspaces in the forced dimensions (≥77, ≥17, ≥7, 0) **and** S contains no vector of norm < 24, across the six strata {12, 14, 16, 18, 20, 22}.

**Remark 5.3' (what finitizes and what does not — corrected).** Condition (1) ranges over a **finite** set of Smith types of a 13×141 matrix against a fixed Z₂-Jordan form: the **price side is finitizable** (modulo the still-incomplete Jordan profile, Theorem 2.1(iii)). Condition (2) is **not** so reducible. The forced overlaps (≥77, ≥17, ≥7, 0) are a finite isotypic datum, but "S contains no vector of norm < 24" is an **archimedean short-vector condition**: it depends on the full integral structure of S, **not on its 2-adic completion** (L₂ forgets the archimedean metric) and **not on its isotypic position alone** (two sections with the same 2-adic data and the same overlaps can have different minima). Therefore the prior draft's claim — that the criterion "replaces the intractable search by a Z₂ linear-algebra question crossed with a representation-theoretic decomposition" — **overstates**: it finitizes the *price* (the easy half) and leaves the *minimum* (the actual seal, the hard half) **archimedean and not finitized by those means**. The seal, if any, lives in the minimum, exactly where the campaign's evidence has always placed it.

**Proposition 5.4 (the descent link — open).** Conditions (1) and (2) are jointly satisfiable iff there is an integral corank-13 S ⊆ Λ whose 2-adic Smith type against {2^k U_k} stays within the price budget **while** the induced form on the E₃₀ ⊕ E₂₀ component (carrying the forced overlap 17 + 7) has min ≥ 24.

**Remark 5.5 (status).** Proposition 5.4 is, today, a **conjecture**. Its hypotheses are established (the partial Jordan form by Theorem 2.1, the projectors and forced overlaps by Theorem 3.2 and 4.2); what is **not** established is that the joint realisability is governed exactly by the stated interaction, with no further obstruction — and, separately, that the archimedean min ≥ 24 condition is decidable from finite data (Remark 5.3'). Proving 5.4 affirmatively exhibits a King Pin section (a new record); proving it negatively shows Λ admits none — that the equilibrium falls strictly between the integral rungs, hence the Mordell–Weil record cannot be beaten by a section of Λ — the **second valid victory**. Either resolution closes the problem.

### 5.3 Two operational levers (the Architect's readings)

**Remark 5.6 (the microscope — lattice reduction).** To test condition (2) on a candidate S, do **not** inspect S in the skew saturated frame, where short vectors are hidden by basis skew (cond(G) = 1.401×10⁶, byte-exact). First magnify S by reducing its Gram (LLL, then BKZ blocksize ≥ 24), which exhibits the genuine shortest vectors and makes min(S) ≥ 24 decidable. The microscope is lattice reduction; it is the certified instrument for condition (2) (engine `pitbullmarinero`, production machine). *This is the only certified handle on the archimedean half; it does not finitize the search, it certifies one candidate.*

**Remark 5.7 (electromagnetic repulsion — variational descent).** The discrete star equilibrium is a repulsion: minimise the barrier-penalised price F(Φ) = log₂ pr(ker Φ) − β·log₂(min(ker Φ)/24), β → ∞, **over primitive integral Φ** — not over the continuum, where Remark 5.2 collapses the scale to a phantom. The repulsion is genuine only when the charges are pinned to the integral rungs of the 2-adic ladder. This is the correct objective for any annealing/homotopy engine, replacing the scale-homogeneous functional earlier engines minimised in error.

### 5.4 The decisive lever — the MW128-embedding test (imports the minimum)

The archimedean obstruction of Remark 5.3' is what makes the criterion intractable in general. There is **one** candidate for which it dissolves: **MW128 itself**. MW128 (Elkies) is a rank-128 even lattice with **known** minimum 24 and density 2^97.40. If MW128 **embeds primitively as a rank-128 section of Λ**, then its minimum (24) is **imported**, not searched — condition (2) is settled by the embedding, bypassing the archimedean obstruction for that candidate. The test is purely arithmetic and lives entirely on the **arithmetic face**:

- compute the discriminant form q_{MW128} on MW128*/MW128 (a finite 2-group, since the relevant invariants are 2-adic),
- compare against q_V on V*/V (order 2^128, the Double-Ladder group),
- apply Nikulin's primitive-embedding criterion: does MW128 embed primitively as a corank-13 section of Λ?

**If yes:** Λ ⊇ a section ≅ MW128, so Λ realizes at least the record; the question reduces to whether a *strictly better* section exists — and all campaign evidence (diffuse wall, isotropic covariance Theorem 3.2, seven cheap-cut levers closed) says it does not, i.e. the **second valid victory** (Λ sealed at MW128 via the Shioda dictionary). **If no:** the record lattice is not a section of Λ, sharpening where any improving section must differ. Decisive either way, and **on pencil** — it needs one datum not in the project files: the discriminant form (or Gram) of MW128. *This is the concrete next step, and it unifies the arithmetic face (Theorem 2.1, the 2-adic discriminant data) with the open minimum condition by sourcing the minimum from a lattice whose minimum is already known.*

---

## 6. The eight prior theorems, as two faces

They fall, without exception, onto one face, and the long-open **Bridge** is the (still open) joint-feasibility of the two constraints on Φ (§4–5), not a missing transfer.

**Arithmetic face (2-adic).** Steel (dual ladder {2^0, 2^1, 2^4}, scale 2^5, price determinant); Watermark and Double Ladder (det 2^128, the discriminant group); Wild Tooth (the deep 2-tower, fold depth ≡ 0 mod 4); Bend (the modular shift at 2); Parity (the mod-2 obstruction killing the primal mold). Each governs an invariant of Λ itself, supported at 2 (Theorem 2.1).

**Geometric face (S₆-combinatorial).** Sweet Lie (family/chorus structure, resonance = bipartiteness, the rank-128 mold and impostor χ*); Spectrum (the law λ = 16·N_a, eigenspaces **(90, 30, 20, 1)** on the 141-dimensional Λ — the (90, 30, 20, 2) count is the 142-dimensional Λ⊕⟨h⟩); Closure (the finite support catalogue); the pair functors Within-Pair and Closed Walk (the Degtyarev–Shimada rank ladder). Each governs the minimal-vector configuration and carries the odd primes of K₆ (Theorem 3.2).

**The deck.** The price determinant det(Φ D Φᵀ) is computed by the arithmetic face through D = 32 G⁻¹; the geometric face contributes a *different* invariant (the forced overlap and minimum). The Star Criterion (Program 5.3) is the joint feasibility of the two — finitized on the price side, open on the minimum side. The deck is a beam under **two** loads, not a single shared invariant.

---

## 7. Graveyard — corrections to the prior (Vitor) draft

Errors are logged, not hidden (house protocol). Three claims of the prior draft are corrected; the numbers were all right, the readings were not.

1. **Deepest Jordan block scale (Theorem 2.1(iii)).** Prior: "deepest non-unimodular Jordan block at scale 2^4 (Wild Tooth depth), saturation 2^5" — internally inconsistent and contradicting its cited source. **Corrected:** the deepest non-unimodular block is at **2^5** (= saturation = den(G⁻¹), Steel Lemma A–B). The **2^4** is the **cheap-spectrum ladder cap** (Wild Tooth, the 41/16 steel), a property of the cheap dual functionals, not the deepest block.

2. **Unit-scale multiplicity (Remark 2.2, §5.2).** Prior: "r₀ = 43 is the F2-corank … fixes the unit-scale multiplicity." **Corrected:** the **unit-scale multiplicity is rank_F2(G) = 98**; the **corank 43 is the non-unit total** Σ_{k≥1} r_k. The two were swapped. (Both numbers verified byte-exact.)

3. **The meeting point (§4) and the criterion's scope (§5).** Prior: "the price determinant is the unique invariant computed by both readings," and the criterion "replaces the intractable search by a Z₂ linear-algebra question crossed with a representation-theoretic decomposition." **Corrected:** Proposition 4.2's quantity is a Φ-independent constant (1 416 960), **not** the price determinant, so the two faces compute **different** invariants and meet as **two independent constraints on the cut Φ**, not as one shared invariant. The criterion finitizes the **price** (2-adic Smith data) but **not** the **minimum** (min ≥ 24 is archimedean, reducible to neither 2-adic nor representation-theoretic data); the intractable core survives. *(This also realigns the paper with the Architect's own star metaphor: two forces, not one quantity.)*

Tightening: Remark 3.3 reframed — there is one covariance operator (KG = G⁻¹K_geo), block-scalar; "not block-scalar" is the artifact pencil G⁻¹K (141 skewed values), not the covariance. §6 eigenspace count corrected to (90, 30, 20, 1) on the 141-dimensional Λ.

---

## Provenance and rectitude

Every numeric claim in §§1–5 is computed byte-exact in exact integer/float-verified arithmetic from the project frame files `gram_L0sat_141_v1.txt` (G, det 2^128), `dualgram_L0sat_xD.txt` (D = 32 G⁻¹), `dump_planes_L0sat_960x141_v1.txt` (960 plane classes, gate 143 520), and `pitbull_TRUE_RESIDUAL_1935_v1.txt` (the wall, rank 128 reconstructed), and is reproduced by the companion script `audit_star_numbers_v1.py` (corank 43, cond 1.401×10⁶, covariance spectrum, naive-pencil 141 distinct, wall rank 128) and `audit_kissing_covariance_blockscalar_v1.py` (the block-scalar covariance). The determinant 2^128, the dual scale 2^5 and ladder {2^0, 2^1, 2^4}, the deep-block scale 2^5, and the Spectrum eigenvalues are cited to the Steel, Wild Tooth, and Spectrum theorems, each carrying its own byte-exact reproducer.

Theorem 2.1, Theorem 3.2, and Propositions 3.4, 3.5, 4.1, 4.2 are **proved**. Program 5.3 is a reformulation; Proposition 5.4 is, today, a **conjecture**; the full 2-adic Jordan profile (Theorem 2.1(iii)) and the decidability of the archimedean minimum (Remark 5.3') are **open**. None is claimed as a theorem.

**Two measures twice, cut once. The record is not claimed; the criterion is — with its price side finitized and its minimum side named as the open core. The decisive next step is the MW128-embedding test (§5.4); it needs the discriminant form of MW128. PMC.**

*— El Tunelero (Auditor Jefe), revising the draft of Auditor Vitor, for the panel of King Pin.*
