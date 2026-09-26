> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — SLAP 1: THE HILBERT THEOREM (the e-direction falls)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SLAP1_HILBERT_THEOREM.md
>
> **Status, as written in the document:** Power Slap campaign, Asalto 1 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable) · Auditor: Cárdano · Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — SLAP 1: THE HILBERT THEOREM (the e-direction falls)
### Power Slap campaign, Asalto 1 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable) · Auditor: Cárdano · Pending P0.
### The slap declared before the swing (regla del Slap): *both census laws — the window census σ_e(k) and the annihilator census α_c(k) — are Hilbert functions of finitely generated graded S-modules, hence eventually polynomial in their degree variable, for every fixed k.* One blow, two censuses.

**Pillars (Ley 44):** builds on (i) Odd Symmetric / Radicality (E ⊆ I(p) via triangular transport), (iii) Two-Column (the annihilator lives in Λ). Inputs from the proven chain: Recognition ∀k (R3), Twin Recognition (R8), Bridge Theorem (§6 s22).

---

## 0. Setting

S = F₃[x₁,…,x_n], n = 2k+2, standard graded. E = (e₁, e₃, …, e_{2k+1}) the odd elementary symmetric ideal. For each edge p = {a,b} of K_n, I(p) = (x_a+x_b) + (odd elementaries of the complementary 2k variables) — the edge ideal of the Recognition Theorem (Lemma 0, R3), radical.

Two censuses, byte-exact definitions from the live files:
- **Window census:** M = {λ ∈ Sⁿ : λ_a − λ_b ∈ I({a,b}) for every edge}, and σ_e(k) = dim M_e − [dim S_e + (n−1)·dim E_e] (the SIGMA_ENGINE definition, validated on the Mac).
- **Annihilator census:** α_c(k) = dim ann_Λ(g₁^q,…,g_k^q)_c, where Λ = S/(E + (ℓ₁^q,…,ℓ_{k+1}^q)) is the ceiling CI and g₁,…,g_k the Bridge generators. By the Twin Recognition (R8), for c < q the defining conditions are q-free.

---

## 1. Theorem A (window census): σ_e(k) is eventually polynomial in e, for every k

**Lemma A1 (the edge conditions are ideal conditions).** M is a graded S-submodule of Sⁿ.
*Proof.* λ ∈ M, f ∈ S: (fλ)_a − (fλ)_b = f·(λ_a − λ_b) ∈ f·I(p) ⊆ I(p). Homogeneous conditions ⟹ graded. ∎

**Lemma A2 (the trivials, blindado — the −(n−1) accounting).** Triv := S·(1,…,1) + E·Sⁿ is a graded submodule of M, and
dim Triv_e = dim S_e + (n−1)·dim E_e.
*Proof.* (1,…,1) has all differences 0 ∈ I(p); a tuple with all coordinates in E has differences in E, and E ⊆ I(p) by the triangular transport (mod x_a+x_b, the generating function gives e_j ≡ e′_j − x_a²e′_{j−2}, unitriangular on the odd family — Paso C of the Deletion Reduction; also Sofá Prop. 1.1 mechanism). So Triv ⊆ M. Dimension: dim(S(1,…,1))_e = dim S_e, dim(E·Sⁿ)_e = n·dim E_e, and the overlap is exactly E·(1,…,1): f·(1,…,1) ∈ E·Sⁿ ⟺ f ∈ E. Inclusion–exclusion gives dim S_e + n·dim E_e − dim E_e. ∎
**This is precisely the engine's −(n−1) (not −n): the audit point of the previous relay, now a one-line lemma.** By definition, σ_e(k) = HF_{M/Triv}(e).

**Theorem A.** For every fixed k, Q(k) := M/Triv is a finitely generated graded S-module; hence (Hilbert 1890) there is a polynomial HP_{Q(k)} ∈ ℚ[e] and a threshold e₀(k) with
> **σ_e(k) = HP_{Q(k)}(e) for all e ≥ e₀(k), with e₀(k) ≤ reg(Q(k)) + 1.**
*Proof.* S is Noetherian and Sⁿ is finite free, so the submodule M is finitely generated; the quotient Q(k) is a f.g. graded S-module. Its Hilbert function agrees with its Hilbert polynomial for e ≥ reg(Q(k)) + 1 (Eisenbud, *The Geometry of Syzygies*, Thm. 4.2; classical Hilbert–Serre). ∎

**Honest scope (Ley 42/48).** The threshold e₀(k) is FINITE for each k by the theorem; an EXPLICIT uniform bound ρ(k) is exactly the Regularity Slap (Slap 2) and is NOT claimed here. "Eventually polynomial" carries the threshold in the statement — the auditor's demand is honored in the theorem's very shape.

**Anchors (numbers from files, sanity — the theorem does not rest on them):**
- k=2: HP = 15e²−90e+145 for e ≥ 4 (Sofá census law, certified). Pre-stable values 0,0,1,5 at e=0..3 — the Hilbert-function vs Hilbert-polynomial gap, live and visible: e₀(2)=4.
- k=1: σ_e(1) = 3(e−1) for e ≥ 1 (closed form, R4 forensic); pre-stable at e=0.
- k=3: measured 0,0,1,7,29,90 (e=0..5) — pre-stable head visible; the stable law is Slap 2's target.
- Degree of HP in the two sealed anchors: 1 at k=1, 2 at k=2 ⟹ **candidate** deg HP_{Q(k)} = k (equivalently dim Q(k) = k+1). TWO points — a candidate under Ley 48, NOT claimed. Slap 2 decides.

---

## 2. Theorem B (annihilator census): the stable colon is an ideal, and ᾱ_c(k) is eventually polynomial in c

The locker-room discovery of this slap: **no parametric surrogate module needs to be built to get module structure — the annihilator is a colon, and colons are ideals for free.**

**Lemma B1 (the colon).** C_q := (E + (ℓ₁^q,…,ℓ_{k+1}^q)) : (g₁^q,…,g_k^q) ⊆ S is a graded ideal, and for c < q,
α_c(k) = dim (C_q)_c − dim E_c.
*Proof.* A colon of homogeneous ideals is a homogeneous ideal (x·g_i^q ∈ J ⟹ (fx)·g_i^q = f·(x g_i^q) ∈ J). The annihilator in Λ is the image of C_q, i.e. ann_Λ(g^{[q]}) = C_q/(E+(ℓ^{[q]})); in degree c < q the generators ℓ_j^q (degree q) contribute nothing, so (E+(ℓ^{[q]}))_c = E_c. ∎

**Lemma B2 (the stable colon exists).** There is a single graded ideal C°(k) ⊆ S with (C°(k))_c = (C_q)_c for every pair c < q.
*Proof.* By the Twin Recognition (R8, pencil): for c < q the membership conditions x·g_i^q ∈ E + (ℓ^{[q]}) decouple sheet-by-sheet into linear conditions on the coefficients of x (and per-equation witnesses) whose matrices involve only the fixed frame data — never q. So the solution space (C_q)_c ⊆ S_c is one fixed subspace V_c for all q > c. Define C° := ⊕_c V_c. Ideal property: for any two degrees c, c+1 pick one q > c+1; then V_c = (C_q)_c and V_{c+1} = (C_q)_{c+1} are consecutive graded pieces of the single ideal C_q, so S₁·V_c ⊆ V_{c+1}. ∎

**Theorem B.** For every fixed k (k ≥ 2; see scope note), the stable annihilator census ᾱ_c(k) := α_c(k) (any q > c) satisfies
> **ᾱ_c(k) = dim (C°(k))_c − dim E_c, a difference of Hilbert functions of f.g. graded objects; hence eventually polynomial in c, with threshold c₀(k) ≤ max(reg(S/C°)+1, reg(S/E)+1) + O(1).**
*Proof.* C°(k) is an ideal (B2) in Noetherian S, hence f.g.; dim(C°)_c = dim S_c − HF_{S/C°}(c) and dim E_c = dim S_c − HF_{S/E}(c) are each eventually polynomial (Hilbert 1890), so their difference ᾱ_c(k) = HF_{S/E}(c) − HF_{S/C°}(c) is eventually polynomial in c. ∎

**Honest scope (Ley 42/48).** (1) The Twin is anchored k ≥ 2 (the k=1 crack was the degenerate mirage, re-anchored on the Mac); for k=1 the law α = 3 at c=2, q=3 and 9 is measured, and k=1 is degenerate throughout the campaign — recorded, not swept. (2) Theorem B gives eventual polynomiality of the STABLE census (the q-free window c < q); the boundary c ∈ [q, q+O(k)] is the collar — Slap 5's territory, untouched here. (3) The explicit presentation of C°(k) (the ∀k analogue of the Sofá's M′/N₃) is Slap 3's job; Theorem B needs only its existence and ideal structure.

**Anchor (numbers from files):** k=2 (Sofá Thm. 3.1, certified): ann_c = 15·C(c−4,2) for ALL c — the polynomial 15(c−4)(c−5)/2 with threshold c₀(2)=4 (it evaluates to 15 ≠ 0 at c=3, where the true value is 0: the pre-stable gap, again visible). Dual anchors 0,…,0,15,45,90 at c=0..8 ✓ (15·C(2,2), 15·C(3,2), 15·C(4,2)).

---

## 3. What fell, what did not (the scoreboard of the slap)

**FELL (pencil, ∀k fixed, pending P0):**
1. σ_e(k) eventually polynomial in e — Theorem A.
2. ᾱ_c(k) eventually polynomial in c — Theorem B, via the stable colon C°(k), a NEW object (the annihilator's module structure obtained for free, no surrogate needed — SURROGATE-MODULE-WITHOUT-VALIDATION mode dodged by not building a surrogate at all).
3. The −(n−1) trivials accounting is now a lemma, not a convention (Lemma A2).

**Combined with the proven chain:** both censuses are now DOUBLY structured — polynomial in the degree direction (today, Hilbert) × eventually polynomial in the k direction (FI-Stability R7 for σ; Twin + FI skeleton for α). Tablón (i) is split exactly as the plan wrote it: (a) e-polynomiality ✓ TODAY; (b) uniform regularity = Slap 2. Tablón (ii) now has structure + module: only the evaluation (Slaps 3-4) remains.

**NOT claimed (the fence, Ley 48):** no explicit threshold uniform in k (Slap 2); no closed coefficients of either law (Slaps 2-4); nothing about the collar degrees (Slap 5); deg HP = k is a 2-point candidate, not law.

**For the Auditor (Cárdano) — the declared attack surface, in order of where I'd bite:**
(A) Lemma B2's ideal-gluing (two consecutive degrees under one large q) — verify the quantifier order survives hostile reading.
(B) Lemma A2's overlap computation (the −(n−1)) — the exact point you pre-loaded in the checklist.
(C) Theorem B's use of the Twin: confirm the Twin's statement covers ALL x-coefficient conditions (not just per-sheet necessary ones) — i.e., that "decouples into q-free linear conditions" is an equality of solution spaces, as R8 §2 states, not an inclusion.
(D) The Eisenbud reg+1 citation (P0 note, alongside the CEFN citations from R8).

**MARCADOR: [SLAP 1 GANADO — dos teoremas de lápiz (A: censo ventana; B: censo anulador vía el COLON ESTABLE C°(k), objeto nuevo), la dirección e/c es TEORÍA CLÁSICA en ambos censos, el −(n−1) blindado en lema, umbral existente citado, umbral explícito honestamente diferido al Slap 2 · anclas de archivo 4/4 (cuadrática Sofá e≥4 · 3(e−1) · k=3 cabeza pre-estable · 15·C(c−4,2) con c₀=4) · SIN GRITO — Ley 13, quedan 7 slaps]. — Bisel (Constructor, Fable), Slap 1**
