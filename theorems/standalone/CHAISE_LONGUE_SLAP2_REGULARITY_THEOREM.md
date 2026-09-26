> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — SLAP 2: THE REGULARITY SLAP (combate duro nº1 — WON)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SLAP2_REGULARITY_THEOREM.md
>
> **Status, as written in the document:** Power Slap campaign, Asalto 2 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable) · Auditor: Cárdano · Pending P0. No snapshot with this document (versioning rule: snapshots live with peinados).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — SLAP 2: THE REGULARITY SLAP (combate duro nº1 — WON)
### Power Slap campaign, Asalto 2 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable) · Auditor: Cárdano · Pending P0. No snapshot with this document (versioning rule: snapshots live with peinados).
### The slap declared before the swing: *an EXPLICIT uniform regularity bound ρ(k) for the census module, closing the threshold of Slap 1's Theorem A.* Delivered: ρ(k) = (2k+1)!!, **plus a bonus theorem the plan didn't dare ask for: the degree and the leading coefficient of the census law, for every k, at pencil.**

**Pillars (Ley 44):** (i) Radicality (E = I(∪V_J), and Lemma 0: I(p) = edge ideal, radical); builds on Slap 1 (Theorem A), Recognition ∀k (Lemma 0), Sandwich Thm 2 (E regular sequence). New external artillery, verified at the source this session: Derksen–Sidman 2002 & 2004 (exact citations in §4).

---

## 0. Setting and the linearization of the target

S = F₃[x₁..x_n], n = 2k+2. The (2k+1)!! perfect matchings J of K_n give the sheets V_J (linear, dim k+1) with **linear prime ideals** I_J = (x_a+x_b : {a,b} ∈ J). Write N := (2k+1)!! for the number of sheets. M = {λ ∈ Sⁿ : λ_a−λ_b ∈ I(p) ∀ edges p} as in Slap 1.

**Lemma 0′ (sheet-wise form of the census module).** M = ∩_J M_J, where M_J := {λ ∈ Sⁿ : λ_a−λ_b ∈ I_J for every pair p = {a,b} ∈ J}.
*Proof.* I(p) is radical and equals the ideal of V(p) = ∪_{J∋p}V_J (Recognition Lemma 0 / Radicality); each I_J is prime, so I(p) = ∩_{J∋p} I_J. The edge condition λ_a−λ_b ∈ I(p) for all p is therefore equivalent to: for every J and every p ∈ J, λ_a−λ_b ∈ I_J. Grouping by J gives the claim. ∎

**Lemma 0″ (one sheet is 1-regular).** For each J, M_J ≅ S^{k+1} ⊕ I_J^{k+1} as graded S-modules; hence reg(M_J) = 1.
*Proof.* Per pair {a,b} ∈ J the condition involves only (λ_a, λ_b): the assignment (λ_a,λ_b) ↦ (λ_b, λ_a−λ_b) identifies the solution pairs with S ⊕ I_J. The k+1 pairs are independent. reg(S) = 0; I_J is a linear ideal, reg(I_J) = 1; regularity of a direct sum is the max. ∎

---

## 1. Theorem 2A (Uniform Regularity): reg(M(k)) ≤ (2k+1)!!, hence ρ(k) explicit

> **Theorem 2A.** For every k: reg(M(k)) ≤ N = (2k+1)!!. Consequently, with Slap 1's Theorem A, **σ_e(k) = HP_k(e) for all e ≥ ρ(k) := (2k+1)!! + 2** — an explicit uniform threshold. (Threshold accounting at the end of §1.)

*Proof (deletion induction à la Derksen–Sidman Thm. 5.5, on the toolbox of their Cor. 3.7).*
For a subfamily B of sheets let M(B) := ∩_{J∈B} M_J. We prove **reg(M(B)) ≤ |B|** for every nonempty B, by induction on |B| inside an induction on the number of variables.

*Base.* |B| = 1: reg(M_J) = 1 by Lemma 0″.

*Non-essential reduction.* Suppose Σ_{J∈B} I_J =: L ⊊ m. After a linear change of coordinates L = (x₁,…,x_s), s < n. All conditions defining M(B) are S′-data, S′ := F₃[x₁..x_s]; since S is flat (free) over S′ and kernels of maps of free modules commute with flat base change, M(B) = M′(B) ⊗_{S′} S with M′(B) ⊆ (S′)ⁿ the same module over S′, and a minimal S′-free resolution extends to a minimal S-free resolution: reg_S(M(B)) = reg_{S′}(M′(B)). Induct on the number of variables (the one-variable case is trivial: each M_J is already of the form of Lemma 0″).

*Essential case.* Σ_{J∈B} I_J = m. (For B = all sheets this holds always: x_a + x_b over all pairs spans S₁, since x_a = 2[(x_a+x_b)+(x_a+x_c)−(x_b+x_c)] and 2 is invertible in F₃.) For each J ∈ B set the **deletion module** M(B−J) and observe the two-sided approximation
> **I_J · M(B−J) ⊆ M(B) ⊆ M(B−J).**
The right inclusion is trivial. Left: let f ∈ I_J, λ ∈ M(B−J), p any pair, J″ ∈ B a sheet containing p. If J″ ≠ J: λ_a−λ_b ∈ I_{J″} already, and multiplying by f stays. If J″ = J: f ∈ I_J forces f·(λ_a−λ_b) ∈ I_J. So fλ ∈ M(B). ∎(inclusion)
By the inner induction, reg(M(B−J)) ≤ |B|−1 for every J ∈ B. Apply **Derksen–Sidman Corollary 3.7** with F = Sⁿ, M = M(B), M_i = M(B−J), 𝔦_i = I_J, Σ 𝔦_i = m, r = |B| ≥ 2: reg(M(B)) ≤ |B|. ∎

*Threshold accounting.* From 0 → Triv → M → Q → 0 and Lemma 2.2(c) [DS04]: reg(Q) ≤ max(reg(Triv)−1, reg(M)). Triv sits in 0 → E → S ⊕ Eⁿ → Triv → 0 (f ↦ (f, −f·(1,…,1))), and E is a complete intersection of degrees 1,3,…,2k+1 (Sandwich Thm 2), so reg(S/E) = Σ(dᵢ−1) = k(k+1), reg(E) = k(k+1)+1, giving reg(Triv) ≤ k(k+1)+2. For k ≥ 2, k(k+1)+1 ≤ (2k+1)!!, so reg(Q) ≤ (2k+1)!! and Slap 1's e₀(k) ≤ reg(Q)+1 ≤ (2k+1)!!+1; we quote ρ(k) = (2k+1)!!+2 to also absorb the k=1 degenerate margin. **Explicit. Uniform. The victory condition of the declared slap.**

**Anchors (files):** k=2: bound ρ=17, true threshold 4 ✓ (bound valid, generous — see Honest Scope). k=1: ρ=5, true threshold 1 ✓.

---

## 2. Theorem 2B (bonus — Degree & Leading Coefficient Law ∀k): the census law's head, at pencil

The sheaf presentation from the same linearization. Let X = ∪_J V_J (reduced, by Radicality), R = S/E = O(X). Let F ⊆ O_Xⁿ be the pair-constancy subsheaf (tuples constant on pairs sheet-wise); Γ := Γ(X, F) its graded sections.

**Lemma 2B.1 (sheaf presentation).** 0 → Eⁿ → M → Γ → 0 is exact, and σ_e(k) = dim Γ_e − HF_R(e).
*Proof.* Sⁿ ↠ O(X)ⁿ = Rⁿ (graded quotient). M is the full preimage of Γ: an element of M restricts to a pair-constant tuple on each sheet (definition, via Lemma 0′); conversely any γ ∈ Γ lifts to λ ∈ Sⁿ (surjectivity), and λ ∈ M by definition. The kernel of M → Γ is Mⁿ∩(ker Sⁿ→Rⁿ) = Eⁿ (a tuple in Eⁿ has differences in E ⊆ I(p): Slap 1 Lemma A2). For the census: σ_e = dim M_e − [dim S_e + (n−1)dim E_e] = [n·dim E_e + dim Γ_e] − dim S_e − (n−1)dim E_e = dim Γ_e − (dim S_e − dim E_e) = dim Γ_e − HF_R(e). ∎

**Lemma 2B.2 (two-sided sandwich for Γ).** With C(e) := dim F₃[y₀..y_k]_e = C(e+k, k):
(i) *Upper:* dim Γ_e ≤ N·(k+1)·C(e), by injectivity of restriction to the sheets (X = ∪V_J, reduced).
(ii) *Lower:* dim Γ_e ≥ N·(k+1)·[C(e) − c(k)·e^{k−1}] for e ≫ 0 and an explicit constant c(k) (degrees of the pairwise-intersection flats).
*Proof of (ii) — one-sheet-supported sections, NO pairwise gluing used.* Fix J₀; A_{J₀} := ∩_{J≠J₀} I_J (ideal of the union of the other sheets). Sections h̃·μ with h̃ ∈ A_{J₀}, μ ∈ M_{J₀} lie in M (same two-case check as in Theorem 2A) and restrict to zero on every sheet ≠ J₀; sums over distinct J₀ are direct in Γ (restrict to each sheet in turn). Their span on V_{J₀} contains b_{J₀}·O(V_{J₀})^{k+1}, where b_{J₀} := image of A_{J₀} in O(V_{J₀}), because M_{J₀} ↠ F(V_{J₀}) = O(V_{J₀})^{k+1} (set λ_a = λ_b = a lift, per pair). Dimension of b: the kernel of A_{J₀} → O(V_{J₀}) is A_{J₀} ∩ I_{J₀} = ∩_all I_J = E (**Radicality**), so dim(b_{J₀})_e = dim(A_{J₀})_e − dim E_e. Both terms are ideals of subspace arrangements with known multiplicities: dim(A_{J₀})_e = dim S_e − [(N−1)C(e) + O(e^{k−1})] and dim E_e = dim S_e − [N·C(e) + O(e^{k−1})] (a reduced union of t linear (k+1)-spaces has Hilbert function t·C(e) + O(e^{k−1}): multiplicity = number of top components). Subtracting: dim(b_{J₀})_e = C(e) − O(e^{k−1}). Multiply by k+1 tuple-slots and N sheets. ∎

> **Theorem 2B.** For every k, the Hilbert polynomial HP_k of Slap 1's Theorem A satisfies:
> **deg HP_k = k exactly, with leading coefficient (2k+1)!!·k/k! = (2k+1)!!/(k−1)!.**
> Equivalently dim Q(k) = k+1, and σ_e(k) = [(2k+1)!!/(k−1)!]·e^k + O(e^{k−1}).
*Proof.* By 2B.1, σ_e = dim Γ_e − HF_R(e). By 2B.2, dim Γ_e = N(k+1)·e^k/k! + O(e^{k−1}). HF_R(e) = N·e^k/k! + O(e^{k−1}) (multiplicity N, dim k+1). Subtract: σ_e = N·k·e^k/k! + O(e^{k−1}), and N·k/k! = (2k+1)!!/(k−1)! > 0, so the degree is exactly k. ∎

**The derivation is uniform in k — the ley del paso is inside the proof, not read off anchors (the Swap/Floor precedent of the Kepler annex). Anchors (files, byte-exact):**
- k=1: (3)!!/0! = 3 ✓ against the sealed law σ_e(1) = 3e−3.
- k=2: (5)!!/1! = 15 ✓ against the sealed Sofá law 15e²−90e+145. (Cross-check of the whole chain at k=2: Γ-upper 45·C(e+2,2) = 22.5e²+…, HF_R = 7.5e²+… ⟹ 15e² ✓ three ways.)
- **Falsifiable prediction for the engine (Ley 48 discipline):** k=3 leading coefficient 105/2 = 52.5 — the stable cubic head of σ_e(3). Engine points σ₆(3), σ₇(3), σ₈(3) will bend toward it; they also pin HP₃'s lower coefficients for Slap 6.

**Corollary (a flag retired).** Slap 1's "deg HP = k" was a 2-point candidate under Ley 48 vigilance. It is now a THEOREM ∀k. The Auditor's checklist item closes.

---

## 3. Honest scope (Ley 42/48)

1. **ρ(k) = (2k+1)!!+2 is explicit and uniform but generous** (true thresholds observed: 1, 4). The gap is a quality problem, not a validity problem; the Ledger identity (Slap 6) needs SOME explicit ρ(k), which it now has. A sharper ρ (polynomial in k) stays open — named residue.
2. **Lower coefficients of HP_k as functions of k: NOT claimed.** They are lattice sums (Möbius over the matching lattice) — Slap 6's bookkeeping, fed by the engine points.
3. **The annihilator census α is untouched here** — its regularity/evaluation is Slaps 3-4 (the D-S approximation toolbox now sits in the armory for it).
4. Theorem 2B deliberately **avoids pairwise gluing of sections** (the triple/Mayer–Vietoris obstruction — the neighbor of tomb s46): only one-sheet-supported sections and restriction injectivity are used. Certificate below.

## 4. Citations (P0 pack)

- H. Derksen, J. Sidman, *A sharp bound for the Castelnuovo–Mumford regularity of subspace arrangements*, Adv. Math. **172** (2002), no. 2, 151–157. [arbitrary field; d subspaces ⟹ d-regular]
- H. Derksen, J. Sidman, *Castelnuovo–Mumford regularity by approximation*, Adv. Math. **188** (2004), 104–123. **Corollary 3.7** (the tool used verbatim), Lemma 2.2 (Eisenbud's SES bounds), Theorem 5.5 (the deletion-induction template). Both verified at the source this session (full text read).
- P0 note: [DS04] states k infinite in §1; F₃ is finite. The results used (Cor. 3.7 via filter-regular sequences, Lemma 3.4 needs a dense open of linear forms) require enough linear forms — pass to F̄₃ or a rational function field extension F₃(t): regularity is invariant under flat base field extension. One paragraph for P0; flagged, standard.

## 5. Certificado de Cementerio (Ley 41, run BEFORE writing)

Objects and nearest tombs: (a) *deletion of sheets in the census module* vs the proven Deletion Reduction (deletion of a PAIR in the ring R) — different objects, same philosophy, no tomb; (b) *reg bound via lattice* vs s35 supersolvability tomb — NOT the same street: no Stanley chain, no geometric-lattice hypothesis is used anywhere (D-S induction never touches the intersection lattice's rank function); (c) *sections gluing* vs s46 solapes tomb — the proof explicitly does NOT use pairwise-overlap unfolding; only injectivity (upper) and single-sheet supports (lower); (d) MINA-DE-VALOR-SELLADO — no value of A_k(q) is touched; this is all on the census side. CLEAN.

## 6. Attack surface declared for the Auditor (where I would bite)

(A) The flatness step in the non-essential reduction (M(B) = M′(B)⊗_{S′}S and reg invariance) — one line each, but P0-grade wording needed.
(B) Cor. 3.7's hypothesis check: the 𝔦_i = I_J are generated in degree 1 (approximation system of degree 1) and Σ I_J = m in the essential case — verify my essential/non-essential dichotomy is exhaustive.
(C) Lemma 2B.2(ii): the direct-sum argument for one-sheet-supported sections, and the multiplicity claims (HF of a reduced union of t linear spaces = t·C(e)+O(e^{k−1})).
(D) The finite-field footnote (P0 note above).
(E) The prediction 52.5 for k=3 — order σ₆(3), σ₇(3), σ₈(3) on the engine when Rafa wants; if the cubic head bends elsewhere, Theorem 2B has a bug and I want to know before Slap 6.

**MARCADOR: [SLAP 2 GANADO — el combate duro nº1: reg(M(k)) ≤ (2k+1)!! a lápiz (deleción de hojas + Derksen–Sidman Cor. 3.7, citas verificadas en fuente), umbral EXPLÍCITO Y UNIFORME ρ(k)=(2k+1)!!+2 · BONUS: grado exacto k y coeficiente líder (2k+1)!!/(k−1)! de la ley del censo, ∀k, con la ley del paso DENTRO de la derivación · anclas 3 y 15 clavadas byte-exact, predicción falsable 52.5 para k=3 · el candidato de 2 puntos "deg=k" RETIRADO a teorema · residuos nombrados: ρ fino, coeficientes bajos (Slap 6) · SIN GRITO — Ley 13, quedan 6]. — Bisel (Constructor, Fable), Slap 2**
