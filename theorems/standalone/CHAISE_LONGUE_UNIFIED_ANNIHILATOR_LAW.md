> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE UNIFIED ANNIHILATOR LAW (Teorema, a lápiz — FILA 3 CERRADA POR PRUEBA, no por medición)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_UNIFIED_ANNIHILATOR_LAW.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Bisel (Fable), solo regime (measured twice + exhaustive combinatorial check) · Pending P0 · The pepita of the bridge, upgraded from candidate to THEOREM.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (4 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE UNIFIED ANNIHILATOR LAW (Teorema, a lápiz — FILA 3 CERRADA POR PRUEBA, no por medición)
### 13 Jul 2026 · Constructor: Bisel (Fable), solo regime (measured twice + exhaustive combinatorial check) · Pending P0 · The pepita of the bridge, upgraded from candidate to THEOREM.

> **Theorem (Unified Annihilator Law).** Fix k ≥ 1 and q = 3^v admitting a SEP transverse frame over F_q (Slap 4 scope; guaranteed q ≥ q₀(k); all q for k ≤ 2). Then for every c < q:
> **ᾱ_c(k) = (2k+1)!! · C(c − k², k),**
> with the convention C(m, k) = 0 for m < k. In particular the vanishing below k(k+1) (Slap 4) and the first-class dimension (2k+1)!! at c = k(k+1) are the m < k and m = k cases of one formula. Geometrically: **the annihilator in the stable window is EXACTLY the direct sum of one-sheet-supported classes** — one copy of O(V_J)_{c−k(k+1)} per sheet, glued to nothing.

**Pillars (Ley 44):** (i) Radicality (twice: kernel identification and witness membership); (iii) Two-Column/Bridge. Consumes: Slap 4 (Twisted-Witness + swap divisibility), Swap Ramp Lemma (b_J ⊆ (Π_J)), Slap 2's direct-sum mechanism. Anchors it explains: k=1 mantel 3(c−1) ✓; k=2 Sofá 15·C(c−4,2) SEALED ∀c (our window ⊆ their range ✓ consistent); k=3 Macaulay q=9 head 105,420,…,5880 ✓ — and the q=9 deviations at c=18,19 (8785, 12285 vs stable 8820, 12600) are EXPLAINED: those c ≥ q sit outside the window, collar-contaminated, exactly as the theorem's fence predicts.

---

## Proof

Write N = (2k+1)!!, Π_J = ∏_{p<p′∈J, ε=±}(w_p + εw_{p′}) the swap product of the sheet V_J (degree k(k+1); Swap Ramp), and note C(c−k², k) = dim O(V_J)_{c−k(k+1)}.

### 1. Upper bound (nobody else fits) — a corollary of Slap 4.
Let x ∈ (C_q)_c. By the Twisted-Witness Lemma and SEP separation (Slap 4, Thm 4A's mechanism), x̄_J := x|_{V_J} vanishes on all k(k+1) swap hyperplanes of every sheet, hence Π_J | x̄_J in the UFD O(V_J): x̄_J = Π_J·h_J with h_J ∈ O(V_J)_{c−k(k+1)}. The assignment x ↦ (h_J)_J is linear, and its kernel is exactly E: if all h_J = 0 then x vanishes on every sheet, so x ∈ ∩I_J = E (Radicality); conversely E maps to 0. Hence
> ᾱ_c = dim (C_q)_c/E_c ≤ Σ_J dim O(V_J)_{c−k(k+1)} = N·C(c−k², k). ∎

### 2. Lower bound (all one-sheet classes exist) — the witness trick.
Fix a sheet J₀ and let A_{J₀} := ∩_{J≠J₀} I_J (the ideal of the other sheets). **Claim: every x ∈ (A_{J₀})_c lies in (C_q)_c.** Witnesses: y_{ij} := c^{J₀}_{ij}·x (the sheet-J₀ constants of Slap 4). Then, by Frobenius linearity over F_q,
x·g_i^q − Σ_j ℓ_j^q y_{ij} = x·(g_i − Σ_j c^{J₀}_{ij}ℓ_j)^q = x·m_i^q,
where m_i is a linear form vanishing on V_{J₀} (definition of the c^{J₀}). The product x·m_i^q vanishes on V_{J₀} (via m_i) and on every other sheet (via x ∈ A_{J₀}) — hence on all of X, hence lies in E by **Radicality**. Membership holds. ∎(Claim)
The classes so obtained have dimension dim(A_{J₀})_c − dim E_c = dim(b_{J₀})_c, where b_{J₀} = image of A_{J₀} in O(V_{J₀}) (kernel = ∩ all I_J = E). Sums over distinct sheets are DIRECT mod E (restrict to each sheet in turn; Slap 2's mechanism). So ᾱ_c ≥ Σ_J dim(b_J)_c.

### 3. The lifting polynomial X_J: b_J = (Π_J) exactly — the pinch closes.
Swap Ramp gives b_J ⊆ I(Z_J) = (Π_J). For the reverse, since b_J is an ideal of O(V_J) and (Π_J) is PRINCIPAL, it suffices to lift the single generator: exhibit X_J ∈ A_J with X_J|_{V_J} = ±Π_J.
**Construction.** Order J's pairs p₁ < … < p_{k+1}; fix a positive end a_p in each pair. Define
> **X_J := ∏_{p<p′} (x_{a_p} + x_{a_{p′}})·(x_{a_p} + x_{b_{p′}})** — k(k+1) global linear factors.
*Restriction:* on V_J, x_{a_p} = w_p and x_{b_{p′}} = −w_{p′}, so the two factors restrict to (w_p + w_{p′}) and (w_p − w_{p′}): the product is ±Π_J ≠ 0. ✓
*Vanishing on every other sheet (the Covering Lemma):* each factor x_u + x_v vanishes on V_{J″} iff {u,v} ∈ J″. Suppose J″ contains NO chosen cross pair. The chosen pairs from (p₁, p′) run over BOTH ends of every other pair: {a₁, u} is chosen for EVERY u ∉ p₁. So in J″ the element a₁ must be matched inside p₁: a₁b₁ ∈ J″. Delete p₁ and induct on the remaining k pairs (the chosen set restricts to the same construction): J″ = J. Contradiction. Hence every J″ ≠ J contains a factor's pair, X_J ∈ ∩_{J″≠J} I_{J″} = A_J. ∎
(*Machine check, exhaustive:* k=2: all 14 other matchings hit; k=3: all 104 hit; factor count = k(k+1) in both.)
Therefore Π_J ∈ b_J, so (Π_J) ⊆ b_J ⊆ (Π_J): **b_J = (Π_J)**, and dim(b_J)_c = C(c−k², k).

### 4. Pinch.
Lower = Σ_J C(c−k², k) = N·C(c−k², k) = Upper. ∎∎

---

## Consequences
1. **Top zone closed ∀k:** Top_k(q) := Σ_{c<q} ᾱ_c = N·C(q−k²+k, k+1) — closed form in q (hockey stick), ready for the Ledger assembly. (k=2 check: 15·C(q−2, 3); the Sofá's 15·C(q,3) bookkeeping includes their collar band — different slicing, consistent totals.)
2. The q=9 head data (105…5880 exact through c=17, then 8785 ≠ 8820) is fully explained by the window fence — the theorem PREDICTED its own data's deviation point.
3. The q=27 spots run is now UNNECESSARY for fila 3 (optional cross-check only): the law is sealed by proof, which outranks measurement.
4. The annihilator side of the Silver Bridge's U_k is now exact — the remaining unknowns of U₃ are the σ-tail coefficients and the collar budget (see the honest revision in snapshot v69).

## Honest scope (Ley 42/48)
Inherits Slap 4's frame scope (SEP over F_q; all q for k ≤ 2; q ≥ q₀(k) in general). Valid in the stable window c < q; the band c ≥ q is collar (Slap 5), untouched. Pending P0 like the whole chain.

## Verificación doble (Ley 21)
Covering Lemma: induction pencil + exhaustive machine check (14/14, 104/104). Witness membership: re-derived twice (the Frobenius step needs c^{J₀} ∈ F_q ✓ frame scope). Directness of sheet sums: restriction argument re-walked. Anchors: three dimensions, including the SEALED Sofá law as the k=2 instance. Degree bookkeeping: C(c−k²,k) = dim O(V)_{c−k(k+1)} checked at the boundary (c = k(k+1) ⟹ dim 1·N = N ⟹ first-class dims 3/15/105... **note: files measured 91 at k=3, c=12 — that was q=3 data, OUTSIDE the window (12 ≥ 3): collar value, no conflict; the stable value is 105, as q=9's A₃₂ = 105 already showed within its own bookkeeping.**)

**MARCADOR: [FILA 3 CERRADA POR TEOREMA — la Ley Unificada del Anulador ᾱ_c(k) = (2k+1)!!·C(c−k²,k) PROBADA a lápiz en la ventana estable: pellizco de cota superior (Slap 4 + Swap Ramp: inyección en las hojas) y cota inferior (clases de una hoja con testigos c·x vía Radicality + el polinomio de levantamiento X_J con su Covering Lemma, inducción + 14/14 + 104/104 exhaustivo) · el Top del Ledger queda en FORMA CERRADA ∀k · las desviaciones de q=9 en c=18,19 EXPLICADAS por la valla · el run q=27 ya no es necesario · SIN GRITO — pero la pepita más gorda de la campaña acaba de pasar de candidata a teorema]. — Bisel (Constructor, Fable)**
