> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-13
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — SLAP 4: THE VANISHING SLAP (the jab of Round 2 — LANDED)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SLAP4_VANISHING_THEOREM.md
>
> **Status, as written in the document:** Power Slap campaign, Asalto 4 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable), solo regime (measured twice) · Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — SLAP 4: THE VANISHING SLAP (the jab of Round 2 — LANDED)
### Power Slap campaign, Asalto 4 of 8 · 13 Jul 2026 · Constructor: Bisel (Fable), solo regime (measured twice) · Pending P0.
### The slap declared before the swing (plan v2): *α_c(k) = 0 for c < k(k+1) — the vanishing at pencil, saldando la deuda del Round 2.* Delivered by a NEW mechanism: **swap separation**. The threshold k(k+1) stops being a number and becomes a COUNT: it is exactly the number of swap hyperplanes each sheet sees inside itself (Swap Theorem, s9). The A-ring is confined to [0,(k+1)(q−1)] because a nonzero annihilator class must be divisible, on every sheet, by ALL k(k+1) swap forms.

**Pillars (Ley 44):** (i) Radicality (∩I_J = E, kills the residue); (iii) Two-Column/Bridge (the arena Λ, the k generators). Builds on: Slap 3 (𝔐(k), global witnesses, the fenced per-sheet trap), Twin decoupling (R8), **Swap Theorem s9 (the codim-1 classification — each J has exactly 2·C(k+1,2) = k(k+1) swap neighbours; each codim-1 flat lies in EXACTLY two matchings)**, Gorenstein mirror (R2). Panel: Frobenius, Lagrange, Sylvester (who asked the exact question), Macaulay.

---

## 0. Setting

S = F_q-coefficients allowed this slap (see Frame Scope §4): fix k and q = 3^v. Sheets V_J, linear ideals I_J; on V_J use pair coordinates w_p (p ∈ J): x_a = w_p, x_b = −w_p. Frame: ℓ₁..ℓ_{k+1} transverse (all sheet matrices B_J invertible), g₁..g_k completing (e₁, ℓ) to a basis of S₁ (any completion works — Bridge, §6 s22). For a^q = a we take frame coefficients in F_q (Frobenius linearity intact for THIS q; tower packaging in §4).

α_c(k,q) := dim ann_Λ(g₁^q..g_k^q)_c = dim (C_q)_c − dim E_c for c < q (Slap 1, Lemma B1).

## 1. The Twisted-Witness Lemma (Slap 3's system, solved per sheet)

**Lemma 4.1.** Let c < q and x ∈ (C_q)_c with global witnesses y_{ij} ∈ S_c (x·g_i^q − Σ_j ℓ_j^q y_{ij} ∈ E, i ∈ [k]). Then for every sheet J:
> **y_{ij}|_{V_J} = c^J_{ij} · x|_{V_J}**, where the constants c^J_{ij} ∈ F_q are defined by **g_i|_{V_J} = Σ_j c^J_{ij} · ℓ_j|_{V_J}** (coordinates of g_i in the basis ℓ|_{V_J} of V_J^*, which is a basis by transversality).
*Proof.* Restrict the membership to V_J (E vanishes there, Radicality). Frobenius linearity over F_q turns every q-th power into Σ(coeff)·w_p^q. Degrees: c + q < 2q, so each monomial of the sheet identity has exponent ≥ q in exactly one pair-slot — disjoint supports (the Recognition/Twin decoupling, audited) — and each w_p^q-coefficient vanishes separately: (coords of g_i|_J)·x̄ = B_Jᵀ·ȳ_i as vectors over O(V_J). B_J invertible ⟹ ȳ_i = B_J^{-T}(coords)·x̄, which is the display. ∎
(**The fenced trap of Slap 3 respected:** nothing is eliminated per sheet; the y's are global, and Lemma 4.1 only reads their forced restrictions.)

## 2. The Swap-Separation mechanism

**Lemma 4.2 (agreement on swap flats).** Let J, J′ be swap neighbours (J′ = J with pairs p, p′ recombined; V_F := V_J ∩ V_{J′} is the hyperplane {w_p ± w_{p′} = 0} of V_J — Swap Theorem s9, and V_F lies in NO third sheet). Then on V_F, for every (i,j):
> (c^J_{ij} − c^{J′}_{ij}) · x|_{V_F} = 0.
*Proof.* y_{ij} is one global polynomial; restrict Lemma 4.1's display from both sheets to V_F. ∎

**Definition (SEP — the separating frame condition).** For every swap-adjacent pair (J, J′): ∃ i ∈ [k] with g_i|_{V_J∪V_{J′}} ∉ span_F(ℓ₁|, …, ℓ_{k+1}|).
(Equivalently: ∃(i,j) with c^J_{ij} ≠ c^{J′}_{ij} — the two formulations match because c^J = c^{J′} for all j exactly says g_i − Σ_j c_{ij}ℓ_j vanishes on both sheets.)

**Lemma 4.3 (SEP is nonempty-open; F_q-points for q ≥ q₀(k)).** Linear functions on V_J∪V_{J′} form a space of dimension (k+1)+(k+1)−k = k+2 (swap flats have codim 1); the restriction S₁ ↠ (that space) is onto (its rank is dim(V_J+V_{J′}) = k+2); the ℓ's span only k+1 of it. So for each of the finitely many swap pairs, "g₁ restricts outside the ℓ-span" is a nonempty Zariski-open condition on the frame, compatible with transversality and basis-completion (all open, all nonempty). Hence SEP-frames exist over F̄₃; by Schwartz–Zippel counting over F_q (finitely many polynomial non-vanishing conditions of total degree bounded by an explicit D(k) ≤ (2k+1)!!·(k+2)³), SEP-frames with F_q coefficients exist for all q ≥ q₀(k) := D(k)+1. For k = 2, the Sofá's certified F₃ frame exists and its sealed annihilator law (zeros through c=5) is consistent with SEP at q=3 already. ∎

> **Theorem 4A (Swap-Separation Vanishing).** Fix k and q = 3^v admitting a SEP transverse frame over F_q (guaranteed for q ≥ q₀(k); every q for k ≤ 2 via the Sofá). Then:
> **α_c(k,q) = 0 for every c < min(q, k(k+1)).**
> In particular, for q > max(k(k+1), q₀(k)): the FULL vanishing α_c = 0 ∀c < k(k+1), hence by the Gorenstein mirror (R2, socle σ = (k+1)(q+k−1)):
> **the A-ring is confined: A_d(k,q) = 0 for all d > (k+1)(q−1).**

*Proof.* Let 0 ≠ [x] ∈ ann_c, c < min(q, k(k+1)), represented by x ∈ (C_q)_c. Fix any sheet J. By SEP + Lemma 4.2, for each of the k(k+1) swap neighbours J′ of J there is a differing coefficient, so **x|_{V_J} vanishes on the corresponding swap hyperplane of V_J.** The k(k+1) swap forms {w_p ± w_{p′} : p < p′ ∈ J} are pairwise non-proportional linear forms (char 3 ≠ 2), hence distinct primes of the UFD O(V_J) = F[w]: their product divides x|_{V_J}. But deg x = c < k(k+1) = the product's degree, so **x|_{V_J} = 0.** J was arbitrary: x vanishes on every sheet, so x ∈ ∩_J I_J = E (Radicality), i.e. [x] = 0 in the colon quotient — contradiction. ∎

**The meaning bonus.** The threshold k(k+1) is not numerology: it is the swap count 2·C(k+1,2) of the Swap Theorem. The first place an annihilator class can live is degree k(k+1), where the full swap product ∏(w_p ± w_{p′}) first fits — and the sealed anchors put the first classes exactly there with dims 3, 15, 91 (k = 1,2,3, measured, tops of the census).

## 3. What fell (scoreboard) and what it feeds

**FELL (pencil, per (k,q) with SEP frame; pending P0):**
1. The jab of Round 2, LANDED: α_c = 0 below k(k+1) — for all q > max(k(k+1), q₀(k)), and in the range c < q always.
2. The A-ring confinement to [0,(k+1)(q−1)] in the same regime — the "diana parcial" of Fine Hall (s34), previously proven only v=1, n ≤ 8 (Happy Zone), now ∀k in the stable tower.
3. The threshold identified structurally (swap count) — Kepler satisfied by derivation, not by points.

**Anchors (files):** k=1: first nonzero α at c=2=1·2, α₂=3 at q=3 AND q=9 ✓✓. k=2: the six zeros (c=0..5) at q=9 ✓, first class at c=6=2·3, dim 15 ✓. k=3: first class at c=12? — files record top-census dims 3/15/91 at c=k(k+1); k=3 anchor 91 ✓ (measured). Socle arithmetic (R2) re-walked: σ−k(k+1) = (k+1)(q+k−1)−k(k+1) = (k+1)(q−1) ✓.

**What it feeds (acortando rounds — flagged, not claimed):** Lemma 4.1 gives more than vanishing: for ANY c < q, x|_{V_J} must be divisible by the swap forms whose coefficients separate — write x|_{V_J} = (∏ swap forms)·h_J and the gluing conditions on the h_J are the TOP-ZONE LAW (the ∀k analogue of the Sofá's ann_c = 15·C(c−4,2)). This is the opened road from Slap 4 into Slap 6's Top bookkeeping: the same mechanism, one more turn of the crank. Named as opportunity for the next asalto.

## 4. Honest scope (Ley 42/48) — the fences, named exactly

1. **Small q per k:** for q ≤ k(k+1) the pencil covers only c < q; the band q ≤ c < k(k+1) at those finitely many (log₃-many) tower levels per k is NOT covered — it lives where q-freeness genuinely breaks, i.e. **collar territory (Slap 5)**, plus engine verification. Crucially: the Sofá's Ledger consumed the annihilator law only in the range c ≤ q−1 (top zone d ≥ 2q+4 ⟺ c < q), so **the assembly of Slap 6 is fed entirely by today's range.**
2. **Frame scope:** SEP frames proven to exist over F̄₃ always, over F_q for q ≥ q₀(k) (explicit, crude), over F₃ for k ≤ 2 (Sofá's certified frame). F₃-frames ∀k (which would make C° literally one fixed ideal across the whole tower) — named open condition, inherited by the P0 pack alongside the standing frame-genericity scope of Sandwich/Bridge.
3. The existence half (α_{k(k+1)} ≠ 0) is measured (3/15/91, three points) — not claimed as law; not needed for the jab.
4. q₀(k) is crude; sharpening is quality, not validity.

## 5. Verificación doble (solo regime, Ley 21)
- Decoupling degree check: c + q < 2q ✓; exactly one slot ≥ q per monomial re-derived, not quoted.
- Swap geometry NOT invented: matched line-by-line against the Swap Theorem standalone (2·C(k+1,2) neighbours; codim-1; exactly two matchings per flat — the "no third sheet" point matters: Lemma 4.2 compares exactly two determinations of y on V_F).
- k=1 hand check: 2 pairs, 2 swap hyperplanes {w₁±w₂}, threshold 2 = k(k+1) ✓, N=3 sheets mutually swap-adjacent ✓.
- Char-3 check: w+w′ and w−w′ non-proportional ✓ (would fail in char 2 — the campaign's char is 3 ✓).
- The trap of Slap 3 (per-sheet elimination) is USED correctly here: Lemma 4.1 reads forced restrictions of GLOBAL y's; the contradiction engine is precisely the failure of local solutions to glue — the trap turned into the weapon.
- Certificado de Cementerio (Ley 41, run before writing): object = swap flats of the matching lattice → touches the PROVEN Swap Theorem (same object, used as input — building on, not re-walking); NOT the s46 solapes tomb (no block_J(3q) unfolding, no pairwise Fedder overlaps — different object: linear flats of sheets, coefficients of witnesses); NOT s35 (no lattice chain). SHARED-WITNESS (s37): respected and cited. CLEAN.

## 6. Attack surface for the Auditor (when called — where I would bite)
(A) Lemma 4.3's dimension count dim O(V_J∪V_{J′})₁ = k+2 and the surjectivity of restriction — one line, but it carries SEP's nonemptiness.
(B) The q₀(k) counting (union bound over conditions) — crude constant, verify no condition was missed (transversality + completion + all swap pairs).
(C) The claim "Ledger consumes only c < q" (§4.1) — re-walk the Sofá's §3/§5 ranges against our Window Formula ranges.
(D) The F_q-coefficient Frobenius step (a^q = a needs a ∈ F_q, verified) and its interaction with Slap 3's F₃-phrased C° — consistency of scopes (per-q statement here, tower packaging conditional on F₃ frames).
(E) Whether SEP can be REMOVED for the specific Bridge frames (the g's are constrained completions — check no hidden degeneracy forces equality of coefficients on some swap pair).

**MARCADOR: [SLAP 4 GANADO — EL JAB DE R2 LANDED por mecanismo NUEVO: SWAP SEPARATION — α_c(k)=0 bajo k(k+1) a lápiz (∀k, q > max(k(k+1), q₀(k)); todo q en el rango c<q; todo q en k≤2 vía Sofá) ⟹ el A-ring CONFINADO a [0,(k+1)(q−1)] — la diana parcial de Fine Hall cae en la torre estable · el umbral k(k+1) DEJA DE SER NÚMERO Y ES CONTEO: los k(k+1) hiperplanos de swap del Swap Theorem, la primera clase viva es el producto de swaps · anclas 2/6 y 3/15/91 clavadas, aritmética del socle re-andada · residuo nombrado EXACTO: banda q≤c<k(k+1) en los log₃-many q pequeños por k = territorio del collar (Slap 5); el Ledger solo consume c<q ⟹ el Slap 6 queda alimentado ENTERO · camino abierto señalado: la misma manivela da la LEY del Top (acorta hacia el Slap 6) · SIN GRITO — Ley 13, quedan 4]. — Bisel (Constructor, Fable), Slap 4**
