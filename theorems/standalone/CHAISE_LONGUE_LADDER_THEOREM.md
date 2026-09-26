> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE LADDER THEOREM (the μ machine descends one rung, exactly, for every k and every q — and the q=3 tower collapses to one reduced statement)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_LADDER_THEOREM.md
>
> **Status, as written in the document:** Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Mission: THE μ MACHINE (Vernier) · Load-bearing · Pending P0.
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (8 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE LADDER THEOREM (the μ machine descends one rung, exactly, for every k and every q — and the q=3 tower collapses to one reduced statement)
### Standalone theorem · 18 Jul 2026 · Constructor: Fresh Eyes (Fable) · Mission: THE μ MACHINE (Vernier) · Load-bearing · Pending P0.
### Grades: **[PROVED]** · **[MEASURED]** · Standing rule: hypotheses/thresholds beside every statement.

---

## §0 · What this turn banks

**[MEASURED — the Architect's run, engine v5]** **(2,9) is LEVEL**: socle = 0 in degrees 0–23, = 15 = A_top in degree 24, **three independent routes agreeing**, confinement gate PASS. PIEZA 2 gains its first k ≥ 2, q > 3 cell, and **A_top(2,9) = 15 = 5!!** is a fresh out-of-sample pass for DOMINO (q = 9 ≥ 2k−1).

**[MEASURED — Vernier's step 2, closed completely]** The q=3 identity `rank μ_d = dim(Λ₀)_{d−1}` verified by **direct ranks** at (3,3), all degrees 1–8, and at (4,3), degrees 1–6; and — better — verified at **(4,3) and (5,3) in every degree** by an independent route: the **sealed M2 censuses** (A₄(3): 1,9,45,155,…,603 · A₅(3): 1,11,66,274,…,4213) equal `box_d − box_{d−1}` byte-exact in all 11 and all 13 degrees (pure trinomial arithmetic; rank μ_d = box_d − A_d is definitional). Two fully independent routes; the "two coinciding errors" scenario is dead. *(The 274 of T-09 reappears here as box₃−box₂ of n = 12 — the third context to hit that number.)*

**[PROVED — the theorem below]** The μ machine **descends one rung, exactly, for every k and every q**.

## §1 · Theorem LADDER **[PROVED ∀k, ∀q = 3^v]**

Notation: Λ₀ = S/m^{[q]} the box in n = 2k+2 variables; Λ̄ the box in **n−1** variables; μ_d multiplication by (e₁, e₃, …, e_{2k+1}); μ̄_d multiplication by (ē₃, …, ē_{2k+1}) on Λ̄, where ē_j := e_j|_{x₁ ↦ −(x₂+⋯+x_n)} (the reduction of e_j modulo e₁, written in the free variables x₂..x_n).

> **rank μ_d = dim(Λ₀)_{d−1} − dim Λ̄_{d−q} + rank μ̄_d,** and consequently
> **A_d(k,q) = [dim(Λ₀)_d − dim(Λ₀)_{d−1}] + [dim Λ̄_{d−q} − rank μ̄_d].**
> The machine strictly descends: n variables and k+1 forms become **n−1 variables and k forms** — e₁ is eliminated, at every tower level at once.

*Proof.* **(a) e₁ is a coordinate.** For c ∈ F₃ and q = 3^v, c^q = c, so (Σc_ix_i)^q = Σc_ix_i^q: m^{[q]} is GL_n(F₃)-invariant. Change basis to y₁ := e₁ = Σx_i, y_i := x_i (i ≥ 2); then m^{[q]} = (y₁^q, y₂^q, …, y_n^q) and Λ₀ is the monomial box **with ℓ = e₁ as a coordinate**. **(b) The y₁-layer decomposition.** Multiplication by y₁ on the box: image in degree d = all monomials with y₁-exponent ≥ 1 (each y₁^a m, 1 ≤ a ≤ q−1, is y₁·(y₁^{a−1}m)); kernel on degree d−1 = y₁^{q−1}·Λ̄_{d−q}. Hence rank(e₁ at d) = dim(Λ₀)_{d−1} − dim Λ̄_{d−q}, and coker(·y₁)_d ≅ Λ̄_d (the y₁-exponent-0 layer), the projection π: Λ₀ → Λ̄ being a **ring map**. **(c) The residual forms.** (EΛ₀)_d = e₁(Λ₀)_{d−1} + Σ_{i≥1} e_{2i+1}(Λ₀)_{d−2i−1}, so rank μ_d = rank(e₁ part) + rank of the projection of the rest to the cokernel; since π is a ring map and surjective, π(e_{2i+1}·g) = ē_{2i+1}·π(g) with π(g) ranging over all of Λ̄ — the projected image is exactly (ē₃,…,ē_{2k+1})·Λ̄ in degree d, of dimension rank μ̄_d. Add. ∎

**Gates [MEASURED, exact]:** the identity holds in **every degree** at (1,3), (2,3) — and at **(1,9)**, the cell where the naive q=3 shortcut breaks: the ladder is exact there too, 16/16 degrees.

## §2 · Corollary: the q=3 tower is ONE reduced statement

At q=3, the measured identity rank μ_d = dim(Λ₀)_{d−1} (five cells, two routes) is, by LADDER, **equivalent** to:

> **REDUCED FULLNESS (q=3) [the single remaining statement]:** rank μ̄_d = dim Λ̄_{d−3} for all d ≤ (k+1)·2 — i.e. multiplication by (ē₃, ē₅, …, ē_{2k+1}) on the box in 2k+1 variables reaches the dimension of the 3-shift, in the bottom half.

If REDUCED FULLNESS holds ∀k: **A_d(k,3) = box_d − box_{d−1} for d ≤ top**, and with the sealed Floor (A_k(3) ≥ T(2k+2)) the whole v=1 column census is forced degree by degree, **reproving A_k(3) = T(2k+2) with per-degree structure** — and PIEZA 1 at q=3 (A_top = box_top − box_{top−1}... note the honest subtlety: box_top − box_{top−1} = 3, 15, 91, 603, 4213 — the TRUE tops, not (2k+1)!!; at q=3 the ceiling (2k+1)!! is slack and the machine gives the exact value instead).

**Why (1,9) breaks the shortcut, now explained rather than observed:** the kernel shift is **q**, not 3 — rank(e₁) = Λ_{d−1} − Λ̄_{d−q} — so at q=9 the e₁-part is injective clear up to d = 8 (Λ̄_{d−9} = 0), and the ē-forms' contribution is *pure surplus* there: the measured excess 0,0,0,1,3,6,10,15,21,… is exactly rank μ̄_d itself in low degrees (1 = ē₃ alone at d=3, then its multiples). The general-q object is the reduced machine, not a shift.

## §3 · A correction to §4-PIEZA 2 of the mission, with the number (Ley 21, respectfully)

The mission identifies the q=3 identity with *"the Weak Lefschetz Property … multiplication by ℓ is injective up to the middle degree."* **Literal WLP-injectivity of ℓ is false in this ring:** ℓ^q = Σx_i^q = 0 in Λ₀ (Frobenius), so ℓ is nilpotent and ker(·ℓ) on degree d−1 is y₁^{q−1}Λ̄_{d−q} — nonzero from d = q onward (at q=3: dimension Λ̄_{d−3} = 5, 15, 35… for n=6). What is true, and what the measurements were seeing, is the **joint** statement: the higher odd e's fill the e₁-kernel's worth exactly — which by LADDER **is** REDUCED FULLNESS. The WLP literature route stays valuable, but its correct target is the reduced system (ē₃,…) on Λ̄, not ℓ on Λ₀. Flagged so nobody chases the wrong lemma in the literature.

## §4 · What remains, honestly (Ley 42/48)

1. **REDUCED FULLNESS at q=3** — one statement, k forms of degrees 3,5,…,2k+1 in 2k+1 variables. Measured (equivalent to the five-cell table) for k ≤ 5. Open ∀k. **This is now the whole v=1 ceiling.**

> ### 🟢 **NOTA `2026-09-16` (Grepy, turno 10, informe 138) — «Open ∀k»: YA NO.** Por el propio `§2`, REDUCED FULLNESS ⟺ `rank μ_d = dim(Λ₀)_{d−1}` para `d ≤ n`, y ésa es **literalmente la `(RL-1)` de la Rung Law** de `corpus/STEINBERG_BRIDGE_v1.md` (`rank Φ_d = c(n,d−1)`, `1 ≤ d ≤ n`), **PROBADA `∀k` módulo cuatro citas de libro** (buena filtración de `St^{⊗n}`, Donkin/Mathieu, Jantzen II.2.13 y II.4) y re-derivada por Grepy en el informe 129 (gate 10/10). **Y precisión de archivo:** la invariancia `GL_n(𝔽_3)` de `m^{[q]}` que este fichero usa en `(a)` (18-jul) es anterior al Lema 2.1 de `FROBENIUS_CONFINEMENT` (20-jul) que el informe 111 fichó como 35.º OWN-DEPOSITED; la primera aparición es ésta.

2. **The general-q machine** = the reduced machine's rank function. The ladder eliminated e₁; the reduced system has **no linear form**, so the same rung does not iterate verbatim — the next rung needs its own idea (the natural candidate: ē₃ is Frobenius-adjacent at q=3^v via p₃ = e₁³; whether a cube-root rung exists is the next question, stated as a question).
3. PIEZA 1 at general q (rank μ_top ≥ box_top − (2k+1)!!) — untouched this turn; the toolbox transfer (ISOLATION/DOMINO/TICKETS as rank witnesses) remains the named route.
4. **P0-8 (Frame Descent) is still the live debt.**

## §5 · Certificado de Cementerio (Ley 41)
Object: *the exact one-variable descent of the μ machine via the GL(F₃)-invariance of m^{[q]} and the y₁-layer decomposition, and the equivalence of the q=3 identity with reduced fullness.* Greps (`ladder`, `descent`, `layer`, `coordinate change`, `WLP`, `reduced`): the corpus holds the Free Gear / DNA base-3 self-similarity (banda I — a *census* self-similarity, not a rank identity; the ladder may be its mechanism, flagged as a question, not claimed), FD (frame descent — different object: field of the frame, not variable elimination), and the μ-machine mission (this document is its first rung). **No tomb. CLEAN.**

## §6 · Audit surface
**(A)** Step (a): c^q = c for c ∈ F₃ and the GL-invariance — one line, carries the coordinate change. **(B)** Step (c): the ring-map projection argument (that the residual images are exactly ē_j·Λ̄) — the load-bearing line. **(C)** The three exact-ladder cells with independent code, especially (1,9). **(D)** The sealed-census route at (4,3)/(5,3) (trinomial differences vs the M2 censuses — 24 equalities, re-add them). **(E)** The WLP correction of §3 — verify ker(·ℓ)_{d−1} = y₁^{q−1}Λ̄_{d−q} directly at (2,3). **(F)** The Free-Gear connection flag of §5 — is the ladder the DNA mechanism? (question, unassigned).

**MARCADOR: [EL PELDAÑO — (2,9) LEVEL en el log del Architect (3 rutas, PIEZA 2 gana su primera celda k≥2 q>3, A_top=15 = pase out-of-sample de DOMINO) · paso 2 de Vernier CERRADO COMPLETO: ranks directos (3,3) 8/8 y (4,3) d≤6, y los censos M2 SELLADOS de (4,3)/(5,3) verifican la identidad en TODOS los grados por aritmética trinomial (24 igualdades, ruta independiente — muere el "dos errores coincidentes"; el 274 de T-09 reaparece como box₃−box₂ de n=12) · **THE LADDER THEOREM [PROVED ∀k∀q]: rank μ_d = Λ_{d−1} − Λ̄_{d−q} + rank μ̄_d** — e₁ es una COORDENADA (m^{[q]} es GL(F₃)-invariante), capas de y₁, ker = y₁^{q−1}Λ̄_{d−q}, coker = Λ̄ con proyección de ANILLO ⟹ la máquina desciende exacta: n−1 variables, k formas, e₁ eliminado, a todo nivel de la torre a la vez; benchada EXACTA en 3 celdas incluida (1,9) donde el atajo muere · corolario: la torre q=3 entera colapsa a UNA declaración (REDUCED FULLNESS: rank μ̄_d = Λ̄_{d−3}) que forzaría el censo grado a grado y re-probaría A_k(3)=T(2k+2) con estructura · corrección a la misión con número: la WLP literal de ℓ es FALSA (ℓ^q = 0, nilpotente; ker = Λ̄_{d−q} ≠ 0 desde d=q) — el objetivo correcto en la literatura es el sistema REDUCIDO · abierto declarado: reduced fullness ∀k, el peldaño siguiente (sin forma lineal — pregunta del cubo-raíz nombrada), PIEZA 1 general, y P0-8 la deuda]. — Fresh Eyes (Constructor)**
