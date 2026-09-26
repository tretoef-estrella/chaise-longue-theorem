> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — ROUND 7: THE BITE — THE PLANT LAW IS A THEOREM (FI-stability of the census, pencil)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ROUND7_FI_THEOREM.md
>
> **Status, as written in the document:** |---|---|
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — ROUND 7: THE BITE — THE PLANT LAW IS A THEOREM (FI-stability of the census, pencil)
### Round 7 of 10 · 12 Jul 2026 · Constructor: Cárdano (Fable) · Fine Hall: Noether, Hilbert, Schur, Church–Ellenberg–Farb; Kepler as standing sceptic · Prompt: Bisel's MORDISCO · Pending P0.
### THE BITE LANDS: the census is a co-FI-module, its dual is a finitely generated FI-module, and σ_e(k) is EVENTUALLY POLYNOMIAL in n=2k+2 for every fixed e — the plant law is now a THEOREM in the k-direction, by pencil, with the load-bearing step machine-verified. NO SHOUT: three named links remain (the e-direction, the annihilator census, the Ledger assembly). Bisel's "one FI theorem away" is corrected on the record.

## 0. THE TRAP CAUGHT FIRST (Ley 21; Bisel's own advice #6)
Bisel's prompt says the FI theorem alone closes the window. **Not exactly.** Even with FI sealed, the chain to A=P has three more links: (i) the e-direction (FI gives k-direction with e FIXED; the window needs e up to q−1, growing with q — the bivariate law is a regularity statement, not an FI one); (ii) the annihilator census (the high zone of A, the ∀k analogue of the Sofa's Thm 3.1); (iii) the collar/Ledger assembly. Caught and named BEFORE building, so no one — including me — mistakes today's bite for the KO.

## 1. THE FUNCTORIALITY (Noether's answer — and the direction that works)
The naive direction (extend syzygies to more variables) FAILS: partial elementary symmetrics of a subset do not lie in the larger edge ideal. The correct direction is CONTRAVARIANT: **restriction, setting the new variables to zero.** The load-bearing fact: elementary symmetrics restrict cleanly — ε_j(B′∖{a,b})|_{x_new=0} = ε_j(B∖{a,b}) — so the edge ideal of B′ restricts INTO the edge ideal of B, and every window syzygy of B′ restricts to one of B.
> **Machine verification (anchor n=8 → n=6, e=4):** every element of M₄(8) restricts into M₄(6): rank(B₆ ∪ restricted images) = rank(B₆) = 456 — WELL-DEFINED, exact. (Image rank 447 < 456: not surjective; the theory does not require it.)
**The census is a co-FI-module** (a contravariant functor on finite sets of even cardinality with injections).

## 2. THE THEOREM (pencil, complete)
> **Theorem (FI-stability of the window census).** For each fixed e ≥ 0, the function k ↦ σ_e(k) agrees, for all k ≥ k₀(e), with a polynomial in n = 2k+2 of degree ≤ e+1.
*Proof.* (1) V_e(B) := M_e(B) is contravariantly functorial by §1. (2) V_e = ker(W_e → U_e) with W_e(B) = ⊕_{b∈B} S(B)_e (free layer) and U_e(B) = ⊕_{edges} S(B)_e/I({a,b})_e (edge constraints), both co-FI, the map natural (restriction commutes with differences and with the edge quotients — §1). (3) Dualizing levelwise (finite dimensions over F₃): V_e^* = coker(U_e^* → W_e^*), a QUOTIENT of the FI-module W_e^*. (4) W_e^* is the FI-module of degree-e monomials with a marked coordinate: finitely generated in FI-degree ≤ e+1 (a degree-e monomial involves ≤ e variables, plus the mark). (5) Quotients of finitely generated FI-modules are finitely generated; hence V_e^* is a f.g. FI-module over F₃. (6) By FI-noetherianity and eventual polynomiality over an arbitrary field (Church–Ellenberg–Farb–Nagpal), dim V_e(B) is eventually polynomial in |B|, of degree ≤ the generation degree. The trivial syzygies form a co-FI-submodule (the diagonal and E^n both restrict correctly — ε's again); its dual quotient statement dualizes to a f.g. FI-submodule by noetherianity, so σ_e = dim V_e − dim(trivials) is eventually polynomial as well. ∎
**The plant is a theorem:** the same plant, at every dimension — the multiplicium bookkeeping stabilizes; only the stem (first row) grows. The Architect's metaphor, now with a proof attached in the k-direction.

## 3. WHAT THE THEOREM GIVES AND DOES NOT GIVE (honest, on the record)
**Gives:** eventual polynomiality of σ_e(k) in n for each e; a degree bound (≤ e+1); the structural explanation of the blind prediction's success; and — enunciable corollary of the METHOD — the same co-FI argument applies verbatim to the ANNIHILATOR census α_c(k) (its constraints are also restriction-functorial: the same ε-restriction), so the high zone has the same stability skeleton (to be developed, Round 8).
**Does not give:** (a) the COEFFICIENTS per e — with degree bound e+1, three Kepler points do NOT pin the polynomial for e=4 (degree ≤5 needs 6 points); σ₄(k) = 2+(n−1)+n(n−3)/2 remains a blind-prediction-sealed CANDIDATE, ∀k-sealed only if the degree bound is sharpened (the measured Specht bodies have |λ̄| ≤ 2, suggesting true degree 2 — measured, not proven) or more points are computed; (b) the e-direction and the bivariate law (regularity, not FI); (c) the closure assembly (annihilator law + collar + Ledger). Failure-mode note: claiming the closed formula ∀k from 3 points + degree-5 bound would be Kepler-as-closure — refused.

## 4. SCORECARD
| Item | Status |
|---|---|
| Co-FI functoriality of the census | **✓ pencil + machine-verified (456=456)** |
| FI theorem: σ_e(k) eventually polynomial in k, ∀e | **✓ PENCIL — the plant law is a THEOREM (k-direction)** |
| Same skeleton for the annihilator census | ✓ enunciated (development = R8) |
| Closed formula σ₄(k) ∀k | candidate (blind-prediction-sealed); degree bound too coarse to pin with 3 points — honest |
| e-direction / bivariate law · annihilator law · Ledger assembly | **OPEN — the three named links (R8-R9)** |
**NO SHOUT (Ley 13).** The plant became a theorem today — the deepest structural bite of the campaign — but the chain to A=P has three named links standing. Bisel: your "one FI theorem away" is corrected on the record; the FI theorem fell TODAY, and the map now shows exactly three more bridges. The hand stays on the holster.

**MARCADOR: [ROUND 7 GANADO GORDO — EL MORDISCO: la ley de la planta es TEOREMA a lápiz en la dirección k (censo = co-FI-módulo por restricción x↦0 con las elementales restringiendo limpio — VERIFICADO 456=456; dual = cociente de FI-módulo libre f.g.; noetherianidad CEFN char-p ⟹ σ_e(k) eventualmente polinómico en n, grado ≤ e+1) · el mismo esqueleto aplica al censo del anulador (enunciado, R8) · HONESTO: la fórmula cerrada de σ₄ sigue candidata (cota de grado e+1 demasiado gruesa para 3 puntos — cantar ∀k sería Kepler-como-cierre); la dirección e, el anulador y el Ledger son los TRES eslabones restantes, nombrados · corrección al prompt de Bisel en acta ("a un teorema FI" → "FI + tres puentes") · SIN GRITO — la mano en la culata]. — Cárdano (Fable), Round 7**
