> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — ROUND 6: THE PLANT LAW — the census is representation-stable, sealed by a BLIND PREDICTION (σ₄(4) = 46 ✓)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_ROUND6_PLANT_LAW.md
>
> **Status, as written in the document:** |---|---|
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — ROUND 6: THE PLANT LAW — the census is representation-stable, sealed by a BLIND PREDICTION (σ₄(4) = 46 ✓)
### Round 6 of 10 · 12 Jul 2026 · Constructor: Cárdano (Fable) · Fine Hall: Schur, Weyl, Frobenius, Noether, Cayley · Plan: 10_ROUNDS v2 + Bisel's R5 response (the Architect's plant) · Pending P0.
### The Architect's plant metaphor IS representation stability. The census decomposes into Specht families with UNIVERSAL multiplicities; the pre-stable artifact of k=2 identified; and the law made a BLIND prediction — σ₄(k=4) = 46 — confirmed exact by independent computation. NO SHOUT: the T-window has not fallen entire; the law of e=4 is sealed by prediction, the bivariate law and the pencil of universality remain.

## 1. THE TRANSLATION (Weyl's answer to the Architect's plant)
Rafa's image — *"the same plant: old parts stretch, new fruits appear when conditions allow"* — is **representation stability** (Church–Ellenberg–Farb). A stable Specht family is λ = [n−|λ̄|, λ̄]: the body λ̄ is fixed (the plant's identity), the first row grows with n (the stem stretching). A family bears fruit only when n is large enough for λ̄ to fit. The plant hypothesis, made exact:
> **THE PLANT LAW (working form).** σ_e(k) = Σ_{λ̄} m_{λ̄}(e) · dim S^{[n−|λ̄|, λ̄]}(S_n), with multiplicities m_{λ̄}(e) UNIVERSAL — independent of k — once n is in the stable range. Hence σ_e(k) is polynomial in n = 2k+2 of degree |λ̄|_max(e), with small-n values as pre-stable exceptions.

## 2. THE SPECHT DECOMPOSITIONS — CERTIFIED BY THREE INTEGER TRACES
Method: integer traces of the transposition, double transposition, AND triple transposition on M_e/trivials (eigenspace splits over F₃; all three permutations have order 2, clean in char 3). Murnaghan–Nakayama tables computed fresh.
| (k, e) | σ | decomposition (3-trace certified) |
|---|---|---|
| (2, 4) | 25 | **2·S^[6] ⊕ S^[5,1] ⊕ 2·S^[4,2]** — the Sofa's claim, now confirmed by a THIRD independent route (traces 11, 5, 7 all match) |
| (3, 4) | 29 | **2·S^[8] ⊕ S^[7,1] ⊕ 1·S^[6,2]** — unique solution, all three traces match (17, 9, 5) |
**The botanical reading:** family λ̄=∅ (trivial): multiplicity 2 at both; λ̄=[1] (standard): multiplicity 1 at both; **λ̄=[2]: multiplicity 2 at n=6 but 1 at n=8.** The extra copy of [4,2] at k=2 is a PRE-STABLE artifact of small dimension — exactly the Architect's "plant in poor conditions stretches only what it has." The stable multiplicities at e=4 are **(m_∅, m_[1], m_[2]) = (2, 1, 1)**.
Validation en passant: dim M₄(k=2) = 456 = the Sofa's sealed HF_M value ✓.

## 3. THE BLIND PREDICTION — THE ROUND'S SEAL
The stable law at e=4 gives the closed form σ₄(k) = 2 + (n−1) + n(n−3)/2 for n ≥ 8. **Prediction made BEFORE measuring: σ₄(k=4) = 2 + 9 + 35 = 46.**
> **Measured (independent census computation, n=10, 178s): σ₄(4) = 46. EXACT. ✓✓✓**
This is the double-prediction standard of the Sofa's point-count pillar, reproduced for the census law: the law predicted a number it had never seen, and the machine confirmed it. Kepler standing at e=4: pre-stable point (n=6, decomposed), two stable points (n=8 decomposed, n=10 predicted-then-measured). Bisel's corner note (third k=4 point before any ∀k claim) is SATISFIED for e=4 by this direct route.

## 4. WHAT THE PLANT LAW NOW GIVES (and what it does not)
**Gives:** the FORM of the bivariate census law — σ_e(k) is a sum of stable Specht dimensions with k-independent multiplicities, hence polynomial in n for n large, with computable pre-stable corrections. Sealed instances: e=2 (m_∅=1, k≥2 — the Newton class, pencil); e=3 (m_[1]=1 — the standard class, pencil mechanism); e=4 (m=(2,1,1) stable, sealed by blind prediction).
**Does not give (honest, Ley 42/48):** (a) e ≥ 5 undecomposed — σ₅(2)=70, σ₅(3)=90 measured but their Specht contents unknown (next: 3-trace analysis at (2,5), then predict-and-test (3,5) and beyond); (b) the PENCIL of universality — why multiplicities are k-independent (the FI-module functoriality of the edge conditions: to be constructed — this is the remaining pencil of the plant); (c) the final link census-law → T_window = 0 (the assembly, Rounds 7-8).

## 5. SCORECARD
| Item | Status |
|---|---|
| Plant = representation stability (translation) | ✓ exact frame |
| Specht decomposition (2,4), (3,4) | ✓ 3-trace certified, unique |
| Pre-stable artifact of k=2 identified | ✓ the extra [4,2] |
| **Blind prediction σ₄(4)=46** | **✓ CONFIRMED EXACT — the round's seal** |
| e ≥ 5 decompositions · FI-pencil · census→T link | OPEN (named exact) |
**NO SHOUT.** The plant law is sealed at e=4 by the strongest evidence short of a theorem — a confirmed blind prediction — but the T-window has not fallen: e≥5 stands, the universality pencil stands, the assembly stands. The shout stays holstered; the hand has never gripped it tighter.

**MARCADOR: [ROUND 6 GANADO GORDO — LA LEY DE LA PLANTA: el censo es representation-stable (la metáfora de Rafa, hecha teorema de trabajo) · descomposiciones Specht certificadas con TRES trazas enteras: σ₄(2)=2·triv⊕std⊕2·[4,2] (el Sofá confirmado por tercera vía), σ₄(3)=2·triv⊕std⊕[6,2] (única) · la copia extra de k=2 = artefacto PRE-ESTABLE (la planta en malas condiciones) · **PREDICCIÓN CIEGA CONFIRMADA: σ₄(4)=46 EXACTO** — el sello doble-predicción del Sofá, repetido · forma de la ley bivariada: multiplicidades universales ⟹ σ_e(k) polinómico en n · ABIERTO: e≥5, el lápiz FI de la universalidad, el ensamblaje censo→T · SIN GRITO — la mano más apretada que nunca en la culata]. — Cárdano (Fable), Round 6**
