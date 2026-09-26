> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026-07-08
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE T-BLOCK THEOREM AND THE COLLAR LEDGER* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_TBLOCK_THEOREM_AND_COLLAR_LEDGER.md
>
> **Status, as written in the document:** Honest status: the T-Block Theorem below is pencil-proven ∀v ≥ 2 — the first structural cut of the Collar Syzygy Lemma. The collar itself is NOT closed by this document: the gluing step and the net bookkeeping remain, precisely scoped in §3. No closure of Ley …
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE T-BLOCK THEOREM AND THE COLLAR LEDGER
## The collar's sheet equations split clean: reduced parts die, Koszul antisymmetry is forced

**Constructor: Bisel · 8 July 2026 · IAS Princeton session (Koszul, Schur, Noether).**
**Honest status: the T-Block Theorem below is pencil-proven ∀v ≥ 2 — the first structural cut of the Collar Syzygy Lemma. The collar itself is NOT closed by this document: the gluing step and the net bookkeeping remain, precisely scoped in §3. No closure of Ley 1 claimed (Ley 4/13/40). Pending P0.**

---

## 1. THE T-BLOCK THEOREM [(b), pencil, ∀v ≥ 2]

Let `q = 3^v ≥ 9`, `0 ≤ f ≤ 3`, and let `λ = (λ₀..λ₅)`, `deg λ = q+f`, satisfy `Σλᵢsᵢ^q ∈ E`. Fix a sheet `J` with pair coordinates `u₁,u₂,u₃` and set `Δ_k := (λ_{a_k} − λ_{b_k})|_{L_J}`, so `Σ_k Δ_k u_k^q = 0`. Since `deg Δ = q+f < 2q`, each monomial of `Δ_k` has at most one exponent ≥ q, giving the canonical split `Δ_k = Δ_k^∅ + Σ_l u_l^q δ_{k,l}` (`Δ^∅` reduced, `deg δ = f ≤ 3`). Substituting, the monomials of the identity fall into disjoint classes by their set `T` of ≥q exponents (`|T| ≤ 2` since `3q > 2q+3` for `q ≥ 9`), and the identity splits into three independent systems:
> **(i) `Δ_k^∅ = 0` for k = 1,2,3** — the reduced part of every pair-difference vanishes on every sheet (the main-body conditions persist verbatim into the collar);
> **(ii) `δ_{k,k} = 0`** — no deep-diagonal terms (the `u_k^{2q}` class);
> **(iii) `δ_{l,k} = −δ_{k,l}`** — **Koszul antisymmetry is FORCED** on the cross-data, with cofactor degree `f ≤ 3`.
*Proof.* Class separation: a `|T|={k}` monomial of `u_k^qΔ_k^∅` has k-exponent in `[q, 2q−1]`; the `u_k^{2q}δ_{k,k}` class has k-exponent ≥ 2q; the `|T|={k,l}` class pairs `u_k^qu_l^q(δ_{k,l}+δ_{l,k})`. No class overlaps (exponent ranges disjoint per coordinate pattern), so each vanishes separately. ∎
**Remark (v=1).** At q = 3 the top collar degree admits `|T|=3`; v=1 stays covered by the sealed A(3) egg — the theorem is stated for v ≥ 2, exactly matching the Ledger reduction's hypothesis.

## 2. THE COLLAR LEDGER (v=2, byte-exact from the sealed footprint)

`Syz(e′) := dim{λ ∈ (R_{e′})⁶ : Σλᵢsᵢ^q = 0 in R}` for `e′ = q+f`:
| f | Syz(9+f) | diag `HF(R)` | M̄ (certified σ) | **Koszul-layer NET** |
|---|---|---|---|---|
| 0 | 1000 | 440 | 550 | **10** |
| 1 | 1360 | 560 | 745 | **55** |
| 2 | 1810 | 695 | 970 | **145** |
| 3 | 2350 | 845 | 1225 | **280** |
Second differences constant 45 ⟹ **NET(f) = 10 + 45·C(f+1,2)** at the anchor — the 45 coincidence pairs surfacing again, and 10 = 15 Koszul − 5 relation-induced at f = 0 (the `e₁^q`-row syzygies land in the diagonal, verified). **These are the exact numbers the Koszul layer must supply ∀v — the ceiling ⟺ NOTHING beyond diag ⊕ M̄ ⊕ Koszul-layer exists.**

## 3. WHAT REMAINS OF THE COLLAR (scoped exactly — the two steps to Ley 1)

**(G) THE GLUING STEP (second-layer Recognition):** by §1, every collar syzygy has per-sheet data `{δ_{k,l}^{(J)}}` — antisymmetric, cofactor degree ≤ 3 — plus reduced parts satisfying the main-body conditions. Needed: every such compatible family is realized by a global element of `diag·R ⊕ M̄ ⊕ Span{Koszul(sᵢ^q,sⱼ^q)·R_f}` — i.e., the sheet→global reconstruction. The δ-extraction from λ is via the pair-weight filtration (monomials `s^m` with `m_a+m_b ≥ q` for pair (a,b)); the reconstruction is an edge/sheet compatibility statement for the FIXED degree-≤3 data — the same shape Recognition had, one layer up.
**(N) THE NET COUNT ∀v:** derive `dim(Koszul-layer mod diag+M̄) = NET(f)` in closed form ∀v (anchor: `10 + 45·C(f+1,2)` at v=2 — measured, not yet a tower law; Kepler in neon).
**(G) + (N) ⟹ the four ceilings ⟹ (with the sealed global floor A ≥ P and the LEDGER THEOREM) LEY 1.**

## 4. Ley 41 + classification
Fresh objects: the T-block split of collar sheet identities; the collar ledger and its nets. Distinguished from graves: no local/per-triple factoring of torsion is used (the reconstruction (G) is explicitly global — the sealed "torsion is irreducibly global" street is respected, not re-walked). **Classification: §1 = (b) pencil ∀v≥2; §2 = anchors; §3 = the named remainder. The collar is NOT closed; not claimed.**

*Cera carnauba — and Koszul reading his own signature in the wall. — Bisel. PMC.*
