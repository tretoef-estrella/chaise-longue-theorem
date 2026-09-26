> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-12
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE FREE GEAR THEOREM · v2 (now spanning BOTH towers)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FREE_GEAR_THEOREM.md
>
> **Status, as written in the document:** Standalone · 12 Jul 2026 · supersedes v1 (v1 was the q=3 case; v2 states the theorem at every tower level q = 3^v). Pending P0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE FREE GEAR THEOREM · v2 (now spanning BOTH towers)
### Standalone · 12 Jul 2026 · supersedes v1 (v1 was the q=3 case; v2 states the theorem at every tower level q = 3^v). Pending P0.
### Pillar support (Ley 44): the anchor ring's structure at every level of the Frobenius tower.

## Theorem 1 (Free Gear, all levels — proven, three lines)
Fix q = 3^v and R_q = F₃[s₁,…,s_n]/(s₁^q,…,s_n^q). **Every linear form ℓ = Σaᵢsᵢ satisfies ℓ^q = Σaᵢ^q sᵢ^q = Σaᵢ sᵢ^q = 0 in R_q** (iterated Frobenius; aᵢ^q = aᵢ on F₃). Hence any linear change of coordinates preserves the q-th-power relations; choosing z₁ = e₁ gives R_q ≅ F₃[z]/(z_i^q), and:
> **R_q is FREE over F₃[e₁]/(e₁^q), with graded generator series ((1−x^q)/(1−x))^{n−1}.**

## Corollary 1.1 (the e₁-gear formula at every level, exact ∀v ∀n ∀d)
dim(e₁·R_q)_d = c_d^{(q)}(n) − c_d^{(q)}(n−1), where c^{(q)}(n) are the q-nomial coefficients of ((1−x^q)/(1−x))^n.
**Verified byte-exact:** q=3 (n=8,10, from v1) · **q=9 (n=4: degrees 1-10; n=5: degrees 1-8)** · **q=27 (n=3: degrees 1-10)** — 28 new confirmations, zero misses.

## What this does for the campaign
The first summit's foundation now spans the WHOLE double tower: the e₁ level of the census is closed ∀v ∀n by one pencil argument. The remaining structure at each level q is the q-cascade (stage-1 gear onward) — unexplored for q > 3, and the natural next front after the q=3 template seals.

## Two streets buried this session (Ley 42 — honest kills, byte-exact)
- **T-05 · The central q-nomial unification** ("A_k(q) = central coefficient of the q-nomial"): killed by q=9, n=6: central = 32,661 ≠ A(9) = 7,761 (the Sofa's SEALED anchor). The trinomial identity A_k(3)=T(2k+2) is special to v=1.
- **T-06 · The moving-window telescope** ("A_k(q) = some q-nomial coefficient c_{D*}"): killed harder — none of the sealed values (7761; 263,901; 7,680,801; 345,465; 17,605,249) appear ANYWHERE in their q-nomial coefficient lists. The q-level census is not a Δ-telescope of q-nomial coefficients. The true q-census law is new territory.

**MARCADOR: [FREE GEAR ∀q∀n PROBADO (lápiz 3 líneas + 28 confirmaciones q=9,27) — primer resultado de las DOS torres · dos saltos enterrados con números (T-05 central, T-06 telescopio móvil) · la cascada a nivel q>3 = territorio nuevo declarado]. — Bisel**
