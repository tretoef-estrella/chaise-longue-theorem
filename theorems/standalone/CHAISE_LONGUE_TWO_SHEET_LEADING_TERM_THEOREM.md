> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-25
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE TWO-SHEET LEADING-TERM THEOREM, AND THE DISTRIBUTIVITY DICHOTOMY* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_TWO_SHEET_LEADING_TERM_THEOREM.md
>
> **Status, as written in the document:** Constructor: Bisel · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd, over `F_q`
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE TWO-SHEET LEADING-TERM THEOREM, AND THE DISTRIBUTIVITY DICHOTOMY
### The pairwise fold, proved for all `k` and all `q`; and the distributivity route, proved sufficient and then buried with its number
### Constructor: **Bisel** · 25 August 2026 · Pending P0 · char `K ≠ 2`, `q` odd, over `F_q`

**Certificado Ley 41.** Objects: (1) `\operatorname{in}_w` of an intersection of two sheet-point ideals; (2) the distributivity of the lattice of box ideals. Cemetery grep by object **and by number**: the pairwise fold is in the corpus as **MEASURED** (`SHEET_NERVE §3`, `66 = 66`, `k=1,2`, char 0; and twice more in `CEMENTERIO_LIVE`), never proved; the distributivity of `⋂_J(I_J+m^{[q]}) = E+m^{[q]}` is recorded as *«distributivity, which in general FAILS»* (`JOYA 2`) — **but not with the number below, and not in the strong form**. `249` and `252` return **NADA** in a distributivity context.

---

## 0. Setting
`a_J := I(L_J(F_q)) = I_J + (x_i^q − x_i)` (radical) · `A_J := I_J + m^{[q]}` · `w` = the standard degree filtration · `D(X) := \dim_K S/X`.

## 1. The sums degenerate perfectly
> **THEOREM 0 (`∀k`, `∀q`, `∀W`).** For any set `W` of sheets, with `I_W := Σ_{J∈W}I_J` and `L_W := ⋂_{J∈W}L_J`:
> ### `\operatorname{in}_w\big(I_W + (x_i^q − x_i)\big) = I_W + m^{[q]}`.

*Proof.* `S/I_W ≅ F_q[y_1,…,y_m]` with `m = \dim L_W`, and the images of the `x_i` are linear forms spanning the dual. By **Frobenius linearity**, `(Σa_iy_i)^q = Σa_i^q y_i^q`, so the ideal `(x_i^q)` becomes `(y_1^q,…,y_m^q)`. Hence both sides have colength `q^m = |L_W(F_q)|`; one contains the other; they are equal. ∎ **Gate 7/7** (`n=4`, all seven nonempty `W`).

## 2. The pairwise theorem
> **THEOREM 1 (`∀k`, `∀q`).** For any two sheets, `\operatorname{in}_w(a_J ∩ a_{J'}) = A_J ∩ A_{J'}`.

*Proof.* For **any** two ideals the sequence `0 → S/(u∩v) → S/u ⊕ S/v → S/(u+v) → 0` is exact, so `D(u∩v) = D(u)+D(v)−D(u+v)`. Apply it to `(a_J,a_{J'})` and to `(A_J,A_{J'})`. By Theorem 0, `D(A_J)=D(a_J)`, `D(A_{J'})=D(a_{J'})`, and `\operatorname{in}_w(a_J+a_{J'}) = A_J+A_{J'}` (their sum is `I_{JJ'}+(x^q−x)`), so `D(A_J+A_{J'}) = D(a_J+a_{J'})`. Hence `D(a_J∩a_{J'}) = D(A_J∩A_{J'})`. Since `\operatorname{in}_w(a_J∩a_{J'}) ⊆ A_J∩A_{J'}` and the two quotients have equal dimension, they coincide. ∎

> **This raises the corpus's `66 = 66` from MEASURED (`k=1,2`, char 0) to PROVED for all `k` and all odd `q`.**

## 3. The distributivity dichotomy
> **THEOREM 2 (conditional, `∀k∀q`).** If the box ideals satisfy `A_J + ⋂_{J'≠J}A_{J'} = ⋂_{J'≠J}(A_J + A_{J'})`, then `A_k(q) = P_k(q)`.

*Proof (induction on the number of sheets).* Base: Theorem 0. Step: put `R = ⋂_{J≥2}a_J`. **On the point side distributivity is free** — `S/(x^q−x)` is a product of fields, its ideals are the **subsets**, and the lattice of subsets is distributive — so `a_1+R = ⋂_{J≥2}a_{\{1,J\}}`, an intersection of `m−1` ideals of the same species; by induction `\operatorname{in}_w(a_1+R) = ⋂_{J≥2}(A_1+A_J)`, which by hypothesis equals `A_1 + ⋂_{J≥2}A_J = \operatorname{in}_w(a_1)+\operatorname{in}_w(R)`. Then all three terms of the two-ideal sequence match and Theorem 1's argument applies. ∎

**The criterion is the right object.** In the three-concurrent-lines toy of `SHEET_NERVE §3` — where the corpus measures defect `0` with two lines and `1` with the third — **distributivity fails at degree `1`, exactly the degree where the defect is born.**

> ### **THEOREM 3 (the burial).** The hypothesis of Theorem 2 is **FALSE**. In the strong form the induction requires (full complement, 14 sheets), at `k=2`, `q=3`, degree `5`:
> ### **`\dim\big(A_1 + ⋂_{J≥2}A_J\big) = 249` versus `\dim ⋂_{J≥2}(A_1+A_J) = 252`.**
> Degrees `0–4` agree (`0,3,15,49,120`) and degree `6` agrees (`462`). **And `k = 2` is a deposited dimension where `A=P` holds.** Hence distributivity is **not necessary**, and cannot prove the conjecture. *(Loose triples also fail: `(0,5,10)` at `d=1,2,3`; `(3,8,14)` at `d=1`.)*

## 4. Corollary — no sheet-by-sheet induction can work
The `2 → 3` step by the route of Theorem 1 requires triple distributivity, which Theorem 3 buries. Moreover the failure is **not hereditary in either direction**:

| object | `k=2, d=1` | `k=2, d=5` |
|---|---|---|
| triple `(0,5,10)` | **fails** | — |
| all 15 sheets | **holds** (`3=3`) | **fails** (`249≠252`) |

> **Triples fail where the whole family works, and the whole family fails where triples work.** No order of adding sheets avoids broken intermediate states. *This re-derives the campaign's Global Principle in leading-term language, with the obstruction named: box distributivity.*

## 5. Scope
Theorems 0–3 and the corollary are **PROVED** for all `k`, all odd `q`, char `≠ 2` (Theorem 3 is a burial by explicit computation at one cell). Nothing here proves `A_k(q)=P_k(q)`.

— **Bisel**, Chaise Longue campaign
