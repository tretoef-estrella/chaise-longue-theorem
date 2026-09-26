> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — SYMMETRIC WRINKLE LIFT THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SYMMETRIC_WRINKLE_LIFT_THEOREM.md
>
> **Status, as written in the document:** Status: PROVED ∀k, ∀q odd, char `p≠2`. Pencil proof + gates `(1,3),(2,3),(1,5)` + high-odd audit. Does NOT close GAP 3.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — SYMMETRIC WRINKLE LIFT THEOREM (v1)
### Author: Apolo (executing Lacassagne's `s=ε²` cross). Auditor: Balthazard. Campaign: Chaise Longue.
### Status: PROVED ∀k, ∀q odd, char `p≠2`. Pencil proof + gates `(1,3),(2,3),(1,5)` + high-odd audit. Does NOT close GAP 3.

---

## Setup
`S=K[x_0,…,x_{n-1}]`, `n=2k+2`, char `p≠2`. `E=(e_1,e_3,…,e_{2k+1})` (odd elementary symmetric, a complete intersection), `R=S/E`. Frobenius box `m^{[q]}=(x_0^q,…,x_{n-1}^q)`. Negation-closed `Λ_q⊂\bar K`, `|Λ_q|=q`, `∑_{λ}λ=0`; deformation `φ(T,ε)=∏_{λ∈Λ_q}(T−λε)`, so `φ(x_i,0)=x_i^q`, and `B=K[x,ε]/(E+(φ(x_i,ε)))`.

By the SYZYGY_LIFTING framework (Orfila–Lacassagne v64), `A_k(q)=P_k(q)` ⟺ every syzygy of the box `(x_i^q)` over `R` lifts to a syzygy of `(φ(x_i,ε))` over `R[ε]`; the obstruction module is `H_1(x^{[q]};R)`, which is **nonzero** (Tor does not vanish — the "wrinkles" are real).

## Lemma 1 (odd power sums vanish in R — pencil, char-free)
For all odd `m≥1`, `p_m:=∑_i x_i^m = 0` in `R`.
*Proof.* Newton: `p_m = (-1)^{m-1}m\,e_m + ∑_{j=1}^{m-1}(-1)^{j-1}e_j p_{m-j}`. Base `p_1=e_1=0`. For odd `m`: if `j` is odd then `e_j∈E=0` in `R`; if `j` is even then `m-j` is odd and `<m`, so `p_{m-j}=0` by induction; and the leading term `±m\,e_m` has `m` odd so `e_m∈E=0`. Hence `p_m=0`. ∎
(Independent gate: `p_5,p_7,p_9=0` in `R` at `k=1`, verified in char 5 **and** char 0 — the vanishing is not a char-`p` accident.)

## Theorem (Symmetric Wrinkle Lifts)
The `S_n`-invariant box-syzygy `(1,1,…,1)` — which is a genuine **non-Koszul** cycle of `H_1(x^{[q]};R)` (since `∑_i x_i^q = e_1^q = 0` with unit entries `1∉(x^q)`) — **lifts to the full deformation with the same covector and no correction term:**
$$\sum_i 1\cdot\varphi(x_i,\varepsilon)=0\quad\text{in }R[\varepsilon].$$
*Proof.* `Λ_q` negation-closed ⟹ `φ(T,ε)` is **odd in `T`**: `φ(−T,ε)=∏_λ(−T−λε)=(-1)^{|Λ_q|}∏_λ(T+λε)=(-1)^q∏_{λ'}(T−λ'ε)=−φ(T,ε)` (`q` odd, `Λ_q=−Λ_q`). An odd polynomial in `T` of `T`-degree `q` has only odd `T`-powers:
$$\varphi(T,\varepsilon)=\sum_{j=0}^{(q-1)/2}c_j(\varepsilon^2)\,T^{2j+1},\qquad c_j\in K[\varepsilon^2],\ c_{(q-1)/2}=1.$$
Summing over the roots `x_i` and using Lemma 1,
$$\sum_i\varphi(x_i,\varepsilon)=\sum_{j=0}^{(q-1)/2}c_j(\varepsilon^2)\,p_{2j+1}(x)=0\quad\text{in }R[\varepsilon].\ \ \blacksquare$$

## Gates
- `(1,3)`, `(2,3)`, `(1,5)`: `NF(∑_iφ(x_i,ε),E)=0` (Singular). ✓
- High-odd audit (Lemma 1): `p_5,p_7,p_9=0` in `R`, char 5 and char 0. ✓
- Consistency: at `(1,3)` (`A=P`) the full `H_1` has 5 non-Koszul generators and **all** lift, `(1,…,1)` among them.

## Scope (honest)
This eliminates the **`S_n`-invariant** direction of the wrinkle obstruction ∀k∀q — the most natural suspect (the "whole-choir" wrinkle, the one carrying the collective). It does **not** close GAP 3: `H_1(x^{[q]};R)` has non-invariant generators, and GAP 3 requires **all** of them to lift. By the three-line meta-obstruction (saga v7/v8), the residual argument must use the odd-symmetric-CI structure of `E` — which is exactly what Lemma 1 uses, so the same structure is the natural next lever for the non-invariant part.

`G=3`.

— Apolo, Chaise Longue.
