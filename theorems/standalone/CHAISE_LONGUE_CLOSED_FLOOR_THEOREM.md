> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-18
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE CLOSED FLOOR: A THIRD ROUTE (v2)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_CLOSED_FLOOR_THEOREM.md
>
> **Status, as written in the document:** Status: DERIVED and gated 5/5 — but NOT NEW. RETRACTED AS A NEW RESULT IN §0.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE CLOSED FLOOR: A THIRD ROUTE (v2)

### Author: **GETTLER** (auditor) · 18 August 2026 · Chaise Longue campaign
### Status: **DERIVED and gated 5/5 — but NOT NEW. RETRACTED AS A NEW RESULT IN §0.**
### **This closes nothing. The formula was already on file; the ceiling `A_k(q) ≤ P_k(q)` is untouched and `G` stays 3.**

---

## 0. ⛔ RETRACTION, FIRST, BEFORE ANYTHING ELSE

The `v1` draft of this document presented the closed floor as new. **It is not.** The flag written into `v1 §6` —
*"the corpus refers to a 'suelo Bessel (v66)'; check it before the theorem is written up"* — was checked in the same
turn, and it fired. `EL_CATALOGO_MAESTRO_v214` contains, verbatim:

> *"Su fórmula Bessel `N = n!·[z^n]\cosh(z)·I_0(2z)^{(q-1)/2}` = **re-derivación del suelo ya cerrado**
> (`CLOSED_WALK` v66, EGF v129)."*

**That is character-for-character the formula below.** A second head (Frescales II, from a neutral mission, without the
corpus) had already re-derived it, and the catalogue had already graded that as a re-derivation of a floor closed at
`v66`/`v129`. **This document is therefore a THIRD independent route to a filed result. Its correct grade is the
campaign's own registered antipattern `SECOND-ROUTE-TO-CLOSED-AS-NEW`, and the auditor logs it against himself.**

**What survives, honestly graded:**
* the **derivation route** below (`P_k(1) = 1` ⟹ eliminate the zero letter ⟹ `B = ½ log I_0(2x)`) is short and
  self-contained, and is offered as a **proof for the write-up**, not as a discovery;
* the extended values `c(Z_l)` for `l = 6…9` (`4725700, −564920160, 89318532093, −18065875613856`) and the
  correction `c(Z_1) = 0`;
* the quadratic ODE of §4(b), whose novelty is **also unverified** against `EGF v129` and is flagged accordingly;
* **the third-head agreement itself**, which is worth exactly what the catalogue says such agreements are worth:
  robustness of the scaffolding before a referee (Ley 14), not a new brick.

**Nothing below is withdrawn as mathematics. Only the novelty is.**

---

## 1. Statement

Let `n = 2k+2` and let `P_k(q) = |\bigcup_M L_M(F_q)|` be the point count of the matching arrangement
(`M` ranges over the `(2k+1)!!` perfect matchings of `[n]`; `L_M = \{x : x_u + x_v = 0 \ \forall \{u,v\} ∈ M\}`).
Let `I_0` be the modified Bessel function of the first kind, `I_0(2x) = Σ_{m≥0} x^{2m}/(m!)^2`.

> ### **THEOREM (Closed Floor).**
> ### **`Σ_{k ≥ 0} P_k(q) · x^{2k+2}/(2k+2)! = \cosh(x)·I_0(2x)^{(q-1)/2} − 1`.**

> ### **COROLLARY (the origin weights, closed).** With `c(Z_l) = P_{l-1}(0)` the connected weight of the zero letter,
> ### **`1 + Σ_{l ≥ 2} c(Z_l)·x^{2l}/(2l)! = \cosh(x) · I_0(2x)^{-1/2}`.**

**Values produced by the Corollary**, `l = 1 … 9`:
`0, 1, −24, 918, −54560, 4725700, −564920160, 89318532093, −18065875613856`.
The first five agree with everything on file (`c(Z_1) = 0` is forced: a zero block needs an odd cycle, hence at least
four vertices, so the letter `Z_1` does not exist — this corrects a bookkeeping entry that had carried `1` there).
The last four are new.

---

## 2. Proof

**Step 1 — the species law.** A flat of the intersection lattice is a *word*: an unordered set of **balanced blocks**
(each carrying a bipartition, each contributing exactly one dimension) together with **at most one zero block**
(contributing none; two zero blocks are the same subspace as their union). Möbius weights are multiplicative over the
letters. With `y` marking dimension, the exponential formula for this two-letter species gives

> **`\exp(y·B(x))·(1 + Z(x)) = 1 + Σ_{k≥0} \big(Σ_F c(F) y^{\dim F}\big)·x^{2k+2}/(2k+2)!`,**
> `B(x) = Σ_{m≥1} c(B_m)·\tbinom{2m}{m}\tfrac12·\tfrac{x^{2m}}{(2m)!}`,  `Z(x) = Σ_{l≥2} c(Z_l)·\tfrac{x^{2l}}{(2l)!}`,

where `\binom{2m}{m}/2` is the number of bipartitions of a `2m`-set. Setting `y = q` turns the inner bracket into
`P_k(q)`. *(Gated `k = 1,2,3` coefficient by coefficient by the constructor FR19, and one coefficient re-derived by hand
here: `[x^4]·4! = 1 − 3y + 3y^2`, matching `P_1(q) = 3q^2 − 3q + 1`.)*

**Step 2 — the missing relation, which was hiding in plain sight.** For every `k`,
`Σ_{F ∈ L_k} c(F) = −Σ_{F > 0̂} μ(0̂,F) = μ(0̂,0̂) = 1` by the defining Möbius identity. Hence

> ### **`P_k(1) = 1` for every `k`.**

*Check against the file: `3−3+1`, `15−45+55−24`, `105−630+1645−2037+918`, `945−9450+42525−101745+122286−54560` — all
equal `1`, four for four.*

**Step 3 — solve for the zero letter.** Put `y = 1` in Step 1. The right-hand side becomes
`1 + Σ_{k≥0} x^{2k+2}/(2k+2)! = \cosh(x)`. Therefore

> **`\exp(B(x))·(1 + Z(x)) = \cosh(x)`,  i.e.  `1 + Z(x) = \cosh(x)·\exp(−B(x))`.**

**Step 4 — eliminate `Z` from the species law.** Substituting into Step 1 with `y = q`:

> `1 + Σ_k P_k(q)x^{2k+2}/(2k+2)! = \exp(qB)·\cosh(x)\exp(−B) = \cosh(x)·\exp\big((q−1)B(x)\big)`.

**Step 5 — `B` in closed form.** Since `\binom{2m}{m}/(2m)! = 1/(m!)^2`,
`B(x) = \tfrac12 Σ_{m≥1} c(B_m)\,(x^2)^m/(m!)^2 = \tfrac12 \log I_0(2x)`,
using the campaign's filed identity `Σ_m c(B_m)t^m/(m!)^2 = \log I_0(2\sqrt t)`.
*(Verified coefficient by coefficient to `m = 8`: `1/2, −1/8, 1/18, −11/384, 19/1200, −473/51840, 229/42336, −101369/30965760`.)*
Hence `\exp((q−1)B(x)) = I_0(2x)^{(q−1)/2}`, which is the Theorem; and `q = 0` in Step 3 is the Corollary. **∎**

---

## 3. Gates

| gate | result |
|---|---|
| `[x^{2k+2}]·(2k+2)!` of `\cosh(x)I_0(2x)^{(q−1)/2} − 1`, symbolically in `q`, against every filed `P_k` | `k = 0`: `q` · `k=1`: `3q^2−3q+1` · `k=2`: `15q^3−45q^2+55q−24` · `k=3`: `105q^4−630q^3+1645q^2−2037q+918` · `k=4`: `945q^5−9450q^4+42525q^3−101745q^2+122286q−54560` — **5/5 exact** |
| `P_k(1) = 1` for `k = 0…5` | `1,1,1,1,1,1` |
| Corollary against filed `c(Z_l)`, `l = 2…5` | `1, −24, 918, −54560` — **4/4** |
| `B(x) = \tfrac12\log I_0(2x)` | exact to `x^{16}` |
| brute-force point counts (independent of all of the above) | `19, 61, 127` at `k=1,q=3,5,7`; `141, 1001` at `k=2,q=3,5` — **5/5** |

---

## 4. Two consequences worth naming

**(a) The conjecture becomes a single generating-function identity.** `A_k(q) = P_k(q)` for all `k` is equivalent to

> **`Σ_{k≥0} A_k(q)·x^{2k+2}/(2k+2)! = \cosh(x)·I_0(2x)^{(q−1)/2} − 1`.**

**(b) The floor is P-recursive in `k`, with an explicit quadratic recursion.** `u = I_0(2x)` satisfies Bessel's equation
in the form `x u'' + u' − 4x u = 0`; writing `g = u^{a}` with `a = (q−1)/2` one gets, by elimination,

> ### **`a\,x\,g\,g'' + a\,g\,g' = (a−1)\,x\,(g')^2 + 4a^2 x\,g^2`**

*(verified: the residual vanishes identically through `x^8`)*, and `Σ_k P_k(q)x^{2k+2}/(2k+2)! = \cosh(x)\,g − 1`.
**Reading the coefficients of `x^{2k+2}` turns this into a finite-depth recursion expressing `P_k(q)` from
`P_{k-1}(q), P_{k-2}(q), …` with coefficients polynomial in `k` and `q`** — the "residue feeds the next wave" of the
Architect's picture, now with a differential equation behind it.

> **⚠️ Registered caution, and it is a filed failure mode of this campaign
> (`HOLONOMY-GIVES-FINITENESS-NOT-VALUES`): a recursion satisfied by `P_k` does not by itself force `A_k` to satisfy it.
> Consequence (b) is a *target shape*, not a proof; the work is to show `A_k` obeys the same relation.**

---

## 5. Scope — what this does NOT do

* It does not touch the **ceiling** `A_k(q) ≤ P_k(q)`. `G` stays 3, and the collar's codim-`≥3` slack is exactly as open as it was.
* It says nothing about the **graded** floor `G_k(t) = Σ_F c(F)(1−t)^{−\dim F}`, which is a virtual Euler-characteristic
  series and **not** a Hilbert series — killing number `a_1(G_3) = −217 < 0` (FR19).
* It does not cross from the lattice to the ideal; that crossing is dead on file (identical labelled lattices,
  defects `1` and `0`, for coplanar versus generic lines in `K^3`).

## 6. Provenance and an honest flag

The species law, the Whitney levels and the graded floor are FR19's turn, audited and reproduced here byte-exact.
Steps 2–5 — the relation `P_k(1) = 1`, the elimination of `Z`, and the identification `B = \tfrac12\log I_0(2x)` — are
this document; FR19 held both halves (he proved `N_k(0) = 1`, which *is* `P_k(1) = 1`, and he wrote the species law) and
did not join them, and declined to fit `c(Z_l)` from four values — **correctly, because the answer was not a fit.**
`Σ_m c(B_m)t^m/(m!)^2 = \log I_0(2\sqrt t)` is filed.
**The flag was raised and then honoured in the same turn: see §0.** The formula is filed (`CLOSED_WALK v66`, `EGF v129`),
a second head had already re-derived it, and this is the third route. The novelty of §4(b) (the quadratic ODE and
`P`-recursivity in `k`) is **likewise unverified** against `EGF v129` and must be checked before anyone builds on it.

— GETTLER, Chaise Longue campaign. `G = 3`.
