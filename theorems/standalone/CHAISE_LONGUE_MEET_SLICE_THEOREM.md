> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE MEET & SLICE THEOREMS (the gluing loses NOTHING: the image of E on each slice is PRINCIPAL, the meet of the two families is EXACTLY the zero-blocks, and the entire nilradical is relocated into ONE identity between letter Hilbert series)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MEET_SLICE_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Vidocq (Fable) · Turn W13 · Four deliveries. (S) THEOREM SLICE, pencil: the image of the odd ideal on each pair-slice is PRINCIPAL — `E·O(W₂^{(cd)}) = (x_c)·O(W₂^{(cd)})` — one line: `ē₁ ≡ −t mod E′`. Verified 5/5 by machine. (M) THEORE…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE MEET & SLICE THEOREMS (the gluing loses NOTHING: the image of E on each slice is PRINCIPAL, the meet of the two families is EXACTLY the zero-blocks, and the entire nilradical is relocated into ONE identity between letter Hilbert series)
### 21 Jul 2026 · Constructor: **Vidocq** (Fable) · Turn W13 · **Four deliveries. (S) THEOREM SLICE, pencil: the image of the odd ideal on each pair-slice is PRINCIPAL — `E·O(W₂^{(cd)}) = (x_c)·O(W₂^{(cd)})` — one line: `ē₁ ≡ −t mod E′`. Verified 5/5 by machine. (M) THEOREM MEET, pencil, characteristic-free: `W₁ ∩ W₂ = ⋃ zero-blocks` EXACTLY, ∀k — a multiset count (`#\{t\} = 2+a > a = #\{−t\}` forbids `t ≠ 0`). (L) THE LOCALIZATION, measured and decisive: at `N=4`, all degrees 3–6, `dim(E·O(W₂))_d = dim I(ZB)_d − dim I(W₂)_d` byte-exact (`10/16/22/28` on both sides) — equivalently **`E + I(W₂) = I(ZB)` in every measured degree: the Mayer–Vietoris sum of the two radical ideals IS the radical of their meet. The gluing of `E` across the slices is LOSSLESS; there is NO gluing defect.** (R) THE RELOCATION: the entire nilradical is now `Nil_d = T_k(d) − [\dim I(ZB)_d − \dim I(W₂)_d]` — one identity between three letter-series. Plus: `σ₅(3) = 90` byte-exact against TANDA7's filed head (free cross-validation of R45 below its proven threshold), and the sealed prediction `σ₅(4) = 173`.**

**Certificate (Ley 41):** consumes R41–R46, T1 (certified import, R46), TANDA7 heads (filed values, cited as gates only). Instruments examined per the mission: the **D1 method stands down with honor** — there is nothing to glue (measured lossless); the **T1-regularity bound stands down with its line written** — regularity (Derksen–Sidman type) cuts from ABOVE (agreement in degrees ≥ reg), my statement lives BELOW; wrong direction, stated. The instrument that fits what remains is the CENSUS machinery itself (stratified letters). Panel: Macaulay, Whitney (the multiset count).

---

## 1. Theorem SLICE (the image of `E` on a slice is principal)

> On each pair-slice `O_{cd} = F₃[t] ⊗ S′/E′` (Theorem P of R46): **`E·O_{cd} = (t)·O_{cd}`**, hence `Hilb(E·O_{cd}) = t·∏_{i=1}^{k−1}[2i−1]_t/(1−t)^k`.

*Proof.* `ē_j = e_j|_{x_d=x_c} = e′_j + 2t\,e′_{j−1} + t²e′_{j−2}`. In `O_{cd}` the odd `e′` vanish, so for odd `j`: `ē_j ≡ −t\,e′_{j−1}` (char 3: `2 = −1`). In particular `ē₁ ≡ −t`, so `(t) ⊆ E·O_{cd}`; and every `ē_j ∈ (t)`. ∎ *(Machine: `dim(E·O_{cd})_d = d` at `N=4`, `d = 1..5`, 5/5.)*

**Reading:** on the doubled part, the whole odd ideal collapses to ONE coordinate — the doubled value `t`. The slice-wise image of `E` is as simple as an ideal can be.

## 2. Theorem MEET (`W₁ ∩ W₂` = the zero-blocks, ∀k, characteristic-free)

> The plain part meets the doubled part EXACTLY in the zero-blocks:
> **`W₁ ∩ W₂ = ⋃_{c<d} \{x_c = x_d = 0\} × Z_{k−1}(rest∖\{c,d\})`.**

*Proof.* Take a `W₂` point: `x_c = x_d = t`, rest on a lamina (pairs `(y_i, −y_i)`). Suppose it lies on a full matching (a `W₁` lamina) and `t ≠ 0`. Count coordinates by value: the value `t` occurs `2 + a` times and the value `−t` occurs `a` times, where `a` is the number of rest-pairs with `y_i = ±t` (each such pair contributes one of each; pairs with `y_i ≠ ±t` contribute neither). A full matching must pair every value-`t` coordinate with a value-`(−t)` coordinate (`t + t = 2t ≠ 0` since `t ≠ 0`, char ≠ 2), which requires `2 + a ≤ a` — impossible. Hence `t = 0`, which is precisely a zero-block point. ∎

**Consequence.** `E + I(W₂) ⊆ I(W₁ ∩ W₂) = I(ZB)` always — the sum of the two radical ideals sits under the radical of the meet, with the zero-blocks (`(x_c, x_d) + E′`, radical by disjoint variables + R1) as the meet's exact ideal.

## 3. The Localization (measured, decisive): **the gluing is LOSSLESS**

At `N = 4`, all degrees `3..6`, byte-exact:

| `d` | `\dim I(ZB)_d − \dim I(W₂)_d` | `\dim(E·O(W₂))_d` (actual) | budget `T_k(d)` | `Nil_d` |
|---|---|---|---|---|
| 3 | **10** | **10** | 10 | 0 |
| 4 | **16** | **16** | 19 | 3 |
| 5 | **22** | **22** | 30 | 8 |
| 6 | **28** | **28** | 42 | 14 |

> **The first two columns agree in EVERY degree — including the degrees where the nilradical is nonzero.** Equivalently, `\dim(E + I(W₂))_d = \dim I(ZB)_d` with the containment of §2: **`E + I(W₂) = I(ZB)` in every measured degree. The Mayer–Vietoris sum closes; the image of `E` on `W₂` is EXACTLY the functions vanishing on the zero-blocks; the gluing of `E` across the `C(2k,2)` slices loses NOTHING, anywhere.**
> **Therefore the nilradical is NOT a gluing phenomenon.** The mission's two instruments answer as follows: `D1`'s machinery has no defect to measure here (stands down with honor); regularity cuts from above while the statement lives below (stands down with its line). **The loss is entirely in the budget's other term.**

## 4. The Relocation — what `B(d)` is now

Granting §3's identity (measured 4/4; its proof — the sum-radicality `E + I(W₂) = I(ZB)` — is the new named sub-statement, with §2 supplying the containment and the variety):

> ## `Nil_d = T_k(d) − \big[\dim I(ZB)_d − \dim I(W₂)_d\big]`,
> so **`B(d)` ⟺ `\dim I(ZB)_d − \dim I(W₂)_d = T_k(d)` for `d < N−1`** — an identity between THREE series of REDUCED unions of letter-cylinders: `T_k` (closed form, R46), `I(W₂)` (the doubled-part union: pair-slices, each solved by Theorem P), and `I(ZB)` (the zero-block union: `(x_c,x_d)+E′`, each solved by disjointness + T1). **The two unknown series are stratified-letter censuses — exactly the domain of the campaign's census machinery (`STRATIFIED_CENSUS`, `ZETA`: `Z_m` = full census one dimension down). No new mathematics is required to compute them: only the lattice bookkeeping the campaign already owns.**

**Honest scope:** the sum-radicality is measured at `N=4` only (all its degrees); it is the FIRST thing to gate at `N=6` next turn, before any use. The relocation identity above is exact bookkeeping given it.

## 5. The free cross-validation and the sealed predictions

- **`σ₅(3) = \dim R_3 + \dim R_1 = 83 + 7 = 90`** — **byte-exact against TANDA7's filed head at `e=5`.** A validation of R45's `σ₅` law at `n = 8`, BELOW its proven threshold `n ≥ 12`: evidence the threshold is not sharp (recorded, not claimed).
- `σ₄` anchors: `29` (`k=3`) ✓ and `46` (`k=4`) ✓ against A22's filed values.
- **`σ₆(3) = 232 ≠ 252` (filed head)** — CONSISTENT: `n = 8` is below `σ₆`'s threshold `n ≥ 14`; the filed `252` is a pre-stable head value. **The head/stable boundary is visible in the data, exactly where the thresholds put it.**
- **SEALED (before any machine):** `σ₅(4) = \dim R_3 + \dim R_1` at `n = 10` `= 164 + 9 = 173`.

## 6. Status and inventory notes

- **PROVEN this turn:** SLICE (§1) · MEET (§2, char-free).
- **MEASURED, decisive:** the lossless-gluing identity (§3, 4/4) and the relocation (§4).
- **OPEN, named:** (α) sum-radicality `E + I(W₂) = I(ZB)` beyond `N=4` (gate at `N=6` first); (β) the two letter series `Hilb\,I(W₂)`, `Hilb\,I(ZB)` and the identity of §4. **The collar was NOT opened** — the mission's conditional (`si satura`) did not trigger: the budget statement narrowed (enormously) but did not fall.
- **Inventory note for the Auditor:** `TANDA7`, `EIGENVECTOR_LAW`, `FI_STABILITY` arrived from the Architect's DOWNLOADS — a THIRD location. Bertillon's «15/15 no existen en reto-reto» stands compatible; the reconciliation line should now read three locations, not two.

## 7. Attack surface for the Auditor

(A) SLICE's one line (`ē_j ≡ −t e′_{j−1}`; check the char-3 coefficient). (B) MEET's multiset count (the `2+a > a` step; the `t+t ≠ 0` step; degenerate pairs `y_i = 0`). (C) Reproduce the §3 table (four evaluation ranks at `N=4`). (D) Gate §3's identity at `N=6` (the first task of W14). (E) The relocation bookkeeping (`\dim(E·O(W₂)) = \dim(E+I(W₂)) − \dim I(W₂)`). (F) The `σ₅ = 90` cross-check and the `σ₆` boundary reading against TANDA7's head list.

**MARCADOR: [EL PEGADO NO PIERDE — ★ Theorem SLICE (lápiz): `E·O(rebanada) = (t)` PRINCIPAL, 5/5 · ★ Theorem MEET (lápiz, char-free, ∀k): `W₁∩W₂ = bloques cero` EXACTO — cuenta de multiconjuntos `2+a > a` · ★★ LA LOCALIZACIÓN (medida, 4/4 byte-exact): `dim(E·O(W₂)) = dim I(ZB) − dim I(W₂)` en TODO grado medido ⟹ **`E+I(W₂) = I(ZB)`: la suma Mayer–Vietoris CIERRA, el pegado es SIN PÉRDIDA, no existe defecto de pegado** — D1 se retira con honor (nada que pegar) y la regularidad se retira con su línea (corta por arriba, el enunciado vive por abajo) · ★★ LA REUBICACIÓN: `Nil_d = T_k(d) − [dim I(ZB)_d − dim I(W₂)_d]` — `B(d)` es UNA identidad entre TRES series de letras, y las dos desconocidas son censos estratificados: dominio de la maquinaria que la campaña YA posee · `σ₅(3)=90` clava contra la cabeza archivada de TANDA7 (validación gratis de R45 bajo umbral) · sellado: `σ₅(4)=173` · collar NO abierto (el condicional no disparó) · SIN GRITO]. — Vidocq (Constructor, Fable), turno W13**
