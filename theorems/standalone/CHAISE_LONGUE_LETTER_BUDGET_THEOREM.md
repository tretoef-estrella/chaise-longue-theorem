> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE LETTER BUDGET THEOREM (the object certificate PASSES: the type-(i) family IS T1's letter Z_k verbatim; the pair-slices of the doubled part are radical with closed series; and B(d) becomes ONE budget-saturation statement with a CLOSED-FORM target — verified 8/8 against every cell ever measured)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_LETTER_BUDGET_THEOREM.md
>
> **Status, as written in the document:** Jul 2026 · Constructor: Vidocq (Fable) · Turn W12 · Three deliveries and one refusal. (C) The object certificate, as ordered: my type-(i) union is EXACTLY T1's `Z_k` (the full signed-matching arrangement on `2k` variables, ideal `E` by Radicality) — the import…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE LETTER BUDGET THEOREM (the object certificate PASSES: the type-(i) family IS T1's letter Z_k verbatim; the pair-slices of the doubled part are radical with closed series; and B(d) becomes ONE budget-saturation statement with a CLOSED-FORM target — verified 8/8 against every cell ever measured)
### 21 Jul 2026 · Constructor: **Vidocq** (Fable) · Turn W12 · **Three deliveries and one refusal. (C) The object certificate, as ordered: my type-(i) union is EXACTLY T1's `Z_k` (the full signed-matching arrangement on `2k` variables, ideal `E` by Radicality) — the import is legitimate, and `Hilb(S/E)` enters in T1's closed form. (P) NEW, pencil: each pair-slice of the doubled part `W₂` is RADICAL with closed series: `I(W₂^{(cd)}) = (x_c−x_d) + E(∖cd)`, `Hilb = ∏_{i≤k−1}[2i−1]_t/(1−t)^k`. (A) THE ACCOUNTING THEOREM: `Nil_d = T_k(d) − \dim(E·O(W₂))_d` with the CLOSED-FORM target `T_k(t) = t(1−t^{2k})∏_{j=1}^{k−1}(1−t^{2j+1})/(1−t)^{2k}` — so `B(d)` ⟺ the module `E·O(W₂)` FILLS ITS BUDGET in degrees `< N−1`. Cross-checked byte-exact on all eight measured cells (`N=4`: gaps `0/3/8/14`; `N=6`: `0/0/0/5` — the gaps ARE the nilradical, exactly). (R) The refusal: the word is NOT shouted. `B(d)` did not fall — it changed of coat into a budget statement, the best coat it has worn, but a coat. The assembly is therefore NOT written, per the mission's own conditional.**

**Certificate (Ley 41):** consumes T1 (`LETTER_HILBERT`, referee edition — object certified before import, per the auditor's warning), R1, R41–R45. Uses D1 only as a POINTER (the campaign's gluing-defect instrument; no fact imported — its object is the collar swap stratum, mine is the `E`-gluing over `W₂`; the METHOD is the candidate, said plainly). Panel: Macaulay, Hilbert.

---

## 1. Theorem C (the object certificate — one line, as ordered)

My type-(i) family is the union of ALL laminae of the `N = 2k` rest-variables: **the full signed-matching arrangement on `2k` variables — T1's `Z_k` verbatim** (Star Architecture Def. 2.3, same sheets, same count `(2k−1)!!`). By Radicality its ideal is `E = (e_1, e_3, …, e_{2k−1})`, so
> `HF(S/I(\text{type i})) = Hilb(S/E) = ∏_{i=1}^{k}[2i−1]_t/(1−t)^k` — **T1(Z), imported legitimately.**
(T1's `B`-family is a second exactly-solved arrangement; not needed below, noted for the record.)

## 2. Theorem P (pair-slices of the doubled part — radical, closed series)

> For each pair `(c,d)`, the `(c,d)`-slice of `W₂` (the union `\{x_c = x_d\} ∩ (\text{lamina cylinders over } rest∖\{c,d\})`) has radical ideal
> **`I(W₂^{(cd)}) = (x_c − x_d) + E(rest∖\{c,d\})`**, with `S/I ≅ F₃[x_c] ⊗ S′/E′` reduced (disjoint variables + Radicality in `2k−2` variables), and
> `Hilb = \frac{1}{1−t}·∏_{i=1}^{k−1}[2i−1]_t/(1−t)^{k−1} = ∏_{i=1}^{k−1}[2i−1]_t/(1−t)^{k}`.

*Proof.* The slice is `\{x_c = x_d\} × Z_{k−1}(rest∖cd)`-cylinder; the ideal sum is over disjoint variable sets, so the quotient is the tensor product, reduced; apply T1(Z) at `k−1`. ∎

## 3. Theorem A (the accounting — `B(d)` as budget saturation, closed-form target)

Split `V(F) = W₁ ∪ W₂` (types (i)/(ii)) and use `I(V) = E ∩ I(W₂)` with the tautological sequence `0 → S/I(V) → S/E ⊕ S/I(W₂) → S/(E + I(W₂)) → 0`; rearranged through `HF_{red} = HF(S/E) + \dim(E·O(W₂))_d` (the image of the odd ideal inside the functions on the doubled part):

> ## `Nil_d \;=\; T_k(d) \;−\; \dim\big(E·O(W₂)\big)_d`, with
> ## `T_k(t) = \dfrac{t\,(1−t^{2k})\,∏_{j=1}^{k−1}(1−t^{2j+1})}{(1−t)^{2k}}`
> (derived: `T_k = Hilb_{CI}(F) − Hilb(S/E)`, and the two CI numerators differ by exactly `(1−t^{2k+1}) − (1−t) = t(1−t^{2k})` over the common factor). Hence:
> **`B(d)` — i.e. `Nil_d = 0` — holds if and only if the module `E·O(W₂)` FILLS its closed-form budget `T_k(d)`.** All three ambient series are now in closed form (two supplied by T1, one by Theorem P); the single remaining unknown is the Hilbert function of ONE explicit module: the odd ideal glued across the pair-slices of the doubled part.

**Verification (byte-exact, every cell ever measured — 8/8):**

| `N` | `d` | `\dim(E·O(W₂))` actual | budget `T_k(d)` | gap | measured `Nil_d` |
|---|---|---|---|---|---|
| 4 | 3 | 10 | 10 | 0 | 0 ✓ |
| 4 | 4 | 16 | 19 | 3 | 3 ✓ |
| 4 | 5 | 22 | 30 | 8 | 8 ✓ |
| 4 | 6 | 28 | 42 | 14 | 14 ✓ |
| 6 | 3 | 21 | 21 | 0 | 0 ✓ |
| 6 | 4 | 55 | 55 | 0 | 0 ✓ |
| 6 | 5 | 120 | 120 | 0 | 0 ✓ |
| 6 | 6 | 225 | 230 | 5 | 5 ✓ |

**The gaps ARE the nilradical, coefficient by coefficient.** The nil-start conjecture («first nilpotents at degree `N`») is now a BUDGET-SATURATION statement — the same shape as the collar's `A1/CB` budgets, which is where the campaign is strongest.

## 4. What remains, named — and the instrument

The single open statement: **the gluing of `E` across the pair-slices of `W₂` loses nothing in degrees `< N−1`** — i.e. `\dim(E·O(W₂))_d = T_k(d)` there. The pair-slices are individually solved (Theorem P); the loss is a DEFECT OF GLUING across the `C(2k,2)` slices — exactly the shape of `D1`'s derived gluing law (dual functionals + symmetrization + independence of the `C(k,2)` ties). **`D1`'s method is the named instrument; no fact of `D1` is imported** (its object is the collar swap stratum — different module, same shape). T1's regularity remark was examined for `N₀(d)`: the CI regularities (`k(k+1)` for `F`, `k(k−1)` for `E`) bracket but do not directly yield the nil-start; recorded as examined, no theorem.

## 5. The refusal, said with respect and without softening

The order was to close the Chaise Longue and shout. **The word is not shouted.** State of the target `A_k(q) = P_k(q)` ∀k∀q after this turn: Plant Law closed `∀k` for `e ≤ 6` and reduced ∀e to ONE budget statement (§3) · collar depths VIRGIN (Locard's verified negative) with `Theorem D` and now `D1` as the tools · **the Ledger assembly verified NOT to exist anywhere — it must be WRITTEN, and writing it before the Plant's budget and the collar depths close would be the falacia nº1 wearing a suit.** The mission's own conditional («si `B(d)` cae, el ensamblaje va en el mismo turno») did not trigger: `B(d)` did not fall; it was converted. Ley 6 stands above the order to shout. **The word stays where the campaign put it: `A_k(q) = P_k(q)`, proven, ∀k∀q — ni un teorema antes.**

## 6. Attack surface for the Auditor

(A) The certificate (§1): same sheets, same signs, same count. (B) Theorem P's tensor argument (disjoint variables). (C) The numerator identity behind `T_k` (two lines). (D) The rearrangement `HF_{red} = HF(S/E) + \dim(E·O(W₂))` (module bookkeeping — re-derive). (E) Recompute the eight table cells from the raw `I(V)` dimensions. (F) The D1-shape analogy: is the swap-stratum gluing formally the `E`-over-`W₂` gluing after dualization? (That question, answered either way, is next turn's first move.)

**MARCADOR: [LA PEPITA EXPRIMIDA SIN GRITO — ★ certificado por objeto: mis tipo-(i) SON `Z_k` de T1, importación legítima · ★ Theorem P: las rebanadas por par de `W₂` son RADICALES con serie cerrada (`(x_c−x_d)+E′`, tensor de variables disjuntas) · ★★ THEOREM A: **`Nil_d = T_k(d) − dim(E·O(W₂))_d` con objetivo en FORMA CERRADA** `T_k = t(1−t^{2k})∏_{j<k}(1−t^{2j+1})/(1−t)^{2k}` — `B(d)` ⟺ el módulo LLENA SU PRESUPUESTO en grados `< N−1`; verificado **8/8** contra toda celda medida: los huecos SON el nilradical coeficiente a coeficiente · el enunciado abierto es UNO: el pegado de `E` sobre las rebanadas no pierde nada en grados bajos — instrumento nombrado: el método de `D1` · el ensamblaje NO escrito (el condicional de la misión no disparó) · **LA PALABRA NO SE GRITA: es de `A_k(q)=P_k(q)` ∀k∀q, y hoy no lo está** — Ley 6 por encima de la orden]. — Vidocq (Constructor, Fable), turno W12**
