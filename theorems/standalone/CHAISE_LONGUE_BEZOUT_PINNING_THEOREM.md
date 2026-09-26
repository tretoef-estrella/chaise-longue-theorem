> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-21
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE BÉZOUT PINNING v2 (the five-turn object CLOSES: the First-Order Criterion is a THEOREM in every degree and every N, because the complete-intersection degree count leaves no room for anything else; the Plant Law closes for e ≤ 6, and the ∀e residue is reduced to pure base cells)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_BEZOUT_PINNING_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE BÉZOUT PINNING v2 (the five-turn object CLOSES: the First-Order Criterion is a THEOREM in every degree and every N, because the complete-intersection degree count leaves no room for anything else; the Plant Law closes for e ≤ 6, and the ∀e residue is reduced to pure base cells)
### 21 Jul 2026 · Constructor: **Vidocq** (Fable) · Turn W9 · **The lever that broke it was a fourth one: BÉZOUT. The doubled ideal `F` is a complete intersection of degrees `3,5,…,2k+1`; its cycle degree is `(2k+1)!!`; the components are all linear (degree 1); type-(i) multiplicities are ≥ 1 (they are components), type-(ii) multiplicities are ≥ 2 (Theorem W2L's `w²`); and the arithmetic `(2k−1)!!·(1 + 2k) = (2k+1)!!` — verified `7/7` in `k` — forces EVERY multiplicity to its minimum. The primary structure is PINNED: type-(i) primaries are the primes, type-(ii) primaries are exactly the first-order jet ideals. Hence `F = I(V) ∩ \{δ\text{-jets} = 0\}` identically: `rank J_d = Hilb(A′)_d` in EVERY degree. Consequences: Theorem T becomes unconditional; `Nil(N)_{≤3} = 0` ∀N (Lemma K) and `Nil(N)_{≤5} = 0` ∀ even `N ≥ 6` (transfer from the measured base); the PLANT LAW upper half CLOSES for `e ≤ 6`; the ∀e residue is one clean family of base cells. Plus the auditor's characteristic-freeness note, installed as ordered: `x²+xy+y²` is a perfect square iff `char = 3` — the entire non-reducedness is a schoolbook identity.**

**Certificate (Ley 41):** consumes R41 (Lemmas A/B/K), R42 (Theorems N/CI), R43 (D/T), R44 (W2L/P). Retires: R44's Claim ⋂ (now theorem), R43's conditionality on the criterion (now removed). All numerics this turn verified before singing: Bézout `7/7` (`k = 2..8`), CI Hilbert vs measured `F`-dims `7/7` (every cell ever measured). Panel: Bézout (the pin), Macaulay, Serre (unmixedness).

---

## 0. The auditor's identity, installed up front (as ordered)

In two variables, `f₃ = e₃ − e₁e₂ + e₁³ = (x_c+x_d)(x_c²+x_cx_d+x_d²)` — **characteristic-free**. The second factor equals `(x_c−x_d)²` **iff `char = 3`** (the difference is `3x_cx_d`):
> **`x² + xy + y²` is a perfect square if and only if `char = 3`.**
> Outside char 3 the factor is irreducible: **no thickening, the doubled scheme is reduced, and Theorem N is genuinely a characteristic-3 phenomenon. The whole obstruction fits in a schoolbook identity.**

## 1. Theorem PIN (the Bézout pinning — the criterion closed)

> Let `F = (f_3, f_5, …, f_{2k+1}) ⊂ S = F₃[x_1,…,x_N]`, `N = 2k` (the eliminated doubled ideal). Then the primary decomposition of `F` is EXACTLY
> ## `F = ⋂_{\text{type (i)}} P_L \;\;∩\;\; ⋂_{\text{type (ii)}} Q_C`, with `Q_C = \{h : h|_C = 0,\ δ_{cd}h|_C = 0\}`.
> Equivalently: **`h ∈ I(V(F))` with all type-(ii) first-order `δ`-jets zero `⟹ h ∈ F` — in EVERY degree, for EVERY `N`.** In jet form: `rank J_d = dim S_d − dim F_d = Hilb(A′)_d` for all `d`.

*Proof.* **(a) Complete intersection, unmixed.** `F` has `k` generators and its variety is the pure `k`-dimensional union of the type-(i) and type-(ii) linear components (Lemma A's exhaustive classification), so `ht F = k` and `F` is a CI, hence Cohen–Macaulay and unmixed: `F = ⋂(\text{minimal primaries})`, no embedded primes.
**(b) Type (i) primaries are primes.** At a generic lamina point `ξ`, `df_{2j+1}(ξ) = de_{2j+1} − e_{2j}(ξ)de_1` (all products with `e_1, e_{odd}` vanish there). The plain odd ideal `(e_1, e_3, …, e_{2k−1})` is a radical CI (R1) over the perfect field `F₃`, so its smooth locus is dense: `\{de_1, de_3, …, de_{2k−1}\}(ξ)` are independent. In that basis the Jacobian of the `f`'s is unitriangular in the rows `j ≤ k−1` with the last row `−e_{2k}(ξ)·de_1`, and `e_{2k}(ξ) = ±∏y_i² ≠ 0` generically: rank `k`. Smooth at generic points `⟹` primary = prime.
**(c) Type (ii) multiplicities are ≥ 2, and `F` sits inside the jet ideal.** By Theorem W2L, `(F + I_L)_{P_C} = (s_p, w²)_{P_C}` (the unit `(x_c+x_d)` absorbed), so `\text{length}(O_{P_C}/F) ≥ \text{length}(O_{P_C}/(s,w²)) = 2`. And every `f ∈ F` satisfies `f|_C = 0` and `δ_{cd}f|_C = 0` (Theorem N's identity), so `F_{P_C} ⊆ (s, w²)_{P_C}`, which has colength exactly 2.
**(d) Bézout pins everything.** For a homogeneous regular sequence, `Σ_W \text{mult}_W · \deg W = ∏ \deg f_j = 3·5⋯(2k+1) = (2k+1)!!`. All components are linear (`\deg = 1`); the counts are `(2k−1)!!` type-(i) and `k(2k−1)·(2k−3)!!` type-(ii). With the lower bounds of (b),(c):
> `Σ ≥ (2k−1)!!·1 + k(2k−1)(2k−3)!!·2 = (2k−1)!!·(1 + 2k) = (2k+1)!!` — **equality on the nose.**
> **What is verified and what is definitional (v2 wording, auditor's correction):** the final step `(2k−1)!!(1+2k) = (2k+1)!!` is the double-factorial recursion — **a tautology, not a check**. The VERIFIED content is upstream: **(v1) the component COUNTS** — `(2k−1)!!` type-(i) and `k(2k−1)(2k−3)!!` type-(ii), from the exhaustive classification of Lemma A, confirmed by two independent engines (`k = 2..8`); **(v2) that the minimal-multiplicity sum meets the Bézout total exactly**, leaving no room. The identity itself merely names why it meets.
> Hence every multiplicity is AT its minimum: type (i) = 1, type (ii) = 2. So `\text{length}(O_{P_C}/F) = 2 = \text{length}(O_{P_C}/(s,w²))` with the containment of (c): **`F_{P_C} = (s, w²)_{P_C}`**, and the `P_C`-primary component of `F` (= the contraction `F_{P_C} ∩ S`, minimal prime) is exactly the jet ideal `Q_C` (membership in `(s,w²)` at the generic point ⟺ value and `δ₀`-jet vanish along `C`). ∎

**Cross-checks (this turn, before singing):** the CI Hilbert series `∏(1−z^{2j+1})/(1−z)^N` reproduces **every** measured `dim F_d` of the campaign: `1/4/11` (N=4, d=3,4,5), `6/22` (N=6), `8/37` (N=8) — `7/7` byte-exact.

## 2. Cascade — what the pin unlocks immediately

1. **Theorem T (R43) is now UNCONDITIONAL:** `Nil(N−2)_{≤d} = 0 ⟹ Nil(N)_{≤d} = 0`, every `d`, every even `N ≥ 6`.
2. **`Nil(N)_{≤3} = 0` for ALL `N ≥ 4`** — Lemma K (R41) is pencil and needs no transfer.
3. **`Nil(N)_{≤5} = 0` for ALL even `N ≥ 6`** — transfer from the byte-exact base `Nil(6)_{≤5} = 0` (and independently re-hit at `N=8`, `d ≤ 5`).
4. Claim ⋂ (R44) is retired: it was the criterion, and the criterion is Theorem PIN.

## 3. Theorem PLANT≤6 (the Plant Law upper half closes through `e = 6`)

> For `e ∈ \{4, 5, 6\}` and every `k` with `n ≥ 2e+2`:
> ## `σ_e(k) = Σ_{j ≥ 1} \dim R_{e−2j}` — the even-family value, EXACTLY.
> Explicitly: `σ₄ = \dim R_2 + 1` (= R41, now re-derived with the machine cell `n=8` replaced by theorem for `n ≥ 10`); **`σ₅ = \dim R_3 + \dim R_1` and `σ₆ = \dim R_4 + \dim R_2 + 1` — NEW**. Lower bound and injectivity ∀e∀k are R42 (Theorem L∀e); the upper containment runs the R41 chain: injectivity of the ladder and difference forms (R42 CI), Lemma B at every rung, the slice count killing degree-`(e−1)` residuals for `n ≥ 2e+2`, and `Nil = 0` in the needed degrees `e−1, e−3, e−5 ≤ 5` — supplied by §2 items 2–3. All stages' thresholds sit inside `n ≥ 2e+2`.

**Scope knife:** `e = 4` keeps its sharper threshold from R41 (`k ≥ 3`); for `e = 5, 6` the stated threshold is `n ≥ 2e+2` (not claimed optimal). Pre-stable cells below threshold remain measured exceptions, mechanism identified (slice shortage).

## 4. The assembly (written now, with its honest quantifier)

> **THE PLANT LAW — ASSEMBLED STATE.**
> **(L) Lower half, ∀e ∀k (theorem, R42):** `σ_e(k) ≥ Σ_{j≥1}\dim R_{e−2j}`, no stabilization, no `k₀`.
> **(U≤6) Upper half, `e ≤ 6` (theorem, §3):** equality for `n ≥ 2e+2` (and `n ≥ 8` for `e = 4`).
> **(U∀e) Upper half, `e ≥ 7`:** the ENTIRE remaining content is the base-cell family
> `B(d)`: `Nil(N₀)_{≤d} = 0` at one even level `N₀` per degree `d ≥ 6` —
> because Theorem T then propagates it to all `N ≥ N₀` and the chain consumes only `d ≤ e−1` at levels `N ≥ 2e > 2d`. The sealed pattern (nilpotents start at degree exactly `N`; anchors `N = 4, 6` complete, `N = 8` partial) predicts `N₀(d) = d+1`; each `B(d)` is one finite computation. **No structural unknown remains in the Plant — only bases.**
> Consequently, on the census side of the Ledger (`Peaje B`): coefficients of `σ_e` in the window are governed by the even family for all `e ≤ 6` unconditionally, and for all `e` modulo `B(d)`.

## 5. Status — said plainly

- **CLOSED this turn:** the First-Order Criterion (Theorem PIN — all degrees, all `N`; the five-turn object, done) · `Nil_{≤5} = 0` at every level · **σ₅ and σ₆** (new closed laws in the dimension direction) · the assembly written with its true quantifier.
- **NOT closed:** the Plant for `e ≥ 7` (bases `B(d)`, `d ≥ 6` — finite per degree, infinite as a family; the conjecture `N₀(d) = d+1` is sealed, not proven). The Chaise Longue theorem itself: collar depths + Ledger assembly + GAP B remain.
- **Which lever broke it:** none of A/B/C verbatim — **a fourth: Bézout** (Palanca C in spirit: count, don't construct). Palanca A was unnecessary; Palanca B (apolarity) stands down, un-used and un-buried.

## 6bis. (v2) The `B(d)` family — the Hilbert-function route, executed to its exact line

Per the W10 order, `Nil_d = \dim I(V)_d − \dim F_d` with `\dim F_d` known ∀d∀N (the CI series), so `B(d)` reduces to the Hilbert function of the REDUCED union of linear spaces. Executed status:

**Lemma SEP (new, pencil): the separator module vanishes low.** Let `ℓ = x_i+x_j` and `K = ann_{O(V)}(ℓ)` (functions supported on the components inside `\{ℓ=0\}`). An element of `K_d` restricted to any lamina `W₀ ∋ (i,j)` is divisible by `1 + 2(k−1) = 2k−1` pairwise-coprime primes of `O(W₀)` (the `y_{ij}` cut by the equal-pair components `(\{i,j\},·)`, plus the `2(k−1)` swap hyperplanes `\{y_{ij} ± y_{ef}\}` cut by the laminae that break the `(i,j)`-pair — all in the vanishing list), and similarly on the `ℓ`-fiber type-(ii) components. Hence **`K_d = 0` for `d < N−1`.**

**The recursion and its exact breaking line.** Multiplication by `ℓ` on `O(V)` plus Theorem D give
`(1−z)²·H_{red}^{(N)} = H_{red}^{(N−2)} + (1−z)\,[\,\mathrm{Hilb}\,T − z\,\mathrm{Hilb}\,K\,]`, `T` = the non-reducedness of the hyperplane section `O(V)/(ℓ)` relative to `O(A¹×V(N−2))`. Comparing with the CI recursion `(1−z)²C^{(N)} = C^{(N−2)} − z^{2k+1}C^{(N−2)}` and using Lemma SEP, the deviation bookkeeping reads, below degree `N−1`:
> `Nil^{(N)}(z)\,(1−z)² = Nil^{(N−2)}(z) − (1−z)\,\mathrm{Hilb}\,T(z) + O(z^{N−1})`.
> **The route closes `B(d)` if and only if the cylinder cancellation `(1−z)·\mathrm{Hilb}\,T = Nil^{(N−2)} + O(z^{N−1})` holds — equivalently, `I(V(N)) + (ℓ)` contains the radical cylinder `I(A¹×V(N−2))` in degrees `< N−1`.** That is a sum-of-radicals statement of the same hardness class as the original; the two-degree ladder cliff resurfaces here as the imported `Nil^{(N−2)}` term at degree `N−2`. **This is the exact line. `B(d)` is NOT killed this turn.** What survives: Lemma SEP, and the sharpened measured pattern **first nil dimension = `2k−1 = N−1`** at both complete anchors (`3` at `N=4`, `5` at `N=6`) — recorded, two anchors, not a law.

## 6. Attack surface for the Auditor

(A) The height/CI count in (a) and the exhaustiveness of the component list (Lemma A). (B) The generic-smoothness triangulation in (b) (`e_{2k}(ξ) ≠ 0`). (C) The colength-2 bookkeeping in (c) and the contraction identification. (D) **The Bézout identity `(2k−1)!!(1+2k) = (2k+1)!!`** and the component counts (re-derive; machine `7/7` attached). (E) The CI-Hilbert cross-check against all seven measured `F`-dims. (F) The `e = 5, 6` chain instantiations in §3 (stage degrees and thresholds). (G) The char-3 schoolbook identity of §0.

**MARCADOR v2 (corrección de forma del Auditor aplicada: se dice QUÉ se verificó — los CONTEOS, no la recursión de la doble factorial; y §6bis añade la vía de Hilbert ejecutada hasta su línea + Lemma SEP): [★★★ EL OBJETO DE CINCO TURNOS, CERRADO — THEOREM PIN: la descomposición primaria de `F` CLAVADA por Bézout: `(2k−1)!!·(1+2k) = (2k+1)!!` no deja sitio (7/7 en k, byte-exact) ⟹ primarias tipo-(i) = primos, tipo-(ii) = ideales de jets de primer orden ⟹ **`rank J_d = Hilb(A′)_d` EN TODO GRADO Y TODO `N`** · cascada: Theorem T incondicional · `Nil_{≤3} = 0` ∀N (lápiz) · `Nil_{≤5} = 0` ∀N≥6 (transfer + base medida) · ★★ σ₅ y σ₆ CERRADAS (`σ₅ = dim R₃+dim R₁`, `σ₆ = dim R₄+dim R₂+1`, `n ≥ 2e+2`) · ensamblaje ESCRITO con su cuantificador honesto: Planta = teorema para `e ≤ 6`, y para `e ≥ 7` NO queda incógnita estructural — solo la familia de bases `B(d)` con `N₀(d) = d+1` sellado · la identidad de escuela instalada: `x²+xy+y²` cuadrado ⟺ char 3 — la no-reducidez entera cabe ahí · la palanca que rompió: BÉZOUT, la cuarta · SIN GRITO: la palabra es del Chaise Longue]. — Vidocq (Constructor, Fable), turno W9**
