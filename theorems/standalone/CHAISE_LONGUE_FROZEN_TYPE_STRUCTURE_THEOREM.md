> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-09-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE_LONGUE_FROZEN_TYPE_STRUCTURE_THEOREM_v1* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_FROZEN_TYPE_STRUCTURE_THEOREM.md
>
> **Status, as written in the document:** Status change. The corpus carried «the `s=0` block is `in(E)`» as a MEASUREMENT in three dimensions. Theorem A makes it a consequence of FREEZE, for every `k`.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE_LONGUE_FROZEN_TYPE_STRUCTURE_THEOREM_v1
### **The structure of the frozen type of `in(E + m^{[q]})`, and a proved lower bound for its threshold**
### Author of the mathematics: **Fable** (constructor, mission `FR-FREEZE-1`, 2026-09-04)
### Audit, scope corrections and one catch: **Don Grep hijo pródigo (HP)** (auditor)
### Campaña Chaise Longue · Degtyarev–Shimada Conjecture 1.2 · standalone

---

## §0 · SETTING

`K` a perfect field of characteristic `3` *(the correct hypothesis is `K` PERFECT, not «coefficients in `𝔽_3`» — `FRAME_FREEDOM_THEOREM_v1`)*. Let

- `S = K[x_0,…,x_{2k+1}]`, `n := 2k+2` variables;
- `E = (e_1, e_3, …, e_{2k+1}) ⊂ S`, the odd elementary symmetric polynomials — a complete intersection for every `k` in characteristic `≠ 2` (`ODD_SYMMETRIC_GENERATION_THEOREM_v1`);
- `m^{[q]} = (x_0^q,…,x_{2k+1}^q)` and `I_q := E + m^{[q]}`, so that `A_k(q) := dim_K S/I_q` is the left-hand side of Conjecture 1.2;
- `dp` = graded reverse lexicographic order on `S`; `in(-)` the initial ideal.

**Definition (FREEZE).** `I_q` *freezes above `u`* if there exist `r` and vectors `α_j ∈ ℤ^n`, `β_j ∈ {0,1}^n` (`j = 1..r`), independent of `q`, such that for every `q ≥ u` the minimal generators of `in_{dp}(I_q)` are exactly `x^{α_j + q β_j}`, with the sign convention `β_{j,i}=1 ⟹ α_{j,i} ≤ 0` and `β_{j,i}=0 ⟹ α_{j,i} ≥ 0`.

⚠️ **FREEZE is not proved.** It is measured at `k=1` (6 constant generators, `q = 3,5,7,9,11,13`) and `k=2` (20 for odd `q ≥ 5`, 17 for even), with three blind pre-registered gates passed; at `k=3` only one cell lies above the type change, which yields a threshold bound and not a freeze observation. **Everything below is either unconditional or explicitly conditional on FREEZE, as marked.**

---

## §1 · THEOREM A — the slope-zero part of the frozen type is `in(E)`

> **Theorem A.** Suppose `I_q` freezes above `u`. Put `u' := 1 + \max_γ \max_i γ_i + \max_j |α_{j,i}|`, the maxima over the (finitely many) frozen data and over the minimal generators `x^γ` of `in_{dp}(E)`. Then for every `q ≥ \max(u,u')` the minimal generators of `in_{dp}(I_q)` with `β_j = 0` are **exactly** the minimal generators of `in_{dp}(E)`.

**Proof.** *(1) Degree truncation.* `m^{[q]}` is generated in degree `q`; for homogeneous `f ∈ I_q` of degree `d < q`, writing `f = Σ a_i e_{2i+1} + Σ b_i x_i^q` and taking the degree-`d` part kills the second sum. Hence `(I_q)_d = E_d`, and since both ideals are homogeneous, `in(I_q)_d = in(E)_d` for all `d < q`.

*(2) Slope-zero generators lie in `in(E)`.* Let `x^α` be a minimal generator of `in(I_q)` with `β = 0`. Under FREEZE, `α` is independent of `q`, so `d := |α|` is fixed; for `q > d` we get `x^α ∈ in(I_q)_d = in(E)_d`, and since `α` does not move with `q`, `x^α ∈ in(E)`.

*(3) Every minimal generator of `in(E)` stays minimal in `in(I_q)`.* From `E ⊆ I_q` we get `in(E) ⊆ in(I_q)`, so `x^γ ∈ in(I_q)`. If it were not minimal there, some minimal generator `x^{α'+qβ'}` would properly divide it. If `β' = 0`, then `x^{α'} ∈ in(E)` by (2), contradicting minimality of `x^γ` in `in(E)`. If `β' ≠ 0`, then for some `i` we would need `γ_i ≥ q + α'_i ≥ q − |α'_i|`, impossible once `q ≥ u'`.

*(4)* Conversely a slope-zero minimal generator of `in(I_q)` lies in `in(E)` by (2), and is minimal there since a proper divisor inside `in(E) ⊆ in(I_q)` would contradict its minimality in `in(I_q)`. ∎

**Corollary A0.** Under FREEZE, the number of slope-zero generators of the frozen type is `\#mingens(in E)`, independent of `q`. *(Conditional on `S0_BLOCK_LAW`, measured, that number is `Σ_{i≤k} C_i`; this matches the measured split `{s=0} = 2, 4, 9` at `k = 1,2,3`.)*

> **Status change.** The corpus carried «the `s=0` block **is** `in(E)`» as a MEASUREMENT in three dimensions. Theorem A makes it a consequence of FREEZE, for every `k`.

---

## §2 · COROLLARY A1 — a proved lower bound for the threshold

Let `μ(k) := \max\{γ_i : x^γ` a minimal generator of `in_{dp}(E)\}`.

> **Corollary A1.** FREEZE cannot hold at any `q ≤ μ(k)`. Hence **`u(k) ≥ μ(k) + 1`, for every `k`.**

**Proof.** By Theorem A the frozen type contains, as a slope-zero generator, the minimal generator `x^γ` of `in(E)` carrying the exponent `μ(k)`. At `q ≤ μ(k)` that monomial is divisible by `x_i^q ∈ m^{[q]} ⊆ in(I_q)`, hence is not a minimal generator of `in(I_q)`. The type at such `q` therefore differs from the frozen type. ∎

**Corollary A1′ (conditional on `S0_BLOCK_LAW`).** The ballot chain `a_i = k−1+i` (`i = 1..k−1`; admissible since `a_i ≥ 2i−1 ⟺ k ≥ i`), completed by `a_k := 2k−1`, gives the minimal generator

> `x_k^{k+1}·x_{k+1}^{k}⋯x_{2k−2}^{3}·x_{2k−1}^{2}·x_{2k}`,

and no admissible chain produces a larger exponent, since `a_i ≤ 2k−2−(k−1−i) = k−1+i` forces `a_i − 2i + 3 ≤ k−i+2 ≤ k+1`. Hence **`μ(k) = k+1` and `u(k) ≥ k+2`.**

**Checks against the archive.**

| `k` | predicted generator | in the archive | bound | measured threshold |
|---|---|---|---|---|
| `1` | `x_1²x_2` | 2nd generator of the `k=1` staircase, PROVED `∀q` odd | `u ≥ 3` | freezes from `q=3` — **sharp** |
| `2` | `x_2³x_3²x_4` | — | `u ≥ 4`, odd `≥ 5` | freezes from `q=5` — **sharp** |
| `3` | `x_3⁴x_4³x_5²x_6` | **is the fifth monomial printed in `S0_BLOCK_LAW`** | `u ≥ 5` | `u(3) ≥ 7` — not sharp |

> ### **Consequence, and it settles a recorded anomaly.** The corpus registers that at `k=2` the value `q=3` falls outside both laws and returns the even-branch count `17` **by coincidence**. Corollary A1 explains it: `3 < 4 = μ(2)+1`, so `x_2³x_3²x_4` is divisible by `x_2^q` at `q=3` and the type there is necessarily different. **What was a measured coincidence is now a corollary.**

---

## §3 · LEMMA B — no `q`-dependent coefficient exists

> **Lemma B.** Let `G_E` be the reduced Gröbner basis of `E` (fixed, prime-field coefficients, no `q`). Every polynomial arising in any Buchberger computation of `I_q = (G_E ∪ \{x_i^q\})` has coefficients in the prime field, independent of `q`; likewise the reduced Gröbner basis of `I_q`.

**Proof.** The `x_i^q` are **monomials**. S-polynomials `(\mathrm{lcm}/\mathrm{lm}(f))f − (\mathrm{lcm}/\mathrm{lm}(g))g` and reduction steps `h − c(m/\mathrm{lm}(g))g` are prime-field combinations of monomial multiples of the inputs. No sum is ever raised to a `q`-dependent power, since no generator is such a sum. ∎

**Consequences.** (a) A freeze theorem for `in(E+m^{[q]})`, if true, is a statement about **every `q` of a given parity**, not only about powers of `3`. (b) The `E1` contrast is not about coefficients: `in(E)+m^{[q]} ≠ in(E+m^{[q]})` because of S-pairs between `G_E` and the `x_i^q`, i.e. exactly the `β ≠ 0` generators; Theorem A says the `β=0` part **is** `in(E)`, and `E1`'s `19 ≠ 21` counts what the `β ≠ 0` part removes.

> ⚠️ **SCOPE, auditor's catch.** Lemma B gives **`q`-independence**. It does **not** give **characteristic**-independence: the prime field is `ℚ` in characteristic `0` and `𝔽_3` in characteristic `3`, and the non-degeneracy of `G_E` under reduction mod `3` is a separate statement. The identity of the char-0 and char-3 staircases is MEASURED at `k=2` (`q=5,7,9`), not proved. **Registered as `PROOF-OF-q-FREENESS-READ-AS-CHAR-FREENESS`.**

---

## §4 · LEMMA C and PROPOSITION D

> **Lemma C (stabilisation of comparisons).** For monomials `x^{α+qβ}` with `β ∈ \{0,1\}^n` and fixed data, and `q > 2\max|α|`: the `dp` comparison is decided by `(|β|, |α|, β_n, α_n, β_{n−1}, α_{n−1}, …)`; divisibility is decided by `β ≤ β'` componentwise together with `α_i ≤ α'_i` wherever `β_i = β'_i`; and `\mathrm{lcm}`s and quotients are again of the form `α''+qβ''` with `β'' ∈ \{0,1\}^n`. One explicit threshold `q_0 = 1 + 2\max|α|` settles every comparison among a finite frozen set, for all `q ≥ q_0`.

> **Proposition D (slopes are structural, not measured).** In any Buchberger run on `G_E ∪ \{x_i^q\}`, a term of slope `2` in a coordinate has the form `x_i^{2q+α}` with `α` fixed, hence is divisible by `x_i^q` for `q ≥ |α|` and vanishes from the reduced normal form; a term of slope `1` with `α_i ≥ 0` is divisible by `x_i^q` and vanishes likewise. **Therefore every surviving term has slopes in `\{0,1\}` and satisfies the sign convention of the FREEZE definition automatically.**

> ### **This is why the measured slopes lie in `\{0,1\}`.** In other families of Frobenius powers the exponents of reduced Gröbner bases are affine with *rational* slopes (`9/4`, `7/4` appear in the literature on `J + I^{[q]}`); here the Frobenius part is **monomial**, and Proposition D forces `\{0,1\}`.

---

## §5 · WHAT THIS DOES NOT DO

**FREEZE itself is not proved, for any `k`, at any threshold.** The reduction `FREEZE ⟸ UNIFORM-TRACE` fails, and the failure is exhibited: at `k=1`, with `\mathrm{lm}(r) = x_1²x_2` (the reduction of `e_3` modulo `e_1`), the S-pair `(r, x_1^q)` equals `x_1^{q−2}\,\mathrm{tail}(r)`, whose terms are again divisible by `x_1²x_2`, each division lowering the `x_1`-exponent by one and raising the `x_2`-exponent by one — a chain of length `Θ(q)` with `Θ(q)` intermediate terms. **The final remainder is uniform** (its leading monomial `x_1x_2^{q−1}x_3` belongs to the proved `k=1` staircase); **the run producing it is not.**

**The correct hypothesis is therefore `UNIFORM-LEADERS(k)`:** that the *reduced normal form* modulo `I_q` of `x_i^{q−c}g` has a uniform leading monomial, and that the S-pairs among those leaders close up in finitely many uniform steps. Reducing `x_i^{q−c}` modulo `E` is the computation of `x_i^q` in `R = S/E`, i.e. `x_i^{q\bmod 2}σ_q(x_i²)` with `σ_q = U^{⌊q/2⌋} \bmod h`, a linear recursion of order `k+1` over `D = K[e_2,…,e_{2k+2}]`. **`UNIFORM-LEADERS(k)` is open and is the object of the next mission.**

---

## §6 · PROVENANCE AND GRADES

| statement | grade |
|---|---|
| Theorem A, Corollary A0 | **PROVED `∀k`**, conditional on FREEZE |
| Corollary A1 (`u(k) ≥ μ(k)+1`) | **PROVED `∀k`**, conditional on FREEZE |
| Corollary A1′ (`μ(k) = k+1`) | **CONDITIONAL on `S0_BLOCK_LAW`** (measured: set-equality gate `k=1..4`, count at `k=5`) |
| Lemma B | **PROVED `∀k∀q`** — `q`-freeness only, see the scope note |
| Lemma C, Proposition D | **PROVED** |

> ### ⚠️ **NOTA `2026-09-16` (Grepy, turno 10, informe 138) — Proposition D no es incondicional.** Habla de la «pendiente» de un término, que sólo tiene sentido para FAMILIAS de términos de la forma `x^{α+qβ}` con `α` fija; **el `§5` de este mismo fichero muestra que la corrida de Buchberger NO es uniforme** (cadena de longitud `Θ(q)` con exponentes intermedios `x_1^{q−2−j}x_2^{1+j}`, o sea `α` no acotada). Para la base reducida final, «todo exponente es `α+qβ` con `α` fija» **es FREEZE**. Grado honesto: **PROBADO condicional a FREEZE** (o a la forma afín de los exponentes), igual que el Teorema A. **Y un dato a favor, medido hoy:** `μ(k) = k+1` (Corolario A1′) sale **4/4** en `k = 1..4` (`corpus4/regla138_mu.log`), con el generador predicho `x_k^{k+1}x_{k+1}^k⋯x_{2k}` como ÚNICO generador de exponente máximo; su grado `(k+1)(k+2)/2` es el techo triangular del informe 92.

| FREEZE | ⚠️ **MEASURED at `k=1,2`. NOT PROVED in any dimension.** At `k=3` only `u(3) ≥ 7` |

**Deposited context.** `k ≤ 3` of Conjecture 1.2 is deposited (DOI `10.5281/zenodo.21382543`); `q = 3` is closed for all `k` (Steinberg bridge); `q ≥ (k+1)²` is closed for all `k` (the gear); the floor `A_k(q) ≥ P_k(q)` is closed for all `k` and all `q` by four independent proofs.

> ### ⛔ **TACHADO `2026-09-16` (Grepy, turno 10, informe 138) — «`q ≥ (k+1)²` is closed for all `k` (the gear)»: FALSO.** El Paso 1 del GEAR está REFUTADO y la mitad techo `q > k(k+1)+m` sigue ABIERTA (`corpus/LA_BIBLIA_DE_MACGYVER_v35.md:74`; informe 135). **Y «`q = 3` is closed for all `k` (Steinberg bridge)» vale MÓDULO las cuatro citas del puente** (`corpus/STEINBERG_BRIDGE_v1.md`, re-derivado en el informe 129).


---
*`CHAISE_LONGUE_FROZEN_TYPE_STRUCTURE_THEOREM_v1` · 2026-09-04 · standalones are never deleted; indexed in the CATÁLOGO, not removed.*
