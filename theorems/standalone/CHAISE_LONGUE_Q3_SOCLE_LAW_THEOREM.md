> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-20
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE q = 3 SOCLE LAW* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_Q3_SOCLE_LAW_THEOREM.md
>
> **Status, as written in the document:** Grade: PROVED, uniform in `k`, modulo the same four textbook citations as the Steinberg bridge (H1 below).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE `q = 3` SOCLE LAW
## `dim A_T(k,3) = R(2k+2)` and `dim A_{T-1}(k,3) = R(2k+3)` for every `k`, as a corollary of the Steinberg bridge

**Rafael Amichis Luengo** (Madrid) **· Claude (Anthropic), instance GETTLER** — 20 August 2026
**Grade: PROVED, uniform in `k`, modulo the same four textbook citations as the Steinberg bridge (H1 below).**
*Supersedes the status `CANDIDATE, four cells` recorded in `MASTER v35 §0.-8.3(2)` and `LEDGER v124`.*

---

## 1. Statement

Let `K = F_3`, `n = 2k+2`, `S = K[x_1,…,x_n]`, `E = (e_1, e_3, …, e_{2k+1})` the odd elementary symmetric
polynomials, `m^{[q]} = (x_1^q,…,x_n^q)`, and

```
A = A_k(q) := S/(E + m^{[q]}),        T := (k+1)(q-1)   (the top degree of A).
```

At `q = 3` we have `T = 2(k+1) = n`. Write `c(n,d) := [z^d](1+z+z^2)^n = dim_K (S/m^{[3]})_d`, and let `R` be the
Riordan numbers, `R(0)=1, R(1)=0, R(n) = \frac{n-1}{n+1}\big(2R(n-1)+3R(n-2)\big)`:

```
R = 1, 0, 1, 1, 3, 6, 15, 36, 91, 232, 603, 1585, 4213, 11298, 30537, 83097, 227475, 625992, 1730787, 4805595, …
```

> ### **THEOREM (`q = 3` socle law).** For every `k ≥ 1`:
> ### **`dim A_T(k,3) = c(n,n) - c(n,n-1) = R(2k+2)`  and  `dim A_{T-1}(k,3) = c(n,n-1) - c(n,n-2) = R(2k+3)`.**
> Moreover `A_d = 0` for `d > T`, so `A_T ⊆ soc(A)`.

## 2. Proof

**(a) The graded Hilbert function of `A_k(3)`, for every `k`.** The Steinberg bridge
(`STEINBERG_BRIDGE_v1`, Theorem RL-1/RL-2 and its Corollary) proves, uniformly in `k`:

```
h_d := dim A_k(3)_d = c(n,d) - c(n,d-1)   for d ≤ n,        h_d = 0   for d > n.
```

*Chain, for the record:* `S/m^{[3]} ≅ St^{⊗n}` as rational `SL_2`-modules, with `A_d` the weight space of weight
`2d-2n`; the odd elementary team generates exactly the ideal of the divided-power raising operators `E^{(m)}`
(the identity `G(t)E(t) = E(-t)` in characteristic 3); hence `Ann_A(E) = A^{U^+}`; dominance vanishing kills all
negative weights, and good-filtration multiplicities read off the character give the rest; Gorenstein duality on
`S/m^{[3]}` converts annihilator dimensions into ranks. **Grade: PROVED modulo H1.**

**(b) The two top values.** `T = 2(k+1) = n`, so `h_T = c(n,n) - c(n,n-1)` and `h_{T-1} = c(n,n-1) - c(n,n-2)`. ∎

**(c) Identification with the Riordan numbers.** `R(n) = c(n,n) - c(n,n-1)` is the classical trinomial description
of the Riordan numbers: `c(n,n) = T(n)` is the central trinomial coefficient and `R(n)` is the difference of the
two central entries of the `n`-th trinomial row. Applying it twice gives the second value. ∎

**Machine gate, `k = 1..8`, 8/8, no exceptions** (`gettler_free_v3.py`, exact integer arithmetic):

| `k` | `n` | `A_k(3) = T(n)` | `c(n,n)-c(n,n-1)` | `R(2k+2)` | `c(n,n-1)-c(n,n-2)` | `R(2k+3)` | `(2k+1)!!` |
|---|---|---|---|---|---|---|---|
| 1 | 4 | 19 | **3** | 3 | **6** | 6 | 3 |
| 2 | 6 | 141 | **15** | 15 | **36** | 36 | 15 |
| 3 | 8 | 1107 | **91** | 91 | **232** | 232 | 105 |
| 4 | 10 | 8953 | **603** | 603 | **1585** | 1585 | 945 |
| 5 | 12 | 73789 | **4213** | 4213 | **11298** | 11298 | 10395 |
| 6 | 14 | 616227 | **30537** | 30537 | **83097** | 83097 | 135135 |
| 7 | 16 | 5196627 | **227475** | 227475 | **625992** | 625992 | 2027025 |
| 8 | 18 | 44152809 | **1730787** | 1730787 | **4805595** | 4805595 | 34459425 |

## 3. Three consequences of record

**3.1 · The `(4,3)` gate is closed by theorem, not by machine.** The campaign's declared *cheapest open item* —
`dim A_{10}` and `dim A_9` at `(k,q) = (4,3)`, with the archived prediction `603` and `1585` — is now a corollary,
in closed form, for every `k`. **The engine `gate43.cpp` is retired: there is nothing left for it to decide.**
*(The archived run's intermediate values are consistent with the theorem: `|V_{10}| = 8953 = c(10,10)`,
`rank J_{10} = 8350 = c(10,9)`, `rank J_9 = 6765 = c(10,8)`.)*

**3.2 · A free, exact, infinite death criterion, in every dimension.** Any construction the campaign builds —
a leading-term map, a bigraded refinement, `origin_k`, a proposed structural law for the socle — **must return
`h_d = c(n,d) - c(n,d-1)` and the two values above at `q = 3`, for every `k`.** Until now the campaign's gates were
two or three measured cells; this one fires in all dimensions at once and costs nothing.

**3.3 · The `q = 3` side of the freezing criterion is now proved, not measured.**
The criterion `dim A_T = (2k+1)!! ⟺ q ≥ k+1` has, at `q = 3`, the requirement `k ≤ 2`. The theorem confirms it
exactly: `R(4) = 3 = 3!!` and `R(6) = 15 = 5!!` (the two cells where `q = 3 ≥ k+1`), and `R(2k+2) < (2k+1)!!`
strictly at `k = 3, 4, 5, 6, 7, 8` (`91<105`, `603<945`, `4213<10395`, `30537<135135`, `227475<2027025`,
`1730787<34459425`). **Six proved negatives replace two measured ones.**

**3.4 · What this does NOT do.** It says nothing about `q ≥ 9`, which is the open regime. At `q = 3` the conjecture
is closed anyway by the same bridge, so this theorem is an exact anchor and a gate — **not a step of the main proof.**

## 4. Honest scope, and one open flag

**H1 — citation pinning (inherited, bibliographic).** The Steinberg bridge uses four standard facts cited from
memory: Kostant `Z`-form comultiplication of divided powers; `Hom_G(Δ(μ), M) ≅ (M^{U^+})_μ` (believed Jantzen,
*Representations of Algebraic Groups*, II.2.13(b)); `Hom(Δ,∇)` orthogonality and `Ext^1(Δ,∇) = 0` (Jantzen II.4);
tilting modules closed under tensor product (Donkin / Mathieu / Wang for `SL_2`). **These were cold-audited and
confirmed independently, but the exact statement numbers are not personally verified.** This theorem inherits that
flag and nothing else. *What closes it: one library pass with Jantzen open.*

**Not claimed:** that the bridge cannot be extended to `q = 3^v`, `v ≥ 2`. It has not been done, and the naive
transport is dead with four numbers (see the campaign's ledger: `217/489`, `7761/32661`, `345465/2306025`,
`17605249/167729959`), but **"not done" is not "proved impossible"** and this document does not say otherwise.

---

*Script: `gettler_free_v3.py`. Data: `RESULTS_q3law.tsv`. Every number recomputed in exact integer arithmetic;
none from memory.*
