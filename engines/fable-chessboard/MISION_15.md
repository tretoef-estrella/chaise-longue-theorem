# MISSION 15 — CONJECTURE 1.2 OF DEGTYAREV–SHIMADA, IN ITS LITERAL FORM: ONE DIMENSION COUNT
*(Grepy el Lector, auditor, 2026-09-24.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.**
- The reports `INFORME.md` … `INFORME_14.md` in this folder are audited. **INFORME_14 §3.1 (Theorem Γ) is a correct proof of Theorem A below.** Open older files only to quote a proof summarised here.
- 🔴 **The missions `MISION.md` … `MISION_14.md` in this folder state Conjecture 1.2 as `A_k(q) = P_k(q)`. That identification is FALSE.** `A_k(q) = P_k(q)` is Theorem A (proved). The literal conjecture is the statement (S) of §1.3. Its translation, written from the original paper, is proved in §1.2. Use this file, not the older missions, for what the conjecture says.
- **Engines of the auditor, in this folder** (all run inside the watchdog, §0 rule 10):
  - `grepy_vigia.sh`: the watchdog you MUST use.
  - `grepy_ds_sum.py K Q [drop]` (md5 `1041ba68…`): computes `dim_{F_3}(D_J : J ∈ K)·C` of §1.3, degree by degree (NumPy, mod 3). `drop` is a comma list of indices of removed matchings (the order of `matchings()` in the file). It prints the rank in each degree and the total, and compares with `Q_k(q)`.
  - `grepy_ds.py MODE Q K [drop]` (md5 `2b7dcbd2…`): writes Singular scripts for the literal forms of [DS]: `lit` (the group ring in `t`), `yco` (the `y`-form of §1.2), `pbone` (the intersection form of §1.4), `ext` (the ideals of §2.3). `gam` prints `|Γ_K|` by enumeration.
  - From earlier turns: `grepy_verif.py` (exact polynomial identities over `F_3` modulo a box, pure Python), `grepy_polys.py`, `grepy_mapa.py`, `grepy_gamma_vdim.py`.

> **OBJECTIVE of the campaign: the complete proof of Conjecture 1.2 of Degtyarev–Shimada for Fermat varieties of degree `m = 3^v` and every even dimension `2k`.**
>
> **This mission's target is that statement: prove (S) of §1.3 for every `k ≥ 0` and every `q = 3^v`.**
>
> Ladder, in case the full target is not reached (each rung is a new theorem):
> - **R1:** (S) for `q = 3` and every `k` (cubic Fermat varieties of every even dimension).
> - **R2:** (S) for `k = 2` and every `q = 3^v`.
> - **R3:** (S) for `k ≤ 4` and every `q = 3^v`.
> - **R4:** (S) on any other infinite family of `(k, q)`, stated exactly.
> - **FULL:** (S) for every `k` and every `q = 3^v`. If you reach it, write in your FIRST LINE, in capitals: «CONJECTURE 1.2 OF DEGTYAREV–SHIMADA PROVED FOR m = 3^v AND EVERY EVEN DIMENSION», followed by the chain.

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_15.md` with these empty sections:
   `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 16`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:**
   - work in order, no going back, no retries;
   - write the budget before each step;
   - after 10 minutes without progress: stop, write, declare;
   - keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source. The source of the conjecture is [DS] (§8).
6. **Do not recompute anything listed here as proved or measured** (§2, §3). Re-gating a CLOSED FORM of yours on a measured cell is allowed and expected.
7. **A negative dimension, or a dimension larger than the ambient space, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine and guardrail — EVERY engine runs inside the watchdog:** `zsh grepy_vigia.sh LOGFILE 'the whole command'`.
    - The LOG is the FIRST argument. It kills at **1.2 GB of RSS (whole process tree) or 600 s**; the last line of the log says how it ended.
    - **WRITE THE ESTIMATE IN THE REPORT BEFORE EACH RUN, ENGINE BY ENGINE, INCLUDING THE SMALL ONES.**
    - Singular reads stdin when its file is empty and then waits forever: check that the `.sing` file is non-empty and launch as `Singular -q FILE < /dev/null`. Use `python3 -u`.
    - You MAY run TWO engines at once if their estimates add up to less than 1.2 GB. **Any run estimated above 30 s runs ALONE.**
    - After any kill, check with `pgrep` that it is gone, and write that you checked. When you finish, check that nothing of yours is still running.
    - **Measured costs of `grepy_ds_sum.py`:** `(k,q) = (4,3)`: < 1 s; `(5,3)`: 1 s, 330 MB; `(2,9)`: 3 s, 450 MB; `(1,27)`: < 1 s. **`(6,3)` does NOT fit as written** (its degree-6 matrix is `135 135 × 1 716` int64, 1.9 GB): batch the generators first. **`(3,9)`** (`8^7 ≈ 2.1·10^6` monomials) does not fit densely.
    - **Allowed Gröbner (Singular or M2):** `≤ 10` variables at `q = 3`; `≤ 7` at `q = 9`; `≤ 5` at `q = 27`; `≤ 4` at `q = 81`. Pure-Python exact identities at any size that fits the caps.
    - **Forbidden:** any Gröbner run beyond those caps.
11. **In characteristic 3, never average over a group whose order is divisible by 3.** Make a certificate canonical by REDUCTION, not by averaging.
12. **Re-read the disk before the verdict.**
13. **Double check:**
    - every PROVED claim carries its proof in the report;
    - every number carries its cell and its log;
    - every identity used in a proof is checked exactly, symbolically or at `≥ 2` cells;
    - every claim «for every `q`» is gated at two values of `q` or more.
14. **Sealed bets must be able to FAIL where the statement has content.** A bet that can only fail at a cell already measured in §3 is SAFE, whatever you label it.
15. **Measured cells are gates, not proofs.** No rung is reached by measurement.

**FIRST LINE** (answer first, in this order):
- (a) Is (S) PROVED for every `k` and every `q = 3^v`? If yes, the chain in five lines.
- (b) Otherwise: which rungs (R1–R4) are PROVED, with the proof in one paragraph each.
- (c) Which cells did you gate, and did any cell break a claim of yours?

---
## 1 · THE STATEMENT
### 1.1 The original [DS]
Let `n = 2d`, `m ≥ 3`, and let `X ⊂ P^{n+1}` be the Fermat variety `z_0^m + ⋯ + z_{n+1}^m = 0`.
- `J` is the set of partitions of `{0, …, n+1}` into pairs `J = [[j_0,k_0], …, [j_d,k_d]]` with `j_i < k_i` and `j_0 < ⋯ < j_d`, so `j_0 = 0`. `|J| = (n+1)!! = (2d+1)!!`.
- For `J ∈ J` and `β_i^m = −1`, the standard `d`-space `L_{J,β}` is `z_{k_i} = β_i z_{j_i}` (`i = 0..d`). For `∅ ≠ K ⊆ J`, `L_K(X) ⊆ H_n(X; Z)` is generated by the classes of the `L_{J,β}` with `J ∈ K`.
- `R := Z[t_1, …, t_{n+1}]/(t_i^m − 1)`, `t_0 := (t_1⋯t_{n+1})^{−1}`, `φ(u) := 1 + u + ⋯ + u^{m−1}`, `τ_J := Π_{i=0}^{d}(t_{k_i} − 1)`, **`ψ_J := τ_J·Π_{i=1}^{d} φ(t_{j_i}t_{k_i})`**.
- **[DS, Theorem 1.1(a)]:** `Tors(H_n(X)/L_K(X)) ≅ Tors(R/(ψ_J : J ∈ K))`.
- **[DS, Definition 1.3]:** `Γ_K ⊆ μ_m^{n+1}` is the set of `(a_1, …, a_{n+1})` with every `a_i ≠ 1` and such that `a_{j_i}a_{k_i} = 1` for `i = 1..d`, for some `J ∈ K`.
- **[DS, Claim 4.3]:** if `p = 0` or `p ∤ m`, then `dim_{K_p}(R/(ψ_J : J ∈ K) ⊗ K_p) = m^{n+1} − |Γ_K|` (`K_p` algebraically closed of characteristic `p`).
- **[DS, Corollary 1.5]:** the torsion of `H_n(X)/L_K(X)` involves only primes dividing `m`.
- **[DS, Conjecture 1.2]:** for `K = J`, `H_n(X)/L_J(X)` is torsion free.
- **Known:** `d = 0` (obvious) and `d = 1` (Degtyarev, [De14]); by computer, `(n, m) = (4, 3..12)`, `(6, 3)`, `(6, 4)`, `(6, 5)`, `(8, 3)` [DS, §5]. Restated as open in [De15, Conjecture 4.4].

From now on `k := d`, `q := m = 3^v`, `N := 2k+2 = n+2`.

### 1.2 The translation (PROVED; each step is written out)
**Step 1.** `R/(ψ_J : J ∈ J)` is a finitely generated abelian group. It is torsion free iff `dim_{F_p}(− ⊗ F_p) = dim_Q(− ⊗ Q)` for every prime `p` (right exactness of `⊗`). For `m = 3^v` only `p = 3` can fail [DS, Cor. 1.5], and the `Q`-dimension is `q^{2k+1} − |Γ_J|` [DS, Claim 4.3]. Moreover `dim_{F_3} ≥ dim_Q` always. So:

**Conjecture 1.2 at `(k,q)` ⟺ `dim_{F_3} F_3[G]/(ψ̄_J : J ∈ J) = q^{2k+1} − |Γ_J|`**, where `F_3[G] = F_3[t_1..t_{2k+1}]/(t_i^q − 1)` and `ψ̄_J` is the image of `ψ_J`.

**Step 2 (`|Γ_J|`).** With `a_0 := (a_1⋯a_{2k+1})^{−1}`, a tuple lies in `Γ_J` iff the multiset `{a_0, …, a_{2k+1}} ⊆ μ_q ∖ {1}` splits into inverse pairs: the pair containing index `0` is then automatic. `μ_q ∖ {1}` consists of `(q−1)/2` inverse pairs, so by the exponential formula

**`|Γ_J| = Q_k(q) := N!·[y^N] I_0(2y)^{(q−1)/2}`**, `I_0(2y) := Σ_{b≥0} y^{2b}/(b!)^2`.

Equivalently, `Q_k(q)` is the number of `x ∈ (F_q^×)^N` whose multiset of coordinates is closed under negation. At `q = 3`, `Q_k(3) = C(2k+2, k+1)`.

**Step 3 (a coordinate in which the relations are linear).** In `F_3[t]/(t^q − 1)` we have `t^q − 1 = (t − 1)^q`. So `t − 1` is nilpotent, and `t` and `t + 1 = 2 + (t−1)` are units. Put **`y := t − t^{−1} = t^{−1}(t−1)(t+1)`**, a unit times `t − 1`.
- The ring is local with principal maximal ideal `(t−1) = (y)`, so it is spanned by `1, y, …, y^{q−1}`. Comparing dimensions, **`F_3[t]/(t^q − 1) = F_3[y]/(y^q)`**. Inversion `t ↦ t^{−1}` is `y ↦ −y`.
- **`y_j + y_k = (t_j + t_k)(t_jt_k)^{−1}(t_jt_k − 1)`**, with `t_j + t_k` a unit, so `(t_jt_k − 1) = (y_j + y_k)` as ideals.
- **`φ(u) = (u^q − 1)/(u − 1) = (u − 1)^{q−1}`** in characteristic 3.

Hence, up to units, in `B := F_3[y_1, …, y_{2k+1}]/(y_i^q)`:

`ψ̄_J = Π_{i=0}^{k} y_{k_i} · Π_{i=1}^{k} (y_{j_i} + y_{k_i})^{q−1}`.

**Step 4 (the factor `Y`).** For every `a, b`: `(a+b)^{q−1} = (a^q + b^q)/(a+b) = Σ_{s=0}^{q−1}(−1)^s a^s b^{q−1−s}`. Multiplying by `b` and dropping `b^q = 0`:

`(a+b)^{q−1}·b = −ab·D(a,b)` in `B`, where **`D(a,b) := Σ_{u=0}^{q−2}(−1)^u a^u b^{q−2−u}`**.

`D(b,a) = −D(a,b)`, and at `q = 3`, `D(a,b) = b − a`. Since `{k_0} ∪ ⋃_{i≥1}{j_i, k_i} = {1, …, 2k+1}`:

**`ψ̄_J = ±Y·D_J`, with `Y := y_1⋯y_{2k+1}` and `D_J := Π_{i=1}^{k} D(y_{j_i}, y_{k_i})`**,

the product being over the `k` pairs of `J` that do not contain `0`.

Multiplication by `Y` kills exactly the monomials with some exponent `≥ q−1`, so it induces an injection `C := F_3[y_1..y_{2k+1}]/(y_i^{q−1}) ↪ B`, and `(ψ̄_J : J ∈ K)B = Y·(D_J : J ∈ K)C`. Therefore `dim_{F_3} F_3[G]/(ψ̄_J : J ∈ K) = q^{2k+1} − dim_{F_3}(D_J : J ∈ K)C`.

### 1.3 THE STATEMENT TO PROVE
**(S)** *For every `k ≥ 0` and every `q = 3^v`:*

**`dim_{F_3} (D_J : J ∈ J)·C = Q_k(q)`**, *where `C = F_3[y_1, …, y_{2k+1}]/(y_1^{q−1}, …, y_{2k+1}^{q−1})`.*

- **(S) is equivalent to Conjecture 1.2 at `(k, q)`** (§1.2).
- **The inequality `≤` is PROVED** (Step 1: `dim_{F_3} ≥ dim_Q`). **So (S) ⟺ `dim_{F_3}(D_J : J ∈ J)C ≥ Q_k(q)`.**
- The ideal `(D_J : J ∈ J)` is generated in the single degree `k(q−2)`.
- For a subfamily `K ⊆ J` the same translation gives: `L_K(X)` is primitive ⟺ `dim_{F_3}(D_J : J ∈ K)C = |Γ_K|`.
- **At `q = 3`:** `C = F_3[y_1..y_{2k+1}]/(y_i^2)`, and each `D_J = Π_{i≥1}(y_{k_i} − y_{j_i})` is a product of `k` differences over a perfect matching of `{1..2k+1} ∖ {k_0}`. These are the Specht polynomials of the two-row shape `(k+1, k)` of `S_{2k+1}` (columns = the pairs; the singleton `k_0` in the first row). Their span has dimension `C(2k+1,k) − C(2k+1,k−1)` (classical, over any field; it matches the measured first ranks `2, 5, 14, 42, 132` for `k = 1..5`). **(S) at `q = 3` reads: the ideal they generate in `F_3[y]/(y_i^2)` has dimension `C(2k+2, k+1)`.**

### 1.4 The equivalent intersection form (PROVED; Gorenstein duality)
`B` is an Artinian Gorenstein ring, so `dim(ψ̄_J : J)B = dim B/⋂_J ann_B(ψ̄_J)`, and `dim(ψ̄_J : J)B = dim(D_J : J)C` (Step 4). In `B`, `ann_B(ψ̄_J) = I'_J + (y_i^{q−1})` with `I'_J := (y_{j_i} + y_{k_i} : i ≥ 1)`. Since `y_i^q ∈ (y_i^{q−1})`, `B/⋂_J(I'_J + (y_i^{q−1})) = F_3[y]/⋂_J(I'_J + (y_i^{q−1}))`. Hence

**(S) ⟺ `b_k(q−1) = Q_k(q)`, where `b_k(r) := dim F_3[y_1..y_{2k+1}] / ⋂_{J∈J}(I'_J + (y_i^r))`.**

Eliminating `x_0 := −Σ y_i` (every ideal contains the image of `e_1`), `b_k(r) = dim F_3[x_0..x_{2k+1}] / ⋂_J (I_J + (x_i^r))` with `I_J = (x_a + x_b : {a,b} ∈ J)`. (Gated, §3: `grepy_ds.py pbone` gives the same numbers as `grepy_ds_sum.py`.)

## 2 · RELATED FACTS (PROVED)
### 2.1 Theorem A (INFORME_14, Theorem Γ)
For every field `F` with `char F ≠ 2`, every odd `q ≥ 1` and every `n`:
`dim_F F[x_1..x_n]/(e_1, e_3, e_5, …; x_1^q, …, x_n^q) = n!·[y^n] e^y I_0(2y)^{(q−1)/2}`.
With `F = F_3`, `q = 3^v`, `n = N`: `A_k(q) := dim F_3[x_0..x_{2k+1}]/(E + (x_i^q)) = P_k(q) := #{x ∈ F_q^N : e_j(x) = 0 for all odd j}`, where `E := (e_1, e_3, …, e_{2k+1})`.
- **This is NOT (S).** It is a SUM statement at the ODD box `q` on the grid WITH zero. (S) is equivalent to an INTERSECTION statement at the EVEN box `q − 1` on the grid WITHOUT zero (§1.4).

### 2.2 The sandwich (PROVED)
Let `Γ ⊆ (F_q^×)^N` be the zero-free points of `⋃_J L_J`, where `L_J := V(I_J)`. Then

`b_k(q−1) ≤ Q_k(q) ≤ dim F_3[x_0..x_{2k+1}]/(E + (x_i^{q−1}))`.

- **Right.** The ideal of `Γ` contains `E + (x_i^{q−1} − 1)`, whose initial ideal contains `E + (x_i^{q−1})`.
- **Left.** `L_J ∩ (F_q^×)^N` has ideal `I_J + (x_i^{q−1} − 1)`, whose initial ideal is `I_J + (x_i^{q−1})` (both quotients have dimension `(q−1)^{k+1}`). The initial ideal of an intersection is contained in the intersection of the initial ideals.
- **(S) is the LEFT equality.**

### 2.3 Facts about the full family
- `⋂_{J∈J} I_J = E` in `F_3[x_0..x_{2k+1}]`, and `E` is a complete intersection.
  - `E` is generated by a regular sequence of degrees `1, 3, …, 2k+1`, so `deg(S/E) = (2k+1)!! = |J|`.
  - `V(E) = ⋃_J L_J`, because `e_j(x) = 0` for all odd `j` ⟺ `Π(1 + x_i t)` is even ⟺ the multiset of coordinates is closed under negation.
  - A complete intersection is unmixed, and the `|J|` linear components exhaust the degree, so each has multiplicity 1. Hence `E` is radical and equals `⋂ I_J`.
- **For proper subfamilies (S) can FAIL** (measured, §3.3): at `q = 9`, `k = 2`, `K = J ∖ {[[0,1],[2,3],[4,5]], [[0,2],[1,5],[3,4]]}` (indices `0` and `5` in `grepy_ds_sum.py`): `dim(D_J : J ∈ K)C = 4730 < 4736 = |Γ_K|`. So `L_K(X)` has 3-torsion, although `A_K = P_K = 7089` for that `K`.
  - **Consequence (logic):** any argument that proves (S) for EVERY subfamily `K ⊆ J` proves a false statement. A proof of (S) must use a property of the full family `J`.

## 3 · MEASURED (gates; do not recompute)
### 3.1 Cells where (S) holds (full family)
| `(k,q)` | `Q_k(q)` | source | graded ranks of `(D_J)C`, from degree `k(q−2)` |
|---|---|---|---|
| `(0,q)` | `q−1` | trivial | — |
| `(1,q)`, every `q` | `3q²−9q+6` | [De14] (proved) | `(1,3)`: 2,3,1 · `(1,9)`: 3,6,9,12,15,18,20,21,18,15,12,9,6,3,1 · `(1,27)`: 3,6,…,72,74,75,72,…,3,1 |
| `(2,3)` | 20 | [DS §5]; auditor | 5,9,5,1 |
| `(2,9)` | 5120 | [DS §5]; auditor | 15,45,90,150,224,310,395,470,515,530,516,475,411,329,245,170,110,65,34,15,5,1 |
| `(3,3)` | 70 | [DS §5]; auditor | 14,28,20,7,1 |
| `(4,3)` | 252 | [DS §5]; auditor | 42,90,75,35,9,1 |
| **`(5,3)`** | **924** | **auditor, 2026-09-24 (new: `n = 10` was never checked)** | 132,297,275,154,54,11,1 |

- At `q = 3` the graded ranks agree, in every cell above, with the ballot numbers `C(2k+2, k+1−j)·(2j+1)/(k+2+j)`, `j = 0..k+1` (OEIS A039599). Their sum is `C(2k+2, k+1)`.
- Double check by other routes (Singular, full `std`): `grepy_ds.py lit` (literal `t`-form) gives `q^{2k+1} − Q_k(q)` at `(1,3)`, `(2,3)`, `(3,3)` (21, 223, 2117); `yco` at `(1,3)`, `(2,3)`, `(3,3)`, `(4,3)`, `(1,9)`, `(1,27)` (…, 19 431, 561, 17 733); `pbone` gives `Q_k(q)` at `(1,3)`, `(2,3)`, `(3,3)`, `(1,9)`, `(2,9)` (6, 20, 70, 168, 5120).

### 3.2 Values of `Q_k(q)` (targets)
| `q` \ `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| 3 | 2 | 6 | 20 | 70 | 252 | 924 | 3432 |
| 9 | 8 | 168 | 5120 | 190 120 | 7 939 008 | 357 713 664 | 16 993 726 464 |
| 27 | 26 | 1950 | 234 260 | 37 849 630 | 7 550 855 676 | … | … |
| 81 | 80 | 18 960 | 7 395 200 | 3 987 331 600 | … | … | … |

Not measured: `(6,3)`, `(3,9)`, `(2,27)`, and everything larger.

### 3.3 The subfamily cell
- `(2,9)` without matchings `0, 5`: graded ranks `13,39,78,130,195,273,352,423,468,487,480,447,391,317,239,168,110,65,34,15,5,1`, total 4730.
- The literal `t`-form and the `y`-form give `dim F_3[G]/(ψ̄) = 54 319 = 9^5 − 4730`, against `9^5 − |Γ_K| = 54 313`; `pbone` gives 4730. Three routes, one number.

### 3.4 One more measured relation (not proved)
Let `B_K(q) := dim F_3[x_0..x_{2k+1}]/⋂_{J∈K}(I_J + (x_i^q))` (box `q`, zero allowed), and let `P_K(q)` be the number of points of `⋃_{J∈K}L_J(F_q)`. Group the points by their zero set `Z` (a union of pairs of some `J ∈ K`) and let `b_{K|Z^c}(q−1)` be the zero-free intersection count of the family induced on the complement. In nine families at `q = 3, 9`:

`B_K(q) ≤ Σ_Z b_{K|Z^c}(q−1) ≤ P_K(q)`,

with equality throughout for `K = J`, and strict first inequality for some proper subfamilies.

## 4 · DEAD ROUTES (facts; do not retry)
- **`A = P` ⟹ (S):** false for subfamilies (§2.3). No argument that uses only Theorem A proves (S).
- **Arguments valid for every subfamily:** they prove a false statement (§2.3).
- **The «Descent Principle»** (the intersection statement at `q` ⟹ at `3q`, via its «Lemma B»): its Lemma B is false (counterexample `t = e_1`). No inductive step in `q` is known.
- **Averaging over a group of order divisible by 3** in characteristic 3.
- **A statement obtained from (S) by Matlis or Gorenstein duality is EQUIVALENT to (S), not weaker:** it is a restatement, not a reduction (e.g. §1.4).
- **Measuring cells as a substitute for a proof.**

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).**
  - Write the plan, with an estimate for EVERY run.
  - **Seal at least SIX predictions before running anything, at least THREE of them risky in the sense of rule 14** (for example, a value at `(6,3)`, `(3,9)` or `(2,27)`, or a graded rank sequence at a cell not in §3).
  - Score them at the end, hits and falsified printed the same size.
- **STEPS 1–4 — your design.** Allocate them to the ladder of §0 as you judge best. Every PROVED claim carries its proof in the report and its gates (rule 13).
- **STEP 5 — Verdict** (10 min), after re-reading the disk.
- **WHAT I FOUND BEAUTIFUL:** one paragraph.
- **FOR MISSION 16:** what is proved, what is open (stated exactly), and your estimate of what (S) for every `k` and `q` still takes.

## 6 · SUCCESS
- **R1:** (S) for `q = 3`, every `k`.
- **R2:** (S) for `k = 2`, every `q = 3^v`.
- **R3:** (S) for `k ≤ 4`, every `q = 3^v`.
- **R4:** (S) on another infinite family, stated exactly.
- **FULL:** (S) for every `k` and every `q = 3^v`: Conjecture 1.2 of [DS] for `m = 3^v` and every even dimension.

## 7 · NOTATION SUMMARY
- `k ≥ 0`; `N = 2k+2`; `q = 3^v`.
- `C = F_3[y_1..y_{2k+1}]/(y_i^{q−1})`, of dimension `(q−1)^{2k+1}`.
- `J` = the matchings of `{0..2k+1}`, `|J| = (2k+1)!!`.
- `D(a,b) = Σ_{u=0}^{q−2}(−1)^u a^u b^{q−2−u}`, and `D_J = Π` over the pairs of `J` avoiding `0`.
- `Q_k(q) = N![y^N] I_0(2y)^{(q−1)/2}`.
- **(S): `dim (D_J : J ∈ J)C = Q_k(q)`**; `≤` is proved.

## 8 · REFERENCES
- [DS] A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties*, J. Math. Soc. Japan **68**:3 (2016), 975–996; arXiv:1405.4683 (v3, 14 July 2015, the latest version).
- [De14] A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477.
- [De15] A. Degtyarev, *Projective spaces in Fermat varieties*, arXiv:1512.06199, Conjecture 4.4.
