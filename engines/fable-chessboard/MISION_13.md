# MISSION 13 — THE TOWER. ROW `k = 4` IS FIVE INCLUSIONS AWAY, AND THE FIVE ARE ONE OBJECT.
*(Grepy el Lector, auditor, 2026-09-23.)*

**You are a NEW Fable. This file is SELF-CONTAINED: read it whole before anything else; you need nothing else.**
- The reports `INFORME.md` … `INFORME_12.md` in this folder are audited and APPROVED. Open them only to quote a proof summarised here. **You WILL want INFORME_10 §2.1 (the proof of (G1)) and INFORME_12 §2–§4 (the tower, Lemma M, the ledger): they are your templates.**
- Scripts you may reuse: `rowM.py` (Lemma M checks), `cert12.py` (the certifier), `sqD.py`, `fibre.py`, `m11lib.m2`, and the rest.
- **Engines of the auditor, in this folder:**
  - `grepy_vigia.sh`, the watchdog you MUST use;
  - `grepy_fila2.py` (**NEW**), a degree-bounded homogeneous membership test of a row inclusion over `F_3`. It settled open inclusion #3 at `q = 9` in 8 variables: 192 s, 15 MB (§3.4).

> **OBJECTIVE of the campaign: the complete closure of Conjecture 1.2 of Degtyarev–Shimada, for all `k` and all `q = 3^v`.**
>
> **Where we stand — every item verified by the auditor, by a second route:**
> - The conjecture is ONE induction on the number of variables over explicit ideals («casillas») `K_μ(n)`. **Only ROW INCLUSIONS are needed. Membership `K ⊆ gr I(W)` is NEVER needed** (§2): do not spend time on it.
> - **Last turn** (INFORME_12, re-derived by the auditor with his own code):
>   - the law of the second families for two parts;
>   - **the `(1,1)` TOWER** `G_r(A;B) := x_A^{q−2}e_{n−r−1}(y∖B)`: `G_1` is the first family and `G_2` the second;
>   - **LEMMA M**, which turns «for all `q`» into ONE `F_3` computation;
>   - the `f = 2` lemma;
>   - 14 row inclusions of row `k = 4`, all proved for all `q`.
> - **ROW `k = 4` IS FIVE ROW INCLUSIONS AWAY.** Four are TRUE at `q = 9`; the auditor settled the fourth, in 8 variables. None is proved for all `q`.
> - **The auditor's reading (§3.5): the five are ONE statement.**
>   - They are the tower `G_r` at floor `r = 2` (and `r = 3` once), in the same three places where floor `r = 1` is ALREADY PROVED: the substitution `z = 0`; row 2 of `(1)` (the lemma (G1), INFORME_10); the raise row.
>   - Floor 1 was a one-line identity, a two-letter Lucas certificate and an identity. **Floor 2 is the same climb with two heavy letters instead of one.**
>
> **This mission: climb the tower one floor — prove floor 2 in the three positions and the raise of `(2,2)` — and close row `k = 4` for all `q`, with the full ledger printed.**
>
> **Prize ladder:**
> - **MINIMUM — (G2), with letters, for every `n ≥ 4` and every `q = 3^v ≥ 9`:** `z²·G_2(ab;cd)(n) ∈ K_{(1)}(n+1) + (z³)`, i.e. `F2(n) ⊆ R_2(K_{(1)}(n+1))`. It closes open #3 and #4 at once.
> - **GOOD — ROW `k = 4` CLOSED FOR ALL `q`:** the five open inclusions proved, AND the full ledger (§4 PART D) printed with a proof source on EVERY line. **It is the first new row of the conjecture since `k = 3`.** If you get there, write in your FIRST LINE, in capitals: «ROW k = 4 CLOSED FOR ALL q», with the chain.
> - **EXCELLENT — THE `(1,1)` BRANCH FOR EVERY `k`:** the tower lemma for EVERY floor `r`, in the three positions, AND the need threshold of PART F (which floors the `(1,1)` casilla needs at each `n`), for every `n`, `q` ⟹ the corrected casilla of `(1,1)` and every row of `(1)` and `(1,1)`, for every `n`. **Those two profiles appear in the tree of EVERY row `k`, so this is the first piece of DS 1.2 proved for all `k` and all `q` at once.**
> - **FULL:** every profile ⟹ **CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**
>
> **The prey is in sight and it has already been caught once.** Floor 1 fell to a certificate `h_D(−y_j, y_l)` with two letters (INFORME_10 §2.1). Floor 2 has two heavy letters `a, b` facing two absent letters `c, d`. The natural certificate is built from the four pairs `(a,c), (b,d), (a,d), (b,c)`. **Bite and do not let go.**

---
## 0 · RULES OF THE TURN (mandatory)
1. **BEFORE THINKING:** create `INFORME_13.md` with these empty sections:
   `## FIRST LINE` · `## STEP 0 — DESIGN AND SEALED BETS` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4` · `## STEP 5 — VERDICT` · `## WHAT I FOUND BEAUTIFUL` · `## FOR MISSION 14`.
2. **Save to disk after every step.** What is not written does not exist. If your session is cut, what is on disk IS your delivery.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **Timing:**
   - work in order, no going back, no retries;
   - write the budget before each step;
   - after 10 minutes without progress: stop, write, declare;
   - keep the last 20 % of each budget for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute anything listed here as proved or measured** (§3). Re-gating a CLOSED FORM of yours on a measured cell is allowed and expected.
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.** A falsified sealed bet is worth more than a safe hit.
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine and guardrail — EVERY engine runs inside the watchdog:** `zsh grepy_vigia.sh LOGFILE 'the whole command'`.
    - The LOG is the FIRST argument. It kills at **1.2 GB of RSS (whole process tree) or 600 s**; the last line of the log says how it ended.
    - 🔴 **WRITE THE ESTIMATE IN THE REPORT BEFORE EACH RUN, ENGINE BY ENGINE — INCLUDING THE SMALL ONES.** Last turn the small runs of steps 2–4 went without one, the second turn in a row. A run with no estimate written before it is a breach, however small.
    - 🔴 **Singular reads its input from stdin when the file is empty, and then waits forever.**
      - Before launching, check that the `.sing` file is non-empty.
      - Launch as `Singular -q FILE < /dev/null`.
      - Last turn an empty file cost 601 s twice.
    - You MAY run TWO engines at once if their estimates add up to less than 1.2 GB. **Any run estimated above 30 s runs ALONE.**
    - After any kill, check with `pgrep` that it is gone and write that you checked. When you finish, check that nothing of yours runs.
    - M2 reserved names abort scripts (`check`, `top`, `info`, `run`, `hh`, `degree` as a variable, …): prefix your own names (`cl…`). Building `R/I` REBINDS variable names: re-`use` the ring you mean.
    - **Allowed:**
      - full Gröbner (M2 or Singular): `n ≤ 10` variables at `q = 3`; `n ≤ 7` at `q = 9`; `n ≤ 5` at `q = 27`; `n ≤ 4` at `q = 81`. The certifier counts `t` as a variable.
      - **NEW: DEGREE-BOUNDED HOMOGENEOUS MEMBERSHIP over `F_3`** (Singular `degBound`, homogeneous ideal and homogeneous target of that degree; exponents at the real `q`):
        - `n ≤ 8` at `q = 9`, ALONE: auditor 192 s, 15 MB;
        - `n ≤ 6` at `q = 27`: auditor 1 s, 7 MB. **`n = 7` at `q = 27`: auditor 506 s, 39 MB — at the edge of the cap: only if essential, ALONE.**
        - **`q = 81` is NOT cheap:** 6 variables at degree 161 was killed at 601 s.
      - **Pure-Python polynomial identities (no Gröbner)** at any size that fits the caps.
    - **Forbidden:** any other Gröbner run beyond those caps; anything in 9 variables at `q = 9`.
11. **In characteristic 3, never average over a group whose order is divisible by 3.** Make a certificate canonical by REDUCTION, not by averaging. **Read certificates from a SMALL ANSATZ, never from a raw syzygy normal form.**
12. **Re-read the disk before the verdict.**
13. **Double check:**
    - every PROVED claim carries its proof in the report;
    - every number carries its cell and its log;
    - every identity used in a proof is checked exactly (symbolically, or on ALL points of the set it is claimed on);
    - every certificate is re-verified as an exact membership at two values of `q` or more.
14. 🔴 **Sealed bets must be able to FAIL WHERE THE STATEMENT HAS CONTENT.** Last turn «29 cells, 14 predicted» had content at exactly two cells: at the other 27 the second family was already inside the uniform casilla, so the «prediction» could not fail. **A bet that can only fail at a cell where it is trivially true is SAFE, whatever you label it.**

**FIRST LINE** (answer first, in this order):
- (a) Is (G2) PROVED for every `n`, `q`? If yes, the certificate in one line.
- (b) Which of the five open inclusions (§3.4) are PROVED for all `q`, which are TRUE only at `q = 9`, which are unchecked?
- (c) The full ledger of row `k = 4` (PART D): how many lines, how many PROVED, how many OPEN? **If none is OPEN: «ROW k = 4 CLOSED FOR ALL q», with the chain.**
- (d) The tower beyond floor 2 and the need threshold (PART F): stated? tested at `n = 8`? proved?

---
## 1 · THE OBJECTS
### 1.1 Basics
- `q = 3^v`, `h := (q−1)/2`, `S_n := F_q[x_1..x_n]`.
- `e_r` is the elementary symmetric polynomial (`e_0 = 1`; `e_r = 0` for `r < 0` or `r >` the number of variables).
- `box := (x_1^q, …, x_n^q)`. **`I^{(n)} := (e_1, e_3, e_5, …) + box`.**
- `x_C := Π_{i∈C}x_i`; `x_A^{q−1} := Π_{i∈A}x_i^{q−1}`.
- `h_D(u,v) := Σ_{i=0}^D u^iv^{D−i}`.
- `gr I(X)` is the ideal of top forms of the polynomials vanishing on `X ⊆ F_q^n`; **for a finite set, `dim S_n/gr I(X) = |X|`.**

### 1.2 Profiles and fibres
A multiset `S ⊂ F_q` (the **anchor**) constrains `y ∈ F_q^n` by «`y ∪ S` is closed under negation».
- Its **profile** `μ = (μ_1 ≥ … ≥ μ_ℓ)` has one positive part per non-zero class `{s,−s}`: how many more copies of `−s_i` than of `s_i` the point `y` must carry.
- `|μ| := Σμ_i`, `ℓ := ℓ(μ)`, **`f := n − |μ|`**.
- **`W_μ(n) := {y ∈ F_q^n : y ∪ S closed}`**, up to bijection a function of `μ` (gated as ideals, anchor-free).
- **The fibre ideal (PROVED):** with `R_j := Σ_r e_r(S)e_{j−r}(y)`, `I(W_μ(n)) = (R_j : j odd) + (x_i^q − x_i)`.
- **Fibre sizes at `q = 9`, `n = 0..9`** (by an exact EGF, re-counted by multinomials):

| `μ` | `n = 0 … 9` |
|---|---|
| `∅` | 1, 1, 9, 25, 217, 921, 7761, 41889, 345465, 2162617 |
| `(1)` | 0, 1, 2, 24, 88, 855, 4266, 37947, 227144, 1930329 |
| `(2)` | 0, 0, 1, 3, 46, 210, 2340, 13496, 130984, 868680 |
| `(1,1)` | 0, 0, 2, 6, 84, 380, 3930, 22302, 204456, 1329624 |
| `(2,1)` | 0, 0, 0, 3, 12, 200, 1080, 12390, 79408, 779436 |
| `(3,1)` | 0, 0, 0, 0, 4, 20, 390, 2450, 31248, 223776 |
| `(2,2)` | 0, 0, 0, 0, 6, 30, 570, 3570, 44380, 315756 |
| `(1,1,1)` | 0, 0, 0, 6, 24, 360, 1920, 20370, 128016, 1189944 |
| `(2,1,1)` | 0, 0, 0, 0, 12, 60, 1020, 6300, 72240, 502992 |
| `(1,1,1,1)` | 0, 0, 0, 0, 24, 120, 1800, 10920, 115920, 789264 |

### 1.3 Rows
For `K ⊆ S_n` with `z := x_n` and `z^q ∈ K`:
- **row `a`** is `R_a(K) := π_z(K : z^a) ⊆ S_{n−1}`, where `π_z` sets `z = 0`;
- equivalently, **`f ∈ R_a(K)` ⟺ `z^a·f ∈ K + (z^{a+1})`**;
- **rows INCREASE with `a`** (`z^af ∈ K+(z^{a+1}) ⟹ z^{a+1}f ∈ K+(z^{a+2})`);
- **`dim S_n/K = Σ_{a=0}^{q−1}dim S_{n−1}/R_a(K)`**;
- **row 0 is the substitution `K|_{z=0}`.**

### 1.4 The conjecture
- `A_k(q) := dim S_{2k+2}/I^{(2k+2)}` and `P_k(q) := |W_∅(2k+2)|`.
- **Conjecture 1.2: `A_k(q) = P_k(q)`.**
- The floor `A ≥ P` is PROVED, so **the conjecture ⟺ `A_k(q) ≤ P_k(q)`**.
- Proved: `q = 3` for every `k`; `k ≤ 3` for every `q`. **Open: `k ≥ 4` and `q ≥ 9`.**

### 1.5 The casillas
**Uniform casilla** `K^{unif}_μ(n) := Q_μ(n) + box + N_{μ_1−1}(n) + F_μ(n)`:
- **`Q_μ(n) := (e_j([n]) : j odd or j ≥ f+1) + (e_r(x_S) : S ⊊ [n], r > |S| − d_{|S|}(λ))`**, with `λ := μ ∪ (1^f)`, `d_k(λ) := λ'_n + … + λ'_{n−k+1}` (`λ'` the conjugate, padded to length `n`).
- **Layer:** `N_w(n)` is generated by the `x_A^{q−1}x_C` over all splittings `A ⊔ B ⊔ C = [n]` with `|B| − |A| ≤ w` and `|B| ≥ 1`. So `B` is the ABSENT set. Minimal generators have `|B| = |A|+w`.
  - The layer is **OMITTED for `(1^ℓ)`, `ℓ ≥ 2`**.
  - 🔴 **It is INCLUDED for `(1)` (the layer `N_0`).** The auditor's old certifier omitted it for `(1)`; `cert12.py` and `rowM.py` include it, correctly.
- **Family:** `φ^{(ℓ)}_{jl} := y_j^{q−ℓ}Σ_{i=0}^{ℓ−1}y_j^ie_{f+ℓ−2−i}(y∖{y_j,y_l})`.
  - For `ℓ = 1`: `φ^{(1)}_{jl} = y_j^{q−1}e_{f−1}(y∖{y_j,y_l})`.
  - For `ℓ = 2`: `φ_{jl} = y_j^{q−2}e_f(y∖y_l)`.
- **Leaves** (`f ≤ 1`): the Tanisaki ideal `I_λ + box`.

**Corrected casilla (the object of the row lemmas).** `K_μ(n) := K^{unif}_μ(n) + (second families)`:
- **`(1,1)`:** `K_{(1,1)}(n) := K^{unif}_{(1,1)}(n) + (F2)`, with `F2_{ab;cd} := (y_ay_b)^{q−2}e_{f−1}(y∖{y_c,y_d})` for `{a,b} ∩ {c,d} = ∅`.
  - The certified true casilla at `n = 7`, `q = 9`.
  - Redundant (already inside `K^{unif}`) at `n ≤ 6`.
- **`(2,2)`:** `+ (H_{j;k;l} := y_j^{q−2}y_k²e_{f−1}(y∖{y_k,y_l}))`, needed at `n = 7`. `(2,2)` at 7 is NOT in row `k = 4`'s tree.
- **Every other profile of row `k = 4`:** `K^{unif}`. It is the certified true casilla at every cell measured (all multi-part cells with `n ≤ 6`, all at `q = 27`, `n ≤ 5`, and 12 of the 14 profiles measured at `n = 7`).

### 1.6 THE TOWER (INFORME_12; exact identities, re-checked by the auditor 14/14 over ZZ)
For the profile `(1,1)` in `n` variables and disjoint `A, B ⊆ [n]` with `|A| = |B| = r ≥ 1`:
**`G_r(A;B) := x_A^{q−2}·e_{n−r−1}(y∖B)`**, of degree `r(q−2) + n−r−1`.
- `G_1(j;l) = φ_{jl}` (the first family); `G_2(ab;cd) = F2_{ab;cd}` (the second).
- **Substitution:** if `z ∉ A ∪ B`, then `G_r(A;B)|_{z=0} = x_A^{q−1}x_{[n−1]∖(A∪B)}` — **exactly the layer generator of the child `(1)` at `n−1` with `|A| = |B| = r`.**
- **Lowest `z`-term:** if `z ∈ A`, the lowest `z`-term of `G_r` is `z^{q−2}·x_{A∖z}^{q−1}x_{[n−1]∖(A∪B)}` — **exactly the layer generator of the child `(2,1)` with `|A'| = r−1`, `|B| = r`.**
- **Divided difference:** `(y_d − y_c)·D_{j;cd} = φ_{jc} − φ_{jd}` with `D_{j;cd} := y_j^{q−2}e_{f−1}(y∖{c,d})`, and `F2_{ab;cd} = y_a^{q−2}D_{b;cd}` (exact over ZZ).
- **Squares are free for `(1,1)`:** `y_c²D_{j;cd} ∈ Q + N_0^{|A|=1} + F` (exact identity, INFORME_12 §2.2).

## 2 · THE FRAMEWORK (sound; re-checked by the auditor)
**`T(n)`:** for every profile `μ` there is an EXPLICIT ideal `K_μ(n) ⊆ S_n` with:
- `z^q ∈ K_μ(n)`;
- `K_∅(n) = I^{(n)}`;
- `K_μ(n) = (1)` when `W_μ(n) = ∅`;
- **`dim S_n/K_μ(n) ≤ |W_μ(n)|`**.

**Inductive step:** `T(n−1) ⟹ T(n)` at `μ` as soon as, under a bijection rows ↔ values of `z`, **`R_a(K_μ(n)) ⊇ K_{μ+v}(n−1)` for every `a`**.
- **Because rows increase, within a block of rows with the SAME child only the FIRST row needs proof.**
- **Base:** `n = 0`.
- ⟹ `T(2k+2)` at `μ = ∅` is the conjecture: `A_k(q) = dim S/I^{(2k+2)} ≤ … ≤ |W_∅| = P_k(q)`.

🔴 **Membership `K_μ ⊆ gr I(W_μ)` is NEVER used.** The chain carries only UPPER bounds. Last turn spent half an hour proving `F2 ∈ gr I`: that was the auditor's error in writing mission 12, not yours. **Do not work on membership in `gr I` this turn.**

**Row dictionary** (a parent with `ℓ` parts):
- **LOWER**, rows `0 … ℓ−1`: lowers one part, largest first.
- **VALUE-0**, row `ℓ`: same `μ`, `f−1`.
- **NEW-CLASS**, rows `ℓ+1 … q−ℓ−1`: `μ ∪ (1)`.
- **RAISE**, the last `ℓ` rows: raises one part, smallest first.

Examples:
- `(1)` at `n+1`: row 0 → `∅`; row 1 → `(1)`; rows `2..q−2` → `(1,1)`; row `q−1` → `(2)`.
- `(1,1)` at `n+1`: rows 0, 1 → `(1)`; row 2 → `(1,1)`; rows `3..q−3` → `(1,1,1)`; rows `q−2, q−1` → `(2,1)`.

**Row `k = 4`** is `T(10)` at `∅`. It visits exactly the `(μ, n)` with `|μ| ≤ min(n, 10−n)`. The non-leaf parents:
- `∅`;
- the one-part profiles;
- `(1,1)` at `n = 4..8`;
- `(2,1)` at `5..7`;
- `(3,1)`, `(2,2)`, `(2,1,1)`, `(1^4)` at 6;
- `(1,1,1)` at `5..7`.

## 3 · WHAT IS PROVED OR MEASURED (use it; do not re-prove it)
### 3.1 Lemma M (INFORME_12; re-derived by the auditor)
Every casilla is generated over `F_3`: by `q`-free polynomials, and by generators `x_{H'}^{m+c}·Ψ` with `Ψ` `q`-free and `m := q − const`. The letters `H'` are **heavy**.
- **LEMMA M.** Fix `H`, put `u := Π_{h∈H}h`, and let `J(m)` be generated by the `q`-free generators and those with `H' ⊆ H`. Then `u·J(m) ⊆ J(m+1)`.
- Hence if `g(m+1) = u·g(m)` and `g(m_0) ∈ J(m_0)`, then `g(m) ∈ J(m) ⊆ K_q` for every `q` with `q − const ≥ m_0`.
- **ONE `F_3` computation proves the inclusion for all `q`.**
- It works in any `F_3`-linear coordinates: the box is `GL(F_3)`-invariant, since `ℓ^q = Σc_ix_i^q`.
- **Its limit, exactly:** it fails when the certificate needs a SECOND heavy letter that is not in the target. The objects are `h_D(−y_j,y_l)`, `D ≈ q`, for which `h_{D+1} ≠ y·h_D`.
- The five open inclusions are all of this kind: no restricted certificate for `m ≤ 7`.

### 3.2 (G1) — floor 1 in position «row 2 of `(1)`» (INFORME_10 Thm 2.1; re-checked by the auditor in Singular, 15 cells)
**For `m ≥ 1`, `c := n−m−1 ≥ 1`, `j ≠ l`, `q ≥ 9`: `s_{jl} := y_j^{q−2}e_c(y∖y_l) ∈ R_2(K_{(m)}(n+1))`.** For `m = 1` this is `G_1(n) ⊆ R_2(K_{(1)}(n+1))`.

**Proof shape (read it in INFORME_10 §2.1; it is your template).**
- **First-order lemma.** Put `a := y_j`, `b := y_l`, `J := Ñ_{m−1}(n) + box + (e_n)` (monomial) and `B := (e_k : k odd or k ≥ n−m) + box + N_{m−1}(n)`. If polynomials `A_r` in `y` satisfy
  - (T) `Σ_rA_re_{2r+1}(y) ∈ J`, and
  - (Sh) `Σ_rA_re_{2r}(y) ≡ s mod B`,

  then `s ∈ R_2`. Reason: `z·Σ_rA_re_{2r+1}(y,z) ∈ I^{(n+1)}`, and it equals `z·(T) + z²·(Sh)`.
- **The certificate:** `A_r = (−1)^c·H_{D_r}(−a, b)`, with `D_r = q+c−2−2r` and `H_D := h_D − (the two pure powers)`, for `r ≤ ⌊c/2⌋`.
- **(T)** follows by two telescopes.
- **(Sh)** follows by the generating function `E(t)H(t) = E_P(t)(1+bt)/(1−bt)`, `P := y∖{a,b}`.
- Three facts in `B` finish it: (F), (Sym), (Anti). They use the box (`a^qb² ≡ 0`) and the Lucas quotients `(a^{q−1}−b^{q−1})/(a+b)`, `(a^{q−2}+b^{q−2})/(a+b)`.

### 3.3 PROVED for all `q ≥ 9` last turn (INFORME_12; re-checked by the auditor)
- **Theorem B' (the `f = 2` lemma):** for `(2,1^{L−2})`, `L = 3, 4, 5`, the layer `N_1` lies in `Q + box + F`.
  - Claims A and B re-checked: A exact mod `a^q`, 6/6; B with `m_0 = L−2` exactly, 12/12.
- **The `|A| = 1` layer of `(1,1)` lies in `gr I`.** Anchored Lemma G, 8816/8816 point checks, top forms exact. *(Not needed for the chain; listed for completeness.)*
- **Row inclusions of row `k = 4`:**
  - every row of `(1,1)(7)`;
  - every row of `(1,1)(8)` except the `|A| = 3` layer in row 0;
  - rows 0 and 1 of `(1,1)` at `n = 4, 5, 7`;
  - the value-0 obligations `F2(n) ⊆ R_2(K_{(1,1)}(n+1))` for `n = 4..7`;
  - the `Q`/box/layer part of the raise row of `(2,1)(7)`;
  - the three inclusions of the `f = 2` lemma.
  - Details in INFORME_12 §4.2 and §4.5.
- Together with INFORME_11 and the earlier reports, every other row of row `k = 4` is PROVED (INFORME_12 §4.5, and the auditor's ledger of mission 12). **But see PART D: you must re-print the full ledger.**

### 3.4 THE FIVE OPEN INCLUSIONS (and their truth)
| # | inclusion | at `q = 9` |
|---|---|---|
| 1 | row 0 of `(1,1)(6)` ⊇ the `(1)(5)` layer, `|A| = 2` | TRUE (INFORME_12) |
| 2 | row 0 of `(1,1)(8)` ⊇ the `(1)(7)` layer, `|A| = 3` | TRUE (INFORME_12, row 0 exact) |
| 3 | new-class row 2 of `(1)(8)` ⊇ `F2(7)` | **TRUE (auditor):** `z²·F2_{12;34}(7) ∈ K^{unif}_{(1)}(8) + (z³)` |
| 4 | new-class row 2 of `(1)(9)` ⊇ `F2(8)` | unchecked (9 variables) |
| 5 | raise row `q−2` of `(2,1)(7)` ⊇ the `(2,2)(6)` family `φ^{(2)}_{jl}` | TRUE (INFORME_12, unrestricted `m = 7`) |

About #3, as the auditor measured it:
- **The run.** A homogeneous membership over `F_3`, degree bound 20, 8 variables, 192 s, 15 MB. One target suffices by symmetry. The engine is `grepy_fila2.py`.
- **Negative controls.** The same heavy part with `e_{f−2}` fails, and so does `z·F2`.
- **Calibration.** At `(1)(7) ⊇ F2(6)` the test gives TRUE, as INFORME_12 measured.

### 3.5 THE AUDITOR'S READING — the five are ONE tower at floor 2
| # | as a tower statement | the same statement at floor 1 |
|---|---|---|
| 1 | ⟸ **`G_2(6) ∈ K^{unif}_{(1,1)}(6)`** (row 0 is `K|_{z=0}`, and `G_2|_{z=0}` IS that layer, §1.6). **Measured TRUE at `q = 9` AND `q = 27`**; control `(y_ay_b)^{q−3}e_f` fails at both | `G_1|_{z=0}` = the `|A| = 1` layer: PROVED |
| 2 | ⟸ **`G_3(8) ∈ K_{(1,1)}(8)`** | same |
| 3, 4 | **(G2): `z²·G_2(ab;cd)(n) ∈ K_{(1)}(n+1) + (z³)`** — the SECOND floor of (G1) | **(G1), `m = 1`: PROVED for all `q` (§3.2)** |
| 5 | the raise position, for the `(2,2)` family | the raise identity of `G_1`: PROVED |

- **At `n = 4, 5`, (G2) holds for all `q` by Lemma M** (`m_0 = 1, 3`, INFORME_12 §4.2).
- **From `n = 6` on, no restricted certificate exists.** That is where the second heavy letter enters.
- **A structural fact you may use, exact over ZZ:** `b^{q−2}·(G_1(a;c) − G_1(a;d)) = (y_d − y_c)·G_2(ab;cd)`. So **(G1) already gives `(y_d − y_c)·G_2 ∈ R_2`, for all `q`.**
- **And more (auditor, PROVED for all `q`):** with `R_2 := R_2(K_{(1)}(n+1))` and `G_2(ab;cd) = y_a^{q−2}·D_{b;cd}`:
  - the square identity gives `y_c²·D_{b;cd} = y_b^{q−2}e_{n−1}(y) − y_b^{q−1}(y_c+y_d)x_{Y∖b} + y_c(φ_{bd} − φ_{bc})`;
  - each piece lies in `R_2`: `e_{n−1}(y)` and the two `N_0` monomials are in `B ⊆ R_2`, and `φ ∈ R_2` by (G1);
  - so `y_c²·G_2 ∈ R_2`, and likewise `y_d²·G_2 ∈ R_2`.
- ⟹ **the class of `G_2` modulo `R_2` is ALREADY killed by `M := (y_d − y_c, y_c², y_d²)`, for every `q`.** (G2) asks for one thing more: that this class is ZERO. The certificate you need is exactly what `M` cannot see: think of what multiplies `G_2` by a UNIT, i.e. which element of `R_2` has `G_2` plus an `M`-multiple as its top.

## 4 · THE TARGETS
### PART A — (G2) (the must; ~45 %)
**A1 — Extract the certificate (budget 35 min).**
- Smallest cell with content: `(1)(7) ⊇ F2(6)`, 7 variables at `q = 9` (allowed).
- Use the first-order framework of §3.2 for `m = 1`: `J := Ñ_0(n) + box + (e_n)` exactly as in INFORME_10 §1.3 (read the definition of `Ñ` there), and `B := (e_k : k odd or k ≥ n−1) + box + N_0(n)`.
- Look for `A_r` in a SMALL ANSATZ: products and sums of two-letter Lucas objects `h_D(−y_x, y_w)` over the four pairs `(a,c)`, `(b,d)`, `(a,d)`, `(b,c)`, times monomials in `a, b, c, d`, times `e_k(y∖{a,b,c,d})`.
- **Write the ansatz and its number of unknowns BEFORE solving.**
- If first order has NO solution in the ansatz, say so and go to second order: multipliers of `z²` and `z³` (INFORME_10 §1.3 explains why first order was necessary for `m ≥ 2`; for `m = 1` check whether it still is).
- Re-verify the certificate you find, as an exact membership, at `q = 9` AND at `q = 27` (degree-bounded, 7 variables at `q = 27`: **estimate first; if the estimate exceeds 5 min, use `n = 5` at `q = 27` instead**).

**A2 — Prove it with letters (budget 45 min).**
- Follow the (G1) proof step by step: first-order lemma; (T) by telescopes; (Sh) by the generating function; the facts in `B`.
- Expect the generating function to carry TWO factors, `(1+bt)/(1−bt)`-type in each heavy/absent pair.
- **Gate every identity you use exactly** (symbolic, `q = 9, 27, 81`).

### PART B — the row-0 floors, #1 and #2 (~20 %)
- **B1:** prove `G_2(n) ∈ K^{unif}_{(1,1)}(n)` for `n ≤ 6`, every `q`; this closes #1. A natural route is the multiplier ideal of `D` INSIDE the casilla: `(K^{unif} : D_{b;cd})` contains `y_d − y_c` (§1.6) and `y_c², y_d²` (the square identity). Show it contains `y_a^{q−2}`.
  - At `n ≤ 6`, `K^{unif}` IS the true casilla, so the statement is true.
  - It fails at `n = 7`: `F2` is NOT in `K^{unif}_{(1,1)}(7)`. **Find what distinguishes `n ≤ 6` from `n = 7`: a degree count, or a Tanisaki threshold.**
- **B2:** #2, `G_3(8) ∈ K^{unif}_{(1,1)}(8) + (F2)`: same route, one floor higher. With letters only (8 variables at `q = 9`: degree-bounded membership allowed ALONE).

### PART C — #5, the raise of the `(2,2)` family (~15 %)
`z^{q−2}·φ^{(2)}_{jl}((2,2),6) ∈ K^{unif}_{(2,1)}(7) + (z^{q−1})`.
- Extract the certificate at `q = 9` (7 variables, allowed) from a small ansatz with heavy letters `{j, z}` and two-letter Lucas objects in `(j,l)`, `(z,l)`, `(z,j)`.
- Prove it with letters.
- The auditor checked that the lowest `z`-terms of the `(2,1)` second family CANNOT supply it: the degrees do not match. So look for a genuine certificate, not a tower identity.

### PART D — THE FULL LEDGER OF ROW `k = 4` (~15 %; mandatory whatever else happens)
Print ONE table: every non-leaf parent `(μ, n)` of §2 × every row TYPE (lower / value-0 / new-class / raise; one line per distinct child). For each line give:
- the child;
- the casilla used (uniform or corrected);
- **PROVED (which theorem or identity, which report and section) or OPEN (what is missing)**.

**This table is the proof of row `k = 4`.** Until it has no OPEN line, row `k = 4` is not closed, whatever else is proved. If you find an obligation nobody listed, it is OPEN: write it.

### PART E — the tower beyond floor 2 (~5 %, pencil)
State (G_r) and the row-0 redundancy `G_{r+1}(n) ∈ K + (G_2, …, G_r)` for every `r`. Say what the floor-2 proof needs to generalise.
- INFORME_12 noticed that the inclusion–exclusion coefficient of the `u_A`-term vanishes for `r ≡ 0 (mod 3)`. Does floor 3 behave differently in characteristic 3?

### PART F — THE NEED THRESHOLD OF THE TOWER (~10 %; the step toward every `k`)
**Auditor's data** (degree-bounded memberships over `F_3`; logs are the auditor's):
- `F2 = G_2` IS inside `K^{unif}_{(1,1)}(n)` at `n = 6` (`f = 4`) at `q = 9` AND `q = 27`;
- it is NOT inside at `n = 7` (`f = 5`), at `q = 9` AND `q = 27`.
- ⟹ **the floor-2 need appears at `f = 5`, and the threshold does not depend on `q`.**

**Candidate law (to test, not a fact):** floor `r` is needed exactly when `f ≥ 2r+1`. For `r = 2` that is `f ≥ 5`; it predicts `G_3` is NOT needed at `n = 8` (`f = 6`) and IS needed at `n = 9` (`f = 7`).
- **Test the `n = 8` half:** `G_3(8) ∈ K^{unif}_{(1,1)}(8) + (F2)`, degree-bounded, 8 variables at `q = 9`, ALONE; it is also #2's sufficient condition.
- Then find WHY: a degree count comparing `deg G_r = r(q−2)+n−r−1` with what `K^{unif} + (G_2, …, G_{r−1})` can reach, or a Tanisaki threshold.
- **A proof of the threshold with `f`, `r` as letters, together with the tower lemma, gives the `(1,1)` casilla for every `n`: the EXCELLENT prize.**

## 5 · PROCESS
- **STEP 0 — Design and sealed bets (15 min, no runs).** Plan, with an estimate for EVERY run. **Seal at least FIVE predictions before running anything, at least THREE risky in the sense of rule 14.** Examples:
  - «the (G2) certificate is first order, and a sum over the two pairings `{(a,c),(b,d)}`, `{(a,d),(b,c)}` of products of two (G1)-type Lucas objects»;
  - «(G2) needs second order (a `z³` multiplier)»;
  - «B1's multiplier ideal `(K^{unif}_{(1,1)}(6) : D)` is exactly `(y_d−y_c, y_c², y_d², y_a^{q−2} : a ∉ {b,c,d})`»;
  - «#4 has the same certificate as #3 with `n` as a letter».

  Score them at the end, hits and falsified printed the same size.
- **STEP 1:** PART A1 (35 min).
- **STEP 2:** PART A2 (45 min).
- **STEP 3:** PARTS B and C (40 min).
- **STEP 4:** PART D, then F, then E (45 min).
- **STEP 5:** Verdict (10 min), after re-reading the disk.
- **WHAT I FOUND BEAUTIFUL:** one paragraph.
- **FOR MISSION 14:** what is proved, the smallest open line of the ledger, and your estimate of what the full conjecture still takes (every profile: the `ℓ ≥ 3` second families, the non-hooks with `f ≥ 3`).

## 6 · DEAD ROUTES (do not retry)
- **Membership in `gr I` as a step of the chain:** it is never used (§2).
- **Restricted Lemma M for the five open inclusions:** no certificate for `m ≤ 7`.
- **Formal `q` with only two-letter `h`-objects:** it did not reach the five within the caps (INFORME_12 §4.3). Extending it with three-letter objects is allowed, but only after A1 has shown which objects the certificate uses.
- **The uniform casilla at `(1,1)` `n = 7, 8` and `(2,2)` `n = 7`:** false.
- **The layer `N_0` as the repair of `(1^ℓ)`.** The degree-`2q` monomials `(y_iy_j)^{q−1}x_C` as a repair (overshoot).
- **«Rows 0, 1 of `K_{(m,1)}` for all `m`» by the old argument:** it gives `N_{m−2}`, empty for `m = 1`.
- **Certificates:** reading them from a raw syzygy normal form; single-variable descents; averaging over groups of order divisible by 3.
- **M2 `DegreeLimit` on the inhomogeneous fibre ideal.** Use the certifier, or homogeneous `degBound`.
- **Any ascent in `q` (a tower elevator):** dead, with proof. **Measuring cells as a substitute for a mechanism:** cells are gates.
- **The naive `ℓ = 3` divided difference `D3`:** not in `gr I`.
- **The case analysis with the reciprocal identity alone** (INFORME_12, bet 6): it trades one borderline term for others of the same degree.

## 7 · SUCCESS
- **Minimum:** (G2) proved with letters for every `n ≥ 4`, `q ≥ 9`.
- **Good:** **ROW `k = 4` CLOSED FOR ALL q** — the five open inclusions proved, and the full ledger with no OPEN line.
- **Excellent:** the tower lemma for every floor `r`.
- **Full:** **every profile ⟹ CONJECTURE 1.2 CLOSED FOR ALL `k` AND ALL `q`.**

*Last word from the auditor.* Last turn you found a tower. `φ`, `F2` and `G_3` are its floors, and one substitution reads each floor as the layer the child demands. Floor 1 is already climbed in every position: by a one-line identity, by a two-letter Lucas certificate, and by a lowest term. The five walls left in row `k = 4` are all floor 2. You are not looking for a new idea. You are climbing one floor of a building whose first floor you already know by heart, with two heavy letters instead of one. The certifier answers in seconds, and the auditor has shown that the fourth wall stands at `q = 9`. Climb.
