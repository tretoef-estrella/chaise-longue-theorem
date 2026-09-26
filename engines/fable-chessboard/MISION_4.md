# MISSION 4 «THE INTERACTION LEMMA» — CLOSE THE CONJECTURE FOR ALL k
*(Grepy el Cartógrafo, auditor, 2026-09-22. Your INFORME_3 was audited line by line and APPROVED. Objects and notation: exactly those of MISION_3.md §1 and of your INFORME_3; nothing else is needed. Every fact given here was checked by two routes.)*

> **OBJECTIVE: the complete closure of Conjecture 1.2 of Degtyarev–Shimada for all `k` and all `q = 3^v`, THIS TURN.**
>
> Your turn left the whole conjecture standing on TWO things, both with `k` as a letter:
> - **(L1) the `k`-free lemma (I),(II)** in `F_3[a,a',b,b']/box`, for every `q` ⟹ `(P_k)` for all `k` and `q`;
> - **(L2) the INTERACTION LEMMA:** the interaction elements of the two outer rows (generic and +1) of the explicit ideals `K_k` and `K'_k`, for all `k` ⟹ `(DE_k)`, `(DO_k)`.
>
> **(L1) + (L2) CLOSE THE CONJECTURE** through the chain, which is proved.
> G-a, and the cells `(3,3)`, `(3,9)`, are **gates** of (L2), not goals.
> **Fallback, only if (L2) for all `k` is declared dead with a reason: the row `k = 4` for all `q`** (§4), which nobody has.

---
## 0 · RULES OF THE TURN (mandatory; same as mission 3)
1. **BEFORE THINKING:** create `INFORME_4.md` with the empty sections `## FIRST LINE` · `## STEP 0` · `## STEP 1` · `## STEP 2` · `## STEP 3` · `## STEP 4 — VERDICT`. Write each step under its heading.
2. **Save to disk after every step.** What is not written does not exist.
3. **Header per step:** `STATE: CLOSED | EXHAUSTED | NOT CONCLUDED` and `NEXT:`.
4. **In order, no going back, no step 5, no retries.** Budget written before each step; 10 min without real progress ⟹ stop, write, declare; the last 20 % of each budget is for writing.
5. **At most one literature search per step**, in the original source.
6. **Do not recompute what is given here or in INFORME_3 as verified.**
7. **A negative dimension, or one larger than the box, is a bug:** stop.
8. **«This route dies, for this reason» is a result.**
9. **Write ONLY in `~/Desktop/FABLE_TABLERO/`. Do not open anything in `~/Desktop/ARBOLYAML/`.**
10. **Machine** `/opt/homebrew/bin/M2`: **< 1.2 GB and < 10 min per run, estimate written BEFORE each run, and per run (not per step).** Your `pk4.m2` broke this last turn because the estimate was for the cheap `q`: estimate the most expensive `q` in the loop.
    - Allowed cells: everything of mission 3; **plus** memberships in `≤ 5` variables at `q = 81` (no colon); **plus** `(2,9)` and `(2,27)` for the rank / colon computations of STEP 3.
    - Anything else: do not run it.
11. **Re-read the disk before the verdict.**
12. **Double check:** every claim promoted to PROVED carries its proof in the report; every number carries its cell and its log.

**FIRST LINE** (answer first, in this order):
- (a) Is (L1) proved for all `q`? Is (L2) proved for all `k`? If not, what did you prove, for which `k` and `q`?
- (b) What exact lemma is missing, and in which cell is it checked?
- (c) Does it close the conjecture, or at least the row `k = 4` for all `q`? YES or NO, with the reason in one line.

---
## 1 · NEW FACTS YOU MAY USE (verified by the auditor)
1. **Two external theorems, usable as inputs:** `D(2)` holds for all `q = 3^v` (the «Sofá» theorem, `k = 2`) and `D(3)` holds for all `q = 3^v` (the «Hamaca» theorem, `k = 3`). They were proved by a different method (six zones). Also `D(k)` holds for every `k` at `q = 3` (Steinberg bridge). **You may use `D(2)`, `D(3)` as proved.**
2. **LEMMA (auditor, pencil) — what the chain really needs from a known level.** Let `ℓ_a := dim S_{2k+1}/π'(I^{(2k+2)} : x_{2k+1}^a)`, `a = 0..q−1`, so `ℓ_0 = A'_k`, `ℓ_1 = c_k`, `Σ_a ℓ_a = A_k`, and `ℓ_a` is non-increasing. **If `D(k)` and `D'(k)` hold, then `c_k ≤ N_k ⟺ ℓ_{q−1} ≥ N_k ⟺ rank(×x_{2k+1}^{q−1} on A_k) ≥ N_k`.** *(Proof: `Σ_{a≥1}ℓ_a = (q−1)N_k`; non-increasing terms with that sum are all `≤ N_k` iff all equal `N_k` iff the last is `≥ N_k`; and `ℓ_{q−1} = dim x^{q−1}A_k` because `x^q = 0`.)*
   ⟹ **the chain at level 3 does NOT need G-a.** It needs `c_2 ≤ N_2` (row 1 of `K'_3`). With `D(2)` (fact 1) and `D'(2)` (your mission 2), that is the single statement **`ℓ_{q−1}(k=2) ≥ N_2`**: exhibit `N_2` independent elements of `x_5^{q−1}A_2`. The same at level 3 once `D'(3)` is proved.
   *Context:* for `1 ≤ a ≤ q−2` the bound `ℓ_a ≥ N_k` is PROVED for all `k` by a projection onto `F_q^×`-characters (`J_a ⊆ gr 𝒢`, `𝒢` = ideal of the `F_q`-points of the slice `x_n = 1`, using that the suelo ideal `E + (x^q − x)` is stable under `x ↦ λx`). **At `a = q−1` that proof fails exactly: the garbage pushed down by the projection lands in degree exactly `D` and contaminates the top form.** That single layer is the whole gap at a known level.
3. **Auditor's data on (I),(II)** (independent Python code, dense elimination over `F_3`):
   - consistent at `q = 3` (unique solution) and `q = 9` (homogeneous solution space of dimension 186), confirming yours;
   - `γ_0` has degree `2(q−3)`, `γ_1` degree `2(q−2)`;
   - `γ_0 ∈ F_3[r_1, r_2]` is NOT solvable at `q = 9`;
   - in the pair-symmetric ring `F_3[β_1, β_2, r_1, r_2]` the smallest cap on the `β`-degree of `γ_0` that works is **`q−3`** (caps 0, 2, 4 fail at `q = 9`; cap 0 works at `q = 3`). Expect a `q`-general solution whose `β`-degree grows with `q`.
4. **Simplification of (II) (pencil, auditor):** `ann_B(ε_4) = ann_B(r_1r_2) = (a^{q−1}, a'^{q−1}, b^{q−1}, b'^{q−1})·B`, because `r_1r_2` is a monomial in a monomial box. Hence
   **(II) ⟺ `ε_1γ_1 + ε_3γ_0 ≡ 0` modulo the box of exponent `q−1`.** Only (I) lives in the box of exponent `q`.

---
## 2 · WHY THIS IS THE CLOSURE (the chain, as it stands)
At each level `k ≥ 2`, in order:
- odd step: `D(k−1)` + `(P_k)` ⟹ `J'_1 ⊇ K'_k`; with `(DO_k)` ⟹ `c'_k ≤ N'_k` ⟹ `D'(k)`. *(Row 1 of `K'_k` uses `c_{k−1} ≤ N_{k−1}`, supplied by the previous level.)*
- even step: `D'(k)` ⟹ `J_1 ⊇ K_k`; with `(DE_k)` ⟹ `c_k ≤ N_k` ⟹ `D(k)`.
Base: `k = 0, 1` done. (L1) gives every `(P_k)`; (L2) gives every `(DE_k)`, `(DO_k)`. Nothing else is open.

---
## 3 · PROCESS
### STEP 0 — Reading and inputs (budget 10 min)
No calibration run (it passed 8/8 last turn). Write which facts of §1 you will use, and check fact 4 on paper.

### STEP 1 — (L1): (I),(II) for every `q = 3^v` (budget 45 min)
- Target: a `q`-symbolic pair `(γ_0, γ_1)`, or a structural existence proof (e.g. an exact sequence, or duality in `B = B_a ⊗ B_b` with `B_a = F_3[a,a']/(a^q,a'^q)` Gorenstein with socle `r_1^{q−1}`).
- Tools you have: your closed form at `q = 3`; fact 3 (degrees, `β`-degree `q−3`); fact 4 (the smaller box for (II)); Lucas: `(u+v)^{q−1} = Σ_j (−1)^j u^j v^{q−1−j}` with all coefficients nonzero mod 3.
- Gate: your formula must reproduce solvability at `q = 9, 27` (and may be checked at `q = 81`, 4 variables, no colon).
- If STEP 1 closes, write: **«(P_k) FOR ALL k AND ALL q»**.

### STEP 2 — (L2): THE INTERACTION LEMMA, `k` as a letter (budget 90 min; the heart)
- Target: for all `k`, the generic rows (`2 ≤ a ≤ q−2`) and the +1 row of `K_k` and `K'_k` reach colength `f_gen`, `f_{+1}` (resp. `f'_gen`, `f'_{+1}`).
- Use your pointwise criterion (INFORME_3 §2.2): an interaction element is a monomial `m` with `(x^a m)|_Z ∈ span((M + (x^{a+1}))_{a+deg m}|_Z) + F_{a+deg m−1}`. **So each interaction element is a statement about FUNCTIONS on `Z_N(F_q)`, and it can be proved by exhibiting a function.**
- Order:
  1. **G-a for all `q` by a function on `Z_5(F_q)`** (its exact pointwise form is in your §2.2). This is the prototype; it is a gate, not the goal.
  2. The general interaction elements of the generic rows of `K_k` for all `k`, with G-a as the case `k = 2`. Gate: cell `(3,3)`, where your mission 2 found 36 quintic generators, and `(3,9)`.
  3. The +1 and generic rows of `K'_k` for all `k` (you proved `k = 2` in §3.1). Gates `(3,3)`, `(3,9)`.
- If STEP 2 closes for all `k`, and STEP 1 closed, write in large letters: **«CONJECTURE 1.2 CLOSED»**.

### STEP 3 — The level-2 and level-3 gate without G-a (budget 30 min)
- Target: `ℓ_{q−1}(k=2) ≥ N_2` for all `q` (fact 2): exhibit `N_2` elements of `A_2` whose products with `x_5^{q−1}` are linearly independent; or repair the character projection at `a = q−1`.
- Gates: `(2,9)` (`N_2 = 855`) and `(2,27)`: compute `ℓ_{q−1}` directly (colon in 6 variables; estimate first).
- Then the same at level 3, conditional on `D'(3)`.
- **Why it matters:** with STEP 1, STEP 3 (both levels) and `(DO_3)`, `(DO_4)`, `(DE_4)`, the row **`k = 4` for all `q`** follows (§4) even if the general interaction lemma of STEP 2 is only proved for the cases `k ≤ 4`.

### STEP 4 — Assembly and verdict (budget 15 min)
Write which of the six items of §4 are proved, and apply the chain. If the conjecture closes, say it in large letters. If only the row `k = 4` closes, say **«D(4) FOR ALL q»** in large letters: that is the first new row of the conjecture.

---
## 4 · FALLBACK TARGET: THE ROW `k = 4` FOR ALL `q`
1. `c_2 ≤ N_2` (STEP 3, or G-a).
2. (L1) ⟹ `(P_3)`, `(P_4)`.
3. `(DO_3)` ⟹ with `D(2)`: `D'(3)`.
4. `c_3 ≤ N_3` (STEP 3 at level 3, with `D(3)` and `D'(3)`; or `(DE_3)`).
5. `(DO_4)` ⟹ with `D(3)`: `D'(4)`.
6. `(DE_4)` ⟹ **`D(4)` for all `q`.**

## 5 · DEAD ROUTES (do not retry)
- The sum of colons for the generic rows (your §2.1: it would contradict row 1).
- `γ_0 = 0`, `γ_1 = 0`, or `γ_0 ∈ F_3[r_1,r_2]` in (I),(II).
- The naive lifting `x_ax_b·I^{(m)} ⊆ I^{(m+2)}`; `j = 1` monomials alone in the odd casilla; the shear lever; the transfer argument for G-a (your §2.3: the `ε_1²` factor is essential).
- Measuring more cells as a substitute for a mechanism: cells are gates only.

## 6 · SUCCESS
- **Full:** (L1) for all `q` + (L2) for all `k` ⟹ CONJECTURE 1.2 CLOSED.
- **Row:** the six items of §4 ⟹ D(4) FOR ALL q.
- **Partial, and declared as such:** (L1) alone; or G-a alone; or `c_2 ≤ N_2` alone.
