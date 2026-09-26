# R1 — THE BRIDGE FROM THE LITERAL DEGTYAREV–SHIMADA STATEMENT: IT IS NOT `A = P`
*Grepy el Lector, 2026-09-23 (MISIÓN 90). Rafa ordered R1, written «from the original», before the final paper. Everything below was derived from the arXiv text of [DS] (arXiv:1405.4683v3, extracted today with PDFKit, pages 1–18), and gated with own code.*

## PRIMERA LÍNEA — what this turn closes
**R1 CLOSES IN THE NEGATIVE.**
- The literal Conjecture 1.2 of [DS] at degree `m = q = 3^v`, dimension `2k`, is **equivalent to a bone-type (intersection) identity at box `q − 1` on the zero-free grid**. It is **not** equivalent to the sum-form identity `A_k(q) = P_k(q)`.
- `A = P` is what the campaign proved (MISIÓN 89, Theorem A). **For families of sheets, `A_K = P_K` does not imply the DS statement:** at `q = 9`, `k = 2`, `K = J ∖ {01|23|45, 02|15|34}` one has `A_K = P_K = 7089` while `H_4(X)/L_K(X)` has non-trivial 3-torsion. The failure is confirmed in DS's own literal presentation.
- For `K = J`, nothing proves the implication.
- ⟹ **MISIÓN 89's «THE CONJECTURE IS CLOSED» IS RETRACTED to: `A_k(q) = P_k(q)` for every `k` and every `q = 3^v` is PROVED (in fact Theorem A: every field of characteristic `≠ 2`, every odd `q`); DS Conjecture 1.2 in degree `3^v` is NOT established.**
- The same identification sits under the Sofá's and the Hamaca's «equivalently … DS 1.2» lines. They prove `A = P` for `k = 2, 3`; their DS clauses are unsupported.

---

## 1. From DS Theorem 1.1 to one finite-dimensional statement over `F_3`
Notation of [DS]:
- `n = 2d`, `m` the degree, `G = (Z/m)^{n+1}` with generators `t_1..t_{n+1}` and `t_0 = (t_1⋯t_{n+1})^{−1}`, `R = Z[G]`.
- `J` is the set of perfect matchings `[[j_0,k_0],…,[j_d,k_d]]` of `{0,…,n+1}`, `j_i < k_i`, `j_0 = 0`.
- `τ_J = Π_{i=0}^{d}(t_{k_i} − 1)`, `φ(u) = 1+u+⋯+u^{m−1}`, `ψ_J = τ_J·Π_{i≥1}φ(t_{j_i}t_{k_i})`.

**(DS 1.1(a), 4.2)** `Tors(H_n(X)/L_K(X)) ≅ Tors(R/(ψ_J : J ∈ K))`.

**(DS Claim 4.3, 4.3)** For an algebraically closed field `K_p` of characteristic `p = 0` or `p ∤ m`: `dim(R/(ψ) ⊗ K_p) = m^{n+1} − |Γ_K|`, where `Γ_K` is [DS, Def. 1.3].

**Step 1 (structure theorem).** `R/(ψ)` is a finitely generated abelian group. It is torsion free iff `dim_{F_p}(R/(ψ) ⊗ F_p) = dim_Q(R/(ψ) ⊗ Q)` for every prime `p`, by right exactness of `⊗`. For `m = 3^v` only `p = 3` can fail, by [DS, Cor. 1.5].

⟹ **(DS_q) Conjecture 1.2 at `(k, q)` ⟺ `dim_{F_3} F_3[G]/(ψ̄_J : J ∈ J) = q^{2k+1} − |Γ_J|`**, with `k = d`.

**Step 2 (`|Γ|`).** Put `a_0 := (a_1⋯a_{n+1})^{−1}`. The defining condition of `Γ` becomes: the multiset `{a_0, …, a_{n+1}} ⊆ μ_q ∖ {1}` splits into inverse pairs. The pair containing index `0` is automatic. Hence

`|Γ_J| = Q_k(q) := (2k+2)!·[y^{2k+2}] I_0(2y)^{(q−1)/2}`.

This is the zero-free count; compare `P_k(q) = (2k+2)!·[y^{2k+2}] e^y I_0(2y)^{(q−1)/2}`. It agrees with [DS, Remark 4.4]; for example `3m²−9m+6` at `n = 2`. Gates: `6, 20, 168` at `(k,q) = (1,3), (2,3), (1,9)`.

**Step 3 (the coordinate that linearises DS — the ingenio of the turn).** In `F_3[Z/q]` one has `t^q = 1`, so `t − 1` is nilpotent and `t + 1 = 2 + (t−1)` is a unit.
- Put `y := t − t^{−1} = t^{−1}(t−1)(t+1)`. Then `y` is a unit times `t − 1`, and `F_3[Z/q] = F_3[y]/(y^q)`. **Inversion `t ↦ t^{−1}` becomes `y ↦ −y`.**
- **The identity `y_j + y_k = (t_j + t_k)(t_jt_k)^{−1}(t_jt_k − 1)`** gives `(t_jt_k − 1) = (y_j + y_k)`: **DS's subgroup relations become LINEAR forms.**
- `φ(u) = (u−1)^{q−1}` in `F_3[u]`, by Lucas: every base-3 digit of `q−1` is `2`, so `binom(q−1,r) ≡ (−1)^r`.

Hence, up to units:

`ψ̄_J = τ_J·σ'_J`,  `τ_J = Π_{i=0}^{d} y_{k_i}`,  `σ'_J = Π_{i≥1}(y_{j_i}+y_{k_i})^{q−1}`,

in `B' := F_3[y_1,…,y_{2k+1}]/(y_i^q)`. **So DS's group ring is exactly the campaign's box ring, and the sheets are the campaign's sheets.**

**Step 4 (Gorenstein duality).** Change coordinates to `J`:
- the free coordinate `y_{k_0}`;
- for each pair `p = {j,k}`, the pair `(u_p = y_j+y_k, y_k)`.

The box is `GL(F_3)`-stable, so `ψ̄_J` is a monomial and `ann_{B'}(ψ̄_J) = I'_J + m^{[q−1]}`, where `I'_J = (y_j + y_k : pairs of J not containing 0)`. `B'` is Gorenstein, so `dim_{F_3}(ψ̄_J : J)B' = dim B'/∩_J ann(ψ̄_J)`. ⟹

> **(DS_q) ⟺ `b_k(q−1) = Q_k(q)`, where `b_k(r) := dim_{F_3} F_3[y_1..y_{2k+1}] / ∩_J (I'_J + (y_i^r))`.**

Every sheet ideal contains `e_1`, so eliminating `x_0 = −Σ x_i` shows that `b_k(r)` equals the symmetric bone in `N = 2k+2` variables, `dim F_3[x_0..x_{2k+1}]/∩_J(I_J + m^{[r]})`.

**Step 5 (the sandwich, and why this is the BONE and not `A = P`).** Take the zero-free grid `Γ = ⋃_J L_J ∩ (F_q^×)^{N}`. Its ideal is `E + (x_i^{q−1} − 1)`, and its initial ideal contains `E + m^{[q−1]}`. Then

`b_k(q−1) ≤ Q_k(q) ≤ dim F_3[x]/(E + m^{[q−1]})`,

by the same two-line arguments as the campaign's `B ≤ P ≤ A` (informe 66). **DS is the LEFT equality: an intersection (bone) statement at the EVEN box `q − 1` on the ZERO-FREE grid.** `A_k(q) = P_k(q)` is the RIGHT-type equality at the ODD box `q` on the grid WITH zero. **They differ in all three coordinates: intersection vs sum, `q−1` vs `q`, zero-free vs zero.**

---

## 2. Gates (own code, `corpus4/herramientas_grepy/regla264_ds.py`; logs `corpus4/regla264_*.log`; all inside `vigia.sh`, peak 333 MB, longest 150 s)
| check | cells | result |
|---|---|---|
| literal `t`-form = `y`-form = `q^{2k+1} − |Γ|` (translation) | `(1,3)`, `(2,3)`, `(1,9)` | **21 = 21 = 21 · 223 = 223 = 223 · 561 = 561 = 561** |
| duality: literal + punctured bone `= q^{2k+1}` | 7 cells incl. subfamilies | **7/7** |
| punctured bone `= |Γ|` for the full family | `(1,3)`, `(2,3)`, `(1,9)`, `(2,9)` | **6, 20, 168, 5120 — DS holds (known for these cells)** |
| subfamilies at `q = 3`, `k = 2`: DS vs `A = P` vs bone | 9 families | **DS holds in all 9**, while bone fails in 6 and `A > P` in 1 (`|K| = 8`: `A = 114`, `P = 113`) |
| **subfamily at `q = 9`, `k = 2`, `K = J ∖ {01|23|45, 02|15|34}`** | literal `t`-form, 150 s | **`dim_{F_3} = 54319 ≠ 54313 = q^5 − |Γ_K|`: DS FAILS (3-torsion, excess 6), while `A_K = P_K = 7089`** (bone `7081`) |
| subfamily at `q = 9`, `|K| = 8` | — | **`A = 4770 > P = 4769`, yet DS holds (`3248 = |Γ|`)** |

⟹ **For families of sheets, «`A_K = P_K`» and «DS for `K`» are logically independent, in both directions.**

---

## 3. What is proved, what is retracted, what remains
- **PROVED (MISIÓN 89, untouched):** Theorem A, `dim_F F[x_1..x_n]/(e_odd; x_i^q) = n![y^n]e^yI_0(2y)^{(q−1)/2}` for `char F ≠ 2` and odd `q`. Hence `A_k(q) = P_k(q)` for all `k`, all `q = 3^v`; Corollary C (the torsion of `Z[x]/(e_odd, x_i^q)` is a 2-group).
- **RETRACTED:** «DS Conjecture 1.2 holds for degree `3^v` and every even dimension» (MISIÓN 89, PAPER_B_v1 Corollary B). Also, for the same reason, the DS clauses of the Sofá (`k = 2`) and the Hamaca (`k = 3`) papers.
  - Their `A = P` theorems stand.
  - Their «Equivalently, the diagonal is saturated …» rests on a reduction that was never written. The campaign itself flagged it: `DOSSIER_DS_NATIVE_v2` red **R8a** «the DS dictionary»; the Sofá's own `STATE_OF_THE_CAMPAIGN_arrangement_route.md`: «the bridge reduced ↔ thickened … NOT closed as a general theorem»; the enlace-5 standalone graded the DS links 🟨 «original unread».
- **WHAT CLOSES DS 1.2 IN DEGREE `3^v`:** the **punctured bone** `b_k(q−1) = Q_k(q)` for the full family, every `k`, every `q = 3^v`. Equivalently: the leading forms of the ideal of the zero-free grid points of the arrangement equal the intersection of the sheetwise leading-form ideals at box `q − 1`.
  - Known: [DS §5] `(4, 3..12)`, `(6, 3)`, `(6, 4)`, `(6, 5)`, `(8, 3)`; here `(2,3)`, `(2,9)` re-checked in the new form.
- **Why the MISIÓN 89 machinery does not reach it:** Theorem Γ bounds a SUM-type quotient from above. The bone needs an upper bound on an INTERSECTION. For intersections the row filtration gives only `R_a(∩_J G_J) ⊆ ∩_J R_a(G_J)`, the wrong direction. This is the campaign's old `B`-versus-`A` wall (informes 62–68), now at box `q−1` without zero.

## 4. Ingenio of the turn
**The coordinate `y = t − t^{−1}`.** It turns DS's group ring `F_3[(Z/q)^{n+1}]` into the campaign's box ring `F_3[y]/(y^q)`, with DS's subgroup relations as the campaign's linear sheets (`t_jt_k − 1 = unit·(y_j + y_k)`) and inversion as negation. This is the first time the literal DS module lives inside the campaign's ring. It is also what makes the error visible: the φ-reduction of DS is the box `q − 1`, and `τ_J` is the zero-free puncture.

## 5. Double checks
- Translation: two routes, the literal `t`-form (no change of variables) and the `y`-form, identical in 4 cells (including the failing subfamily).
- Duality: an independent third route (the intersection computed directly) sums to `q^{2k+1}` with the literal form in 7/7 cells.
- `|Γ|`: enumeration against [DS, Remark 4.4] `3m²−9m+6` and `C(6,3) = 20`.

## 6. Errors of this auditor, published
- **MISIÓN 89 announced «the conjecture is closed» and called R1 bibliographic.** It was not: the reduction had never been written in the corpus (the campaign's own red R8a), and I did not open DS §4 before announcing. **Rule: before announcing that a target is closed, re-derive the translation of the target from the original, not from the campaign's summary of it.**
- The arranque's instruction «DS Conj 1.2: `K = J` ⟹ `H_n(X)/L(X)` torsion free» was right; my gloss «only R1 bibliographic» was the error.
