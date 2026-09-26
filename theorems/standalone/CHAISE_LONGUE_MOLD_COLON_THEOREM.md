> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE MOLD = COLON THEOREM (A_b as new colon generators, PENCIL)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MOLD_COLON_THEOREM.md
>
> **Status, as written in the document:** THEOREM (MOLD = COLON) — PROVED ∀k
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (1 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE MOLD = COLON THEOREM (A_b as new colon generators, PENCIL)
### CHAISE_LONGUE_MOLD_COLON_THEOREM_v1 · standalone · char ≠ 2

Setup (as in RAIL_NESTING / INCREMENT_FACTORIZATION): `N=2k+2`, `y=(y_1,y_2)=(x_{N+1},x_{N+2})`,
`I_{k+1}=E_{k+1}+m^{[q]}`. Increment leaders factor `a·b` with `a` I_k-standard, `b∈B` a nontrivial
y-monomial (Thm A). For a y-monomial `b`, put `M_b := (in(I_{k+1}) : b) ∩ κ[x_1,…,x_N]`
(`= { x-monomials a : a·b ∈ in(I_{k+1}) }`), a monomial ideal in the x's.

## THEOREM (MOLD = COLON) — PROVED ∀k
> `A_b = minGens(M_b) \ ⋃_{y_i | b} M_{b/y_i}` — the minimal generators of the colon `M_b` that are NOT
> already in the colon of a smaller y-part. In particular for the seed letter `b=y_1`:
> **`A_{y_1} = minGens( (in(I_{k+1}):y_1)|_x ) \ in(I_k)`** (the new colon generators beyond the old
> staircase). This is Rafa's MOLD rule ("a·b is new iff the mold is not already there") made exact.

*Proof.* `A_b·b` are the minimal generators of `in(I_{k+1})` whose y-part is exactly `b`. A monomial `μ=a·b`
is a minimal generator iff no proper divisor lies in `in(I_{k+1})`. Proper divisors are of two kinds:
(x-drop) `(a/x_j)·b` — absent from `in(I_{k+1})` iff `a/x_j ∉ M_b`, i.e. `a ∈ minGens(M_b)`;
(y-drop) `a·(b/y_i)` — absent iff `a ∉ M_{b/y_i}`. Combining: `a ∈ minGens(M_b)` and `a ∉ M_{b/y_i}` for
every `y_i | b`. For `b=y_1`, `b/y_1 = 1` and `M_1 = in(I_{k+1})|_{y=0} = in(I_k)` (RAIL-NESTING), giving
`A_{y_1} = minGens(M_{y_1}) \ in(I_k)`. ∎

**Control (Ley 27b, existing k=1→2 cell, q=5):** `minGens((in(I_2):y_1)|_x)` has 10 elements = the 6
`in(I_1)` leaders ⊔ the 4 elements of `A_{y_1}` (`x_2^2x_4^2, x_3^3x_4^2, x_2x_3x_4^{q-1}, x_3^2x_4^{q-1}`),
byte-exact. So `A_{y_1}` = the new colon generators, as the theorem says.

## COROLLARY (s=0 LOCALIZATION) — PROVED ∀k

> 🔴 **NOTA `2026-09-16` (Grepy, turno 18, informe 146) — CONDICIONAL, no PROBADO `∀k`:** «An `s=0` leader is an `m(V)`» y el recuento «by the proved m(V)/Catalan law» usan la ley `s=0` `in(E) = J`, cuya pieza (1) `in(E) ⊆ J` está ABIERTA (`corpus/CHAISE_LONGUE_S0_CLOSED_FORM_v15.md:12`, `:49`; medida `k ≤ 7`, informe 139). Probado `∀k`: MOLD=COLON, la localización en la letra `y_1` DADO que los líderes son `m(V)`, y `#m(V) = C_{k+1}`.

> Every `s=0` increment leader lies in the single letter `b=y_1`, and `{a·y_1 : a ∈ (s=0 part of A_{y_1})}`
> = the `C_{k+1}` new level-`(k+1)` `m(V)`.

*Proof.* An `s=0` leader is an `m(V)`; a new one (increment) has level `k+1`, whose cap is `{2k+2,2k+3}`,
so its `x_{2k+3}=y_1` exponent is `(2k+3)−2(k+1)=1` and its `y_2=x_{2k+4}` exponent is `0`. Hence its y-part
is exactly `y_1`. Their count is `C_{k+1}` (the level-`(k+1)` supports), by the proved m(V)/Catalan law. ∎

## WHAT THIS CLOSES / DOES NOT (honest)
- **PROVED ∀k:** the MOLD=COLON theorem (each `A_b` = new minimal generators of the colon `M_b`) and the
  s=0 localization (the s=0 increment is exactly the `C_{k+1}` new m(V), all in letter `y_1`). Together with
  RAIL-NESTING + Thm A/B, the transfer step is now reduced to: **the structure of the colon ideals `M_b`
  for the three non-power letters** — i.e. which x-monomials `a` satisfy `a·b ∈ in(I_{k+1})`.
- **NOT closed (the wall):** the `s≥1` part of the `M_b` (the combos). Measured k=1→2:
  `A_{y_1}` s≥1 `= {x_2x_3x_4^{q-1}, x_3^2x_4^{q-1}}`; `A_{y_1^2y_2}, A_{y_1^{q-1}y_2}` likewise. These are the
  `s≥1` bulk and require the S-polynomials of the new rail `e_{2k+3}` with `y_1^q, y_2^q` — no uniform
  closed form yet. **Does NOT close the increment, the transfer step, GAP 3, or move G.**

**Grade: MOLD=COLON + s=0 localization PROVED ∀k (partial increment, Ley 27 first-class). s≥1 M_b: OPEN.**

> 🔴 **NOTA `2026-09-16` (Grepy, turno 18, informe 146) — CONDICIONAL, no PROBADO `∀k`:** «An `s=0` leader is an `m(V)`» y el recuento «by the proved m(V)/Catalan law» usan la ley `s=0` `in(E) = J`, cuya pieza (1) `in(E) ⊆ J` está ABIERTA (`corpus/CHAISE_LONGUE_S0_CLOSED_FORM_v15.md:12`, `:49`; medida `k ≤ 7`, informe 139). Probado `∀k`: MOLD=COLON, la localización en la letra `y_1` DADO que los líderes son `m(V)`, y `#m(V) = C_{k+1}`.

