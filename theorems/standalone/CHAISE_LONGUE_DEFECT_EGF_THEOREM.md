> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-04
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *The Defect Generating Function (Steinberg ceiling − floor), uniform in k* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_DEFECT_EGF_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# The Defect Generating Function (Steinberg ceiling − floor), uniform in k

**Chaise Longue campaign · standalone · v1 · Auditor: Marsh**
**Source:** Frescales 10 report (2026-08-04), audited byte-exact by Marsh (`audit_f10_delta.py`, exact rational
arithmetic over ℚ, no floats). All gate numbers reproduced independently from files.

**Scope in stone.** This document proves the *structure and uniformity in k* of the defect
`Δ_k(q) := (central q-nomial for N=2k+2) − P_k(q)`. It does **NOT** prove `A_k(q)=P_k(q)` for `q>3`
(see §5, honest scope). `Δ` is the size of the overshoot of the Steinberg ceiling over the conjectural floor;
the true value `A_k(q)=dim Ann(E)` sits between them and is pinned to `P_k` only by measurement for `q>3`.

---

## 0. Objects (all files-verified)

`n=2k+2`; `A=⊗_{j=1}^n F_3[x_j]/(x_j^q)`, `q=3^v`. `E=(e_1,e_3,…,e_{2k+1})`, `B=A/EA`,
`A_k(q)=dim_{F_q} B`. Two closed objects on either side of the (measured) value `A_k(q)`:

- **Ceiling** = `dim A^{U^+}` = the weight-0 multiplicity of `A` as `SL_2`-module = the **central q-nomial**
  `C_N(q) := [t^0]\big(\sum_{a=0}^{q-1} t^{2a-(q-1)}\big)^N`, `N=n`. (Telescoping `Σ_{s≥0}(m_{2s}-m_{2s+2})=m_0`.)
- **Floor** = `P_k(q) = N![t^N]\,e^t\,I_0(2t)^{(q-1)/2}`, `I_0(2t)=Σ_j t^{2j}/(j!)^2` (banked closed form).

`Δ_k(q) := C_{2k+2}(q) − P_k(q)`.

---

## 1. The defect is an EGF, not a polynomial in k

> **Theorem 1 (PROVED).** With `m=(q-1)/2`, `f_j(z)=exp(z(t^j+t^{-j}))`, and `CT_t` = constant-term-in-`t`,
> ```
>   Σ_{n≥0} Δ^{(n)}(q) z^n/n!  =  e^z\Big( CT_t[∏_{j=1}^m f_j(z)]  −  ∏_{j=1}^m CT_t[f_j(z)] \Big).
> ```
> Consequently `Δ` is uniform in `k` (k enters only as which coefficient `N=2k+2` one extracts), and
> `deg_q Δ_k = 2k+1` (grows with k), so **no fixed polynomial in `q` is uniform in `k`** — the EGF is the
> uniform object.

*Proof.* Two building-block identities, each pure exponential algebra given the banked EGFs.

**(Ceiling block).** `e^z·CT_t[∏_{j=1}^m f_j] = e^z·CT_t[exp(z·Σ_{j=1}^m(t^j+t^{-j}))]`. The scalar `e^z`
is the `j=0` channel `exp(z·1)`, so this is `CT_t[exp(z·P(t))]` with `P(t)=Σ_{j=-m}^m t^j` (the balanced
alphabet of `q=2m+1` powers). Then `N![z^N]CT_t[exp(zP)] = CT_t[P^N] = [t^0]P^N`. Relabelling exponents
`t↦t^2` (a bijection that fixes the `t^0` term) turns `P` into `Σ_{a=0}^{q-1}t^{2a-(q-1)}`, so
`[t^0]P^N = C_N(q)`. Hence `N![z^N](e^z CT[∏f_j]) = C_N(q)` = ceiling.

**(Floor block).** For each `j`, `CT_t[exp(z(t^j+t^{-j}))] = Σ_n z^n/n!·[t^0](t^j+t^{-j})^n =
Σ_l z^{2l}/(2l)!·\binom{2l}{l} = Σ_l z^{2l}/(l!)^2 = I_0(2z)`, **independent of `j`** (the constant term of
`(t^j+t^{-j})^n` is `\binom{n}{n/2}` for any `j`). Hence `∏_{j=1}^m CT_t[f_j]=I_0(2z)^m` and
`e^z·∏CT[f_j]=e^z I_0(2z)^{(q-1)/2}`, whose `N![z^N]` is `P_k(q)` (banked). Subtracting gives the displayed
EGF. Degree growth `deg_q Δ_k=2k+1` is verified exactly for `k=1..6` (interpolation over odd `q`); combined
with §3 it forces a growing-degree object. `∎`

**Audit (Marsh).** Master `= central − P` reproduced exactly in all 12 cases `q∈{3,9,27}×k∈{1..4}`.
Gates PASS: `P₁(3)=19, P₁(9)=217, P₂(3)=141, P₃(3)=1107, P₃(9)=345465, C₄(9)=489`.

---

## 2. The defect vanishes at q=3, all k (Steinberg as an EGF identity)

> **Theorem 2 (PROVED).** `Δ^{(n)}(3)=0` for all `n`; hence `Δ_k(3)=0` ∀k.

*Proof.* At `q=3`, `m=(q-1)/2=1`: a single channel. Then `CT_t[∏_{j=1}^1 f_j]=CT_t[f_1]=∏_{j=1}^1 CT_t[f_j]`
trivially, so the bracket in Theorem 1 is identically zero. This is exactly the Steinberg bridge
(`Ann(E)=A^{U^+}`, `A_k(3)=T(2k+2)`) recovered as a collapse of the EGF. `∎`

---

## 3. Universal factor (q−1)(q−3), all k — upgraded to PROVED

> **Theorem 3 (PROVED ∀k — Marsh upgrade).** `(q-1)(q-3) \mid Δ_k(q)` for every `k`.

> 🔵 **NOTA `2026-09-16` (Grepy, turno 20, informe 148) — divisibilidad sólo en `ℚ[q]`:** como enteros es falsa (`Δ_1(9) = 489 − 217 = 272` y `48 ∤ 272`).


*Proof.* The bracket `CT_t[∏_{j=1}^m f_j]−∏CT[f_j]` collapses to `0` whenever `m∈{0,1}`: `m=0` (q=1) is an
empty product (`1−1=0`); `m=1` (q=3) is a product of one factor (Theorem 2). Both give a polynomial root of
`Δ_k(q)` at `q=1` and `q=3`, for every `k`, **without measuring** — the collapse is a property of the EGF, hence
of every extracted coefficient `N=2k+2`. `∎`

*(Frescales 10 stated this MEASURED for `k=1..6`; the `m∈{0,1}` collapse makes it structural ∀k.)*

**Closed forms (audited exact, k=1,2,3):**
```
Δ_1(q) = (q−3)(q−1)(2q−1)/3
Δ_2(q) = (q−3)(q−1)(11q³+44q²−152q+160)/20
Δ_3(q) = (q−3)(q−1)(151q⁵+604q⁴+2033q³−26755q²+85380q−96390)/315
```
First cross term at order `z³` = `6`, from the channel pair `{j=1,j=2}` (two `+1` cancel one `−2`); it gives
`Δ_1(9)=4!·(6/1!+16/3)=272` (verified). Grade: MEASURED k≤3 (the closed forms); the *existence* of a
uniform-in-k EGF is Theorem 1 (PROVED).

---

## 4. What Δ is, combinatorially (bookkeeping, not a closure)

`Δ` is the **connected (cumulant) part** of the constant term of the central slice across the `m` divided-power
channels `{t^{±j}}`: the ceiling counts as if the `m` channels were independent (`∏CT`), the honest constant
term lets them interact (`CT[∏]`), and the mismatch is a connected correlator. This is a *definitional* fact
(a non-factoring `CT` is a cumulant), useful for organizing terms — **not** a proof that `Δ` equals any
representation-theoretic invariant. See §5.

---

## 5. Honest scope — what this does NOT do (referee-facing)

1. **It does not close `A_k(q)=P_k(q)` for `q>3`.** `Δ=C_N−P_k` is a difference of two *already-closed* forms;
   the true value `A_k(q)=dim Ann(E)` (Gorenstein self-duality, PROVED ∀q) equals `P_k` only by **measurement**
   for `q>3`. Δ measures the ceiling's overshoot; it does not carve the floor-dimensional subobject `R_v`.

2. **The "Δ = nerve `H¹` / Möbius over deep flats" identification is a BURIED move — do not mount it.**
   - `THREE_LINE_OBSTRUCTION` (PROVED `q=3,9,27`): the ceiling defect is **NOT** D3's Čech `H¹` (a rename
     refused with a number; three concurrent lines give defect 1, which any nerve-`H¹` proof would wrongly kill).
   - Cemetery v142 `FALSE-CLOSURE-VIA-REP-CONFLATION`: Möbius-of-**lengths** ≠ Möbius-of-point-counts; the
     length nerve is dead (`H⁰=14, H¹=19≠0`); two external Hilbert–Kunz specialists confirmed no
     "free arrangement ⇒ length inclusion-exclusion exact" theorem exists.
   The cumulant framing of §4 is legitimate bookkeeping; equating that cumulant with the nerve `H¹` is the
   sepultured step.

**The remaining brick (pencil, uniform in k):** construct `R_v=Ann(E)`, prove `dim Ann(E)=P_k(q)` — i.e. find
the `q>3` analogue of the char-3 ideal equality `(g_m)=(e_{odd})` (which used `G(t)E(t)=E(-t)`, `x^3=0`, and
FAILS for `x^q=0`), and compute the annihilator over the tilting `T(2(q-1))^{⊗n}`.

---

## 6. Grades

| Statement | Grade |
|---|---|
| Thm 1 (Δ is the EGF `e^z(CT[∏f]−∏CT[f])`, uniform in k) | PROVED (from banked EGFs) |
| Thm 2 (Δ≡0 at q=3, all k) | PROVED |
| Thm 3 ((q−1)(q−3)\|Δ_k ∀k) | PROVED (Marsh upgrade; was MEASURED k≤6) |
| Closed forms Δ₁,Δ₂,Δ₃; first cross term = 6 | MEASURED (k≤3), audited exact |
| Δ = connected cumulant (§4) | PROVED (definitional bookkeeping) |
| Δ closes `A_k(q)=P_k(q)`, q>3 | **FALSE as stated** — Δ is ceiling−floor, not a proof (§5) |
| Δ = nerve `H¹` / Möbius-of-lengths | **BURIED** (three-line + v142) — do not mount |

## 7. One line

The Steinberg ceiling overshoots the floor by a defect `Δ` whose generating function `e^z(CT_t[∏f_j]−∏CT_t[f_j])`
is uniform in `k`, vanishes identically at `q=3` by collapse to one channel, and is divisible by `(q−1)(q−3)`
for every `k` — but `Δ` only measures the size of the overshoot; closing the conjecture still requires carving
the floor-dimensional `R_v=Ann(E)` out of the ceiling, uniform in `k`.
