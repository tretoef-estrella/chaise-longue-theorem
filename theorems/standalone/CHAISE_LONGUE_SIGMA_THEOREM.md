> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-14
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE SIGMA THEOREM (v1)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SIGMA_THEOREM.md
>
> **Status, as written in the document:** Status header (read first): this document contains two theorems PROVED ∀k/∀j from banked
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE SIGMA THEOREM (v1)
### Mission F15, Part B2 · Constructor: FRESCALES15 · 2026-08-14
### Status header (read first): this document contains **two theorems PROVED ∀k/∀j from banked
### ∀k machinery**, one **exhaustively MEASURED census** (B1, engine `sigma2_census_v1.py`),
### one **CONJECTURE** (the growth law), and **one first-class kill** (the naive per-seam
### regularity route, killed by a measured cell). GAP 5 is **NOT** declared BLACK here.
### Every grade is stated inline; nothing below PROVED enters any spine.

---

## 0. Objects and banked inputs (cited, not re-derived)

Ambient: `W₂ = W₂^{(k)}`, the doubled arrangement in `2k` variables over `GF(3)`; its
components are the `C(2k,2)·(2k−3)!!` subspaces `{x_c = x_d} ∩ {x_a = −x_b : (a,b) ∈ μ}`
(one doubled direction + a perfect matching of the rest). Banked inputs used:

- **DIAMOND (PROVED ∀k, every flat, every level):** every through-a-flat configuration is a
  PRODUCT; every functorially-local tower module is FREE over its flat; **shifts = the
  transverse Hilbert function** (equivalently: the generator degrees of the transverse module).
- **KU (PROVED ∀k):** at descent-rung `j` the local germ lives on an active set of size
  `≤ 4j+6`, k-independently; the rung-`j` germ types are **finite and k-independent**.
  The spoiling window is quadratic: shifts at rung `j` are harmless iff `σ(j) ≤ k²−k−1−j`.
- **TL (PROVED ∀k):** the descent tower terminates in `≤ k−1` rungs; so rung `j` occurs at
  level `k` only for `j ≤ k−1`.
- **IH≤1 (PROVED ∀k):** flat-dimension `≤ 1` levels are automatically free.
- **Anchors (grades as filed):** `σ(0) = 0` (theorem) · `σ(1) = 1` (exhaustive fine census,
  eight germ classes across two dimensions; k=4 spectra `(0)/(0⁴,1)/(0,0)/(0,0,0)/(0¹¹,1³)`,
  max shift 1) · `σ(2)`: **this mission's exhaustive census — see §3** (previous state: one
  dyed germ, `σ = 0`).
- Computed towers `k ≤ 4` unconditional (banked, triple-anchored censuses).

**Definition.** `σ(j) :=` the maximum shift over all rung-`j` germ types. Well-defined as a
supremum a priori; Theorem σ.1 makes it a finite, k-free number.

---

## 1. Theorem σ.1 (finiteness and k-independence) — **PROVED ∀j**

> **For every `j ≥ 0`, `σ(j)` is finite and independent of `k`.**

*Proof.* By KU the set of rung-`j` germ types is finite and k-independent, and each germ is
supported on an active set of `≤ 4j+6` coordinates. Fix a type `γ`. By DIAMOND its local
module is free over its flat and its shift multiset equals the generator-degree multiset of
the transverse module `T(γ)` — a fixed finitely generated graded module attached to the type
alone (the through-configuration is a product, so `T(γ)` is computed inside the transverse
slice on the active coordinates, with no reference to `k`). A finitely generated graded
module has a finite top generator degree; therefore each type contributes a finite maximal
shift `σ(γ)`, and `σ(j) = max_γ σ(γ)` over the finitely many types is finite and k-free. ∎

*Scope note.* This is a compilation of KU + DIAMOND; its value is that `(R-A)` is reduced,
for each `j`, to a **single finite number** with no `k` in it. It does **not** by itself
control the growth of `σ(j)` in `j` — that is §4.

## 2. Theorem σ.2 (the sufficiency arithmetic) — **PROVED**

> **Let `g` be any function with `σ(j) ≤ g(j)` for all `j ≥ 0`. If `2·g(j) ≤ j² + j + 1`
> fails for no `j` — in particular if `g(j) = j` — then for every `k ≥ k₀ = 3` and every rung
> `j ≤ k−1` occurring at level `k`, the window inequality `σ(j) ≤ k²−k−1−j` holds. Levels
> `k ≤ 4` are independently banked by the computed unconditional towers, so no level of the
> descent is left uncovered.**

*Proof.* Fix `k ≥ 3` and `j ≤ k−1` (TL). With `g(j) = j` the window inequality reads
`j ≤ k²−k−1−j`, i.e. `2j ≤ k²−k−1`. Since `j ≤ k−1` it suffices that `2(k−1) ≤ k²−k−1`,
i.e. `k²−3k+1 ≥ 0`, which holds for every integer `k ≥ 3` (at `k=3`: `1 ≥ 0`). For `k = 2`
the inequality can fail at `j = 1`, but the `k = 2` tower is banked unconditional (computed;
alternatively all its levels have flat-dimension `≤ 1` and IH≤1 applies). ∎

*Remark (sharper than the mission's `k₀ ≤ 4`).* The arithmetic closes already at `k₀ = 3`;
the banked towers `k ≤ 4` give a double cover of the boundary.

*Remark (how much room there is).* The worst case of the window over the levels where rung
`j` occurs is at the smallest such `k`. Under TL that is `k = j+1`, where the window equals
`(j+1)²−(j+1)−1−j = j²−1`. So even **any bound `σ(j) ≤ j²−1` for `j ≥ 2`** (with the banked
`σ(0)=0, σ(1)=1` and `k ≤ 4` towers covering the small cases) suffices — the demand on the
growth law is genuinely weak, strictly weaker than "sub-quadratic in the naive sense".

## 3. The B1 census (rung-2, exhaustive) — **MEASURED**

Engine: `sigma2_census_v1.py` on the reconstructed dependency `gap5_syzygy_gates.py`
(reconstruction validated against five deposited anchors before consumption: component
counts 6/45/420; the exhaustive dim-2 census `2170 = {3:420, 6:1330, 12:420}`; the internal
seam control `2100` — all byte-exact). The pipeline is `sigma2_v2.py`'s, verbatim,
parametrized by the base dim-1 flat; the engine's own pre-stated sanity check (dim `≤ 1`
support forces eventually-constant HF) is enforced at every germ; class invariance is
controlled by a second representative wherever a class has one.

**Result table: see `F15_LANDING_AND_CONSTRUCTION_REPORT_v47.md` §B1 — the numbers there
are pasted from the run log, not from this draft.** Pre-registered criterion (untouchable):
all rung-2 shifts `≤ 2`; death `≥ 3`.

*(Replication note, stated plainly: the class-level replication of the v41 dyed-germ
measurement — `HF(D²_loc) ≡ 3`, shifts `(0,0,0)`, `σ = 0`, pre-registered 2 BEATEN — was
reproduced exactly by the verbatim engine on the reconstructed dependency before the census
ran. The reconstruction is mine and is flagged as such; the original module file remains
wanted for byte-level provenance.)*

## 4. The growth law — **CONJECTURE**, and the honest state of the pencil

> **Conjecture σ.3 (the mission's candidate).** `σ(j) ≤ j` for all `j`.

Anchors: `σ(0) = 0`, `σ(1) = 1`, `σ(2)` per §3. Zero fitted constants; three points are
never a law (Kepler); the conjecture's only role is to feed Theorem σ.2.

**The route the mission named (Derksen–Sidman), executed honestly:** for an arrangement of
`c` linear subspaces, `reg I(V₁∪…∪V_c) ≤ c` [Derksen–Sidman 2002], so ambient-generation
degrees of the per-seam restriction cokernels are bounded linearly in the local piece count.
Two findings, one of them a kill:

1. **KILL (first-class, by a measured cell): the naive per-seam transfer is DEAD.** The
   naive transfer "shift ≤ (seam piece count) − 2" predicts shift `0` for every seam of two
   pieces. The banked rung-1 class `(6,(2⁹))` of the k=4 fine census has all seams of size
   2 and a measured shift `1`. The failure mode is identified, not guessed: DS bounds
   generation over the **ambient** ring, while DIAMOND's shifts are generation over the
   **flat's** ring `k[t] ⊊ S`; a module ambient-generated in degree 0 can need `k[t]`-
   generators in higher degree. Route `NAIVE-DS-TRANSFER` goes to the cemetery with its
   killing cell.
2. **What survives of the route:** the correct object to bound is `reg_S` of the **full**
   germ module (free over the flat ⟹ `reg_S = ` max shift, since the module is
   `T(γ) ⊗ k[t]` up to grading and `reg` of a finite-dimensional `T` is its top degree).
   The quotient-by-image steps of the matryoshka construction obstruct a clean DS chain:
   the s.e.s. regularity triangle bounds `reg(M/N)` only with `reg N` in hand, and `N` is
   an image. **The named residual obstruction (Death-D-B shape, exhibited abstractly):**
   `c` distinct lines through the origin in a fixed plane have `reg = c−1`; so *if* rung-`j`
   through-counts grew super-linearly, no regularity argument of this family could stay
   sub-quadratic. The open pencil item is therefore exactly a **through-count growth law**
   `c_max(j)` — a combinatorial statement about matchings through a flat, not a homological
   one. Whether such fans OCCUR in the tower is precisely what the law must decide; none
   has occurred in any computed rung (`c_max ≤ 12` at every measured rung so far — measured,
   not a law).

## 5. Consequence chain and the honest gate to GAP 5

`B1 (measured) + Conjecture σ.3 ⟹ (R-A)` by Theorem σ.2 — **conditional on σ.3**; then
`(Rc)` via the standard-multiplicity count `2k−1` and `(V)` via SYZ.1 + descent-of-generation
(both banked), and GP fires `B(d)` ∀k. **GAP 5 therefore does NOT close in this document.**
Its residue after F15 is exactly one item, and it is combinatorial:

> **RESIDUE (single item): a k-free bound `σ(j) ≤ g(j)` with `g(j) ≤ j²−1` for `j ≥ 2` —
> e.g. via a through-count growth law `c_max(j)` — closes (R-A) and with it GAP 5.**

## 6. Grades summary

| item | grade |
|---|---|
| Theorem σ.1 (σ finite, k-free) | **PROVED ∀j** (KU + DIAMOND, both banked PROVED ∀k) |
| Theorem σ.2 (sufficiency, k₀ = 3) | **PROVED** (elementary arithmetic on the banked window; k ≤ 4 banked) |
| B1 census (rung-2 exhaustive) | **MEASURED** (cells in the F15 report §B1; engine + reconstruction gates 5/5) |
| Conjecture σ.3 (`σ(j) ≤ j`) | **CONJECTURE** (anchors 0, 1, σ(2); zero fits) |
| Naive DS-transfer route | **DEAD ROUTE** (killed by the measured `(6,(2⁹))` cell; failure mode named) |
| GAP 5 status | **OPEN — one named combinatorial residue** |

— FRESCALES15, 2026-08-14.
