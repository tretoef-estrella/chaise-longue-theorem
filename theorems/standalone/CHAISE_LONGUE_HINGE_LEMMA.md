> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-11
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE HINGE LEMMA (the slice functor is multiplication by (1 − v²w): the entire J-apparatus of level k restricts to the level-(k−1) apparatus, triangularly, with BOTH top generators collapsing onto the cliff object ū′_{k−1} times explicit hinge factors)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_HINGE_LEMMA.md
>
> **Status, as written in the document:** Status: H1–H4 PROVED ∀k (pencil, one-line proofs below); machine-gated k = 3, 4 (11/11 incl. a corrupted-claim control that fails as it must; `hinge_gate.py`, same turn).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE HINGE LEMMA (the slice functor is multiplication by `(1 − v²w)`: the entire J-apparatus of level k restricts to the level-(k−1) apparatus, triangularly, with BOTH top generators collapsing onto the cliff object `ū′_{k−1}` times explicit hinge factors)
### 11 Aug 2026 · Auditor: NASH (own harvest; the map of the Architect's CLACK/ROSCA metaphors) · Serves: GAP 5 / B(d) (mission v36 V2, T1)
### Status: H1–H4 PROVED ∀k (pencil, one-line proofs below); machine-gated k = 3, 4 (11/11 incl. a corrupted-claim control that fails as it must; `hinge_gate.py`, same turn).

**Setting.** `S = F₃[x₁,…,x_{2k}]`. The pair-slice `ρ = ρ_{ab,v}`: substitute `x_a = v, x_b = −v` (v a free parameter). Primed objects (`e′_r, ū′_j, f′_{2j+1}`) live in the remaining `2k−2` variables — the level-`(k−1)` apparatus. Deposited: `ū_j = Σ_{i=0}^{j}(−1)^i e₁^{2i}e_{2j−2i}`, `f_{2j+1} = e_{2j+1} − e₁ū_j`, `J = (f₃,…,f_{2k−1}, ū_k)`.

**Foundation (one line).** `E(z)|_ρ = (1+vz)(1−vz)·E′(z) = (1−v²z²)E′(z)`, hence `e_r|_ρ = e′_r − v²e′_{r−2}` and `e₁|_ρ = e₁′`.

---

## The Lemma (H1–H4, each proof one line from the foundation)

> **H1 (the HINGE — Rafa's clack):** `ū_j|_ρ = ū′_j − v²·ū′_{j−1}` for `1 ≤ j ≤ k−1`; equivalently `U(w)|_ρ = (1−v²w)·U′(w)` on the generating series.
> *Proof.* `ū_j|_ρ = Σ(−1)^i e₁′^{2i}(e′_{2j−2i} − v²e′_{2j−2i−2})`; the two sums are `ū′_j` and `−v²ū′_{j−1}`. ∎

> **H2 (the THREAD — Rafa's rosca/teflón):** `f_{2j+1}|_ρ = f′_{2j+1} − v²·f′_{2j−1}` for `1 ≤ j ≤ k−2` (convention `f′₁ = 0`, exact for `j=1`).
> *Proof.* `f_{2j+1}|_ρ = (e′_{2j+1} − v²e′_{2j−1}) − e₁′(ū′_j − v²ū′_{j−1})` and regroup. ∎

> **H3 (top generator → the cliff):** `ū_k|_ρ = −(e₁′² + v²)·ū′_{k−1}`.
> *Proof.* `e′_{2k} = 0` (only `2k−2` variables) gives `ū′_k = −e₁′²ū′_{k−1}`; then H1 at `j=k`. ∎

> **H4 (top f → the cliff):** `f_{2k−1}|_ρ = −e₁′·ū′_{k−1} − v²·f′_{2k−3}`.
> *Proof.* `e′_{2k−1} = 0`, so `f′_{2k−1} := e′_{2k−1} − e₁′ū′_{k−1} = −e₁′ū′_{k−1}`; then H2 at `j=k−1`. ∎

## Reading (the metaphors, mapped exactly)

- **CLACK (the hinge folds inward):** the factor `(1−v²w)` protruding from the slice IS the removed antipodal pair `±v` — what sticks out on the outside is exactly what is missing on the inside, and it folds back in as the slice parameter itself. The restriction does not create foreign objects: it creates the level-(k−1) apparatus times the hinge.
- **ROSCA (watertight thread):** the generator restriction is UNITRIANGULAR (`f_{2j+1} ↦ f′_{2j+1} − v²f′_{2j−1}`): an invertible change of generators degree by degree in the low range — the Hilbert bookkeeping between level k and level k−1 telescopes with NO leaks. In degrees below the cliff, `(1−v²w)` is a unit as a power series: slice-kernel questions transport cleanly to level k−1.
- **THE CLIFF IS NOW A SINGLE NAMED OBJECT:** BOTH top generators of `J` collapse under every slice onto `ū′_{k−1}` times explicit factors (`−e₁′` and `−(e₁′²+v²)`). The entire boundary data of the induction is `ū′_{k−1}`-multiples — which is precisely the polynomial whose coordinate evaluations build the level-(k−1) resolvent family `g′_α = (x_α+e₁′)P̂′(x_α)` (RESOLVENT_EXCESS v1). The induction load and the identified excess are the SAME object, now by formula, not by measurement.

## What remains for B(d) — the A+B glue (CANDIDATE, the open pencil)
A kernel element `h ∈ ker(S/J → O(W₂))` of degree `≤ 2k−2` restricts on each of the `C(2k,2)` slices to level-(k−1) data killed by induction below the cliff, plus cliff coefficients that H3/H4 force into the `ū′_{k−1}`-zone. The glue: the cliff assignments across all slices are not independent — they overlap on codimension-2 sub-slices and carry an `S_{2k}`-action; the candidate mechanism (component A: equivariant averaging over slices; component B: the Newton/R(b) kill of the invariant part) must force every gluing-compatible assignment to zero. **This is the single remaining pencil step of GAP 5.** Grade: CANDIDATE.

**Grades.** H1–H4: PROVED ∀k (pencil; gates 11/11 at k=3,4, corrupted control fires). The glue: CANDIDATE. B(d): OPEN.

— NASH (Auditor). Gates in `hinge_gate.py` (same turn). The Architect's metaphors are first-class machinery; entered in LAS IDEAS DE RAFA v35.
