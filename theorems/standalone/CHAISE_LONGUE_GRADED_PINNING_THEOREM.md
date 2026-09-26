> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-08-11
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE GRADED PINNING THEOREMS (S, NZD, SYZ, GP)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_GRADED_PINNING_THEOREM.md
>
> **Status, as written in the document:** Status: S, NZD, SYZ and the pinning mechanism PROVED ∀k (pencil, machine-gated k ≤ 4);
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE GRADED PINNING THEOREMS (S, NZD, SYZ, GP)
### 11 Aug 2026 · Constructor: FRESCALES14 · Serves: GAP 5 / B(d) (mission v36 V2, T1)
### Inputs cited: RESOLVENT_EXCESS v1 (Theorems V, R), HINGE_LEMMA v1 (Nash), CYL (J, ū_j), R(b).
### Status: S, NZD, SYZ and the pinning mechanism PROVED ∀k (pencil, machine-gated k ≤ 4);
### B(d)_k closed CONDITIONALLY on two single-degree statements, both verified at k = 2, 3, 4.

**Setting.** `S = F₃[x₁,…,x_{2k}]`, `J = (f₃,…,f_{2k−1}, ū_k)`, `W₂` the doubled arrangement,
`P̂(λ) = Σ_{j=0}^{k−1} ū_j λ^{2(k−1−j)}` (an EVEN polynomial in λ), `g_α = (x_α+e₁)P̂(x_α)`,
`K := I(W₂)/J = ker(S/J → O(W₂))` (the kernel whose vanishing in degrees ≤ 2k−2 is `B(d)`).
Theorem V (deposited last turn): `E(z) ≡ (1−e₁z)²·P̂(z²) (mod J)`, coefficientwise exact.

---

## Theorem S (set-theoretic pinning, ∀k)

> **`V(J) = W₂` over `F̄₃`. Hence `√J = I(W₂)` for every k; `(f₃,…,f_{2k−1},ū_k)` is a
> regular sequence; `J` is a complete intersection; `S/J` is Cohen–Macaulay of dimension k;
> the Hilbert series of `S/J` equals `T_k(t)/t`; and `(J : m) = J` (saturated).**

*Proof.* Let `p ∈ V(J)(F̄₃)`. Every λ-coefficient of `∏_α(1+x_αz) − (1−e₁z)²P̂(z²)` lies in
`J` (Theorem V), so evaluating at `p` gives the **polynomial identity**
`∏_α(1+p_αz) = (1−e₁(p)z)²·P̂_p(z²)` in `F̄₃[z]`. The right side is a doubled linear factor
`(1+tz)²` with `t := −e₁(p)`, times a polynomial in `z²`, whose linear factors come in
antipodal pairs `(1+wz)(1−wz)` (zeros of a polynomial in `z²` pair as `±w`; degree
deficiencies are zero coordinates, which pair antipodally with themselves). Hence the
coordinate multiset of `p` is `{t, t} ∪ {±w_i}` — exactly a `W₂`-point. The containment
`W₂ ⊆ V(J)` is Corollary V.1. So `dim V(J) = k`: k forms cutting codimension k in the
Cohen–Macaulay ring S form a regular sequence; the CI series and CM-ness follow, and
`depth S/J = k ≥ 1` gives `m ∉ Ass(S/J)`, i.e. `(J:m) = J`. ∎

**What this removes:** the `k ≤ 4` restriction on the radical half of GAP 5 (the W15
Jacobian/Bézout route is superseded for `√J`; multiplicity 2 stays as its measured
refinement), and every implicit use of the CI series is now a theorem.

## Theorem NZD (the degree collapse, ∀k)

> **`B(d)_k ⟺ K_{2k−2} = 0`.** One degree decides all of GAP 5 at each k.

*Proof.* Graded dimensions are invariant under base change, so extend scalars to `F̄₃`.
`S/J` is CM (Theorem S) with finitely many associated primes, all of positive dimension;
a linear form ℓ outside their union exists over an infinite field and is a nonzerodivisor
on `S/J`. `K` is an ideal of `S/J`, so `·ℓ : K_m → K_{m+1}` is injective for every m.
Hence `K_m ≠ 0` for some `m ≤ 2k−2` forces `K_{2k−2} ≠ 0`. The converse is trivial. ∎

## Lemma (the slices see everything)

> For `h ∈ S_m`: [for every pair `(a,b)`, every `v`-coefficient of `h|_{x_a=v,x_b=−v}`
> lies in `I(W₂^{(k−1)})`] ⟺ `h ∈ I(W₂^{(k)})_m`.

*Proof.* The slice conditions say h vanishes on every component in which `(a,b)` is a
matched pair; every component has `k−1 ≥ 1` matched pairs, so the union over all pairs
is all of `W₂`. ∎
**Consequence for the mission's Step-3 gate:** with the TRUE lower ideals, the overlap
system's global solution space is `I(W₂)_m` identically — the pre-registered "excess over
J = 0" (run FIRST this turn: PASS, k=3, m=4: dim Sol = 6 = dim J₄) re-certifies `B(d)@k=3`
rather than testing the glue; the glue-bearing objects are the syzygies below.

## Theorem SYZ (the virtual Cayley–Hamilton, ∀k)

> ## `(x_α + e₁)·g_α = (x_α+e₁)²·P̂(x_α) ∈ J_{2k}` for every coordinate α and every k.

*Proof.* Let `χ(λ) := ∏_β(λ + x_β) ∈ S[λ]`, the reversal of `E`: `χ(λ) = λ^{2k}E(1/λ)`.
Reversing Theorem V coefficientwise: `χ(λ) ≡ (λ−e₁)²·P̂(λ) (mod J·S[λ])`. Now evaluate at
`λ = −x_α`. The left side is `∏_β(x_β − x_α) = 0` **identically in S** (the `β = α` factor).
The right side is `(−x_α−e₁)²P̂(−x_α) = (x_α+e₁)²P̂(x_α)` — the square kills one sign and
**P̂ is even** in λ, killing the other. Hence `(x_α+e₁)²P̂(x_α) ∈ J`. ∎

**Reading:** each coordinate, weighted by the square of its virtual doubled factor
`(λ+e₁)`, satisfies the full virtual characteristic polynomial modulo J. Machine gates:
direct membership PASS at k = 2, 3, 4 (all 4/6/8 coordinates). The syzygy was FOUND by the
kernel extraction (the unique single-g linear syzygy per coordinate, pattern `−(x_α+e₁)`)
and then proved; the machine served the pencil.

**Corollary SYZ.1 (the syzygy space).** Let `Φ : (S₁)^{2k} → K_{2k}`, `(b_β) ↦ Σ b_β g_β
mod J`, and `V := ker Φ`. Then `V ⊇ Δ ⊕ ⊕_α F·ρ_α` where `Δ = {(b,…,b)}` (Theorem R(b))
and `ρ_α` is the α-row vector `b_β = (x_α+e₁)δ_{αβ}` (Theorem SYZ) — a direct sum of
dimension `4k`, PROVED ∀k. Measured (pre-registered shape gate): `dim V = 8, 12, 16 = 4k`
at `k = 2, 3, 4` — so at those k, **`V = Δ ⊕ rows` exactly**. Also gated: `K_{2k} = im Φ`
(the kernel is generated one degree above onset by the resolvent family) at k = 2, 3.

## Theorem GP (graded pinning, conditional; the k→k+1 law lives inside)

Fix `k ≥ 3` and assume the two single-degree statements:
- **(Rc)_k:** `I(W₂)_{2k−1} = J_{2k−1} ⊕ span{g_α}` (measured k = 2, 3, 4; RESOLVENT v1);
- **(V)_k:** `ker Φ = Δ ⊕ ⊕_α F·ρ_α` (containment proved ∀k; equality measured k = 2,3,4).

> **Then `K_{2k−2} = 0`, and hence (Theorem NZD) `B(d)_k` holds.**

*Proof.* Let `h ∈ I(W₂)_{2k−2}`. For each α, `x_α h ∈ I(W₂)_{2k−1}`, so by (Rc)_k:
`x_α h = j_α + Σ_β c_{αβ} g_β`, `j_α ∈ J`. **First commutation.** For `α ≠ γ`,
`x_γ(x_αh) = x_α(x_γh)` gives `Σ_β (c_{αβ}x_γ − c_{γβ}x_α) g_β ∈ J_{2k}`, i.e. the tuple
`w_β := c_{αβ}x_γ − c_{γβ}x_α` lies in `ker Φ`; by (V)_k there are `b ∈ S₁`, scalars `d_β`
with `w_β = b + d_β(x_α... )`… explicitly `w_β = b + d_β(x_β+e₁)` for all β. For
`β, β′ ∉ {α,γ}` subtract the two equations: the left side lies in `span(x_α, x_γ)`;
comparing the coefficient of `x_δ` for `δ ∉ {α,γ,β,β′}` (here `2k ≥ 5`, i.e. `k ≥ 3`;
`k = 2` is the sealed base) gives `d_β = d_{β′}`; then the `x_β`-coefficient gives
`2d_β − d_{β′} = d_β = 0`. So `d_β = 0` off `{α,γ}`, and then
`(c_{αβ} − c_{αβ′})x_γ = (c_{γβ} − c_{γβ′})x_α` forces `c_{αβ}` constant over
`β ∉ {α,γ}`; varying γ (two choices overlap for `2k ≥ 5`), `c_{αβ} = c_α` for **all**
`β ≠ α`. Hence, using `Σ_β g_β ∈ J` (Theorem R(b)):
`x_α h ≡ (c_{αα} − c_α)·g_α =: d_α g_α (mod J)`.
**Second commutation.** `d_α x_γ g_α − d_γ x_α g_γ ∈ J`, so the tuple supported on rows
α, γ lies in `ker Φ`: `d_αx_γ·δ_{βα} − d_γx_α·δ_{βγ} = b + d′_β(x_β+e₁)`. For each
`β ∉ {α,γ}`: `b = −d′_β(x_β+e₁)`; two such β force (coefficient comparison as above)
`d′_β = 0` and `b = 0`. Row α then reads `d_αx_γ = d′_α(x_α+e₁)`: the `x_α`-coefficient
gives `2d′_α = 0`, so `d′_α = 0` and `d_α = 0`. **Therefore `x_α h ∈ J` for every α**, i.e.
`h ∈ (J : m)_{2k−2} = J_{2k−2}` by Theorem S (saturation). ∎

**Corollary GP.1.** Since (Rc) and (V) are machine-verified at `k = 3, 4` (gates this turn
and RESOLVENT v1), **`B(d)` at `k = 3, 4` now has a mechanism proof** (base `k = 2` sealed):
the 12/12 measured agreement is explained, not just observed.

## The residue of GAP 5, named in final form

> `B(d)` ∀k ⟸ two statements, ONE degree each, both about the resolvent module `K`:
> **(Rc)_k** — `dim K_{2k−1} = 2k−1` (no unnamed kernel elements at onset), and
> **(V)_k** — `dim ker Φ = 4k` (no unnamed linear syzygies one degree up).
> Compressed: **"K is the module generated by the resolvent family with exactly the named
> relations, in degrees 2k−1 and 2k."** Everything else — the set-theoretic pinning, the
> CI, the degree collapse, the syzygies, the commutation glue, the saturation — is proved
> for every k. Sealed for the next machine level: `HF_red(W₂^{(4)})₈ = 5467`
> (equivalently `dim I(W₂^{(4)})₈ = 968`), derived from generation + the identified V.

**Grades.** S, NZD, slices-lemma, SYZ, SYZ.1-containment, GP-mechanism: PROVED ∀k.
(Rc)_k, (V)_k-equality, K-generation: COMPUTED k ≤ 4 (k ≤ 3 for generation); ∀k CONJECTURE.
`B(d)`: PROVED k ≤ 4 by mechanism; ∀k OPEN with the residue above. No fitted constants
anywhere; every gate pre-registered; the shape gate at k=4 passed on its pre-registration.

— FRESCALES14. Engines: `gap5_step3_gate.py`, `gap5_syzygy_gates.py`,
`gap5_kernel_extract3.py`, `gap5_syzygy_addendum.py` (same turn; row counts + controls).
