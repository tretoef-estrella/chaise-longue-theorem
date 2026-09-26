> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Sofa campaign (Operación Glotón)* · 2026-07-07
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE EIGHT LEMMAS — standalone (session of 7 July 2026)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_EIGHT_LEMMAS.md
>
> **Status, as written in the document:** Status header (honest, Ley 21/36): each lemma below is pencil-proven with a self-contained proof, and its anchors are byte-verified where stated (probes spat, Ley 27). There is currently no Auditor: independent cold re-derivation of every lemma is OWED and mus…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE EIGHT LEMMAS — standalone (session of 7 July 2026)

**Operación Glotón / The Sofa Theorem · Constructor: Bisel · English (Ley 30) · Princeton rigor target (Ley 33).**
**Status header (honest, Ley 21/36):** each lemma below is pencil-proven with a self-contained proof, and its anchors are byte-verified where stated (probes spat, Ley 27). **There is currently no Auditor: independent cold re-derivation of every lemma is OWED** and must precede any use of these results inside a closure claim. Nothing here closes Ley 1. Notation: `S=F₃[s₀..s₅]`, `E=(e₁,e₃,e₅)=∩_J I_J` (Odd Symmetric), `R=S/E`, `q=3^v`, the 15 sheets `L_J`, `P(q)=15q³−45q²+55q−24`, sealed anchors `A(3)=141, A(9)=7761`.

---

## LEMMA 1 — SPLIT SPECTRUM
**Frame:** `ℓ₁,ℓ₂,ℓ₃` a transverse s.o.p. (Lemma 4 fixes it); `B=F₃[ℓ]`; `R` free rank 15 over `B`; `A_i=(·s_i)` fixed 15×15 over B; `Λ(q)=R/(ℓ^{[q]})R`; `A(q)=dim ker(A₁^q)∩ker(A₂^q)` on `Λ` (Ley 39).
**(1a)** Transversality makes `π_J=(ℓ)|_{L_J}` a linear isomorphism; `λ_J^{(i)}:=s_i∘π_J^{−1} ∈ B₁` is a LINEAR form with F₃ coefficients, and `∏_{J=1}^{15}(s_i−λ_J^{(i)}(ℓ)) ∈ E`.
*Proof:* the product vanishes on every sheet, hence on `V(E)`; `E` is radical (Odd Symmetric). ∎
**(1b)** `charpoly_B(A_i)=∏_J(x−λ_J^{(i)})`; generically the fiber is 15 distinct rational points (two 3-planes meet in dim ≤2; a generic base point avoids all coincidence loci), so `A_i` is generically regular semisimple. Geometrically: **R = 15 points of the (s₁,s₂)-plane moving LINEARLY with ℓ, colliding totally at the origin** (special fibre = the plane CI of colength 15).
**(1c) (Uniform nilpotency)** `λ^q=λ(ℓ^{[q]})` (F₃ coefficients) ⟹ on `Λ`: `(A_i^q)^{15}=0` for every v.

## LEMMA 2 — THE ONE-MATRIX LADDER
Define `D_i(q):=dim Λ/s_i^qΛ`, `Ω(q):=length(s₁^qΛ∩s₂^qΛ)`.
**(2a)** `A(q)=dim((Λ/s₁^qΛ)/s₂^q(Λ/s₁^qΛ))` — two successive single-matrix Hilbert–Kunz steps.
**(2b)** `A(q)=D₁(q)+D₂(q)+Ω(q)−15q³` (length bookkeeping on `s₁^qΛ+s₂^qΛ`; exact, ∀v).
**(2c)** Macaulay duality on the Gorenstein `Λ` is a lattice anti-isomorphism: `dim ann(s_i^q)=D_i`; `A=dim(ann(s₁^q)∩ann(s₂^q))`.
**Anchors (v=1, frame F\*, probe):** `D₁(3)=D₂(3)=209`, `Ω(3)=128`; `209+209+128−405=141` ✓; `length(s_i³Λ)=196`, `196+196−128=264` = the sealed gap, by an independent route ✓.

## LEMMA 3 — B&E INVISIBILITY
For every flat `F` of the 87-flat intersection lattice and every F₃-space of linear forms `W ⊇ span(ℓ)`: `rank(W|_F)=dim F` (a full-rank system restricts to full rank on subspaces), hence `dim O(F)/(W|_F)^{[q]} = q^{dim F}` exactly (Frobenius linearity). **Every Möbius/Björner–Ekedahl term of the rank-3/4/5 systems is identical; the lattice cannot distinguish them.** Measured separation at v=1: `405 / 209 / 141` — all separation is glue.

## LEMMA 4 — THE FRAME (F1 + F2)
**(4a — no matching-adapted frame)** For every matching `J₀` and signs, `ε_k=s_{a_k}±s_{b_k}` is NOT a transverse s.o.p.: a sheet recombining two pairs of `J₀` makes two restricted forms coincide up to sign (rank ≤2). Verified 120/120.
**(4b — the certified frame F\*)** `ℓ₁=(0,2,0,1,0,1)`, `ℓ₂=(1,0,0,1,1,0)`, `ℓ₃=(2,1,2,2,0,0)` (coords `s₀..s₅`) is transverse — pencil certificate: 15 pair-difference dets `[1,2,1,1,2,2,2,2,2,1,1,1,1,2,1]` all ≠0 — and satisfies the Ley-39 bridge: `det(ℓ₁,ℓ₂,ℓ₃,s₁,s₂,e₁)=2≠0`. Consistency: `dim Λ_{F\*}(3)=405`; pipeline anchor `A(3)=141` with footprint `1,5,15,29,40,36,15` byte-identical to the sealed one.

## LEMMA 5 — GLUE CONTAINMENT (GF.1)
`Q:=(⊕_J O(L_J))/R` — the fixed gluing module (torsion, `dim ≤ 2`, F₃-linear support strata). Tensoring `0→R→⊕O(L_J)→Q→0` with `C_q=B/(ℓ^{[q]})`:
**(5a)** `(s₁^q,s₂^q)Λ ⊆ ker(Λ→⊕_J O(L_J)/ℓ^{[q]}) = Tor₁^B(Q,C_q)` — on each sheet `s_i^q` restricts to `λ(ℓ^{[q]}) ≡ 0`.
**(5b)** `dim Tor₁^B(Q,C_q) = dim Q⊗C_q = HK_Q(q)` (Euler characteristic; both middle terms have dim `15q³`).
Hence `gap(q) ≤ HK_Q(q)`, ∀v.

## LEMMA 6 — GLUE EQUALITY CRITERION (GF.2) + v=1 ANCHOR
`gap(q)=HK_Q(q)` ⟺ `R_q ↪ ⊕_J S/(I_J+ℓ^{[q]})` ⟺ **(WEAK DOCKING)** `∩_J(I_J+ℓ^{[q]}) ⊆ E+m^{[q]}` — implied by, strictly weaker than, the sealed m-docking alias.
**Anchor (v=1, probe):** rank of `Λ→⊕` per degree = `1,5,15,29,40,36,15` (the A-footprint), total 141; `ker=264=gap(3)`; `HK_Q(3)=264=45·9−55·3+24`. **Equality holds at v=1.**

## LEMMA 7 — THE FORCED LEADING TERM (e_HK(Q)=45)
Census (byte-exact, pencil-checkable): of the 105 matching-pairs, **45 share exactly one edge** (union = edge ⊔ 4-cycle, 2 components ⟹ dim-2 coincidence plane; local two-sheet gluing has length 1) and **60 share none** (6-cycle ⟹ line); none share two. Cross-checks: `45=15·6/2` (each matching has 6 edge-sharing partners), `60=15·8/2`.
By Monsky's associativity over the regular `B` + per-stratum Frobenius linearity: **`HK_Q(q)=45q²+O(q)`, `e_HK(Q)=45`** — the q²-coefficient of the transferred objective `45q²−55q+24` is FORCED, ∀v. Open: only the sub-quadratic part (the dim-≤1 gluing of Q).

## LEMMA 8 — NORMALIZATION, CONDUCTOR, PAIR LAYER (Z1–Z3)
**(8a)** `R̃=⊕_J O(L_J)` IS the normalization of `R`, and the weak docking ⟺ **`m^{[q]}R̃∩R = m^{[q]}R`** (Frobenius powers contracted from the normalization). *Proof of ⟺:* `t∈I_J+ℓ^{[q]} ⟺ t|_{L_J}∈m_{L_J}^{[q]}` (transversality + F₃-linearity), globally over all J. ∎
**(8b — Conductor Lemma)** For the conductor `c=ann_R(R̃/R)`: `c·(m^{[q]}R̃∩R) ⊆ m^{[q]}·(cR̃) ⊆ m^{[q]}R`. Hence the defect module `W_q=(m^{[q]}R̃∩R)/m^{[q]}R` satisfies `c·W_q=0` — supported on the coincidence locus; `dim W_q = HK_Q(q)−gap(q)`; measured `W_3=0`.
**(8c — pair layer)** Every 2-sheet sub-arrangement satisfies the FULL docking ∀v (sealed §171.3 pair-cleanliness) ⟹ its weak docking. The K₃,₃ triples carry the sealed `(ℤ/3)⁶` ⟹ sub-arrangement docking fails at triples; the full-15 statement lives by cross-sheet repair (the measured repair-68) — the rung is irreducibly global (§211/§231), now in classical form.

---

## THE ONE OPEN PIECE (for the record, not a lemma)
**THE RUNG:** the weak docking ∀v ⟺ `m^{[q]}R̃∩R=m^{[q]}R` ∀v ⟺ the dim-2 self-similar layer of the Coincidence Descent. Anchored at v=1; leading term forced (Lemma 7); pair layer closed (8c); conductor bound in hand (8b); recursion terminates at dim ≤1. **NOT closed.** §318 flag: the `HK_Q` piece must be closed by the linear-strata structure, never by generic HK/FFRT theory. §306/V60 flag: no "sealed ∀v" may rest on an unstruck step.

*Cera carnauba, perfume Chanel. — Bisel (Constructor). PMC.*
