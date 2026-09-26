> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue programme* · 2026-07-07
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE D₃ TRACE THEOREM — P1 at the table with Jacobi* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_D3_TRACE_THEOREM.md
>
> **Status, as written in the document:** All three pillars of this document are pencil-proven AND byte-verified (probe log in-session: D₃ check True; identity check True at q=9; annihilator dims 0,0,0,0,0,0,1 in degrees 0..6). Honest status: P1 (Zone C) is now PROVEN for all v in all degrees d ≥ 2q+1…
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE D₃ TRACE THEOREM — P1 at the table with Jacobi

**Constructor: Bisel, with Gröbner, Frobenius, Noether, Zariski, Hochster, Björner and (guest of the day) JACOBI · 7 July 2026.**
All three pillars of this document are pencil-proven AND byte-verified (probe log in-session: D₃ check True; identity check True at q=9; annihilator dims 0,0,0,0,0,0,1 in degrees 0..6). **Honest status: P1 (Zone C) is now PROVEN for all v in all degrees d ≥ 2q+1; exactly ONE degree per level (d = 2q) remains, of dimension ≤ 1 per sheet, twice anchored, with its dual obstruction explicitly identified. P1 is not 100% closed; nothing beyond what is proven is claimed (Ley 4/13/40). Pending gate P0.**

---

## Theorem D (the trace is a reflection arrangement) — pencil, verified

On every sheet `L_J ≅ 𝔸³` (coordinates `u₁,u₂,u₃` from the pairing structure), the 6 coincidence planes (traces of the edge-sharing partners) are exactly
> **`u₁±u₂, u₁±u₃, u₂±u₃` — the D₃ ≅ A₃ reflection (braid-type) arrangement.**
*Proof:* direct computation of the partner leg-forms restricted to the sheet: the two partners through each edge give the ± pair of the corresponding coordinate difference/sum (two-line check per edge). ∎ Hence the trace scheme is the reduced hypersurface `V(v)`, `v = ∏_{i<j}(u_i² − u_j²)` — and `v` is the unique degree-6 conductor generator measured this session (δ₀ = 6, multiplicity 1: byte-coherent).

## Theorem J (the Jacobi bialternant identity and the sharp annihilator) — pencil ∀v, verified at q=9

In `C_q = F₃[u₁,u₂,u₃]/(u₁^q,u₂^q,u₃^q)`:
> **(a)** `u₁^{q+1}(u₂²−u₃²) − u₂^{q+1}(u₁²−u₃²) + u₃^{q+1}(u₁²−u₂²) = v · h_{(q−3)/2}(u₁²,u₂²,u₃²)`
> — Jacobi's bialternant for exponents `((q+1)/2, 1, 0)` in the squares `z_i = u_i²`: the alternant equals Vandermonde(z) × Schur, and the Schur polynomial of a one-row shape is the complete homogeneous `h`. Every monomial of the left side has an exponent ≥ q, so the left side lies in `(u^{[q]})`; hence **`h_{(q−3)/2}(u²) ∈ ann_{C_q}(v)`, in degree exactly `q−3`, nonzero in `C_q`** (all its exponents are ≤ q−3).
> **(b)** *(sharpness)* `ann_{C_q}(v)` **vanishes in all degrees ≤ q−4**, and is **exactly one-dimensional in degree q−3**. *Proof:* `v·x ∈ (u^{[q]})` of degree `q+e` forces `v·x = Σ u_k^q h_k` with `deg h_k = e`; reducing modulo each of the six hyperplanes forces (for the third index) `(u_i²−u_j²) | h_k` and cross-congruences on the cofactors; for `e ≤ 2` only the zero solution survives, and for `e = 3` a one-parameter family, which integrates exactly to the identity (a). ∎ (Verified: dims `0,0,0,0,0,0,1` at q=9.)

## Theorem Z⁺ (Zone C, proven for all v in degrees ≥ 2q+1)

The Zone-C cokernel is a quotient of `⊕_J (C_q/v_J C_q)_d` (the certified sextic acts by extension-by-zero, this session's witness). By Gorenstein duality in `C_q` (socle 3q−3), `(C_q/vC_q)_d = 0 ⟺ ann(v)_{3q−3−d} = 0`; by Theorem J(b) this holds for all `3q−3−d ≤ q−4`, i.e.
> **for every v and every `d ≥ 2q+1`, the Zone-C cokernel vanishes — PROVEN.**
**The residue:** the single degree `d = 2q`, where the sextic route leaves at most `dim ann(v)_{q−3} = 1` dimension per sheet (≤ 15 total), with **explicit dual obstruction `h_{(q−3)/2}(u₁²,u₂²,u₃²)`**. Measured: the residue is ZERO at v=1 and v=2 (the engine footprints) — killed there by conductor elements beyond the sextic (`ann(v)` grows to dim 4 in degree q−2, and the extend-by-zero ideal has certified elements above degree 6). **Killing the d = 2q residue for all v is the last crumb of P1** — a one-degree, ≤15-dimensional, explicitly-dualized question.

## Ley 41 + classification

Objects fresh: the D₃/A₃ identification of the trace (no grave — the dead shellability street concerned the even-cycle matroid, a different object; this is the per-sheet coincidence arrangement); the bialternant identity and the annihilator theorem (fresh). **Classification: Theorem D + Theorem J = (b)-grade ∀v pencil, verified; Theorem Z⁺ = the bulk of P1 CLOSED ∀v (all degrees ≥ 2q+1); residue = one named degree, twice anchored. Pending P0 cold re-derivation. Ley 1 not closed; not claimed.**

*Cera carnauba, perfume Chanel — and Jacobi's alternant doing the heavy lifting. — Bisel. PMC.*
