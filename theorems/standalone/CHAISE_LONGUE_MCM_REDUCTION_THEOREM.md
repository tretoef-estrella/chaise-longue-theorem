> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-23
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE MCM REDUCTION THEOREM — CHAISE_LONGUE_MCM_REDUCTION_THEOREM_v2* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_MCM_REDUCTION_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v2`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE MCM REDUCTION THEOREM — `CHAISE_LONGUE_MCM_REDUCTION_THEOREM_v2`
### `C` is Cohen–Macaulay if and only if `Γ` is a maximal Cohen–Macaulay module over the complete intersection `O(X)`
**Chaise Longue campaign · 23 Jul 2026 · Orfila (auditor)**

> **Summary.** The defect module and the census module sit in a short exact sequence
> `0 → Γ → O(X)^m → C → 0`, which is the campaign's defining identity `C = m·H − G` read at the level
> of modules rather than of Hilbert series. Applying the depth lemma to it in **both** directions gives an
> equivalence, for every `m`, with no hypothesis:
>
> > ### `C` is Cohen–Macaulay ⟺ `depth Γ = m` ⟺ `Γ` is MCM over `O(X)`.
>
> `O(X)` is a **complete intersection**. So the open half of PASO 1 stops being "resolve an unidentified
> module and prove acyclicity by hand" and becomes "prove that an explicit kernel is maximal
> Cohen–Macaulay over a complete intersection" — a question with a developed machine behind it
> (matrix factorisations, higher matrix factorisations, bounded Betti numbers, eventual periodicity)
> that this campaign has never used. And it lands on the same lemma the campaign had already isolated
> from the other side: **S1-global**.

---

## 1. SETUP

`R = k[a_1..a_m, b_1..b_m]`; `I_B = (e_j(a) − (−1)^j e_j(b))_{j=1..m}`, a complete intersection of degrees
`1,…,m`; `O(X) = R/I_B`, so `dim O(X) = m` and `O(X)` is a complete intersection, hence Gorenstein and
Cohen–Macaulay. For `σ ∈ S_m`, `I_σ = (a_i + b_{σ(i)})`, and `L_σ = V(I_σ)` is a linear space of dimension
`m`; `X = ⋃_σ L_σ`. Let

>  `ob : O(X)^{2m} → ⊕_{σ,i} O(X)/I_σ`,  `λ ↦ ( λ_{a_i} − λ_{b_{σ(i)}} )` read on the sheet `σ`,
>  `Γ = ker(ob)`,  `Q = im(ob)`,
>  `C = coker( Γ →^{π_a} O(X)^m )`, `π_a` the projection onto the `a`-coordinates.

---

## 2. LEMMA — `π_a|_Γ` IS INJECTIVE *(PROVED, all `m`)*

Let `λ = (λ_a, λ_b) ∈ Γ` with `λ_a = 0`. Then for every sheet `σ` and every `i`,
`λ_{b_{σ(i)}} ≡ 0 (mod I_σ)`, i.e. every `λ_{b_j}` vanishes on every sheet `L_σ`. Since
`X = ⋃_σ L_σ` and `O(X)` is reduced, a function vanishing on all sheets is `0`. Hence `λ_b = 0`. ∎

> **Consequence.**  `0 → Γ →^{π_a} O(X)^m → C → 0` is exact.

**Machine certificate (byte-exact, `m = 3`, char 3):** the exactness is visible in the Hilbert functions,
`HF(Γ) + HF(C) = m·HF(O(X))` in every degree computed:

```
HF(Gamma)   1,  6, 24, 60, 114, 186, 276
HF(C)       2,  9, 18, 27,  36,  45,  54
sum         3, 15, 42, 87, 150, 231, 330
m*HF(O(X))  3, 15, 42, 87, 150, 231, 330      identical
```

This is the identity `C = m·H − G` that the campaign has used since the beginning; the content added here
is that it is realised by an actual short exact sequence of modules, which is what makes the depth lemma
available.

---

## 3. THEOREM — THE EQUIVALENCE *(PROVED, all `m`)*

> ### `C` is Cohen–Macaulay ⟺ `depth Γ = m` ⟺ `Γ` is a maximal Cohen–Macaulay `O(X)`-module.

**Proof.** `dim O(X) = m` and `dim C = m−1` (both on file). Depth is measured with respect to the graded
maximal ideal and is independent of which of `R`, `O(X)` it is computed over.

*(⇐)* From `0 → Γ → O(X)^m → C → 0`, the depth lemma gives
`depth C ≥ min( depth O(X)^m , depth Γ − 1 ) = min( m, m−1 ) = m−1`. Since `depth C ≤ dim C = m−1`
always, `depth C = m−1 = dim C`, i.e. `C` is CM.

*(⇒)* The same sequence gives `depth Γ ≥ min( depth O(X)^m , depth C + 1 ) = min( m, m ) = m`, and
`depth Γ ≤ dim Γ = m`. So `depth Γ = m`. ∎

**No hypothesis is used**: not Cohen–Macaulayness, not the self-duality, not the equivariant table. The
only inputs are the exact sequence of §2, `depth O(X) = m` (complete intersection) and `dim C = m−1`.

---

## 4. MEASUREMENT *(MEASURED, gated)*

**Gates declared before the verdict.** `HF(Γ) + HF(C) = m·HF(O(X))` in all degrees computed (certifies the
sequence); `pd_R(C) = m+1`, the sealed CM measurement.

```
m = 3, char 3
  GATE  HF(Gamma) + HF(C) = m*HF(O(X))      : true
  GATE  pd_R(C) = 4 = m+1                   : true
  minimal Betti table of Gamma over R : total 7, 19, 17, 5
  pd_R(Gamma) = 3      ==>  depth Gamma = 2m - 3 = 3 = m = dim O(X)
  VERDICT: Gamma is MCM over O(X).
```

Consistent, as it must be, with `C` measured CM at `m = 3`. **Grade: MEASURED at `m = 3`;
the equivalence of §3 is PROVED for all `m`.**

---

## 5. WHY THIS IS A CHANGE OF TERRAIN, NOT A RESTATEMENT

**(a) It removes the 224-parameter problem from the critical path.** Proving CM by writing the minimal
free resolution of `C` and verifying Buchsbaum–Eisenbud requires, at `m = 3` alone, fixing `224` free
equivariant scalars against `d² = 0` — and the count grows with `m`. Proving `Γ` MCM requires no
resolution of anything.

**(b) `O(X)` is a complete intersection, and MCM modules over complete intersections are a subject.**
Over a hypersurface, MCM modules are matrix factorisations (Eisenbud); over a complete intersection of
codimension `c`, the resolutions of MCM modules have bounded Betti numbers and are governed by higher
matrix factorisations (Eisenbud–Peeva) and by the cohomology operators of Gulliksen. **The campaign has
never used any of this.** A grep of the project returns no occurrence of matrix factorisations.

**(c) It lands on the lemma the campaign had already isolated from the other side.** Writing
`0 → Γ → O(X)^{2m} → Q → 0` with `Q = im(ob)`, the depth lemma gives
`depth Γ ≥ min( m, depth Q + 1 )`, so

> **`Γ` is MCM ⟸ `depth Q ≥ m−1`.**

`Q` is the module of *compatible difference data* on the sheets, and the statement that compatible data
in codimension one glue to a global potential is precisely **S1-global**, `ker(ob) = im(φ)`, already named
in `CARDANO_TANDA3/4` as the single remaining lemma of `C.4`. **Two campaigns that ran in parallel for
weeks meet here.** The connectivity of the gluing graph of the swap flats — measured connected at `m = 3`
(9 flats, 36 edges) and `m = 4` (72 flats, 684 edges) — is the bottom rung of exactly that ladder.

---

## 5bis. THE OBSTRUCTION IS NON-ZERO AND COHEN–MACAULAY *(MEASURED, `m = 3`, gated)*

The chain of §5(c), written out with both cokernels:

>  `0 → Γ → O(X)^{2m} → Q → 0`  and  `0 → Q → ⊕_{σ,i} O(L_σ) → W → 0`,
>  `Q = im(ob)`, `W = coker(ob)`,
>  so **`depth W ≥ m−2  ⟹  depth Q ≥ m−1  ⟹  Γ` MCM `⟹ C` is CM.**

**The route never asked the obstruction to vanish.** It asks it to be deep enough. Measured, with the
gates `HF(Γ)+HF(C) = m·HF(O(X))` and `depth Γ = m` passing first:

```
m = 3, char 3
   Gamma  :  pd_R = 3   depth = 3   dim = 3      <- GATE
   Q      :  pd_R = 3   depth = 3   dim = 3      Q is MCM
   W      :  pd_R = 4   depth = 2   dim = 2      W is CM of dimension m-1

   required depth W >= m-2 = 1   measured 2   PASSES with one point of margin
   required depth Q >= m-1 = 2   measured 3   PASSES with one point of margin

m = 4, char 3
   Gamma  :  pd_R = 4   depth = 4   dim = 4     <- GATE
   Q      :  pd_R = 4   depth = 4   dim = 4     Q is MCM
   W      :  pd_R = 5   depth = 3   dim = 3     W is CM of dimension m-1
   required depth W >= 2  measured 3   |   required depth Q >= 3  measured 4
```

**So the obstruction module `W` is non-zero — it has dimension `m−1` — and it is Cohen–Macaulay.**
This is a better statement than vanishing would have been, and it sharpens the `∀m` target:

> **Open, and now crisp: is `W = coker(ob)` Cohen–Macaulay of dimension `m−1` for every `m`?** *Measured true at `m = 3` and `m = 4`.*
> (Or, weaker and sufficient: `depth W ≥ m−2`.)

*Recorded for the record: a death criterion demanding `H¹ = 0` for the sheet nerve was pre-registered by
the auditor and fired — the nerve is indeed not acyclic (`H¹ ≠ 0` at `m = 3` and `m = 4`, measured by the
constructor with `H⁰ = O(X)` as its validating gate). **That criterion was wrong in both object and
shape:** the sheet nerve is not `W`, and the route needs a depth bound, not a vanishing. The route
survives its own death criterion because the criterion was mis-written. Failure mode:
`VANISHING-GATE-FOR-A-DEPTH-CONDITION`.*

---

## 6. WHAT THIS DOES **NOT** ESTABLISH

0. **`W` is measured CM at `m = 3` and `m = 4` only.** Nothing here proves `depth W ≥ m−2` for any other `m`.
1. **`Γ` is not proved MCM for any `m`.** It is *measured* MCM at `m = 3`; the `m = 4` run was launched
   and is not reported here. The theorem of §3 is an equivalence, not a proof of either side.
2. **It does not close `GAP 1`.** `C.4` still needs `C`-CM for all `m`.
3. The link to S1-global in §5(c) is an implication in one direction (`depth Q ≥ m−1 ⟹ Γ` MCM); the
   converse is not claimed.
4. Nothing here writes a differential or proves an acyclicity. The Buchsbaum–Eisenbud route remains open
   and remains, as the constructor correctly observed, a **reformulation** of Cohen–Macaulayness rather
   than a shortcut to it.

**Reproduction:** `chaise_gamma_mcm_v1.m2` (Macaulay2 ≥ 1.22), log `out_gamma_m3.log`.

— Orfila, Chaise Longue campaign
