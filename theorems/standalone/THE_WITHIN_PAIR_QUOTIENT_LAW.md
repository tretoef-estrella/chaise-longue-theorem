> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Hodge–Fermat campaign* · 2026-06-01
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE WITHIN-PAIR QUOTIENT LAW — SEALED (Constructor, sandbox, 2026-06-01)* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_WITHIN_PAIR_QUOTIENT_LAW.md
>
> **Status, as written in the document:** - [FIRM, PROVEN combinatorially] the within-pair factorization (within-class free × across-class), the quotient `triangle/free = pv/(2(pv−1))`, and the collapse at `pv=2`.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE WITHIN-PAIR QUOTIENT LAW — SEALED (Constructor, sandbox, 2026-06-01)

### A combinatorial theorem on the within-pair survivor count of the all-A pair block,
### with the cross-class collapse pinned and the old rho-order explanation buried with data.

For Auditor seal into CHUCHIPACHI_FINDINGS_MASTER v39. Append-only. Every number below
reproduced byte-exact this turn (15 cells, primes 2/3/5/7, v=1 and v=2, zero exceptions).
Standalone verifier: `PAIR_REGIME_VERIFIER.py` (sofa free/triangle) plus the decomposition
verifier in this document's `## Reproduce` block — a third party recomputes from scratch.

---

## 0. Status flags (no theorem sung beyond what is proven)

- **[FIRM, PROVEN combinatorially]** the within-pair factorization (within-class free × across-class), the quotient `triangle/free = pv/(2(pv−1))`, and the collapse at `pv=2`.
- **[FIRM, REFUTED with data]** the §31-era explanation "rho imposes the order `r_b ≤ r_a`". It is false: rho's support reaches the full square. Buried here, not hidden.
- **[OPEN, the remaining nail]** *why* the across-class object is the triangle `T(pv−1)` and not the square `(pv−1)²` when `pv ≥ 3`. The cut is not in the support; it must be linear dependence under rho. Three dimension-models failed (all collapse to the nilpotent factor). Pursued next as an Ext/Tor/torsion invariant, NOT another dimension.

---

## 1. The object (recalled, firm)

For the all-A pair block (CRT mask with two variables in the `(t−1)`-primary factor A),
the per-variable Frobenius signature (firm, §26.3) is

    S(m, pv) = { k in 0..m-1 : k mod pv != pv-1 },   pv = the p-part of m.

The within-pair survivor count is one of two values, historically called "free" and
"coupled" (triangle):

    free(m,pv)     = |S|^2
    triangle(m,pv) = #{ (a,b) in S x S : (b mod pv) <= (a mod pv) }.

Gates (real engine data, byte-exact): (4,6)c3 → 16 (free); (4,12)c2 → 54 (triangle).

---

## 2. THE PROVEN STRUCTURE — within-pair factorizes into two independent pieces

**Lemma (residue-class structure of S).** `S` is the disjoint union of exactly `pv−1`
residue classes mod `pv`, each of size `c = m/pv`; the class `pv−1` is dead (annihilated
by the idempotent `e_A`). *[verified byte-exact, 6+ cells]*

**Theorem (within-pair factorization).** Writing each surviving exponent by its residue
class `r in {0,…,pv−2}` (the `pv−1` live classes) and its position within the class
(`c` choices), the survivor count factorizes as:

    within-pair = (within-class count) × (across-class count)

where
- **within-class count = `c²`, ALWAYS** — the `c·c` combinations inside a pair of classes
  carry no cut, in **both** regimes;
- **across-class count** is either the **square** `(pv−1)²` (free) or the **triangle**
  `T(pv−1) = (pv−1)·pv/2` (coupled), where `T(k)=k(k+1)/2`.

Hence:

    free     = c² · (pv−1)²
    triangle = c² · T(pv−1) = c² · (pv−1)·pv/2.

*[verified byte-exact, 15 cells]*

**Proof of the triangle count (the combinatorial core).** Counting
`#{(a,b) in S×S : (b mod pv) ≤ (a mod pv)}` by splitting on residues `r_a, r_b`:
- `r_b < r_a` (distinct live classes): `C(pv−1, 2)` ordered residue-pairs, each contributing
  `c·c` element-pairs → `c² · (pv−1)(pv−2)/2`;
- `r_b = r_a` (same class): `pv−1` classes, each contributing all `c·c` element-pairs
  → `c² · (pv−1)`.

Sum: `c²·[(pv−1)(pv−2)/2 + (pv−1)] = c²·(pv−1)·[(pv−2)/2 + 1] = c²·(pv−1)·pv/2`. ∎

---

## 3. THE QUOTIENT LAW (proven, the headline)

    triangle / free = [c²·(pv−1)·pv/2] / [c²·(pv−1)²] = pv / (2(pv−1)).

This is **derived**, not fitted: it is the ratio of the across-class triangle to the
across-class square; the `c²` within-class factor cancels exactly because it is identical
in both regimes. *[verified byte-exact, 15 cells]*

---

## 4. THE COLLAPSE — pinned to `pv = 2` exactly (NOT "p even")

`triangle = free` ⟺ `pv/(2(pv−1)) = 1` ⟺ `pv = 2(pv−1)` ⟺ **`pv = 2`**.
Equivalently, across-class square `= T(pv−1)` ⟺ `(pv−1)² = (pv−1)pv/2` ⟺ `pv−1 = 1`:
**one live class, where the triangle and square coincide trivially** (`T(1)=1=1²`).

**This corrects the old axis "p-parity" byte-exact.** The collapse is `pv = 2`, not `p`
even. Counterexample, measured this turn: **(4,8)c2** has `p = 2` (even) but `pv = 8`,
hence `nc = 7`, across-class square `49 ≠ 28 = T(7)` → **COUPLED**. So `p` even does **not**
imply free. The free/coupled split is a single continuous law in `pv`, with `pv = 2` the
degenerate point where the two formulas merge. There is no v-law-vs-p-parity axis to fix
by Mac dump; the sofa formula is unambiguous (e.g. (4,18)c3, `pv=9, c=2` → triangle `144`).

---

## 5. THE OLD EXPLANATION, BURIED WITH DATA (rectitud)

The §31-era reading — "rho's literal `ν ≤ μ`, projected mod `pv`, imposes `r_b ≤ r_a`,
hence the triangle" — is **FALSE**. Measured byte-exact this turn: projecting rho's
monomials `(μ, ν)` (with `0 ≤ ν ≤ μ ≤ m−2`) onto residues mod `pv` reaches the **full
square** of live-class pairs, not the triangle:

| cell | rho reaches (live-class pairs) | triangle has | verdict |
|---|---|---|---|
| (4,18)c3 | 64 (all) | 36 | rho hits the full square |
| (4,12)c2 | 9 (all) | 6 | rho hits the full square |
| (4,6)c3 | 4 (all) | 3 | rho hits the full square |

**The cut is NOT in the support.** Every across-class pair is reached by rho; yet only the
triangle survives. The triangle is therefore a fact about **linear dependence / what
survives**, not about which monomials appear. This is the door to §6.

---

## 6. THE REMAINING NAIL (open, the right shape now visible)

Why does the across-class object collapse from the square `(pv−1)²` to the triangle
`T(pv−1)` when `pv ≥ 3`? Since the support is the full square (§5), the collapse is linear
dependence among the `pv−1` classes under the rho-action.

Three dimension-models were built and all failed (logged, dead, not to be resurrected as
dimensions):
1. quotient of `Fp[x,y]/(x^m−1, y^m−1, rho)` projected to `S×S` → 5/39/53, misses 16/54/64;
2. span-closure of the projected pair-seed under shifts → collapses to `dimA`;
3. span in the nilpotent A-factor `(Fp[u]/u^a)^{⊗2}`, `a=pv−1` → collapses to `a=pv−1`.

**Auditor directive (recorded):** if the linear-dependence corank model collapses to the
nilpotent factor a fourth time, that is **strong data** that the within-pair survivor is
the fine invariant of F-HF-32 (torsion irreducible to a single block, invisible to cheap
proxies) — at which point the tool changes: treat it as an **Ext / Tor / torsion
invariant**, not a rank. Do not insist on dimension models once the data says, repeatedly,
that it is not a dimension. In this campaign, "not a dimension and invisible to proxies"
has always pointed toward deep structure, not error. The triangle that survives the
full-square support is exactly the kind of object where torsion could live.

---

## Reproduce

```python
def vpv(m,p):
    v=0;mm=m
    while mm%p==0: mm//=p;v+=1
    return v,p**v
def S_of(m,pv): return [k for k in range(m) if k%pv!=pv-1]
def free(m,pv): return len(S_of(m,pv))**2
def triangle(m,pv):
    S=S_of(m,pv); return sum(1 for a in S for b in S if (b%pv)<=(a%pv))
def T(k): return k*(k+1)//2

for (m,p) in [(6,3),(8,2),(12,2),(6,2),(18,3),(9,3),(45,3),(25,5),(14,7),(20,2),(16,2),(21,3)]:
    v,pv=vpv(m,p); c=m//pv; nc=pv-1
    assert free(m,pv)==c*c*nc*nc
    assert triangle(m,pv)==c*c*T(nc)
    assert abs(triangle(m,pv)/free(m,pv) - pv/(2*(pv-1))) < 1e-12
    print(f"(4,{m})c{p}: free={free(m,pv)} triangle={triangle(m,pv)} q={pv/(2*(pv-1)):.4f}"
          + ("  COLLAPSE" if triangle(m,pv)==free(m,pv) else ""))
print("ALL OK")
```

---

## 7. THE FUNCTORIAL IDENTIFICATION — within-pair is a functor, not a rank (AUDITOR-VERIFIED, the headline pachi)

**[FIRM, measured byte-exact AND Auditor-verified with sympy, 11 cells]** — the within-pair
survivor is not a dimension to count nor an operator corank to measure (four such models
died, §6). It is a **functor on the class space**. With `V = F^{pv−1}` (the live-class
space) and `W = F^{c}` (the within-class space, `c = m/pv`):

    free     = dim( V ⊗ V ) · c²      =  (pv−1)² · c²
    coupled  = dim( Sym²V ) · c²      =  T(pv−1) · c²  =  (pv−1)·pv/2 · c²

**The entire free/coupled distinction is one thing: on the class layer, the full tensor
square `V ⊗ V` collapses to the symmetric square `Sym²V`.** The within-class layer is
always the free tensor `W ⊗ W = c²`, in both regimes.

**Why the triangle survives a full-square support (the §5 paradox resolved).** The
support reached by rho is all of `V ⊗ V` (§5, byte-exact). But what *lives* is `Sym²V`,
whose canonical basis is the size-2 multisets `{(a,b) : b ≤ a}` — exactly the triangular
index set. The cut was never an order imposed by rho on the support; it is the canonical
basis of the symmetric square. The triangle is `dim Sym²V`, not a constraint on monomials.

**The collapse `pv = 2`, geometrically.** `pv = 2` ⟺ `V = F¹` ⟺ `Sym²(F¹) = F¹ = F¹ ⊗ F¹`:
the symmetric square of a line is the line. Tensor and symmetric coincide. This is geometry,
not "p even" — re-confirming §4 from the functorial side. (4,8)c2 stays coupled because
`V = F⁷`, `Sym²(F⁷) = 28 ≠ 49 = F⁷ ⊗ F⁷`.

**The decomposition that names the swan's hiding place (Auditor-verified, closes exact).**

    V ⊗ V  =  Sym²V  ⊕  Λ²V,        dim: (pv−1)² = (pv−1)pv/2  +  (pv−1)(pv−2)/2.

*[byte-exact, 11 cells: e.g. (4,18)c3: 64 = 36 + 28; (4,8)c2: 49 = 28 + 21]*

The coupling keeps `Sym²V`; the complementary piece is `Λ²V` (the alternating square).
**`Λ²V` is exactly where characteristic `p` carries torsion** — `Sym²` and `Λ²` behave
differently in char 2 (they overlap on the diagonal), and the splitting `V⊗V = Sym² ⊕ Λ²`
is not clean in small characteristic. This is the first point in the campaign where **the
*why* of T1-coupled and the *location of a possible swan* point at the same object**: the
fine functorial layer `Sym²/Λ²` that no rank count could see — precisely the prediction of
**F-HF-32** (torsion irreducible to a single block, invisible to cheap proxies).

**[OPEN — the nail, now in algebraic form]** Prove that the rho-action **realizes `Sym²V`,
not `V⊗V`**, on the class layer — i.e. *why rho symmetrizes*. This is an algebra-of-functors
statement, no longer a counting question. **Auditor directive for the chase: track `Λ²V`
in parallel with `Sym²V`.** The swan, if it exists, lives in the `Λ²` that the coupling
discards and that char-`p` makes torsion-sensitive — not in the `Sym²` that survives. Do
not chase `Sym²` alone.

**Provenance.** Functorial identification measured by the Constructor (11 cells) and
independently re-verified by the Auditor with sympy (`Sym²`, `free = V⊗V`, and the
`V⊗V = Sym² ⊕ Λ²` closure all confirmed). Not a theorem: the realization of `Sym²` by rho
is the remaining proof. Identification: FIRM and signed. Mechanism: OPEN, named, with the
correct tool (functor algebra) in hand and `Λ²` flagged as the swan-bearing complement.

```python
# §7 reproduce (Auditor-verifiable)
def tensor(n): return n*n
def sym2(n):   return n*(n+1)//2
def alt2(n):   return n*(n-1)//2
def vpv(m,p):
    v=0;mm=m
    while mm%p==0: mm//=p;v+=1
    return v,p**v
def S_of(m,pv): return [k for k in range(m) if k%pv!=pv-1]
def free(m,pv): return len(S_of(m,pv))**2
def triangle(m,pv):
    S=S_of(m,pv); return sum(1 for a in S for b in S if (b%pv)<=(a%pv))
for (m,p) in [(6,3),(8,2),(12,2),(6,2),(18,3),(9,3),(45,3),(25,5),(14,7),(16,2),(21,3)]:
    v,pv=vpv(m,p); nc=pv-1; c=m//pv
    assert free(m,pv)     == tensor(nc)*c*c     # free = dim(V x V) * c^2
    assert triangle(m,pv) == sym2(nc)*c*c       # coupled = dim(Sym^2 V) * c^2
    assert sym2(nc)+alt2(nc) == tensor(nc)      # V x V = Sym^2 + Alt^2 closes
print("FUNCTORIAL IDENTIFICATION OK — coupled = Sym^2(V)*c^2, V(x)V = Sym^2 + Alt^2")
```

---

## 8. THREAD B CLOSED — the swan is NOT in the class-layer Λ² (Auditor-verified, Smith form, 9 cells)

**[FIRM, measured by Smith normal form over Z — NOT by dimension]** The Auditor directive of
this turn was to test whether characteristic `p` bites the `Λ²V` complement that the coupling
(`Sym²V`) discards — the predicted hiding place of a swan per F-HF-32. Measured, like-for-like:

### 8.1 The result

The symmetrization operator in play is the **swap `τ` of the two pair-variables** — not
ρ-multiplication. Fermat's ρ sets *which classes are live* (the signature `S` → `nc = pv−1`
classes); the symmetrization is the pure swap on those `nc` classes. There is **no separate
"Fermat operator"**: interchanging the two A-variables *is* `τ`.

Smith normal form of `(I + τ)` over `Z`, on Fermat's `nc` live classes, divisors divisible by
the cell's own `p`:

| char | result | cells |
|---|---|---|
| `p = 2` | exactly `nc = pv−1` divisors divisible by 2 → torsion `(Z/2)^{nc}` | (4,6)c2→1, (4,12)c2→3, (4,8)c2→7, (4,16)c2→15, (4,20)c2→3 |
| `p` odd (3,5,7) | zero divisors divisible by `p` → no `p`-torsion | (4,6)c3, (4,9)c3, (4,18)c3, (4,25)c5, (4,50)c5, (4,14)c7 |

**Fermat = generic, like-for-like.** The `(Z/2)^{pv−1}` torsion that char 2 puts in the
`Sym²/Λ²` layer is the **universal torsion of the swap** on `nc` classes; Fermat inherits it
exactly — adds and removes not a single `2`.

### 8.2 The verdict, stated with the Auditor's exact scope

**THE CLASS LAYER IS DISCARDED as a swan site — NOT "Fermat is torsion-free".** This turn
measured *one layer* (the within-pair class layer `V = F^{pv−1}`) and found its char-2 torsion
is the generic swap torsion, with no Fermat-specific deviation. The swan is not here. Other
layers (the full block, the B-factor, the cross-pair structure, the n=4 monster) are **not**
addressed by this measurement and remain open. The campaign's swan hunt is narrowed by one
concrete site closed with data, not concluded.

### 8.3 THE THREE SELF-CATCHES (the lesson — graveyard, do not repeat)

Three constructions were built, measured, and killed by self-audit before reaching a verdict.
Each is a trap for the next Claude:

1. **Dimension argument (the one the Auditor caught, F-HF-32 violation).** "`dim(Sym²)` over
   `F_p` = over `Q` (delta 0) ⟹ no Fermat torsion." **FALSE.** Torsion lives in the cokernel /
   the Smith `2`'s / the rank drop, **never** in the dimension of a subspace. A map with known
   `Z/2` torsion has equal dimension where you'd look naively but drops rank where it matters.
   **NEW PERMANENT RULE: torsion is measured by Smith form / rank drop, NEVER by `dim` over
   `F_p` vs `Q`.** `dim` equal does not imply torsion-free — that is exactly F-HF-32.

2. **Global ρ-multiplication operator.** Building ρ-mult on all of `Z[x,y]/(x^m−1,y^m−1)` mixes
   the A-factor, B-factor, and class layer. Its cokernel gives **one large divisor** (15, 28,
   36, 66…) = the global rank, not the class-layer torsion. **Rule: if a cokernel gives a single
   large divisor, you mixed layers — catch it and rebuild, do not compare.**

3. **`ρ`-multiplication ≠ symmetrization.** Comparing `coker(ρ-mult)` to `coker(I+τ)` is
   pears-to-apples: ρ-multiplication and the swap-symmetrization are different operators. The
   symmetrization in play is the **swap of the two pair-variables**, which is `τ` itself; ρ only
   selects the live classes. There is no distinct "Fermat symmetrizer" to compare.

These three are the lesson of the turn: **measure torsion by Smith/rank; isolate the layer
before building the operator; the symmetrization is the swap, ρ sets the classes.**

### 8.4 Status after §8

- **CLOSED:** the class-layer `Λ²` as a swan site — Fermat inherits the generic swap torsion
  `(Z/2)^{pv−1}`, verified by Smith form in 9 cells, like-for-like.
- **NEW RULE (permanent):** torsion ⟹ Smith form / rank drop, never `dim(F_p)` vs `dim(Q)`.
- **OPEN, unchanged:** the swan in other layers; Thread A (prove ρ realizes `Sym²V`, not `V⊗V`)
  — the next stone, pen-and-paper, now with the class-layer cleared.
