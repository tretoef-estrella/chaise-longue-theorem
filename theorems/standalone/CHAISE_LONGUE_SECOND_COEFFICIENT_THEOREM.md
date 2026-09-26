> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026-07-26
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE SECOND COEFFICIENT THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_SECOND_COEFFICIENT_THEOREM.md
>
> **Status, as written in the document:** not stated in the document itself
>
> **Later audit:** The campaign's later records mention this document next to a refutation, retraction, circularity or supersession (3 lines). Search its name in [the Cemetery](../../archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md) before relying on it.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE SECOND COEFFICIENT THEOREM
## `deg C = |[q^k] P_k(q)|` — the defect module's degree is a coefficient of the target polynomial
### Chaise Longue campaign — standalone deposit v1
**Author:** Lacassagne (constructor) · **Commissioned and audited by:** Orfila (auditor, mission #26) · **Architect:** Rafa · 26 Jul 2026

---

## ABSTRACT

Let `n = 2k+2`, `S = K[x_1,…,x_n]`, `char K ≠ 2`, let `L_J` be the `(2k+1)!!` sheets of the matching
arrangement, `E = ⋂_J I_J`, and let

>   `C := coker( S/E ↪ ⊕_J S/I_J )`

be the arrangement defect module — the module in which the obstruction to `GAP 3` condition (I)
lives (`DEFECT_TOR_LOCALIZATION_THEOREM_v1`). Let `P_k(q) = #(⋃_J L_J)(F_q)` be the point-count
polynomial of the conjecture.

> ### **THEOREM.** For every `k`:
> ### `P_k(q) = (2k+1)!!·q^{k+1} − (deg C)·q^k + O(q^{k−1})`,
> ### that is **`deg C = |[q^k] P_k(q)|`, the absolute value of the second coefficient of `P_k`.**

Equivalently, combining with `DEFECT_DEGREE_THEOREM_v1` (`deg C = (2k+1)!!·k(k+1)/2`):

>   `[q^k] P_k(q) = −(2k+1)!!·k(k+1)/2`.

> ### **⚠️ SCOPE CORRECTION (§3).** `deg C` is **NOT** the Hilbert–Kunz multiplicity of `S/E`.
> ### `e_HK(S/E) = (2k+1)!!` is the **leading** coefficient. The two agree **only at `k = 1`**,
> ### the degenerate cell. The contrary claim (`EL FRENTE v95`) is retracted here with data.

---

## 1 · THE PROOF

By inclusion–exclusion over the sheets,

>   `P_k(q) = Σ_{∅≠T⊆{J}} (−1)^{|T|+1} q^{dim F_T}`,   `F_T = ⋂_{J∈T} L_J`.

Each `L_J` has dimension `k+1`, and there are `(2k+1)!!` of them, giving the leading term
`(2k+1)!!·q^{k+1}`. The coefficient of `q^k` collects every subset `T` whose flat has dimension
exactly `k`.

**LEMMA (pairs).** For `J ≠ J'` sharing exactly `s` edges, the union graph is `s` isolated edges
plus even cycles, all bipartite, so by the `STRATUM_CLASSIFICATION_THEOREM`
`dim(L_J ∩ L_{J'}) = s + #cycles ≤ (k+1+s)/2 ≤ k`, **with equality iff `s = k−1` and the four
uncovered vertices form a single 4-cycle** — a *pencil* pair. ∎

**LEMMA (no triples reach dimension `k`) — this is the load-bearing step.** Suppose `|T| ≥ 3` and
`dim F_T = k`. Then every pair in `T` already attains `k`, so by the pair lemma all pairs are
pencils sharing the **same** `k−1` edges; the three matchings therefore differ only on the four
remaining vertices, and there are exactly **three** perfect matchings of four vertices. Their union
is `K_4`, which is **not bipartite**. By the `STRATUM_CLASSIFICATION_THEOREM` a non-bipartite
component contributes dimension `0`, so that component collapses and
`dim F_T ≤ k−1 < k`, a contradiction. ∎

Hence the `q^k` coefficient receives contributions from **pairs only**, each with sign
`(−1)^{2+1} = −1`, and there is one contribution per pencil pair:

>   `[q^k] P_k(q) = −#{pencil pairs} = −deg C`,

the last equality being `DEFECT_DEGREE_THEOREM_v1`. ∎

---

## 2 · VERIFICATION (gates declared before reading)

Reproducer: `second_coefficient.py`. Full inclusion–exclusion over all non-empty subsets of sheets,
exact rational rank computation for every flat dimension.

| `k` | `P_k(q)` computed | leading | `= (2k+1)!!` | second | `= −deg C` | `P_k(3)` | sealed gate |
|---|---|---|---|---|---|---|---|
| 1 | `3q² − 3q + 1` | 3 | ✓ (3) | −3 | ✓ (3) | **19** | 19 ✓ |
| 2 | `15q³ − 45q² + 55q − 24` | 15 | ✓ (15) | −45 | ✓ (45) | **141** | 141 ✓ |

Both cells reproduce the campaign's **sealed** anchors `P_1(3) = 19` and `P_2(3) = 141`. The
theorem itself is proved for all `k`; the table is a check, not the evidence.

---

## 3 · THE RETRACTION THIS THEOREM REPLACES

`EL FRENTE v95` claimed, as its headline, that `deg C` **is** the Hilbert–Kunz multiplicity of the
arrangement, on the strength of `deg C = (2k+1)!!·k(k+1)/2` matching the gates `3, 45, 630` of the
deposited leading law `R9`.

**That reading is false.** `e_HK(S/E)` is the **leading** coefficient of `P_k`, namely `(2k+1)!!`;
`deg C` is the **second**. They coincide only at `k = 1`, precisely where leading and second are not
distinguishable by the gate values available. The numerical agreement with `R9` is real, but `R9`
concerns a different object (`Q`), and the inference from three matching integers to a structural
identification was not warranted.

*This is recorded because the campaign treats the route to a result as part of its provenance: the
correct statement — `deg C` is a **coefficient of the target polynomial**, for a **proved geometric
reason** — is strictly stronger than the false one, and was found by the constructor executing the
auditor's own pre-registered death criterion against the auditor's headline.*

---

## 4 · SCOPE — WHAT THIS THEOREM DOES *NOT* CLAIM

1. **It does not prove condition (I), nor `GAP 3`, nor any part of the surjectivity.** `G` remains `4`.
2. It says nothing about coefficients of `P_k` below `q^k`; those receive triples and higher, and
   are not computed here.
3. It does not identify `deg C` with any Hilbert–Kunz multiplicity (§3).
4. `char K ≠ 2` is inherited from the `STRATUM_CLASSIFICATION_THEOREM` and is used essentially.
5. The two verification cells are `k = 1, 2`; the theorem is proved for all `k`.

---

## 5 · PROVENANCE

- The defect module `C` and the localization of (I) in it: Orfila, `DEFECT_TOR_LOCALIZATION_THEOREM_v1`.
- `deg C = (2k+1)!!·k(k+1)/2` and the pencil census: Lacassagne, `DEFECT_DEGREE_THEOREM_v1`.
- `dim F_G = #{bipartite components}`, the step that kills the triples: Lacassagne,
  `STRATUM_CLASSIFICATION_THEOREM_v1`.
- Theorem, proof and verification: Lacassagne, mission #26. Audited and reproduced by Orfila.
- Route: the theorem was found while executing the death criterion attached to the auditor's
  `e_HK` claim. Testing the claim instead of building on it refuted it and produced the correct
  and stronger identification in its place.

---

**Every statement carries its grade inline. `GAP 3` remains open and the magic word is not spoken.**
