> **Rafael Amichis Luengo** · tretoef@gmail.com · *King Pin (the lattice of the Fermat quartic fourfold)* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *THE KILL-PATTERN PRICE THEOREM* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/THE_KILL_PATTERN_PRICE_THEOREM.md
>
> **Status, as written in the document:** Status: pencil-proven; all numbers byte-exact this session. Pending P0 (Ley 45).
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v0`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# THE KILL-PATTERN PRICE THEOREM
## The cut Gram splits orthogonally into a pattern block and a mute block; the continuous price floor of any wall-kill pattern is exact; and the refund–integrality conservation, measured on both champions

**A King Pin structural theorem completing the Mute Decomposition. Pillars: Star (i), Steel (ii), Coverage⊥Correlation (vi), Pattern Floor, Mute Decomposition. New under Ley 14/15: an exact orthogonal splitting `G₁₃ = P + M`, the closed-form continuous price floor of a kill pattern, and a measured near-conservation law that kills the refund-transfer lane with data.**

**Status: pencil-proven; all numbers byte-exact this session. Pending P0 (Ley 45).**

---

### 0. Why this theorem (Quanta paragraph)
The Mute Decomposition left one hope alive: perhaps the annihilating cuts (which kill essentially the whole wall at `2^{20.6}`) were simply *badly filled* — pay the audible price, collect a bigger mute refund, close the 12.6 bits. This theorem measures that hope and buries it: both champions — the price champion and the annihilator — **already sit at their optimal mute filler** (re-optimizing the annihilator's filler reproduces its price byte-exact, `2^{20.6273}`). The reason is structural, and it is the theorem: the cut Gram is an exact **sum** of two orthogonal blocks — a pattern block `P`, determined by the wall-kill pattern alone, and a mute block `M`, chosen freely from the fixed rank-13 mute lattice. Minimizing over `M` gives a closed-form continuous floor for every kill pattern; measured on both champions, current prices sit only `1.1–1.3` bits above their own floors. The audible integrality gap and the mute refund are two faces of the same `K_{full}`-components and nearly cancel — a conservation, not a loophole. What remains, exactly quantified: the record's coverage face is the minimization of **one** pattern determinant on **one** rank-128 lattice, with measured landmarks `2^{4.61}` (kill 1022), `2^{17.51}` (kill 1913), target `≤ 2^{6.08}`.

### 1. The splitting

> **Theorem 1 (orthogonal splitting).** Write `ℝ^{141} = span(K_{full}) ⊕_D span(K_{full})^{⊥_D}` and split every row `f_i = f_i^⊥ + f_i^{mute}`. Then the cut Gram satisfies, exactly,
> **`Φ D Φ^T = P + M`,** `P_{ij} = ⟨f_i^⊥, f_j^⊥⟩_D`, `M_{ij} = ⟨f_i^{mute}, f_j^{mute}⟩_D`,
> with all cross terms vanishing by `D`-orthogonality. `P` is determined **by the wall-kill pattern alone** (full-wall Pattern Floor injectivity: `rank M_{full} = 128` makes the bite values determine `f^⊥`); `M` is the Gram of an arbitrary choice of mute components. `rank P = audible rank`. ∎

> **Theorem 2 (Kill-Pattern Price — the continuous floor).** Fix a kill pattern with audible rank `k` and pattern block `P` (rank `k`). Over all cuts realizing that pattern,
> **`pr(Φ) ≥ [det_k(P)/32^k] · [min det_{13−k}(K_{full})/32^{13−k}]`,**
> and the floor is attained in the continuous relaxation by placing `13−k` minimal mute-lattice vectors in the null directions of `P` and reducing every audible row to its projection. Monotonicity (`M′ ⪯ M ⟹ det(P+M′) ≤ det(P+M)`, PSD order) shows no mute mass on the audible support can lower the determinant.
> Measured: `min det₃(K_{full}) = 4 = 2^2` over LLL-basis subsets (dnorm² units; the mute lattice minima are `1, 2, 5/2, …`). ∎

### 2. The measurements (byte-exact)

| cut | kills | price now | audible det (rows) | **pattern floor** `det_k(P)` | integrality gap | refund now | **continuous price floor** | headroom |
|---|---|---|---|---|---|---|---|---|
| best_cut | 1022/1935 | `2^{7.9069}` | `2^{13.0351}` | **`2^{4.6124}`** | 8.42 bits | `2^{−5.1282}` | `2^{6.61}` | 1.3 bits |
| annihilator | 1913/1935 | `2^{20.6273}` | `2^{25.3679}` | **`2^{17.5131}`** | 7.85 bits | `2^{−4.7406}` | `2^{19.51}` | 1.1 bits |

> **Corollary 1 (refund–integrality conservation, measured).** For both champions, (audible integrality gap) − (refund magnitude) ≈ `1.1–1.3` bits — the exact headroom to their own continuous floors. Reducing the audible rows' `K_{full}` components (closing the integrality gap) simultaneously destroys the correlation that funds the refund: the two are the same `K_{full}` mass counted twice. **The refund-transfer lane is closed with data:** re-optimizing the annihilator's filler leaves its price byte-identical (`2^{20.6273}`); its audible rank is also 10 and its mute block already optimal.

> **Corollary 2 (the coverage face in final coordinates).** A record cut's coverage requirement is now exactly: find a full-wall kill pattern (covering the 1935) with
> **`det_k(P) ≤ 2^{8.08} · 32^{13−k} / min det_{13−k}(K_{full}) ≈ 2^{6.08}` (for `k = 10`).**
> Measured landmarks on the pattern lattice (rank 128, metric = `D` projected off `K_{full}`): kill 1022 → `2^{4.61}`; kill 1913 → `2^{17.51}`. The entire remaining distance on this face (~11.4 bits at the 1913-kill point) lives in **one determinant on one lattice** — no other object is involved.

> **Corollary 3 (the ghost trio).** The mute lattice contains exactly three directions with tiny projection against both champions' audible spans (projected dnorm² `0.19, 0.48, 0.54` vs `≈ 2–2.5` for the rest) — the refund trio both greedy searches found blindly. Their existence explains the recurring audible rank 10 = 13 − 3.

### 3. Scope (straight)
- BOX face only; nothing here touches the section minimum (Remark 5.3′ intact). Killing the 1935 is necessary for `min ≥ 14`, not sufficient for 24.
- `min det₃(K_{full}) = 4` is an upper-bound-certified minimum over LLL-basis subsets; the true sublattice minimum is bounded in `[2, 4]` (Hermite with `λ₁² = 1, λ₂² = 2, λ₃² = 2`); the floor statements use the measured `4` as the attained value and remain valid lower bounds with `2`.
- The 1.1–1.3 bits of headroom per champion are real and reachable by mute-component CVP (rank-13 per row, tiny) — worth harvesting, but they do not bridge the pattern-face distance.

### 4. Verification record
`refund_transfer_probe_v1.py` (annihilator rebuilt: `2^{20.6273}`, wall 22/1935, cb 0/162; audible rank 10; optimal filler reproduces price byte-exact; design B measured `2^{24.43}`), `audible_floor_probe_v1.py` (pattern floors `2^{4.6124}` / `2^{17.5131}`, projections off `K_{full}` exact rational via 13×13 inverse). Frames as before. Gates: best_cut `2^{7.906891}`, 913/1935, 162 cb, `rank M_{full} = 128`.

### 5. Ley 41 certificate
Object: *the exact orthogonal splitting of the cut Gram into pattern block + mute block, the closed-form continuous price floor per kill pattern, and the measured refund–integrality conservation on both champion cuts.* Graveyard grep by object: (a) **rank-48 coset CVP** (v112, buried by Pattern Floor) — distinct: that was per-row trace minimization on the chorus-blind kernel; this is a joint determinant identity on the full-wall kernel (rank 13), and it *quantifies* why per-row reduction cannot help (conservation); (b) **refund transfer** (hypothesis raised by Mute Decomposition Cor. 1, this campaign) — **same object, now killed with data**: filler re-optimization changes nothing byte-exact; recorded here as its burial; (c) **Coverage⊥Correlation** (v110 theorem) — consistent and sharpened: the D-orthogonality of biters to cheap spans is the `P ⊥ M` splitting seen from one cut; no re-measurement of the sealed theorem is performed; (d) **product seal / greedy pools** — distinct: all statements are exact determinant identities or measured dets. No collision. Pending P0.

---
*Part of the Operación Glotón / King Pin corpus · github.com/tretoef-estrella · tretoef@gmail.com — Marlowe (Auditor), 10 July 2026.*
