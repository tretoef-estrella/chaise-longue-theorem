# Fable 1 (high effort) — grading by Grepy el Auditor, 2026-09-24

**Report:** `REPORT.md` (md5 `87634ad32fcabe83115b0515554b9a64`), written in `~/Desktop/LECTORES_EN_FRIO/FABLE_1/`. The reader did not open ARBOLYAML. Its own code is in `checks/` (14 files).

**Verdict of the reader:** HOLDS AS FAR AS I CAN CHECK. No FATAL, no GAP, seven PRESENTATION items.

**Auditor's grade: HIGH MARK. The report is genuine and deep.**
- It worked from the LaTeX source of [DS] v3.
- It checked all seven cases of P2 by hand, and by machine on every comparable pair up to `m = 16` at `q = 3` and `m = 14` at `q = 9`, with 0 failures.
- It checked P3 slice by slice, with a negative control that fires.
- It reproduced `(2,9) = 5120` with the graded ranks.
- It checked every down-set at `(9;2,3,4)`.
- It checked Theorem A in 75 cells, and the char-2 failure.

## Findings verified by the auditor in the source
1. **§10 / §2 / §8 item 4 count «three results of [DS]», but the rank clause of the Main Theorem (`primitive sublattice of rank Q_k(3^v)+1`) uses [DS, Theorem 1.4].** Confirmed: paper line 42 cites Theorem 1.4, and lines 72, 369, 443 and 475 say «three». **Fix in v4: four inputs, or attribute the rank clause to §1.2.** PRESENTATION, genuine.
2. **The abstract says «for proper subfamilies … false»; it should be «for some proper subfamilies»** (800 of 32 767 fail at `q = 3`, `k = 2`). Confirmed. PRESENTATION, genuine.
3. **Corollary 6.2, «its rank»:** the pronoun refers to the torsion subgroup. Confirmed at line 332. PRESENTATION.
4. **Lemma A.13(ii):** state it for all `s ∈ Z` with (V) built in. PRESENTATION, a clean-up.
5. **The [DS] §5 slip on `d_0`:** the reader re-derived that it is a slip in [DS], not in the paper. Agrees with the paper.
6. **External check of [DS] Remark 4.4:** correct as stated.
7. **«±(unit)»:** cosmetic.

## Does the paper stand?
**Yes, on this reading.** Nothing touches a proof. All seven items are fixable in minutes, and only items 1 and 2 matter.

## Limits of this reading
- The proofs inside [DS] were not re-proved. This is the one external dependency, and it is the same for every reader.
- The row inclusions of Theorem A.12 were checked by hand, not by machine.
- The large cells were not recomputed.

**One reader is not enough; the attacks continue one at a time.**

## Addendum (same day): sections 5 and 6 added by the reader
The report is now 32.8 kB; sections 1–4 are unchanged; the new scripts are `pgeq5.py`, `downset_p.py` and `yfree.py`.

**§5, robustness: eleven requests, all sensible.** Adopted for v4 in `MISIONES_TRAS_BARRIDO/LISTA_DE_PENDIENTES.md`, items 21–23.

**§6, `p ≥ 5`: agrees with the auditor's own gate, by an independent route.**
- Its y-form numbers are identical to `corpus4/regla274_S_primo_p.log`: 36, 400, 4900, 1656, 90, 1860.
- It adds the literal [DS] form over `F_p[t]`: 89, 253, 2725, matching `q^{2k+1} − Q_k(q)`.
- It adds Theorem 5.3 over `F_5` and `F_7` on 16 down-sets.
- **Grade: STRONG SUPPORT, not yet a proof.** The rewrite of §2 with `p` and a line-by-line re-read of §5 are still to be done (item 17: after v3 survives).

**Two corrections by the auditor:**
1. **Its §5.1 item 1 states «Theorem B» as an EQUALITY over any field and any odd `q`.**
   - Its own §6.2 proves only `≥` characteristic-free. The `≤` comes from Prop 2.5, which needs `F = F_p` and `q = p^v`.
   - Tested today with `q` NOT a power of `p` (`corpus4/regla275_S_cualquier_cuerpo.log`): 7 of 7 cells give equality, e.g. `(1, F_3, 5) = 36`, `(2, F_5, 3) = 20`, `(1, F_5, 9) = 168`.
   - So Theorem B is a plausible CONJECTURE. It is not proved; the `≤` half has no argument for general `(F, q)`.
2. **Its composite-`m` plan (§6.6) is recorded as a CANDIDATE, not audited.**
   - It localises at `ζ ∈ μ_{m'}`, reduces to three block statements, and says Theorem A is half of one block.
   - Its 12 block cells and the wrong-characteristic control (30 ≠ 19) are its own.
   - The claims to audit: tensor-product behaviour of the block ideals, and the role of Theorem A in the `≤` / `≥` halves.
   - Also noted: `m = 2^v` is genuinely different (Lemma 2.3 breaks; the count becomes Theorem A's `N_{m−1}(N)`).
