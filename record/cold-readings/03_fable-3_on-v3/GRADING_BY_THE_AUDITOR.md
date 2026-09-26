# Fable 3 — grading by the auditor (Grepy el Auditor, 2026-09-24)

**Report:** `REPORT.md`, md5 `4462846e0672fcb41bcdbd5523b91dd0`, 226 lines; `checks/` with 16 files (code, logs, the [DS] arXiv v3 LaTeX source). Copied from `~/Desktop/LECTORES_EN_FRIO/FABLE_3/`; origin intact.

**Verdict of the reader:** HOLDS. No FATAL, no GAP, no ERROR in the paper. Seven findings, six PRESENTATION and one ERROR inside [DS] that the paper does not use.

**Grade: HIGH MARK — the most valuable of the three reads so far**, because it opened the one leg nobody had opened: the proofs inside [DS].

## What I checked
- Read the report whole.
- The logs end cleanly and agree with the report's numbers: P1/(5.1) 0 failures up to (27,4); P2 0 same-parity failures (the 852 are mixed-parity pairs, outside the hypothesis of Prop 5.6); P3 logs present for (9,4), (27,2), (27,3), (81,2).
- By hand:
  - F-1 counterexample (`f = 2·id`) is correct;
  - the fix (it holds when `f` is onto, as in [DS]'s use) is correct;
  - F-3 (n = 0) is correct: H_0 of m points has rank m, the Pham cycle only reaches the augmentation-zero part;
  - the new p ≥ 5 numbers: `Q_1(q) = 3(q−1)(q−2)` gives 6, 36, 90, 1950 at q = 3, 5, 7, 27 ✓;
  - the Picard line (F-5): 7 for the cubic surface, 20 for the Fermat quartic ✓.
- Its equality sketch (§5(e)): the direction is right. In F_q[y]/(y_i^{q−1}−1), a product of fields, an ideal is determined by its support, so dim = |support|. The initial forms of (generators) + (y^{q−1}−1) contain (generators) + (y^{q−1}), which gives dim V_Λ ≤ |support| by colength. **The support = Z_Λ step (Gale–Ryser) is NOT audited.** Grade: plausible sketch, candidate theorem, must be audited before v4 prints it.

## Budget note (against the reader)
- Its k = 6 run: the report says **1.45 GB**; the log says a **peak footprint of 1 748 518 448 bytes = 1.75 GB**. Both are above its 1 GB guideline and the 1.2 GB house cap, and the self-report is off by 0.3 GB.
- No process was left running (checked with `ps`).
- It does not change any mathematics.

## What it adds that the other two did not
1. The external dependency [DS] Theorem 1.1(a) holds for every m ≥ 3 and even n ≥ 2. It is an isomorphism of groups, and the sign structure is confirmed independently by Picard numbers.
2. Two slips inside [DS] (a false general lemma in §4.2, a false «=» of rings in §1). Neither touches part (a).
3. k = 0 is not covered by [DS]'s proof but is trivial: one sentence in v4.
4. A self-contained half-page proof of 1.1(a) modulo Pham and Thm 2.2, for v4.
5. Theorem 5.3 holds over any field and any odd q. With a rewritten §2 (Frobenius + 2 invertible), **m = p^v for every odd prime p** is a corollary. This is the third independent reader to say so.
6. A sketch of equality `dim V_Λ = |Z_Λ|`, to be audited.
7. Composite odd m: a character decomposition into subfamilies `K_χ`, which needs a coloured version of Theorem 5.3. m = 2^v needs a new method.
