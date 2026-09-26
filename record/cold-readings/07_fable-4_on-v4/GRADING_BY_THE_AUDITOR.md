# Grading of Fable 4 on v4 — Grepy el Auditor, 2026-09-25 (MISIÓN 100)

**Mark: HIGHEST of the series.** Verdict «HOLDS AS FAR AS I CAN CHECK»: 0 FATAL, 0 GAP, 1 ERROR (wording), 7 PRESENTATION.

What it got right:
- **Appendix B**, line by line against the [DS] LaTeX source. It found that footnote 2 repairs a real slip in DS §4.2, with a minimal counterexample (`f = 2·`).
- **T59-1, the planted imprecision (item 43).**
  - It found it with the correct diagnosis and the correct fix (`in_<(I) ⊇ in_<(I')`, equivalently `gr(I) ⊇ I'`).
  - It found the same phrase twice in §7.1, which I had not listed.
  - It classified it correctly as off the critical path.
- **No hidden 3.** It checked `p = 5, 7, 11, 13` and computed integer Smith forms of the literal [DS] ring at five cells.
- **Theorem 5.3:** all seven cases of P2 and the three constructions of P3 re-derived by hand, plus 491 260 machine tests.
- **It independently found both strengthenings** the auditor proved in MISIÓN 99:
  - (1) equality over every field, with Z-freeness, confirmed by integer Smith forms;
  - (2) the integral Hodge corollary.
  - Its caution is correct: claim prime `m` only, not `p^v`. This matches my Hodge-character count, which gives extra characters at `m = 9, 25, 27, 81`.
- Presentation items B-1, B-2, B-3, P-1, P-2, P-3, P-4: all applied in v5.

Where it fell short:
- **One cap violation, self-reported:** `11_Zform`, 1.32 GB against a wrong estimate.
- **Two runs did not conclude:** P3 membership at `(9,4)`, `(11,3)`; and cell `(4,5)` was killed.

Copied verbatim from `~/Desktop/LECTORES_EN_FRIO/FABLE_4/` (REPORT md5 `07a1cae5…`) with `checks/` (49 files).
