# Grading of Fable 5 on v6 (auditor, 2026-09-25, MISIÓN 106)
**HIGHEST MARK.** 11 section-referees and 6 adversarial verifiers. The report re-derives §6, §7, §10, §11 and the chain.
- Literal recomputation of the degree 15 and 21 fourfolds at both primes. Theorem 7.6 checked at 117 down-sets, 9 of them in new cells. Aoki verified on the page image.
- Memory incidents were declared honestly: five early runs up to 1.45 GB, one run killed at 1.18 GB. All were repeated under the cap.

## Verdicts, finding by finding (checked in the source by the auditor)
- **E1: CONFIRMED, and it is a real upgrade.** Proposition 2.1's inequality uses only Theorem 0(b), which is Appendix B Step 6: the Chinese remainder theorem over a field of characteristic 0.
  - ⟹ **Main Theorem′ (algebraic form):** `Z[G]/(ψ_J)` is free of rank `m^{2k+1} − Q_k(m)` for every odd `m`, with no topology.
  - Corollary 7.8 is unconditional.
  - Gated by the auditor in 12 cells at `k = 1`, including `F_2` (`corpus4/regla285/gate_mainprime.log`, 28 MB).
- **G1: CONFIRMED** (one sentence). [DS] source line 1819 says only «the same continuity argument». The path is now fixed in the subfamily `f_0 = ⋯ = f_s = x^m + y^m`.
- **P1–P29, P31, P33, P35: applied.** Of note:
  - Lemma 7.3′ is renamed 7.2′ and moved before Lemma 7.3 (P8). Its parenthetical is corrected (P10): parity is used in (d1), the cap in the layout and in (e1). Verified in §5.6.
  - «Composite» now reads «not a prime power» (P25).
  - (ii) is new for `k ≥ 2` (P26); Corollary H's ingredient list is corrected (P22).
  - The module bars are corrected against the [DS] source (P18).
  - A table of the nine cases of Prop 7.4 is added (report §5 G).
  - Example 6.11 (`k = 1`, `m = 15`, both primes) is added (report §5 F). Computed by `corpus4/regla285/ejemplo_15.py`: 61/546 and 19/546.
- **P30: not applied.** The claim for even `m` in DS Remark 4.4 is not verified by us, and the restriction is harmless.
- **P32: REFUTED.** The arXiv page reads «Submitted on 28 July 2026 (Version 1)».
- **P34: not applied.** The double meaning is declared in §1.9.
- **Report §5 F (Theorem A as a separate note, §12 as a supplement): NOT applied.** By Rafa's order Theorem A stays; reported to Rafa in CAPITALS.
- **Venue:** the report suggests JMSJ (tier 3), with Math. Ann. or ANT as tier 2.
