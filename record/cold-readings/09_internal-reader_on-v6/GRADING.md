# Grading of the internal cold reader on v6 (auditor, 2026-09-25)
**HIGH MARK.**
- Verdict HOLDS.
  - The reader re-derived by hand §6 (Lemmas 6.1–6.8, Proposition 6.5), §7 (all nine cases of Proposition 7.4, Proposition 7.5 α/β/γ, Theorem 7.6, Corollary 7.8), §10 (Lemma 10.4, (H4), Lemma 10.1) and §11 (the proof of W(ii)).
  - It recomputed with its own code:
    - Lemma 6.8 at 12 sums;
    - Proposition 6.5 in Singular at `(2,21)` over four colourings;
    - Theorem C over `F_p` and in characteristic 0;
    - Proposition 7.4 on 9 712 comparable pairs;
    - Theorem 7.6 on 52 down-sets;
    - `|𝔅|` at the 17 cells;
    - Fact 9.2.
- Findings: 0 FATAL, 0 GAP, 0 mathematical ERROR, 1 citation ERROR, 18 PRESENTATION.
- **The citation ERROR was checked by the auditor and does NOT stand.** arXiv:2608.18134 exists, and its page says «Submitted on 28 July 2026 (Version 1)». The reference is correct as printed.
- Near-gap 1 (`k ≥ 1`, and the case `a = 0` of Corollary 7.8): fixed.
- Item 7, the `N_1(c)` definition, is a real point. As printed, the definition allowed `w_0 = 1` when `|𝒞_1|` is odd, and then Lemma 6.6's claim «both sides are 0» would fail. Fixed: the multiset is now required to lie in `μ_q ∖ {1}`.
- AMV Table 1 (item 14) was checked against the original (`FUENTES_ORIGINALES_AMV_2026-09-25`). The surface rows `m = 5, 7, 11, 13` agree with the Watermark/Double Ladder closed forms: `5^10·25^1`; `7^38·49^5`; `11^158·121^17`; `13^254·169^23`. The claim is kept and made precise.
- Item 18 (process narrative): trimmed in §12.6. The acknowledgements are kept by Rafa's order (AI disclosure and the repository sentence).
- All fixes are in `corpus4/herramientas_grepy/regla284_coldfix.py`, applied as the final pass of the build and verified in the pdf text.
