# Grading by the auditor — cold reading 12 (internal reader, on v10 and on the supplementary note)

Auditor: Grepy. Date: 1 October 2026. Report graded: `COLD_REPORT_V10.md` (md5 `93365bb64dbdec86fb2d4d4adcbbaa89`).

**Grade: HIGHEST MARK.** The reader re-derived every new statement by hand, wrote its own engines, read the sources that the paper quotes, and found things that the author had missed: a gap, a false sentence, an under-claim that is a new corollary, and a hypothesis («`F` infinite») that turns out to be necessary. Verdict of the reader: **HOLDS** — FATAL 0, GAP 1, ERROR 3, PRESENTATION 13. Every finding is accepted. None changes a statement of the Main Theorem, of Theorems A, B, C or of Corollaries H and W.

The texts read by the reader are kept: the paper as `texts-as-read/PAPER_OFICIAL_v10_as_read_by_the_cold_reader.md` (it differs from what the reader read only in the sentence of §12.6 about this reading), and the note as `texts-as-read/THE_REGULAR_CENTRALIZER_NOTE_v1_before_cold_fixes.md`. The fixes are applied by `fixes/regla295_coldfix_v10.py` (paper) and `fixes/regla295_coldfix_note.py` (note); every replacement asserts its anchor.

| # | Finding | Grade | What was done |
|---|---|---|---|
| G1 | Remark 8.7(3) / note §5: «`≤` over every field, by the argument of Proposition 9.1» does not cover characteristic 2 | **accepted** (the auditor had found it independently while the reader worked) | Replaced by: characteristic `≠ 2`, Proposition 8.5(iii) + Theorem A; characteristic 2, the space is spanned by integer vectors, so its dimension is at most the one over `Q`. The colengths `19` and `21` are quoted. |
| E1 | The parity argument about determinants in the sketch (Remark 8.7(2), note §4.3) is false as written | **accepted** | Replaced by the reader's argument: `O_r = {±1} × SO_r`, and `−1` acts trivially on a tensor power of even degree. |
| E2 | [Gin, §4] is stated for semisimple groups, not reductive | **accepted**; checked in the source (line 649) | «semisimple» in Remark 8.4(2) and in the note §2.1. |
| E3 | Note: Theorem B is the algebraic form only for `m = p^v`; the row of the table was looser than the paper | **accepted** | Summary item 3, §4.2 and the row of the table rewritten as proposed. |
| P1 | Under-claim: `dim F[L]/K_μ(L) = N_μ(n)` holds for every `μ` | **accepted**; the auditor re-derived the argument, including the reachability of every `μ` (smallest part lowered by one: a new-class child or the raise child `a = q − ℓ`) | New §A.9 with **Corollary A.17**; Remark 8.4(4), §1.8, §14 and the note (§2.3(c), §7, §8) updated. The paper says that the reader pointed it out. |
| P2 | «PLACEHOLDER» in §12.6 | **accepted** | Replaced by the record of this reading. |
| P3 | Three versions called «the present one» in §1.8 | **accepted** | v8 and v9 in the past tense. Two more stale «previous version» (§1.8, §5.9), found by the auditor while fixing this, now name the version. |
| P4 | «`F` infinite» dropped in the abstract, in Remark 8.7(1) and in the note; false for the points over a finite field | **accepted**; the numbers `9, 27, 19` against `7, 19, 13` were recomputed by the auditor with separate code (`engines/theorem-a-kostant/regla_centralizador_2026-10-01/finite_field_caveat.py`; over `F_5` the two numbers agree at `(3,3)` and `(5,3)`) | Hypothesis restored in every place; Remark 8.4(1) and remark (3) of §1 of the note now say that it cannot be dropped, with the numbers. |
| P5 | Corollary 8.6(ii): the statement says «modulo [BRR]», the proof also used [Kos] | **accepted, second option** | [Kos] removed from the proof: in characteristic 0 the dimension is the rank of a finitely generated abelian group, at most the dimension modulo 3, and (i) gives the lower bound. The same remark added to Remark 8.4(3) and (6) and to the note. The credit to Kostant in characteristic 0 is kept. |
| P6 | Remark 8.7(3): «for `char F ≠ 2`»; «by the sketch (2)» | **accepted** | Both. |
| P7 | Remark 8.7(1): the equivalence with Conjecture 1.2 is with the first half of the statement, for `k ≥ 1`, through Theorem 0 | **accepted** | As proposed. |
| P8 | Clashes of symbols in §8 | **accepted** | The centralizer is `𝒵`; the rank is `h` (as in §1.9 and Appendix A); for even `q` the rank is written `q/2`; the auxiliary `h := 1 + f` is `φ`; the space of Corollary 8.6 is `ℳ`. For `G`, `T`, `W`, `K`, `ℓ`, `u` — the notation of the sources — Remark 8.4 opens with a sentence saying so. A row for §8 added to §1.9. The build script asserts that no `Z` or `m` of the old kind is left in §8. In the note, `𝒵` too. |
| P9 | `f(0) = ±1`; type `A_1` has no bad prime | **accepted** | Both, in the paper and in the note; for `Sp_q`, «every odd prime is good». |
| P10 | Kostant's surjectivity gives `W^{G^e}` | **accepted** | Remark 8.7(2) now defines `G` and `W` and says why `W^{G^e} = W^{𝔤^e}` here; the note agrees. |
| P11 | References: the «only» annotations; the title of [BRR]; [Ric] | **accepted**; the arXiv listings were opened: the title of [BRR] v2 has no «, I» (v1 had it; «minor change of title»), and [Ric] is v4, 19 May 2015 | Annotations list the sections; title corrected; [Ric] dated and moved; «we did not find the count in it». |
| P12 | Note, Theorem 7.1: ties; Lemma A.3; «do not increase»; «for every `n`» | **accepted** | Definition, statement and proof rewritten. |
| P13 | Note: four small inconsistencies with the paper | **accepted** | (a) the cells with odd `n` are listed (the auditor checked the eight characteristic-0 values against a direct count of walks); (b) the account of §1.8 of the paper; (c) hypotheses stated, duality removed; (d) «modulo [BRR]». |

**What the reader did not check** (its own list): [Kos], [KLT], [Bry], [Lus], [Gra], [Jan], [Mat], [DCP] in the original; the inputs of [BRR, Proposition 2.12]; the proofs of Theorem B, of Appendix A and of Propositions 2.5, 2.6 and 9.1 (covered by readings 1–11); the computed claims without logs in its folder; the renderings. The paper says so in §12.6.

**After the fixes.** The fixes use the texts and the arguments proposed by the reader. The auditor then re-read every changed passage against the report (the build scripts assert every anchor), and recomputed the numbers that entered the text (the finite-field caveat; the odd-`n` cells of the note). A second cold pass by the same reader was not possible: its session had reached its limit.

**Own errors of the reader, declared by it:** one run stopped by the memory guard at 1.30 GB (not rerun), and one run of 641 MB without a written estimate.
