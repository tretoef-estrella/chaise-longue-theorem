# regla311 — Grading of the cold reader «Grepy Tinta» on the PRINTED text of version 11

Grepy Mandalay (auditor), 2 October 2026. Object graded: `VIVOS/ATAQUES_Y_REPORTES/V11_PRINTED_1/REPORT_COLD_V11.md` (426 lines, md5 `23274ad9317353a32e6ac487f78d06d0`), with its `checks/` (30 files; copy in `checks_del_lector/`, manifest `MANIFEST_REPORT_md5.txt`). The paper read is `PAPER_OFICIAL_v11.md`, md5 `7b3db0d6…` (the reader's copy has the same md5).

**First line. GRADE: HIGH MARK. The verdict «HOLDS» is ACCEPTED.** The printed text of §7–§10, §12, §13 of version 11 now stands on two readings (its writer and this reader). No error and no gap; 18 presentation notes, all checked against the lines they cite and all accepted for version 12. What stays outside this reading is said in §5 below.

## 1. What was graded, and how
1. The whole report was read (lines 1–426).
2. **Derivation or stamp?** For each row of its table I looked at §3 of the report for an argument in the reader's own words that I could follow and check.
3. **The translation** for even `m` (the failure feared most in the mission).
4. **The controls**: can they fail, and did the reader say when they could not?
5. **The rules**: no agents, its own folder, the watchdog, estimates before runs, predictions sealed before measuring.
6. **Presentation notes** against the lines of the paper.
7. **A sample of its gates re-run** with its own scripts, inside the watchdog (§6).
8. **A cross-check it could not have known about**: Lean piece E7 (§4).

## 2. Derivation or stamp, item by item
Every row is a derivation. The ones I checked line by line against my own cold audit (`regla301`) and the paper:

| Item | The reader's argument | My check | Grade |
|---|---|---|---|
| S2 (translation, even `m`) | Re-read [DS] whole for parity; Proposition 2.1 re-derived (rank over `C`, `p`-torsion); Appendix B Steps 3, 4, 6 with the only places where `m` enters (`0 ≢ 1 mod m`; `p ∤ m`); the count from [DS, Def. 1.3] and from [DS, Rem. 4.4] with `cosh` against `e^x` (`N` even) | Same route as `regla301` §1; the hand cell `(1,4)`: `24·(1/4 + 1/2 + 1/24) = 19` and `3·16 − 36 + 6 + 1 = 19` — right | derivation |
| E2 (Prop. 9.2) | Steps 1–3 written out; `q = 2` and `k = 0` by hand | right; it also states that Step 2 is only an inequality | derivation |
| E3 (Lemma 9.6, `0` as a coordinate) | Colour vectors with product 1; block conditions on disjoint coordinates; the four cases where `0` is in a block matched against the block lemmas | this was a decision of the writer nobody had read; the reader's four matches are the right test | derivation |
| E5 (Cor. 9.12(i)) | «equality per block from the global bound» needs every block count `≥ 1`; it exhibits a tuple for each kind of block | right, and it is the point that could have been a gap | derivation |
| E6 (Example 9.14) | By hand: `6 + 6·2·3 + 19 = 61` and `1 + 12·2 + 6·6 = 61` | arithmetic right | derivation |
| B7 (§7, every `q ≥ 2`) | Each borrowed comparison of §5.6 re-derived; names the two that are NOT borrowed ((d1): parity; (e1): the cap); the field enters only at `C(q−1, r−1)` | agrees with `regla301` §3 | derivation |
| O2 (Lemma 8.4 (D2), `ν_j = 1`) | The count `(r−1−2ℓ) + 1 + 1 = r + 1 − 2ℓ`, «exactly enough: no slack» | right (`r − 1 − 2(ℓ−1) = r + 1 − 2ℓ`); **and now machine-checked, see §4** | derivation |
| O5 (Lemma 8.7) | (a)–(f) in its own words; the sign of (F7) by counting crossings; the case `(0,1)`, `r = 3` expanded by hand | right | derivation |
| O6 (Prop. 8.10) | Seven cases, each with the four things to check (membership, degree, top coefficient, slice) | right; it says honestly (§9) that the membership of each summand was checked by pencil only | derivation |
| O7 (Cor. 8.13) | The five steps; notes that the upper bound needs neither Theorem A nor `char ≠ 2` | right | derivation |
| X2 ((H4′), (H5)) | (H4′) in three lines (`4·second − 2·first`); Aoki read in the original (image and OCR), `n` = dimension, «greater than `n + 2`» | right; (H4′): `N(3) = N(1)`, `N(2)` even | derivation |

No row is a stamp. Two rows are honestly conditional: X1 (Corollary 10.8 «given Theorem A», Appendix A not read) and X3(i) (rests on [DS, §4.6]).

## 3. The controls and the reader's own failures
The reader lists eleven errors of its own (§8 of the report). They are errors of its checks, not of the paper, and it found and declared each one itself:
- Four controls badly conceived or partly vacuous (P1.5 in the cells with `r' = 2`; P2.4: `t ↦ −t` is an automorphism for even `m`; P2b.2: an arithmetic accident, `7 + 36 + 18 = 6 + 36 + 19`; the control clause of P8.1 in 2 of 11 cells). Each is explained. **The explanation of P2.4 is the same finding as the auditor's of 2 October for Lean piece E1** («a control inherited from another piece must be checked to be able to fail»): two independent hands, one fact.
- One sealed number wrong (`64` for `N_{ph}(1,8)`; right value `8 + C(8,2)·4 = 120` — I checked: `q + 2q(q−1)` at `q = 8`).
- Three cells of Lemma 8.7 vacuous (the Pfaffian is zero when `t + 1 > h`).
- Memory estimates off by a factor of two in three runs; one run killed by the watchdog and discarded.
- One run (a text scan) launched before its estimate was written.

The controls that can fail and did fire are enough: a matching removed (`15 < 19`, `45 < 61`, `140 < 141`), the odd-degree sign control (`19 ≠ 6`), (D1) without (D2) (579 of 579), the slice lowered by one, marked patterns with `t = 0` only (`6 < 7`), the generators of one `S` removed in Lemma 8.7 (45 of 45), the signs of `D` removed over `F_3` (`18`, `138`), an even box (`36`, not `37`).

**Rules.** No agent and no workflow (it says a system reminder asked for one and that it refused, as the mission ordered). It wrote only in its folder (the Desktop shows no new folder; nothing in ARBOLYAML was touched). Web: three searches, allowed by §5 of the mission, result pages only, said so. Every run after the first has its estimate written before.

## 4. A cross-check the reader could not know: Lean piece E7
While the reader worked, Aristotle finished piece E7 (`RequestProject/OddLayers/`): `OddLayers.isInterlaced_layerS` is Lemma 8.4 (the layers of an interlaced pair are interlaced pairs), `FS_le_FS_subE` is the inequality behind (D2), `card_ZS_root_odd` and `card_ZS_root_even` are Lemma 8.5. So items O2 of the reader's table (Lemma 8.4 with the delicate case `ν_j = 1`, and Lemma 8.5) have a third, mechanical confirmation, by a different proof of (D2) (through the chain and an exchange claim). State of the Lean check: see §6.

## 5. What this reading does not cover (from §9 of the report; nothing hidden)
- Appendix A (Theorem A) and §4 were not read: Corollary 10.8 is «HOLDS, given Theorem A». Theorem A is not new in version 11; it was read cold in version 10 (cold reading 12).
- The topology (Pham, [DS, Theorem 2.2], (T1), the transport of [DS, §4.6]) is quoted, not re-proved: this is the «modulo» of the Main Theorem.
- (H1)–(H3), (H4), Lemma 12.4, Theorems 5.9, 5.9′, Lemma 6.8, Proposition 6.9, Corollary 7.7: read, not re-derived (unchanged from version 10).
- Proposition 8.10: the membership of each summand in `V_Λ` is checked by pencil only (the slices and their dimensions are checked by machine from the ideals).
- Lemma 8.7 over `Z`: tested over five primes, not over the integers (the pencil proof is over `Z`).
- §14 (the verification record) and §14.8 (Lean) were not examined; the `.pdf` was not opened.

## 6. Sample of the reader's gates re-run by the auditor, and the state of E7
(appended below when the runs end)

## 7. The 18 presentation notes: all accepted for version 12
Checked against the paper, line by line, for the ones that name a defect: 63 (the ideal of leading forms contains `Y` times the ideal of Theorem O, not the ideal itself — right); 970 (`J` is an integer and a matching in one sentence — right); 1008 against 1033 (the header says `k ≥ 1`, `m ≥ 4`; §9.2 needs `k ≥ 0`, `v ≥ 1` — right); 1039/1055/1080 (`N_r` used at `r = 1` — right); 1097 and 1136(2) (the case `0 ∉ 𝒞_{−1}` uses Theorem 8.11 at the second root, not Theorem O — right); 1207 (the two counts are described in §1.6 and §11.1, not in §1.8, which is the note on the history — right: wrong pointer); 1424 (§6 is used at the prime 2 as well — right); 1430 (the torsion-free clause is modulo the topology — right); 555/1089 («since `q − 1` is even» in §6, replaced by a sign in §9 — right); 519 (say that Lemma 6.3 is replaced); 812, 849, 859 (implicit base changes); the overloaded letters (`θ`, `N`, `R`, `σ`, `ζ`, `Ω`, `η`, `ρ`, `S`, `r`). Notes 16–18 say «fine as printed».

Three observations of the reader to carry into version 12 as remarks: (a) some patterns of Definition 8.6 are zero (`t + 1 > h`); (b) for `ℓ = 0` the border of Lemma 8.7 cannot be arbitrary (at `r = 5` the border `{2}` fails) — the paper's Remark (4) is rightly restricted to `ℓ ≥ 1`, and could say why; (c) at an even box the odd-box formula is not the count (`36`, not `37`).

## 8. What this changes, and what it does not
- **Changes:** the item «a cold reading of the PRINTED §8–§10 and §12 by a reader other than the writer», owed before any release, is DONE. The registers may now say that the printed text of version 11 has been read by two.
- **Does not change:** no mathematical grade (Conjecture 1.2 for every `m ≥ 3` was already registered as proved on two readings of the proof; this is the reading of the text). Nothing is released. Still owed before version 12: Lean pieces E8–E20, the literature search for the odd box in the originals (the reader saw result pages only: weak evidence, as it says), the repository folder `record/even-degrees/`, and the 18 notes applied.

---
## 6 (appended, 2 October 2026, 20:00). The sample re-run, and the state of E7

**Six of the reader's gates re-run by the auditor with the reader's own scripts**, inside the watchdog, one after the other, after the Lean build had ended (estimate written before: `corpus4/regla311_tinta/rerun/estimate.txt`; logs in `corpus4/regla311_tinta/rerun/logs/`):

| Gate | What | Ended | Peak | Against the reader's log |
|---|---|---|---|---|
| R1 | the counts (table of §9.1, `|Γ|` from [DS, Def. 1.3], Lemma 9.6 sums, Example 9.14, `|𝔅|`, `|𝔇|`) | `VIGIA-FIN-OK` | 11 MB | 68 lines, 0 differ |
| R2b | the two replacement controls | `VIGIA-FIN-OK` | 5 MB | 5 lines, 0 differ |
| R4 | §7 at an even box (48 down-sets over `F_2`, the roots, `q = 4` over `F_5`) | `VIGIA-FIN-OK` | 30 MB | 37 lines, 0 differ |
| R5 | Lemma 8.12, Corollary 8.13, Corollary 10.8, Theorem 8.15, two controls | `VIGIA-FIN-OK` | 134 MB | 39 lines, 0 differ |
| R6 | Lemma 8.7 (membership, the control, other borders) | `VIGIA-FIN-OK` | 150 MB | 22 lines, 0 differ |
| R8 | the Pfaffian identities behind Proposition 8.10 | `VIGIA-FIN-OK` | 7 MB | 41 lines, 0 differ |

(The comparison leaves out the lines with timings.) The reader's logs are reproducible. Not re-run: R2 (the literal ring, 65 s), R3 (Theorem 8.11 from Definition 8.6), R7 (984 MB: too close to the cap to repeat without need).

**An independent check of the same ground, by the auditor's own code:** the brute force written today for Lean piece E8 (`ARISTOTLE_LEAN/chkE8.py`, 4 491 checks, 0 failures) tests the identities of §8.3 — (i)–(iii), (F1)–(F5), (F7) — with every sign made explicit, from the definition by perfect matchings, on random integer matrices. It shares no code with the reader's R8 and agrees with the reader's item O3 («HOLDS»). The paper prints these signs as «±»; the explicit ones are now in `ARISTOTLE_LEAN/q_pfaffian.md` and can go into version 12 as a remark if wanted.

**Lean E7:** certified at 19:52 (6 of 6 modules built; 15 of 15 results with the standard axioms). So §4 above is no longer conditional: Lemma 8.4 and Lemma 8.5 are machine-checked.

## 9. Summary for the registers
- Cold reading of the printed version 11: **done, HOLDS, high mark.** Two readers now for the printed §7–§10, §12, §13.
- For version 12: 18 presentation notes (one wrong pointer, line 1207), three remarks, and the explicit signs of §8.3.
- Nothing is released; no mathematical grade changed.

— Grepy Mandalay
