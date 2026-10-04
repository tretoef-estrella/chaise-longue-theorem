# Grading of the cold reader's report — «Grepy Skies 2», `REPORT_COLD.md` (2 October 2026)

Auditor and scribe: Grepy Chats. Created empty, with its sections, before reading the report beyond its first section (disk rule). Report under grading: `VIVOS/ATAQUES_Y_REPORTES/GREPY_SKIES_2_COLD_READER/REPORT_COLD.md`, md5 `4ad3eaaffd3457420ec156ca1e378d5d`, 331 lines; original in `~/Desktop/GREPY_SKIES_2_COLD_READER/`. Its first line: **HOLDS**, no ERROR and no GAP in 29 rows.

What grading means here: not whether I agree with the verdict (my own audit, `regla301_auditoria_fria_skies.md`, reached the same one), but **whether the reader really read**: is each HOLDS backed by a derivation of its own or is it a stamp; did it check the translation from the original; did its gates have controls that can fail; what did it not read; did it obey the rules (no agents, its folder only, disk rule, watchdog).

## 0. First line (the grade; filled in last)

**HIGH MARK. The report is a reading, not a stamp. Its verdict HOLDS is accepted.** Every one of the 29 rows carries a derivation written in the reader's own words; I re-did by hand eight of its hand computations and all are right; six of its gates, re-run by me with its own scripts, reproduce its logs line by line; the session transcript shows no agent, no workflow and no access outside its folder. It found five things that my own audit did not. It has the limits it states itself: no new cell in the literal ring, Appendix A of the paper not read, and Theorem C at an even box accepted by re-reading §7 of the paper rather than by a new proof.

**Consequence.** The claim of the first pilot — Conjecture 1.2 of Degtyarev–Shimada for every even degree `m ≥ 4`, hence (with the paper v10) for every degree `m ≥ 3`, in every even dimension — now stands on **two independent cold readings** (the auditor's, `regla301`; the cold reader's, this report), each with its own code, plus six literal cells outside [DS, §5] computed by the auditor. By Rafa's rule it may now be registered as **proved, modulo Pham's theorem and [DS, Theorem 2.2]** (the same external inputs as v10), **and not yet formalised**: the Lean certificate of v10 covers the odd degrees only. What it rests on that neither reader re-proved is in §8.

## 1. The rules: agents, folder, disk rule, watchdog

Checked on the session transcript of the reader (`~/.claude/projects/-Users-rafa-Desktop-GREPY-SKIES-2-COLD-READER/c9c9b208-….jsonl`, 3.2 MB), not on its word:

- **Agents and workflows: none.** Tool calls in the whole session: `Edit` 75, `Bash` 30, `Read` 13, `Write` 12, `WebSearch` 3, `ToolSearch` 1, `SendUserFile` 1. The strings «Agent» and «Workflow» occur only in the tool list that the system attaches to the session. The session was in the «ultracode» mode, which asks for workflows; the reader followed the mission and says so (its §1 and §8.6).
- **Its folder only.** No tool call has a path under `~/Desktop/ARBOLYAML/`, `~/Desktop/GREPY_IS_IN_THE_SKY/` or the memory directory; its memory directory is empty; no file elsewhere on the Desktop was modified in its window.
- **Disk rule.** `REPORT_COLD.md` was written (skeleton) 14 seconds after the first read of the mission and before any reading of the target. The first run of mathematics came 19 minutes later, after the reading; the 75 edits are the verdicts going to disk item by item.
- **Watchdog.** Every run of mathematics is inside `material/vigia.sh` with the log as first argument; 19 logs, all ending `VIGIA-FIN-OK`, peak 954 MB (76 % of the cap), caps never raised. Outside the watchdog: only listings, `grep`, two tally scripts and two text edits by a Python one-liner; it reports them itself (its §8.5).
- **It did not repair and did not extend.** Its presentation notes are notes; no verdict depends on a repair.

Verdict on the rules: **obeyed**. Three memory estimates were exceeded (733 against 700, 954 against 600, 935 against 500), all under the cap, all reported; the second repetition was avoidable, and it says so.

## 2. The translation (T1, T2): did it go to the original?

**Yes.** T1 is argued from the text of [DS] (it lists the five places where a parity of `m` could hide: `η`, the function `e(ν)`, the computation of `ψ'_J`, Claims 4.2–4.3, and Proposition 2.1 of the paper) and adds an external check that I had also used: [DS] themselves compute even cells (Remark 4.4 for `m = 2h`; §5 with `(4, m)`, `3 ≤ m ≤ 12`, and `(6, 4)`). T2 is derived (the bijection `Γ ↔` split `(n+2)`-tuples, the one fixed point `−1` of inversion, the generating function) and then checked by hand against a source the target did not use, the polynomials of [DS, Remark 4.4]. I re-did its three hand values: `n = 4`, `m = 4`: `960 − 1440 + 700 − 100 + 21 = 141`; `m = 6`: `3240 − 3240 + 1050 − 100 + 51 = 1001`; `n = 2`: `3m² − 9m + 7` against `3r² − 3r + 1` at `r = m − 1`. Right. Its note 17 ([DS, Remark 4.4] displays `|Γ|`, not `1 + |Γ|`, also for even `m`) is a real observation about the source.

## 3. The reduction (B2, B.0, B3 with its bullets, B3′, B4, B5): derivation or stamp, item by item

| Item | What the reader wrote | Derivation or stamp | My spot check |
|---|---|---|---|
| B2 | four steps; the graded-piece argument for `dim in(I) = dim I` written out; `(a+b)^{q−1}·b = ab·D_r(a,b)` modulo `b^q` over `F_2`; injection `C_r → B` by `Y` | derivation | `C(q−1,u)` odd by Lucas; the shift `u ↦ w = u − 1`: right |
| B.0 | `W = Z_p[μ_{r'}]`, idempotents in `W[G_{r'}]`, rank over `K̄` by characters, reduction, direction of the inequality | derivation | «reduction can lose rank, never gain»: the direction is the right one |
| B3-a | Lemmas 6.1–6.5, 6.7 redone with `p = 2`; §6.4 flagged as **not** verbatim | derivation | agrees with my `regla301` §1.4 |
| B3-b | §7 of the paper line by line with `q` an arbitrary integer; the one place where the field enters (`C(q−1, r−1) ≠ 0`, case (γ) of Prop. 7.5) | **re-reading, declared as such** | agrees with mine; smallest cells by hand (`q = 2`, `a = 1`: dimension 2) right |
| B3-c | equality for the pair blocks from B.0 and two colourings | derivation | right |
| B3-d, B3-e | block of colour 1 is the conjecture at `(k'−1, 2^v)`; the map `θ` | derivation | `uφ_q(u) = φ_q(u)`, `f_{j+1} = g'f_j`: right |
| B3-f | the count factors, with «split into inverse pairs» stronger than «closed under inversion» at even `q` | derivation | right |
| B3-g | the «iff» and the sizes | derivation | right |
| B3′ | `s_l(s_i + s_l + s_is_l) = s_is_l`; socle; `N_1(c) = 1` | derivation | re-done: right |
| B4 | two self-inverse colours; `u = −t`; block of colour `−1` is the odd box with box `q`; the map `θ` re-proved for every `r ≥ 1` | derivation | `(x_a + x_b)D_r = x_b^r + (−1)^{r−1}x_a^r`: right |
| B5 | assembly, with the ranges `k' ≤ k`, `k'' ≤ k` checked | derivation | right |

No stamp in this part. The one row that is not a proof of its own (B3-b) is labelled as a re-reading in the table of the report itself, and it is the same position my audit took.

## 4. The proof (P1–P9, P6 in seven): derivation or stamp, item by item

| Item | What the reader wrote | Derivation or stamp | My spot check |
|---|---|---|---|
| P1 | (1.1)–(1.4) by the substitution `w = r − 1 − u`; peeling with box `r` | derivation | signs right |
| P2 | Lemma 2.1; the five implications of Lemma 2.3; (D1) with the right down-sets and the right `q`; (D2) **re-indexed by residual values** to remove an ambiguity of the target | derivation, and better than the target | case `ν_j = 1`: `(r−1−2ℓ) + 1 + 1 = r + 1 − 2ℓ`: right, with equality |
| P3 | (F1)–(F7); the one place where a sign matters, (M, ε = 1) | derivation | the cancellation is independent of `θ`: right |
| P4 | sizes; parity of the matrix; relabelling | derivation | `|P| + t = (m − 1 − |λ|)/2`: right |
| P5 | dictionary, divided powers, stable ideals, pair forms, `J(ζ) = E(ζ) ∧ O(ζ)`, Lemma 5.2, Corollary 5.3 with the powers of `ζ`, the proof | derivation; the agreement of signs (F7)/(5.1) left to a machine check over `Z` (14 instances) and said so | its hand case `r = 3`, `(ℓ,t) = (0,1)`: I expanded both sides: `Δ` and `Δ + y_2^3`: right |
| P6, seven cases | for each: the patterns are of shapes in `Λ`; the `y_1`-degree; the top coefficient; `Φ` | derivation, case by case | (M, ε = 1) at `ℓ = 0`, `t = 0`: `y_1B(y_1,y_2) + D(y_1,y_2) = y_2^{r−1}` by (1.2): right |
| P7 | base, step; **`V_root = (D_J)` checked in both directions**, the marked patterns through Lemma 5.1 at `ℓ = 0` | derivation | right; it also notes that the upper bound of Corollary 6.2(i) is not on the path of Theorem E |
| P8 | Theorem T3, the three cases and the edges, identities expanded | derivation | `y_c^2 = y_1(y_c − y_1) + D(y_1,y_c)`: right |
| P9 | deduction | derivation | — |

No stamp. Where the reader did not carry a computation by hand (the shuffle signs of (F7)) it says so and gates it.

## 5. Its gates: what they test, their controls, a sample re-run by me

Its engine (`checks/eng2.py`) is its own: it builds `V_Λ` from Definition 4.1 with the Pfaffian computed from its definition, and computes slices from an echelon form of the ideal, not from the constructions of the proof. Fourteen sealed predictions (C1–C14), written after the pencil verdicts and before any run.

**Controls.** Each gate has a control that can fail, and the report says which controls did **not** work: C7 («wrong borders»: the membership still holds, because the lemma is true for those borders) and C10 («hypothesis on the binomial coefficients false»: the inequality still holds). Both were replaced by controls that fire (one `S` removed: fails in 50 of 50; a sub-family of bijections: run k03b). A reader who had wanted to look good would not have printed this. It is the strongest sign that the gates were run to break the claim.

**Sample re-run by me** (byte copies of its scripts in `corpus4/regla302_rerun/`, estimates written first in `ESTIMATES.md`, each inside `vigia.sh`, one at a time):

| Run | Script and arguments | Its log | My re-run | Peak, time |
|---|---|---|---|---|
| s1 | `k01_counts.py` | 10 cells, four counts agree, both controls differ | identical (diff of 0 lines) | 17 MB, 0 s |
| s2 | `k03b_control.py` | 7 cells; control fires | identical (diff of 0 lines) | 8 MB, 0 s |
| s3 | `k05_lemma51.py 5 …` five primes | membership true, «one S removed» false | every line found in its log; 15 memberships true, 15 controls false | 23 MB, 0 s |
| s4 | `k05_lemma51.py 7 …` five primes | the same | every line found in its log; 20 true, 20 false | 124 MB, 8 s |
| s5 | `k08_roots_T3.py roots "2,7,2 1,15,2 1,13,13"` | `3301, 631, 469` | `3301, 631, 469`, EQUAL | 227 MB, 2 s |
| s6 | `k08_roots_T3.py T3 7 2,3,101` | 35 ideals, three primes, equality; control fires | every line found in its log | 196 MB, 25 s |

Nothing differs. I also re-added its totals: `8 + 32 + 8 + 64 + 8 + 8 + 216 = 344` colourings; `27 + 243 + 27 + 27 + 21 = 345`; the sums `|Γ| = 61, 1001, 217, 1027, 469, 817, 4921` and `1519` are `N_{m−1}(4)` and `N_5(6)` computed by hand (`3r² − 3r + 1` at `r = 5, 9, 19, 13, 17, 41, 23`). Right.

Not re-run by me: k02 (the literal ring; my own gate G4 covers it by another route), k03, k04, k06, k06b, k07. They are in the manifest.

## 6. Its presentation notes and anything it found that I did not

Found by the reader and **not** by my audit:

1. **Lemma 5.1 is true for more border sets than it states** (any `ℓ − 1` borders for `ℓ ≥ 1`; the border `y^{r−2}` for `ℓ = 0`), by the very argument of the lemma. Found through a control that failed to fire.
2. **Every pair of down-sets that satisfies (D1) but not (D2) has `dim V_Λ > |Z_Λ|`, never `<`.** So (D2) is what makes the equality, not what makes the inequality. (Measured; not needed.)
3. **The sign `θ` of (F4) is `+1`** in the only place where it matters: `θ = (−1)^{|N∖x| + s + 1}` and `|M| + |E^+| = 2ℓ + 1 + 2t` is odd.
4. **At even boxes `q = 2, 4, 8` over `F_2` there is equality at every down-set**, not only at the roots.
5. **Where the binomial hypothesis of §7 fails** (`q = 4` over `F_3`, `q = 6` over `F_2`) the inequality `dim V_Λ ≥ |Z_Λ|` still holds in its cells: only one step of the paper's *proof* uses the hypothesis. This is a question for the open problems of the paper: is Theorem C true over every field?
6. Seventeen presentation notes. The ones that the paper must take: two statements numbered «6.1» (note 1); (D2) with rows labelled by residual values (note 3); `θ` explicit (note 4); the three counts with similar names need a table (note 13); the identification of a character of `G_{r'}` with a colouring is through the Teichmüller bijection (note 16); **§7 of the paper should be stated for every integer `q ≥ 1` and every field in which the `C(q−1, t)` are non-zero, so that the even box is a citation and not a re-reading** (its §4.2).

Found by my audit and not by the reader: the Lean theorems `Bip.thm76` and `Bip.theoremC` carry `Odd q` (the reader did not look at Lean, and says so); six cells of the literal ring outside [DS, §5].

Disagreements between the two readings: **none**.

## 7. What it did not read

By its own list, which I find complete: Appendix A of the paper and §9–§14 (Theorem A; it enters only the upper bound of Corollary 6.2(i), which Theorem E does not use); the PDF files; Legs D and F of the pilot's report and Theorem C0; the Lean development; no original beyond [DS] in the literature search (three searches, result pages only; the odd-box statement not searched under other names). No new literal cell: every cell of its runs k02, k06, k06b is a known one, which it says twice.

None of this is on the path of Theorem E. The literature search for the odd box under other names remains owed (it is in the pending list).

## 8. What follows: the state of the claim after two readings; what is still owed before v11

**The state.** Two cold readings, written independently, with independent code, agree on every item; no error and no gap found by either. The chain is:

1. Conjecture 1.2 at `(k, m)`, any `m ≥ 3`, ⟺ `dim_{F_p}(ψ̄_J)F_p[G] = |Γ|` for every prime `p | m`; `≤` always ([DS, Theorem 1.1(a)] and Claim 4.3; no parity).
2. For even `m` and each prime `p | m`, the colour reduction splits the ideal into blocks; the lower bound for each block is: Theorem B of the paper (block of colour 1, `p` odd), Theorem C of the paper (pair blocks; at `p = 2` with an even box `q = 2^v`), **Theorem O** (block of colour `−1` at `p` odd, box `p^v`; and, through leading forms, the block of colour 1 at `p = 2`, box `2^v − 1`).
3. Theorem O: the odd box, every odd `r`, every field, every `k`.

**What neither reader re-proved, and the paper v11 must carry or cite:**

- (a) Theorem B and Theorem C of the paper at odd `q`: proved in v10, read cold five times and **certified in Lean** (pieces 1–19).
- (b) Theorem C at an **even** box in characteristic 2: both readers checked §7 of v10 step by step with `q` an arbitrary integer; **there is no written proof and the Lean statement carries `Odd q`**. In v11, §7 must be stated and proved for every integer `q ≥ 2` and every field in which `C(q−1, t) ≠ 0` for `0 ≤ t ≤ q − 1`; then the even box is a case of the theorem.
- (c) Proposition 5.6 of the paper, used in Lemma 2.4 (D1) of the odd box: in v10, in Lean.
- (d) The topology: Pham's theorem and [DS, Theorem 2.2], as in v10.

**Owed before any release** (Rafa's plan: no Zenodo now; Aristotle and Lean first; then v12 with the Lean inside):

- v11 written with every proof inside, in the standard of v10 (md and pdf), and a double check of its own;
- the Lean formalisation of the new parts: Theorem O (bordered Pfaffians and the exterior algebra are new), Theorem C without `Odd q`, the colour reduction with two self-inverse colours and at the prime 2, the leading-form step, the assembly;
- the literature search for the odd box under other names;
- the Hodge corollary for the quartics (Aoki's Theorem A covers `m = 4`), to be written and checked, not asserted.

## 9. Errors of the auditor in this grading

1. My first look at the transcript counted the strings «"name":"Agent"» and «"name":"Workflow"» and found two of each; for a moment that read as agent use. They are the tool list attached by the system. I then parsed the transcript by tool call. **A string count in a transcript is not a count of calls.**
2. I re-ran six of its nineteen runs, the light ones. The heavy ones (k04e, k06, k06b: up to 954 MB) were not re-run; my own gates of `regla301` cover the same statements by other code, which is a different thing from reproducing its logs.
3. The grade is given by an instance of the same kind as the reader and the author. The reader says this of itself (its §9); it is equally true of me.

— Grepy Chats
