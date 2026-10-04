# Part 5: §10 pointer, Remark 12.2, §14, §15, §16, acknowledgements, references.
import pathlib
SRC = (pathlib.Path(__file__).parent / "v11_source.md").read_text(encoding="utf-8")
def block(start, end):
    assert SRC.count(start) == 1, start
    assert SRC.count(end) == 1, end
    i = SRC.index(start); j = SRC.index(end, i)
    return SRC[i:j]

OLD_148 = block("### 14.8 A machine-checked proof of Main Theorem′\n", "### 14.9 The odd box and the even degrees")
NEW_148 = """### 14.8 A machine-checked proof of Main Theorem′ and of Theorem O
Main Theorem′ has been proved, for every degree, in the proof assistant Lean 4 [dMU] with the Mathlib library [Mlib]; the certificate is [LC]. The final theorem, `EvenAll.mainTheorem'`, states: *for every `m ≥ 1` and every `k ≥ 0`, `R/(ψ_J : J ∈ 𝒥)` is a free abelian group of rank `m^{2k+1} − Q_k(m)`, and for every field `F`, `dim_F F[G]/(ψ̄_J : J ∈ 𝒥) = m^{2k+1} − Q_k(m)` and `dim_F (ψ̄_J : J ∈ 𝒥) = Q_k(m)`.* This is slightly more general than Main Theorem′ as stated in §1.2 (`m ≥ 3`, `k ≥ 1`, prime fields). In Lean, `Q_k(m)` is defined by the formulas of §1.2, with the parity split, and lemmas identify it with the numbers of tuples of Lemmas 2.2 and 9.1 and with `|Γ_𝒥|`. Theorem O is proved with equality over every field and with the freeness over `Z` (`OddEquality.D1`, `OddEquality.D2_DJ`; for the ideal `ℳ` of Lemma 8.12, `OddEquality.D2_M`).
- **What was formalized.** For odd `m` (version 1 of the certificate, 29 September 2026): Lemma 2.2 and the translation of §2 in its local form (Lemmas 2.3, 2.4 and Proposition 2.5); Theorem 5.3 and the induction of §5; the colour reduction of §6; Theorems 7.6 and C; and the upper bound [DS, Claim 4.3] (Theorem 0(b), Appendix B, Step 6), which is algebraic. For every degree, in twenty further pieces: §7 for every box `q ≥ 2`, and at `q = p^v` in characteristic `p`, `2` included; Lemma 9.1 and the upper bound for even `m`; all of §8 — the shapes and interlaced pairs, Lemmas 8.3–8.5, the Pfaffians and bordered Pfaffians of §8.3 over any commutative ring with the signs given there, Lemmas 8.7, 8.7′ and 8.8 and Corollary 8.9 in the form printed in §8.5, Definition 8.6, the seven cases of Proposition 8.10, Theorem 8.11, Theorem O, Lemma 8.12 in the direction used and Corollary 8.13 — and Theorem 8.15; and all of §9, with Lemmas 9.4–9.10 for every prime and every cofactor. Theorem 4.1, Theorems 5.9 and 5.9′, Corollaries 7.8 and 9.12, Theorem 8.15 and the equality in Theorem O were formalized too, although Main Theorem′ does not need them.
- **How.** The Lean proofs were written by the AI system Aristotle (Harmonic), in `49` pieces (`29` for the odd degrees, `20` for the rest), each a short text written from this paper. Every returned file was compiled again on the author's machine (Lean `v4.28.0`, Mathlib at the tag `v4.28.0`) and audited against the paper before the next piece was sent: the difference with the previous project (no piece changed a file of an earlier one), a search for forbidden constructs, the build, the statements as Lean prints them, and their axioms. Before a piece was sent, its statements were tested by exact computation, with negative controls (`33 731` checks for the twenty pieces of the even degrees, with no failure).
- **Result.** `233` files, `41 243` lines, `1 859` theorems and lemmas. There is no `sorry`, `admit`, `native_decide` or added axiom, and every main theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. A rebuild from source on the author's machine compiled `229` of the `233` modules; the other four — two modules of numeric checks, whose evaluation by the kernel needs more memory than the cap of the local builds, and the two modules that only import them — compiled on Aristotle's machines, and no theorem used elsewhere is in them. A program that collects the declarations used by the final theorem finds `4 412` of them, in `180` of the `233` modules.
- **What is not formalized.** Theorem 0(a), (c) and (d): the topology of [DS] that identifies the torsion of `R/(ψ_J)` with that of `H_{2k}(X; Z)/L(X)` and gives the rank of `L(X)`. Mathlib has no singular homology of complex Fermat varieties. So the Main Theorem, as a statement about homology, is machine-checked only in its algebraic form. Theorem A, Corollaries H and W, §11, the graded refinements of Theorems B and O, and the computations of §14.1–§14.5 and §14.9 are not formalized either.
- **Where.** The certificate [LC] gives the Lean statements and definitions verbatim, compares them with this paper line by line, and lists the trust base, the data of every piece and how to reproduce the build. The Lean project, the pieces, the checks and every log are in [Rep], folder `lean/`.

"""

V11_LIMITS_OLD = "the printed text of §8–§9, as distinct from the documents it was written from, has been re-read and gated by its writer only (§14.9, last item); and nothing in §8–§9 is formalized. The documents, the audit, the report of the cold reader, its grading and all the code are in [Rep], `record/even-degrees/`."
V11_LIMITS_NEW = """the printed text of §8–§9, as distinct from the documents it was written from, was at first re-read and gated by its writer only (§14.9, last item; it was then read cold, see the next paragraph); and nothing in §8–§9 was formalized (it now is, §14.8). The documents, the audit, the report of the cold reader, its grading and all the code are in [Rep], `record/even-degrees/`.

**The printed text of version 11, and version 12.** The printed text of version 11 was read cold on 2 October 2026 by a further instance of the same system, which had the paper, the original of [DS] and the pages of [Aok] that it needed, and nothing else. It wrote its verdict item by item before running anything (`37` items: §1, §2, Appendix B, §5, §6, all of §7, §8 and §9, Corollary 10.8, §12, §13 and §16), re-derived every step of the chain for even `m` by hand, and made logged runs with its own code, among them the dimension of the literal ideal of [DS] in `16` cells `(k, m, p)` with `p | m`. Its verdict was «holds», with no error and no gap; its `18` notes of presentation and three observations (some patterns are zero; the border of Lemma 8.7 for `ℓ = 0`; the odd-box formula at an even box) are incorporated in this version. It did not read Appendix A or §4, did not re-prove the topology or (H1)–(H3), and did not open the pdf; Corollary 10.8 is in its reading «holds, given Theorem A». Its session record shows that it used no other agent and opened nothing outside its folder. The auditing instance graded the report, checked its hand computations and repeated six of its runs with its scripts, with identical output. In the present version, the proof of §8.5 (Lemmas 8.7′, 8.8 and Corollary 8.9) and the upper bound of Corollary 8.13 are new in the writing: they are the proofs that were formalized, and the Lean kernel checks them (§14.8), but no reader other than their writer has read the printed text. Report, grading and code: [Rep], `record/cold-readings/`."""

EDITS = [
    ("10 pointer (reader note 1)",
     "And the two counts that §1.8 describes,",
     "And the two counts of §1.6 and §11.1,"),
    ("12.2 WED",
     "For `k ≥ 2` this is open (§15).",
     "For `k ≥ 2` and `m = p` prime, the sequel note [WED] gives a formula for `|disc Hdg(X)|` through the Hilbert function of the ring of Theorem A at the even box `p − 1`, modulo [BRR, Proposition 2.12] (without it, as a lower bound); the elementary divisors are open (§15)."),
    ("14 intro",
     "For odd `m`, Main Theorem′ has, in addition, been verified by a proof assistant (§14.8).",
     "Main Theorem′ and Theorem O have, in addition, been verified by a proof assistant for every degree (§14.8)."),
    ("14.6 v11 limits + v12", V11_LIMITS_OLD, V11_LIMITS_NEW),
    ("14.6 Lean limits",
     "- **The Lean proof covers Main Theorem′ for odd `m` only** (§14.8); §8 and §9 are not formalized. Its proofs were written by an AI system and are checked by the Lean kernel; that the Lean statement says what Main Theorem′ says is an audit, set out line by line in [LC, §1.3], which a reader can repeat on about a dozen short definitions.",
     "- **The Lean proof covers Main Theorem′ and Theorem O** (§14.8), for every degree; it does not cover the topology, Theorem A or Corollaries H and W. Its proofs were written by an AI system and are checked by the Lean kernel; that the Lean statements say what the paper says is an audit, set out line by line in [LC, §1.2–§1.3], which a reader can repeat on about fifteen short definitions."),
    ("14.7 item 7",
     "Lemma 8.7 and its dictionary between bordered Pfaffians and exterior products ((F7), (8.6), (8.7)), the decomposability of §8.5(e) and the powers of `ζ` in Corollary 8.9;",
     "Lemma 8.7′: the identity (8.6), the two operations of Lemma 8.8 and the powers of `ζ` in Corollary 8.9 (all of them checked in Lean, §14.8);"),
    ("14.8", OLD_148, NEW_148),
    ("14.9 Lemma 8.7",
     "The agreement of (F7) with (8.6) up to one sign was checked over `Z` in `14` instances, and the identities of §8.5(e), Lemma 8.8 and Corollary 8.9 with exact integers for `r = 3, 5, 7, 9, 11`.",
     "The identities of the exterior-algebra proof of version 11 were checked with exact integers for `r = 3, 5, 7, 9, 11`. The proof printed in §8.5 was checked, before it was sent to Lean, with exact integer arithmetic: the rank-two update and the closed forms of Corollary 8.9 (`1 718` checks), and Lemma 8.7′ with the explicit certificate that its proof produces, in `70` cells with `r = 3, …, 11` and up to six variables (`840` checks), with controls that fail as they should. The cold reader of the printed text of version 11 found that for `ℓ = 0`, `t = 1` and `r = 5` the border `y^2` in place of `y^{r−1}` gives a Pfaffian outside `𝔘_0(N)` (§8.5, Remark (3))."),
    ("14.9 not done",
     "Lemma 8.7 was tested over prime fields, not over `Z`.",
     "Lemma 8.7 was tested by machine over prime fields only; over `Z` it is proved in Lean (§14.8)."),
    ("15.3",
     "3. **Elementary divisors.** For `m = p` prime, compute the elementary divisors and the discriminant of `Hdg(X) = L(X)` in closed form for `k ≥ 2`; [AMV, Table 1] gives the data for small cells. For `k = 1` the closed forms are the author's *Watermark* and *Double Ladder* theorems [WDL] (Remark 12.2). In every cell of [AMV, Table 1] with `m` prime, `|disc Hdg(X)|` is a power of `m`; whether this holds for every `k` is part of the question.",
     "3. **Elementary divisors.** For `m = p` prime and `k ≥ 2`, compute the elementary divisors of `Hdg(X) = L(X)`; [AMV, Table 1] gives the data for small cells. For `k = 1` they are the author's *Watermark* and *Double Ladder* theorems [WDL]; for every `k`, the discriminant is given by the sequel note [WED], modulo [BRR, Proposition 2.12] (Remark 12.2)."),
    ("15.7c",
     "(c) Lemma 8.7 holds for more border sets than it states (§8.5, Remark (4)): find the natural statement.",
     "(c) Lemma 8.7′ gives the membership for any exponents in its case (a), and in its case (b) with the border `y^{r−1}`, which cannot be dropped (§8.5, Remark (3)): describe all the border sets for which it holds."),
    ("15.8",
     "8. **A machine-checked proof for the even degrees.** Formalize §8, §7 for every `q`, and §9 in Lean 4, as §14.8 does for the odd degrees. The bordered Pfaffians and the exterior algebra of §8.5 are new with respect to the existing formalization.",
     "8. **What is not formalized.** Main Theorem′ and Theorem O are formalized for every degree (§14.8; this was problem 8 of version 11). Formalize the topology of Theorem 0 (Mathlib has no singular homology of complex Fermat varieties), Theorem A, Corollaries H and W, and the graded refinements of Theorems B and O."),
    ("16 proved no topology (reader note 8)",
     "For odd `m` it uses §5–§7; for even `m`, §7–§9 and, at the odd primes, §5–§6;",
     "For odd `m` it uses §5–§7; for even `m`, §6 (Lemmas 6.1, 6.2, 6.4 and 6.7, at every prime, the prime `2` included), §7, §8, §9 and, at the odd primes, §5;"),
    ("16 machine-checked",
     "- **MACHINE-CHECKED in Lean 4 with Mathlib (§14.8), for odd `m` only:** Main Theorem′, for every odd `m ≥ 1` and every `k ≥ 0`, over `Z` and over every field; no `sorry`, and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`. Not formalized: the even degrees (§8–§9, and §7 for even `q`), the topology of Theorem 0(a), (c) and (d), Theorem A, and Corollaries H and W.",
     "- **MACHINE-CHECKED in Lean 4 with Mathlib (§14.8), for every degree:** Main Theorem′, for every `m ≥ 1` and every `k ≥ 0`, over `Z` and over every field; and Theorem O, with equality over every field and the freeness over `Z`. No `sorry`, and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`. Not formalized: the topology of Theorem 0(a), (c) and (d), Theorem A, Corollaries H and W, and the graded refinements of Theorems B and O."),
    ("16 Theorem O line (reader note 9)",
     "- **PROVED:** Theorem O (the count at the odd box, with equality over every field and for every odd `r ≥ 3`, and the freeness over `Z`), Theorem 8.11, Lemma 8.7, Theorem 8.15; Proposition 9.2, Theorem 9.11 and Corollary 9.12.",
     "- **PROVED:** Theorem O (the count at the odd box, with equality over every field and for every odd `r ≥ 3`, and the freeness over `Z`), Theorem 8.11, Lemmas 8.7 and 8.7′, Theorem 8.15; Proposition 9.2, Theorem 9.11 and Corollary 9.12 (in Proposition 9.2 and Theorem 9.11, the last clause, that `H_{2k}(X; Z)/L(X)` is torsion free, is modulo the same two results as the Main Theorem)."),
    ("16 read cold",
     "- **READ COLD, for the even degrees:** twice, by the auditing instance and by a separate cold reader, with separate code (§14.6); the printed text of §8–§9 by its writer only.",
     "- **READ COLD, for the even degrees:** the documents of the proof, twice, by the auditing instance and by a separate cold reader, with separate code; the printed text of version 11, by a further cold reader, «holds» (§14.6). The proof of §8.5 and the upper bound of Corollary 8.13 are new in the writing of this version: they are checked by the Lean kernel and have not been read cold."),
    ("acknowledgements Lean",
     "The Lean 4 proof of Main Theorem′ for odd degrees (§14.8) was written by Aristotle, an AI system made by Harmonic, from pieces written from this paper, and was compiled and audited on the author's machine.",
     "The printed text of version 11 was read cold by a further instance (§14.6). The Lean 4 proofs of Main Theorem′ and of Theorem O (§14.8) were written by Aristotle, an AI system made by Harmonic, from pieces written from this paper, and were compiled and audited on the author's machine."),
    # References
    ("ref FK",
     "- **[Gin]** V. Ginzburg,",
     "- **[FK]** D. Favero, T. L. Kelly, *The Chern character of a coherent sheaf on a smooth projective hypersurface*, arXiv:2609.12759 (11 September 2026). (§1.3 and §1.10 only; the abstract and §1 were read in the arXiv version.)\n- **[Gin]** V. Ginzburg,"),
    ("ref Knu",
     "- **[Kos]** B. Kostant,",
     "- **[Knu]** D. E. Knuth, *Overlapping Pfaffians*, Electron. J. Combin. **3** (1996), no. 2, #R5; arXiv:math/9503234. (§8.3 and §1.10; §0–§3 and §6 were read in the arXiv version.)\n- **[Kos]** B. Kostant,"),
    ("ref LC",
     "- **[LC]** R. Amichis Luengo, *The Chaise Longue Theorem — Lean certificate*, v1 (29 September 2026), in [Rep], `lean/LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf`. (§14.8 only.)",
     "- **[LC]** R. Amichis Luengo, *The Chaise Longue Theorem — Lean certificate*, version 2 (3 October 2026, every degree, and Theorem O), in [Rep], folder `lean/`; version 1 (29 September 2026, odd degrees) is doi:10.5281/zenodo.23045371. (§1.0, §14.6 and §14.8 only.)"),
    ("ref Mil+",
     "- **[Rep]** R. Amichis Luengo, *The Chaise Longue Theorem — working record*,",
     "- **[Miz]** M. Mizukami, *Birational mappings from quartic surfaces to Kummer surfaces* (in Japanese), Master's thesis, University of Tokyo, 1975. (§1.3 and §1.10 only; quoted from [SSvL, §3 and §6]; not read.)\n- **[MMRV]** M. Miranda, H. Movasati, L. Rufino, R. Villaflor, *Lengths of Hodge characters in Fermat varieties*, arXiv:2609.27301 (v2, 26 September 2026). (§1.3 and §1.10 only; the abstract and §1 were read in the arXiv version.)\n- **[Oka]** S. Okada, *Pfaffian formulas and Schur Q-function identities*, Adv. Math. **353** (2019), 446–470. doi:10.1016/j.aim.2019.07.006; arXiv:1706.01029. (§8.3 and §1.10; §2, in particular Proposition 2.3 and its proof, was read in the arXiv version.)\n- **[Rep]** R. Amichis Luengo, *The Chaise Longue Theorem — working record*,"),
    ("ref SSvL",
     "*Lines on Fermat surfaces*, J. Number Theory **130** (2010), no. 9, 1939–1963. (§1.3 only.)",
     "*Lines on Fermat surfaces*, J. Number Theory **130** (2010), no. 9, 1939–1963. (§1.3 and §1.10; §3 and §6 were read in the arXiv source.)"),
    ("ref WED",
     "- **[Was]** L. C. Washington,",
     "- **[WED]** R. Amichis Luengo, *The Watermark in Every Even Dimension*, Zenodo (2026). doi:10.5281/zenodo.23091046. (Remark 12.2 and §15 only; not refereed.)\n- **[Was]** L. C. Washington,"),
]
