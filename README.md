# The Chaise Longue Theorem

### Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every odd degree in every even dimension, and the integral Hodge conjecture for those whose degree is prime or prime to $(n+2)!$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22961150.svg)](https://doi.org/10.5281/zenodo.22961150)

**Rafael Amichis Luengo** · Madrid · tretoef@gmail.com · preprint v10, 1 October 2026

> **Status.** A complete proof, published as a preprint. It has been read cold, step by step, eleven times, by AI systems of three providers; no reader found a fatal error, and every gap or error reported on an earlier version has been repaired. Its algebraic core, Main Theorem′, has been checked in Lean 4 ([lean/](lean/README.md)). **It has not yet been refereed by a human expert.** Version 7 was sent to A. Degtyarev and I. Shimada, the authors of the conjecture, on 26 September 2026. This repository exists so that they, and any referee, can check every step: the paper, every engine and log behind its numbers, every cold reading, and the complete record of how the proof was found, dead ends included.

**Read the paper:** [paper/THE_CHAISE_LONGUE_THEOREM_v10.pdf](paper/THE_CHAISE_LONGUE_THEOREM_v10.pdf) · [Markdown source](paper/THE_CHAISE_LONGUE_THEOREM_v10.md) · the previous versions: [v9](paper/THE_CHAISE_LONGUE_THEOREM_v9.pdf), [v8](paper/THE_CHAISE_LONGUE_THEOREM_v8.pdf), [v7](paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · permanent archive: [doi.org/10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150)

> **Version 10 (1 October 2026): a second correction of attribution, and a dictionary.** Theorem A — the *different* count of §8, which is not the conjecture — is not new as a count. Over an infinite field its ring is the space of coinvariants of the centralizer of a regular unipotent element of $SO_q$ in a tensor power of the vector representation, and the count follows from a theorem of Kostant (1963) in characteristic 0 and from a proposition of Bezrukavnikov, Riche and Rider (arXiv:2005.05583, Proposition 2.12) in odd characteristic. Version 9, of the same day, had credited Kostant and said that no version in positive characteristic was known to us; that was wrong. What the paper contributes to Theorem A is the dictionary and an elementary proof. In the same language, Theorem B — the algebraic form of the conjecture for prime-power degree — says that the invariant tensors of $Sp_{q-1}$ generate the invariants of that centralizer (§8 of version 10). No statement and no proof of the Main Theorem changes. Notes: [the second correction](record/audits/the-1-october-second-correction-bezrukavnikov-riche-rider.md), [the first](record/audits/the-1-october-kostant-correction.md); supplement: [paper/THE_REGULAR_CENTRALIZER_NOTE_v1.pdf](paper/THE_REGULAR_CENTRALIZER_NOTE_v1.pdf).

---

## The question

Take the Fermat variety $X \subset \mathbb{P}^{n+1}$ given by $z_0^m + z_1^m + \cdots + z_{n+1}^m = 0$, of even dimension $n = 2k$. It contains many flat pieces: the standard linear subspaces, cut out by pairing the coordinates, $z_{k_i} = \beta_i z_{j_i}$ with $\beta_i^m = -1$. Their classes generate a sublattice $L(X)$ of the middle homology $H_{2k}(X;\mathbb{Z})$.

In a paper published in 2016, Alex Degtyarev and Ichiro Shimada asked whether these flat pieces generate their part of the lattice *without holes*: whether the quotient $H_{2k}(X;\mathbb{Z})/L(X)$ is torsion free ([*J. Math. Soc. Japan* 68 (2016)](https://doi.org/10.2969/jmsj/06830975), Conjecture 1.2). Before this work it was known for surfaces ($k=1$, Degtyarev) and had been confirmed by computer in a finite table of cells.

## The answer

> **Main Theorem.** For every odd degree $m \ge 3$ and every $k \ge 0$, the group $H_{2k}(X;\mathbb{Z})/L(X)$ is torsion free. Equivalently, $L(X)$ is a primitive sublattice of rank $Q_k(m)+1$, where $Q_k(m) = (2k+2)!\,[x^{2k+2}]\, I_0(2x)^{(m-1)/2}$.

It has an algebraic form that needs no topology at all:

> **Main Theorem′.** For every odd $m \ge 3$ and $k \ge 1$, the group $\mathbb{Z}[G]/(\psi_J : J \in \mathcal{J})$ of Degtyarev–Shimada, with $G = (\mathbb{Z}/m)^{2k+1}$, is free abelian of rank $m^{2k+1} - Q_k(m)$.

And it has a consequence in Hodge theory:

> **Corollary H.** If $m$ is an odd prime, or every prime factor of $m$ exceeds $2k+2$, then every integral Hodge class of middle degree on $X$ is an integral combination of classes of linear subspaces. In particular the integral Hodge conjecture holds for $X$.

**In plain words.** Degtyarev and Shimada turned a question about the shape of a variety into a question about counting: the conjecture holds exactly when, for each prime dividing the degree, a certain family of polynomials — one for each way of pairing up $2k+2$ objects — spans a space of the right size. The proof counts that space by peeling off one variable at a time. Each slice turns out to be a smaller problem of the same kind, the bookkeeping collapses onto partitions of whole numbers ordered by dominance, and at every step the possible values of the new coordinate line up in a single chain. For the degrees that are not prime powers, the problem first splits into independent colour blocks, and one new family of blocks is counted by the same method.

| | Statement | Status in the paper (§14) |
|---|---|---|
| **Main Theorem′** | the algebraic form, every odd $m$ | proved, with no topology |
| **Main Theorem** | Conjecture 1.2, every odd $m$, every even dimension | proved, modulo Pham's theorem and the intersection numbers of [DS, Thm 2.2] |
| **Theorem B** | the dimension count, over every field and every odd $q$, free over $\mathbb{Z}$ | proved |
| **Theorem C** | the bipartite count behind the composite degrees | proved |
| **Corollary H** | the integral Hodge conjecture in the degrees above | proved, modulo classical results that are quoted (Shioda–Katsura, Ran, Aoki) |
| **Corollary W** | the linear spaces on partial Fermat varieties span primitive sublattices | proved (what [DS] had proved conditionally) |
| **Theorem A** | a *different* count, $\dim F[x]/(e_1, e_3, \dots; x_i^q) = n!\,[y^n]\,e^y I_0(2y)^{(q-1)/2}$ | proved; it is **not** the conjecture (§9). **As a count it is not new:** it follows from Kostant's theorem (1963) in characteristic 0 and from Bezrukavnikov–Riche–Rider (2020) in odd characteristic; the paper adds the dictionary and an elementary proof (Remark 8.4) |
| even degrees $m$ | | open (§13) |
| **Lean 4** | Main Theorem′, every odd $m$, every $k$, over $\mathbb{Z}$ and over every field | machine-checked: no `sorry`, only the standard axioms ([lean/](lean/README.md)) |

*Related recent work.* R. Jumagulov, *The Hodge conjecture for Fermat fourfolds of odd degree at most 199* (arXiv:2608.18134, July 2026), gives a computer-assisted proof of the **rational** Hodge conjecture for the Fermat fourfolds $X^4_m$ of every odd degree $m \le 199$, using algebraic cycles beyond linear subspaces. Corollary H is an **integral** statement about **linear** cycles; for fourfolds ($k = 2$) it covers the odd primes and the odd $m$ whose prime factors all exceed $6$, so the composite odd degrees divisible by $3$ or $5$ are not covered by it.

A guided tour of these results, with the lemmas a referee should look at first, is in **[THEOREMS.md](THEOREMS.md)**.

---

## Machine-checked in Lean 4

> **Main Theorem′ is proved in Lean 4 with Mathlib** (29 September 2026), for every odd $m \ge 1$, every $k \ge 0$, over $\mathbb{Z}$ and over every field. The proof has 113 files, 21,126 lines and 937 theorems. It contains no `sorry`, and the final theorem `ColAssembly.mainTheorem'` depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

- **Who wrote the proofs.** The Lean proofs were written by Aristotle (Harmonic), in 29 pieces written from the paper.
- **How they were checked.** Every file was compiled again on the author's machine, and every statement was audited against the paper.
- **What stays cited.** Only the topology is not formalized: [DS, Theorem 1.1(a)] (Pham's theorem and [DS, Theorem 2.2]), which identifies the torsion of $\mathbb{Z}[G]/(\psi_J)$ with that of $H_{2k}(X;\mathbb{Z})/L(X)$.

**Certificate:** [lean/LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf](lean/LEAN_CERTIFICATE_CHAISE_LONGUE_v1.pdf). Archived with the whole Lean folder on Zenodo: [doi.org/10.5281/zenodo.23045370](https://doi.org/10.5281/zenodo.23045370). It gives the exact statement, the comparison with the paper, the trust base, the data of every piece and how to reproduce it. **Code:** [lean/project/](lean/project/).

**Check it yourself, from the evidence to the full rebuild:**
1. The final theorem as Lean prints it, with its axioms: [lean/logs/check_run29.log](lean/logs/check_run29.log). The axiom lines are 55–60.
2. The theorem in the source: [lean/project/RequestProject/ColAssembly/Main.lean](lean/project/RequestProject/ColAssembly/Main.lean).
3. A rebuild from scratch, module by module, 113 of 113 with no error: [lean/logs/clean_rebuild_2026-09-29.log](lean/logs/clean_rebuild_2026-09-29.log). The final full build is [lean/logs/build_after_clean.log](lean/logs/build_after_clean.log).
4. What the final theorem actually uses (2,367 declarations in 90 files): [lean/logs/deps_mainTheorem.log](lean/logs/deps_mainTheorem.log).
5. The audit of each of the 29 runs: [lean/AUDIT_LOG.md](lean/AUDIT_LOG.md). The pieces as sent: [lean/pieces/](lean/pieces/). The brute-force checks run before sending them (kept for pieces 7–16 and 18–29): [lean/checks/](lean/checks/).
6. Rebuild it on your own machine: [lean/README.md](lean/README.md#how-to-check-it).

**Also in Lean: the Watermark and Double Ladder Theorems** of the Hodge–Fermat campaign (30 September 2026). They give the discriminant `m^{3(m−3)²}` of the lattice of lines on the Fermat surface of prime degree `m ≥ 5`, and its discriminant group. Each paper is in [hodge-fermat-campaign/](hodge-fermat-campaign/) next to its Lean certificate: [Watermark](hodge-fermat-campaign/LEAN_CERTIFICATE_WATERMARK_v2.pdf), [Double Ladder](hodge-fermat-campaign/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf). The Lean project and all its evidence have their own repository, [watermark-theorem](https://github.com/tretoef-estrella/watermark-theorem), and are archived on Zenodo: [doi.org/10.5281/zenodo.23062529](https://doi.org/10.5281/zenodo.23062529).

**The sequel: the Watermark in every even dimension** (1 October 2026). Open problem 3 of the paper asks for the discriminant and the elementary divisors of the Hodge lattice of a Fermat variety of prime degree beyond surfaces. The discriminant now has an answer, for prime degree `p` and every even dimension `2k` (the elementary divisors stay open): the discriminant group is the finite ring `Z[G]/(I_𝔅 + I_T)` (this part for every degree `m ≥ 3`), and `|disc Hdg(X)| = p^{E_k(p)}`, with `E_k(p)` computed from the Hilbert function of the Theorem-A ring of this paper with the even box `p − 1`; for surfaces it returns `3(p−3)²`. The general formula rests on a count that follows from a theorem of Bezrukavnikov, Riche and Rider; without it the formula is a proved lower bound, and it was checked by machine in 22 cells. The note was read cold by an independent reader before release. It lives in the [watermark-theorem](https://github.com/tretoef-estrella/watermark-theorem#in-every-even-dimension-1-october-2026) repository and on Zenodo: [doi.org/10.5281/zenodo.23091045](https://doi.org/10.5281/zenodo.23091045).

---

## How to check it

- **[HOW_TO_VERIFY.md](HOW_TO_VERIFY.md)**: which engine certifies which number of the paper, how to run it, and what it prints. Every script runs on a laptop in seconds or minutes, with no external data.
- **[WHERE_TO_ATTACK.md](WHERE_TO_ATTACK.md)**: the load-bearing joints of the proof, named by us, in the order we would attack them.
- **[record/](record/README.md)**: every cold reading of every version of the paper (by Claude, ChatGPT and Gemini), each with its report, its own code and its grading, and the audits of the three proofs that close the conjecture.

The honest limits are stated in the paper (§12.6) and repeated here: every reader so far is an AI system; no human expert has refereed the work; Pham's theorem and the intersection numbers of [DS] are quoted, not re-proved.

---

## How this proof was made — a note from Rafael Amichis Luengo

I am not a mathematician. My background is in psychology.

This proof was built over four months by teams of Claude instances (Anthropic's AI) working in separate roles under my direction: constructors who proposed and wrote proofs, auditors who re-derived them cold and ran their own code, sweepers who searched our own archive for results we had already found and forgotten, and readers who attacked each finished version as referees. Every definition, proof and computation in this repository was written by them and checked by instances that had not watched it being built. I directed: I decided what to attack and when to stop, I kept the team honest, and — again and again — I turned a wall into a picture.

That was the method, and it is the particular thing about this work. When the team was stuck, the AI explained the obstruction to me in a metaphor. I answered with an object from ordinary life. The AI translated the object back into algebra and measured whether it held. Most pictures died on contact with the numbers. Some of them opened the way:

- **The chessboard** (21 September). *«You can count a board without looking at every square: rows times columns.»* Translated: slice the ideal by the powers of one variable, and compare each slice with the points that share one value of that coordinate. Measured the same day, each row of the board was exactly a smaller problem of the same kind. The picture became a mission for an external Claude, *The Chessboard*; fifteen missions and three days later, on 24 September, its report proved the conjecture for the degrees $3^v$ by exactly that move — peel off one variable, match each slice with a fibre of points — and that move is the spine of the proof in the paper (§5). The same line of missions had proved the count behind Theorem A the day before.
- **The hinge that goes *clack*.** *«What sticks out on the outside is what is missing on the inside; press it from the centre and it folds from the edges and fits.»* Translated: when one pair of coordinates is fixed, the generating series of level $k$ restricts to that of level $k-1$ times a single hinge factor, $U(w) \mapsto (1 - v^2 w)\,U'(w)$ — what sticks out is exactly the pair that was removed. That is the Hinge Lemma, proved for every $k$ ([theorems/standalone/CHAISE_LONGUE_HINGE_LEMMA.md](theorems/standalone/CHAISE_LONGUE_HINGE_LEMMA.md)); the file credits it as *«Rafa's clack»*.
- **The tank.** A racing car had been the previous picture, and it failed: it depends on the grip of the asphalt. *«A tank does not move on one part. It has tracks that grip the ground, an engine that pushes, and a gearbox that multiplies.»* Translated: every tool was classified as a *track* (it advances one degree at a time, whatever the field), an *engine* (it is structural and works in every dimension at once) or a *gearbox* (it tries to lift a result from one field to a bigger one). We showed why every gearbox must fail, and measured that the tracks leave a middle band that never shrinks. From then on, no tool was admitted without being classified first. The proof that finally closed the conjecture is of the engine kind: it works for every degree at once, with no gearbox anywhere.

More of these pictures, and what each one produced or failed to produce, are in [THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md). The complete notebook of them, in Spanish, is [archive/CHAISE_LONGUE_LAS_IDEAS_DE_RAFA_v231.md](archive/CHAISE_LONGUE_LAS_IDEAS_DE_RAFA_v231.md).

I say plainly what follows from this, because it matters to anyone reading the proof. A question about a step of an argument is best put to the paper and its verification record, which were written to answer it, and every step can be re-derived from what is in this repository; I will gladly pass such questions on. What I can answer, and am proud to, is how the proof was found.

---

## The record, in numbers

The campaign ran from **23 May to 25 September 2026** — 126 days, of which the Chaise Longue proper took the last 76 — through the *Hodge–Fermat* campaign, the *Sofa* ($k=2$), the *Hammock* ($k=3$) and the *Chaise Longue* (every $k$). Nothing was deleted along the way; every retraction was written under the line it retracts.

| | |
|---|---|
| Distinct Markdown documents written (by content hash) | **9,782** — 2.3 GB of text; **13,862** distinct files in all |
| Versions of the twenty living documents | **5,012** — the Master Catalogue alone reached v524, the Cemetery v502, the Ledger v435 |
| Dead routes recorded, each with the reason it failed | **316** tombs in the Cemetery by mid-September; more after |
| Standalone write-ups of intermediate results | **222** families, published here with a header each, plus the theorems of the earlier Hodge–Fermat campaign |
| The tree of the proof (`arbol.yaml`) | **1,295** nodes, **12,733** lines, **293** versions |
| Named Claude instances | more than **80** names, more than **100** incarnations |
| Auditor's reports and missions | **144** reports, **107** missions, **99** technical audit records |
| Results found again that the archive already held | **129**, each caught and logged (`OWN-DEPOSITED`) |
| The great sweep | **20** reports; **2,403** never-classified documents brought to **0** |
| Cold readings of the paper | **11**, of versions 3 to 7 |
| Lean 4 formalization of Main Theorem′ | **29** pieces; **113** files, **21,126** lines, **937** theorems; **0** `sorry` (28–29 September 2026) |
| Time invested, in the author's own words | more than **1,000 hours** for the whole route (Hodge–Fermat, Sofa, Hammock, Chaise Longue); the Chaise Longue alone, **76 days at about 12 hours a day**, often more |

The story behind these numbers — the dogs' sweep, the gold found where we had already walked, the day we discovered we had been proving the wrong statement, and the three days that closed it — is told in **[THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md)**.

*On the time, from Rafael Amichis Luengo.* Some think that work like this means giving the problem to an AI, pressing a button and receiving the result. That is not how this proof was made.

- The whole route took me more than a thousand hours.
- The Hodge–Fermat campaign helped: its splitting into blocks by the Chinese remainder theorem is the precedent of the colour reduction of §6, which closed the degrees that are not prime powers.
- The Sofa and the Hammock were the first cases, $k = 2$ and $k = 3$.
- The Chaise Longue alone took 76 days, from 11 July to 25 September, at about twelve hours a day and often more. You do not stop thinking about it, not even in the shower.

---

## Repository map

```
paper/                      the paper, v10 (PDF and Markdown source; §12.8 is the Lean proof), v9, v8, v7, and the supplement on the regular centralizer
THEOREMS.md                 a guided tour of the results, for referees
theorems/INDEX.md           the 222 standalone documents, by campaign, with their status
theorems/standalone/        the standalone documents, each with a citation header
hodge-fermat-campaign/      the earlier campaign: Watermark, Double Ladder, Localization, Block Decomposition,
                            the Nail, the sixteen machine verdicts, and their engines and logs
engines/                    every engine and log behind the paper's numbers (see HOW_TO_VERIFY.md)
record/                     cold readings of every version, and the audits of the proofs
lean/                       the Lean 4 proof of Main Theorem′: certificate, project, pieces, checks, logs
archive/                    the working notebooks: the Master Catalogue, the Cemetery, the tree, Rafa's ideas
```

**Earlier work.** [The Sofa Theorem](https://github.com/tretoef-estrella/sofa-theorem) ($k=2$) and [The Hammock Theorem](https://github.com/tretoef-estrella/hammock-theorem) ($k=3$) were written under an identification that the paper shows to be false (§1.8); their conclusions about Conjecture 1.2 are nevertheless true, as the cases $k=2,3$ of the Main Theorem.

---

[CITATION.md](CITATION.md) · [LICENSE-TEXT.md](LICENSE-TEXT.md) · [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) · [THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md) · [A personal note](A_PERSONAL_NOTE.md) · [On AI and mathematics](ON_AI_AND_MATHEMATICS.md)

*Cite as:* Amichis Luengo, R. (2026). *The Chaise Longue Theorem* (preprint, version v10). Zenodo. https://doi.org/10.5281/zenodo.22961150
