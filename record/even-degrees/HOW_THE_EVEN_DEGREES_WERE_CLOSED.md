# How the Even Degrees Were Closed

### A light aeroplane, two wings, and two days in October

**Rafael Amichis Luengo** · Madrid · 4 October 2026

*A note on how Conjecture 1.2 of Degtyarev–Shimada was proved for the Fermat varieties of even degree: what happened, in what order, and what belongs to whom. It is written from the working diary kept on those days; times are local (Madrid). The proof itself is in version 12 of the paper, and the full record is in this folder.*

---

## The result

Degtyarev and Shimada conjectured that for the complex Fermat variety `X` of degree `m` and even dimension `2k`, the classes of the standard linear subspaces generate a primitive subgroup `L(X)` of `H_{2k}(X; Z)` [DS, Conjecture 1.2]. Version 10 of our paper (1 October 2026) proved it for every **odd** degree, and listed the **even** degrees as its first open problem.

On 2 October the even degrees were proved, and with them the conjecture for **every** degree `m ≥ 3` in every even dimension, modulo two published results that Degtyarev and Shimada use: Pham's theorem and their own Theorem 2.2. Between 2 and 3 October the whole algebraic part of the proof was checked in Lean 4. Version 12 of the paper was published on 4 October.

Two consequences came out of the writing. The integral Hodge conjecture holds for the Fermat quartic of every even dimension, with its linear subspaces as generators: dimension 2 was classical, and dimensions 4 and 6 already followed from computations; the statement for every dimension is new, to the best of our knowledge after the search recorded in [../literature/](../literature/README.md). And an old obstacle of this campaign, which we called «the bone» — at the odd box, the sum and the intersection of the matching ideals coincide for the full family — became a theorem (Corollary 10.8 of the paper).

This note tells how it happened. It is a story of a quick flight and a long runway, and it is told as honestly as we can.

## 1. The ground: why the car stops

On the morning of 2 October I asked where a trophy larger than the odd degrees could be, and why everything broke for even degree — as if it were a Formula 1 race. The answer, read from §2 and §6 of version 10, without computing anything, was a table:

| in the car | in the proof for odd degree | in even degree, at the prime 2 |
|---|---|---|
| the steering | inversion `t ↦ 1/t` becomes the change of sign `y ↦ −y` | `−1 = 1`: the wheel turns and the car does not |
| the tyres | `t + 1` is a unit, which gives the coordinate `y = t − 1/t` | `t + 1 = t − 1` is nilpotent: no grip, no coordinate |
| the track | the pairing conditions are straight lines `y_i + y_j = 0` | they bend: `t_j t_k − 1 = s_j + s_k + s_j s_k` |

The proof for odd degree drives on all three. At the prime 2 none of them is there.

## 2. The idea: an aeroplane

My reply was an image. The car — or the tank, which had served us for the odd degrees — should be left on the ground. The even case needed *a beautiful light aeroplane called «Grepy is in the Sky», which needs no steering wheel, no grip and no straight, firm ground: that is the even case.*

With it came a few orders: measure first, from the rooftop; then send an outside pilot, in a folder of its own, on a reconnaissance flight; give it a helmet and a jacket, because it is cold up there; have it tell us whether the aeroplane wants a turbine or propellers; it works alone, with no helpers; and keep a diary of how this mission was born.

Before measuring anything, the assistant who audits the project translated the image and sealed the translation:

| the image | what it means here |
|---|---|
| the car / the tank | the proof for odd degree: a linear coordinate, a sign, division by 2 |
| the aeroplane | a method for even degree that uses none of the three |
| no steering wheel, no grip, no straight ground | no inversion as a sign; no division by 2; no linear relations |
| helmet and jacket | memory and time limits, writing to disk as it goes, no helpers, its own folder |
| the reconnaissance flight | no proof asked for: a map of what holds, what fails and where |
| turbine or propellers | a structural method, or a step-by-step induction like §5 of the paper |

In one sentence: do not repair the three broken things; find what is left when they are gone.

## 3. The rooftop

Around 07:30 the auditor measured, with small programs of its own (the longest run took ten seconds). Two things came back.

**What is left is enough.** At the degrees `m = 2^v`, in the coordinates `s = t − 1`, each generator of Degtyarev and Shimada is a product whose lowest part is a clean expression: the shape of the odd case, without the signs. In the seven cells measured, these lowest parts alone already span an ideal of the full dimension, with the same Hilbert function degree by degree. If that holds in general, the curvature of the ground does not matter: only its tangent plane does. *In the image: the aeroplane flies above the ground and looks at it from above.*

**Where that leads.** The problem of the lowest parts turned out to be a count that the paper had left open as its seventh problem: the same count as before, but on a grid with an odd number of values, one of which is its own opposite — «the odd box». It held in 18 cells of 18, over four fields, and the controls that should fail did fail.

So the old side problem of the campaign was not a side problem any more: it was what the even case asked for.

## 4. The two wings

Later the same morning I added two wings. The flight, I said, would rest on the principle of lift and on the laws of air resistance that make turns possible; and *the odd comes before the even, just as cars came before aeroplanes.* If they served, they would be the two pillars of the flight.

Again the translation was sealed before measuring:

- **lift**: the lowest-order problem carries the true one — a rank can only go up when one leaves the special point;
- **the turns**: in characteristic 2, inversion is no longer a sign but an involution `ι` with `(ι + 1)² = 0`, whose leading part is the derivation `E = Σ s_i² ∂/∂s_i`;
- **the odd before the even**: the ideal of the even degree `2^v` lies inside the ideal of the odd number `2^v + 1`, where everything is already proved.

The measurement (six cells, seventeen seconds) said that lift served, that the odd number above did contain the even problem, and that the turn existed: both problems were stable under it, with the same homology. The auditor had bet that this homology would be `1`. It was `3, 3, 3, 15, 19, 37`, and we did not know what those numbers meant. That was written down as it was.

The mission went out with the two wings in it.

## 5. The flight

The pilot was a fresh Claude instance with no access to the archive, working in its own folder from the mission alone. It was given a name, **Grepy Skies**, and it flew in the morning of 2 October, writing its report to disk as it went.

It landed before noon with two documents — a report of 374 lines and a proof of 322 — and forty program runs, none of them stopped by the memory guard. It claimed two things: a proof by hand of the odd-box count for every odd box, every field and every dimension; and a proved reduction of every even degree to that count. Together with the paper, that meant the conjecture for every degree. It graded its own work honestly: *proved by one pilot in one flight, read by nobody else.*

It also judged the wings, with no stake in them:

- **lift carried weight**: it is the step that takes care of the prime 2;
- **the odd before the even carried weight, one step lower than proposed**: the proof uses the odd number *below*, through the identity `D_r(a, b) = b^{r−1} − a·D_{r−1}(a, b)`, which drives every construction;
- **the turn was decorative so far**: true, and it gives no bound.

And it answered the question about the engine with an image of its own: *a propeller aeroplane with a small turbine in the nose, used only to take off from the root.*

## 6. Two readings before any belief

Nothing was believed on one reading.

**The same hour**, the auditor checked by hand the smallest odd box, case by case, and by its own code; the step for the prime 2; and the key lemma. Two things already followed from the part checked: the old «bone» at the smallest box, for every dimension, and the conjecture for the Fermat quartics in every even dimension.

**In the afternoon**, the auditor wrote a full cold audit, every step in its own words, with new code: 163 interlaced pairs of 163 with equality, 12 530 memberships with no failure, 51 down-sets of 51, and the reduction recomputed from the literal generators of Degtyarev and Shimada with another program. It also checked the conjecture itself, in their own literal ring, at six degrees outside their published list, `(n, m) = (4, 14), (4, 18), (4, 20), (4, 28), (4, 30), (6, 12)`. One of its own controls turned out unable to fail; it was replaced, and that is recorded.

**A second pilot**, Skies 2, read cold with only the two proof documents, version 10 of the paper and the original article of Degtyarev and Shimada. Its single job was to break the proof. Its first line was «holds»: no error and no gap in 29 items, 17 notes of presentation. It had re-derived the translation from the original, and found things neither the first pilot nor the auditor had seen. Graded item by item, its «holds» were derivations, not stamps.

Only then was the claim registered as proved: modulo Pham's theorem and [DS, Theorem 2.2], read by two, and not yet checked by a machine.

## 7. The machine

That evening version 11 of the paper was written (77 pages). It was not published. The decision was to put the proof through Lean first, and to publish only with the machine-checked proof inside.

The algebraic chain was cut into twenty pieces, each written as a precise statement, tested by brute force before it was sent (33 731 checks in all, with negative controls that fire), proved by Aristotle (Harmonic), and then downloaded, compiled and read line by line against the paper on our own machine. The first piece went out on 2 October at about 13:00; the last came back on 3 October at 16:51 — about 28 hours for the twenty.

Formalizing did more than confirm. Three times it shortened the proof:

- Aristotle found that one lemma needed no hypothesis on the size of the box at all;
- writing the pieces, the auditor proved one step through the chain of options itself, instead of through the paper's count;
- and the hardest piece, which the paper had done in an exterior algebra with divided powers, became a **rank-two update of a bordered Pfaffian**, found by the auditor while another piece was compiling; version 12 prints that shorter proof.

At the end, the final theorem `EvenAll.mainTheorem'` states, for every degree `m ≥ 1` and every `k`, that the quotient of the group ring by the generators of Degtyarev and Shimada is free over the integers of the predicted rank, with no unproved step and no axiom beyond the three standard ones of Lean. The pieces for the even degrees add 120 files, 20 117 lines and 922 theorems to the 113 files of the odd degrees; the whole project, rebuilt from source on our machine in 3 h 40 min (all but four modules of numerical checks, which the certificate declares), has 233 files, 41 243 lines and 1 859 theorems. The topology — Pham's theorem and [DS, Theorem 2.2] — is cited, not formalized.

## 8. More readers, then the release

Three more cold readers read what was new before anything was published: one the printed text of version 11 («holds», 18 notes), one every passage new in version 12 («holds», 17 notes, and one observation that went into the paper), and one the Lean certificate, with the compiled project in its hands («holds as far as I can check», nine findings, none about a proof). A literature search on 3 October, in the original papers, found nothing that already claimed these results.

Version 12 and the Lean project went to Zenodo on the night of 3 to 4 October.

## 9. What belongs to whom

- **Degtyarev and Shimada**: the conjecture, and the criterion that turns it into algebra. Everything here stands on it.
- **The author**: the question of why the car stops; the aeroplane, which gave the point of take-off — look at what is left when the three broken things are gone; the two wings, two of which carried weight; the rules of the flight; and the decision to put the proof through a machine before showing it.
- **The auditor** (Grepy Chats, and from the evening of 2 October Grepy Mandalay): the rooftop measurements, the translation of the images, the mission, the cold audit, the writing of versions 11 and 12, and the design of the twenty Lean pieces.
- **Grepy Skies**, the pilot: the engine of the proof — the shapes with a mark, the interlaced pairs, the bordered Pfaffians. The image gave the direction; the proof was built by the pilot.
- **Skies 2, Grepy Tinta, Grepy Lupa and Grepy Sello**, the cold readers; and **Aristotle**, which proved the Lean pieces.

## 10. The runway

The method that closed the even degrees had been built over the two months before, for the odd degrees: peeling one variable at a time, down-sets of partitions, options that form a chain. The even case is the same machine on a grid with one zero. The image said where to point it, and the rooftop showed in seven cells that it was the right place. What had to be invented that morning — the mark on a shape, and the Pfaffians that carry it — the pilot invented.

The proof was then read by two readers the same day, by three more before release, and checked by a machine in twenty pieces.

## Where to look

- The mission, the proof and the pilot's report: [pilot-proof_grepy-is-in-the-sky/](pilot-proof_grepy-is-in-the-sky/MISSION.md)
- The auditor's cold audit: [auditor-cold-audit_regla301.md](auditor-cold-audit_regla301.md)
- The second pilot's reading: [../cold-readings/14_skies-2_on-the-odd-box-and-even-degrees/](../cold-readings/14_skies-2_on-the-odd-box-and-even-degrees/REPORT_COLD.md)
- The rooftop and the two wings, with their logs: [engines-new-cells/](engines-new-cells/)
- The Lean proof: [../../lean/README.md](../../lean/README.md)
- The paper, version 12: [../../paper/THE_CHAISE_LONGUE_THEOREM_v12.pdf](../../paper/THE_CHAISE_LONGUE_THEOREM_v12.pdf) — §8 and §9 for the proof, §14.8 for Lean
- The whole campaign, in short: [../../THE_STORY_AND_THE_NUMBERS.md](../../THE_STORY_AND_THE_NUMBERS.md)

---

*This note was written with the AI assistant that kept the diary of those days. The work used AI systems throughout, as the paper discloses, and it has not been refereed by a human expert.*
