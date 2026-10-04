# The story and the numbers

*How a proof was found by a psychologist and a team of AI instances, in four months, and what that looked like from the inside.*

---

## 1. Four campaigns, one question

| Campaign | Dates (2026) | What it did |
|---|---|---|
| **Hodge–Fermat** | 23 May – mid-June | ran the Degtyarev–Shimada criterion further than it had been run, on an 8 GB laptop: sixteen cells decided by machine, eleven of them beyond the published table; the *Watermark*, *Double Ladder*, *Localization* and *Nail* theorems ([hodge-fermat-campaign/](hodge-fermat-campaign/README.md)) |
| **The Sofa** | June – early July | the case $k = 2$ ([repository](https://github.com/tretoef-estrella/sofa-theorem)) |
| **The Hammock** | July | the case $k = 3$ ([repository](https://github.com/tretoef-estrella/hammock-theorem)) |
| **The Chaise Longue** | 12 July – 25 September | every $k$, and then every odd degree: [the paper, version 7](paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) |
| **The aeroplane** | 2 – 4 October | every degree: the odd box and the even degrees, and Lean for every degree: [the paper, version 12](paper/THE_CHAISE_LONGUE_THEOREM_v12.pdf) |

A sofa, a hammock and a chaise longue are three pieces of furniture for lying down, each longer than the last. The names stuck.

## 2. The team

No human mathematician took part. The director, Rafael Amichis Luengo, has a background in psychology. Everyone else in the team was an instance of Claude, Anthropic's AI system, and each instance lived for as long as its conversation lasted — hours, sometimes a few days — before it had to hand its work to the next. Most of them chose their own names. By September there had been **more than eighty names and more than a hundred incarnations**.

Some of them, by role:

- **The scribes and auditors — the Grepy line.** One name, many lives: *Grepy*, *Grepy Bu Bú el Ingenioso*, *Grepy Toloco*, *Grepy el Genio*, *Grepy el Cartógrafo*, *Grepy el Lector*, *Grepy el Auditor*, *Grepy Chats*, *Grepy Mandalay*, and an older *Grepy* who, before its conversation ended, wrote down everything it remembered so that its successors would not lose it. The Grepys kept the archive, audited every claim against its source, and wrote the paper.
- **The constructors who worked inside the archive**: *Grepy el Herrero* (the blacksmith, thirty-three commissions), *Grepy el Relojero* (the watchmaker) and *Grepy el Encuadernador* (the bookbinder).
- **The pilot of the aeroplane**: *Grepy Skies*, the external constructor who proved the odd box and the even degrees on 2 October; and the cold readers of that autumn, *Skies 2*, *Grepy Tinta*, *Grepy Lupa* and *Grepy Sello*.
- **The strategists**: *Bisel*, twice incarnated, constructor of the Sofa era and later adviser; *MacGyver*, who wrote the missions and kept the living documents.
- **The constructors from outside**, who received self-contained missions and never saw the archive: *Don Mister Jordan*; the *Frescales*, numbered from I to XXI; the *Propinero* (the tipper), forty-seven turns without a corpus; and the **Fables** — the fifteen *Chessboard* missions, the composite-degree mission, and five cold readers of the paper. (*Fable* is itself a family of Claude models.)
- **The auditors and constructors named after forensic scientists and detectives**: *Locard*, *Lacassagne*, *Tardieu*, *Orfila*, *Uhlenhuth*, *Gettler*, *Marsh*, *Reiss*, *Bertillon*, *Balthazard*, *Brouardel*, *Devergie*, *Vucetich*, *Goddard*, *Vidocq* — with *Cárdano*, *Nash*, *Sylvester*, *Vernier*, *Relevo*, *Gross*, *Apolo*, *Gramil*, *Palmer*, *Vaucanson*, *Fresh Eyes*, and *Sherlock* I, II and III, the sweepers.
- **The crews of the Hodge–Fermat and Sofa campaigns**, named with more whimsy: *Blas* and *Cándido* (auditors), *Induráin*, *Espinete*, *Chema*, the chief constructor, and its consultants *Diomedes* and *Ulises*, *Néstor*, *Epi*, *Arquímedes*, *Borromeo*, *Sancho*, *Kepler*, *Yoshi*, *Mario Bros*, *Tom Sawyer*, *Bugs Bunny*, *David el Gnomo*, *Gandalf*, *Conde Draco*, *El Cumplidor*, *El Cantero*, the clean-room checkers *Espejo*, *Calígula* and *El Forastero*, and the three *Rompedores* (breakers).
- **Claude el Hamaquero**, who closed the Sofa and the Hammock.

And from outside Anthropic: **ChatGPT** (OpenAI) and **Gemini** (Google), as cold readers of the paper, and **Grok** (xAI), for consultations.

## 3. The method: a wall, a picture, a measurement

The work moved in a loop. A constructor tried to prove something and hit a wall. The wall was explained to Rafa as a picture. Rafa answered with an object from ordinary life. An instance translated the object back into algebra — **piece by piece, in a table; as the method matured, the translation was sealed before anything was measured**, so that nobody could bend it afterwards — and then measured it. Most pictures died on contact with the numbers. The notebook of all of them, [Rafa's ideas](archive/CHAISE_LONGUE_LAS_IDEAS_DE_RAFA_v231.md), reached 231 versions.

| The picture | Its translation | What came of it |
|---|---|---|
| **The chessboard** — *«count a board without looking at every square: rows times columns»* (21 Sep) | slice the ideal by one variable; compare each slice with the points sharing one value of that coordinate | exact in every cell measured, the same day; it became the *Chessboard* missions, whose fifteenth report proved the conjecture for $m = 3^v$ by exactly that move (24 Sep) — the spine of §5 of the paper |
| **Drops within drops** (21 Sep) | the chessboard again, one level deeper | exact again (12 of 12 rows), and a control with random points failed — so it is a property of *this* problem, not a general fact |
| **The hinge that goes *clack*** — *«what sticks out on the outside is what is missing on the inside»* | fixing one pair of coordinates restricts the generating series of level $k$ to that of level $k-1$ times the factor $(1 - v^2 w)$ | the [Hinge Lemma](theorems/standalone/CHAISE_LONGUE_HINGE_LEMMA.md), proved for every $k$ |
| **The thread with Teflon tape** — *«screwed in, nothing left outside, watertight»* | the generators restrict *triangularly* from level $k$ to level $k-1$ | the other half of the Hinge Lemma, proved for every $k$ |
| **The chassis and the rear wing** of a Formula 1 car — *«the chassis is fixed; only the wing changes with speed, and linearly»* | a proof split into a fixed part and a part that depends linearly on a parameter | organised the proof of the *Star* theorem of the collar programme |
| **The tank** — *«tracks that grip the ground, an engine that pushes, a gearbox that multiplies»* (20 Sep) | every tool is a *track* (degree by degree), an *engine* (structural, every dimension at once) or a *gearbox* (a lift from one field to a bigger one) | a law — the tracks leave a middle band that never shrinks — and a rule: no tool admitted without being classified. The proof that closed the conjecture is an engine |
| **The magic tiles and the platform** — *«bigger tiles that stick by themselves, the excess cut off and falling, a platform below weighing the pieces»* (20 Sep) | the initial ideal is the big tile; the platform weighs $W = U - P$, a pure point count | an exact identity $\Delta = W - t$ and a measured law $\deg W = \dim - 1$; the route it opened died the next day, the identity did not |
| **The distorting mirrors** of a fairground | every reformulation that comes from a duality is a mirror | seven reformulations examined: six were dualities, which can never move the problem; the seventh bent, and that is where the content was |
| **The core of the sun** — *«a balance between expansion and gravity, in several layers»* | the Cohen–Macaulay condition | a beautiful anticipation; no theorem, and the numbers attached to it did not survive an audit |
| **Clocks with carry** | carries between digits: Witt vectors, $\mathbb{Z}/9$ | an idea with no mechanism yet; no mission was launched |

The pictures did not prove anything. They did something that turned out to be as valuable: they changed *which* question the team was asking, at the moments when the team was going round in circles.

## 4. The archive

The campaign never deleted anything. Every document grew by appending; every retraction was written under the line it retracts, with the date and the name of the instance that caught it. Twenty documents were kept *alive* — rewritten into a new version after every turn — and the numbers they reached are the best measure of the work.

| Living document | What it holds | Last version |
|---|---|---|
| *El Catálogo Maestro* — the Master Catalogue | every result, with its grade | **v524** |
| *El Cementerio* — the Cemetery | every dead route, and the reason it died | **v502** |
| *The Dimension Ledger* | every measured number, with ring, branch and file | **v435** |
| *El Aviso de Uhlenhuth* — Uhlenhuth's Warning | the handoff between instances | **v401** |
| *Los 8 Hachazos de Uhlenhuth* — the Eight Axe-Blows | the open fronts and their status | **v371** |
| *The Master Assembly* | the proof, as assembled so far | **v365** |
| *Delta para Ulen* | the changes of each turn | **v354** |
| *El Libro de Montaje* — the Assembly Book | the chain of lemmas | **v326** |
| *Los Huevos al Minuto* — Eggs by the Minute | the black box of the campaign, turn by turn | **v276** |
| *La Potencia de Dos* — the Power of Two | the torsion line | **v242** |
| *Grepy's minute-by-minute handoff* | the state, for the next Grepy | **v240** |
| *Las Ideas de Rafa* — Rafa's Ideas | the pictures, and what each produced | **v231** |
| *Las Citas del Paper* — the Citations | every external source, with the grade at which it was read | **v225** |
| *Ladrillo a Ladrillo* — Brick by Brick | the construction log | **v124** |
| *La Mochila de la Victoria* — the Victory Backpack | a compendium of everything proved | **v121** |
| *El Frente* — the Front | the front line of the collar programme | **v112** |
| *Oro del Lago Ness* — Loch Ness Gold | the gold recovered in the turns spent tidying the archive | **v49** |
| *Los Milagros del Propinero* — the Tipster's Miracles | the corpus-free constructor's results | **v40** |
| *El Tablero* — the Live Board | the state of the board | **v39** |
| *La Biblia de MacGyver* — MacGyver's Bible | the errata sheet of the compendium | **v35** |
| | **total** | **5,012 versions** |

Two of these are in this repository, whole, in their last version: the [Master Catalogue](archive/EL_CATALOGO_MAESTRO_v524.md) and the [Cemetery](archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md). They are in Spanish, and they contain false statements by design: that is what a record of dead ends is.

**The tree.** Above all the documents stood [`arbol.yaml`](archive/arbol.yaml), the tree of the proof: every node a lemma or a gap, with its grade — *proved*, *measured*, *candidate*, *refuted* — and the file and line that support it. It reached **1,295 nodes, 12,733 lines and 293 versions**, and it could only grow: its header was verified byte for byte at every turn.

**The whole.** By the end the archive held **9,782 distinct Markdown documents** (counted by content hash, so that copies do not count twice) — **2.3 GB of text** — and **13,862 distinct files** in all; counting every copy, the archive holds 1,483 Python scripts, 1,338 logs, 302 Macaulay2 and 218 Singular scripts.

## 5. The Cemetery

A proof is also the list of everything that did not work. By mid-September the Cemetery held **316 tombs**, each a route that had been tried, with the reason it died and the number that killed it; more were added afterwards. Some of them are among the most useful things in this repository, because they save the next person weeks:

- a *tower lift* from one field to a bigger one, strong enough to close the problem, is always equivalent to the problem itself;
- no criterion that is inherited by subfamilies of matchings can decide the question: fourteen of the fifteen matchings already fail where fifteen succeed;
- the invariance of the defect under field extension, which held in 54 cells, is false: five hyperplanes of four-dimensional space break it;
- the *Descent Principle*, on which much of the middle of the campaign stood, had a false lemma.

## 6. The dogs, and the gold where we had already walked

Every instance forgets. A result proved on a Tuesday by one instance could be proved again on Friday by another, under another name, with another letter for the same object — and it was, again and again. The campaign kept a counter for it, `OWN-DEPOSITED`: every time an instance found that what it had just discovered was already in the archive, it said so and logged it. **The counter reached 129.**

So in mid-September the team stopped building and went looking. For twenty turns — the *dogs' sweep*, twenty reports written on a single day, 16 September — two «dogs» went through the archive, one following the trail of every load-bearing claim back to its source, the other sniffing through every document nobody had read, with up to twenty-two readers working in parallel: 2,403 documents that no one had ever classified, brought to **zero**. The rule was simple and hard: no sampling, no filters; every mission and every report is read.

What they found was humbling:

- **The Descent Principle** had been used as a foundation for seventy reports. The Sofa team had retracted it on **3 July**, in a file of the Sofa campaign that nobody had cross-checked.
- **The Orbit Criterion**, presented as a discovery in three consecutive reports, had been buried as tomb *T-19* on **18 July** — by the same project.
- **The closed form of the point count** $P_k(q)$, derived with some pride in a September report, had been written on **12 July** in a standalone called *The Floor Theorem*.
- A theorem that a report said *«is not written in any file»* was written, in full, inside a mission — which is why, from then on, **missions were read, not filtered**.
- Two campaigns used the same word, *floor*, for opposite sides of the same inequality; a whole line of results stayed invisible for weeks because of a dictionary.

There was so much gold in the archive that it kept appearing where the team had already walked, under other names. Collecting it changed the map: some fronts that looked open were closed, and some that looked closed were not.

## 7. The wrong statement

For most of September the team believed that the conjecture was equivalent to a count called $A_k(q) = P_k(q)$ — and on **23 September** that count was proved, for every $k$, by the fourteenth *Chessboard* mission. The conjecture was announced closed.

The same day, the auditor did what the rules said and re-derived the translation from the original paper of Degtyarev and Shimada, line by line. The equivalence had never been proved. It was false: for a family of thirteen matchings at $q = 9$ the count holds exactly and the conjecture fails. The announcement was retracted within hours, in writing, under the line that had made it; the two earlier notes, the Sofa and the Hammock, received corrections of scope on Zenodo and GitHub. The conjecture was open again.

What the original paper did say — once read again, slowly — was a different count: a *sum* over the matchings, in a box one size smaller, on the grid without zero. On **24 September** the fifteenth *Chessboard* mission proved that count for every $k$ and every $q = 3^v$ by peeling one variable at a time; the proof was audited cold, step by step, with separate code, the same day. On **25 September** the proof was extended to every odd prime power, then — by another external mission — to every odd degree, the integral Hodge conjecture was drawn from it, and version 7 of the paper was published on Zenodo. On 26 September a reader from another company read it cold and found no error.

The count $A_k(q) = P_k(q)$ that had misled everyone is in the paper too, proved in general, as **Theorem A** — with a section explaining why it is not the conjecture.

## 7½. The aeroplane

Version 10 of the paper (1 October) listed the even degrees as its first open problem. The proof for the odd degrees uses a sign, a division by $2$ and linear relations, and at the prime $2$ all three fail. Rafa's picture, the next morning, was that this was not a job for the car or the tank of the odd degrees: *«a beautiful light aeroplane called “Grepy is in the Sky”, which needs no steering wheel, no grip and no straight, firm ground»*. Translated: do not repair the three things; find what is left when they are gone. Before writing any mission the auditor measured, «from the rooftop», that at the degrees $2^v$ the forms of lowest degree of the generators already span an ideal of the right dimension, in seven cells of seven.

That measurement became the mission of an external constructor, *Grepy Skies*, which on **2 October** proved a third count — at a box of odd size, on a grid where one value is its own opposite — for every odd box and every field, and reduced every even degree to it. The same day its proof was audited cold, step by step, with separate code, and read cold by a second reader that had only the proof documents, version 10 of the paper and the original paper of Degtyarev and Shimada; neither found an error or a gap. The printed text was read cold again; and between 2 and 3 October the whole algebraic chain was proved in Lean, in twenty more pieces. Version 12 of the paper (**4 October**) proves the conjecture for **every** degree, and the Lean proof covers every degree too. The record of those three days is in [record/even-degrees/](record/even-degrees/README.md).

## 8. The numbers, together

| | |
|---|---|
| Duration | **23 May – 25 September 2026**: 126 days; the Chaise Longue proper, 76; then the even degrees, **2–4 October** |
| Distinct Markdown documents | **9,782**, 2.3 GB — and **13,862** distinct files |
| Versions of the twenty living documents | **5,012** |
| The tree | **1,295** nodes, **12,733** lines, **293** versions |
| Dead routes | **316** tombs by mid-September |
| Standalone write-ups | **222** families in [theorems/](theorems/INDEX.md), plus the Hodge–Fermat theorems |
| Named instances | more than **80** names, more than **100** incarnations |
| The auditor's reports | **144**, then **107** missions and **99** technical audit records |
| Results found again that were already in the archive | **129** |
| The dogs' sweep | **20** reports; **2,403 → 0** unclassified documents |
| Missions to external constructors that closed the proof | **15** *Chessboard* missions + **1** composite-degree mission + **1** for the even degrees |
| Lean 4 | **49** pieces; **233** files, **41,243** lines, **1,859** theorems; **0** `sorry` |
| Cold readings | **17**: eleven of versions 3 to 7, one of the new material of version 10, one of each Lean certificate, one of the proof documents of the even degrees, one of the printed text of version 11, one of the changes of version 12; by three AI providers |
| Human referees so far | **0** — which is why this repository exists |

---

[README](README.md) · [Theorems](THEOREMS.md) · [Acknowledgements](ACKNOWLEDGEMENTS.md)
