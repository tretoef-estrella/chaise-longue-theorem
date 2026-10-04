# Where to attack

We believe the proof is correct. If it is not, the error is most likely in one of the places below, and we would rather hear about it than be agreed with. This page names the load-bearing joints ourselves, in the order in which we would press on them; it follows §14.7 of the [paper](paper/THE_CHAISE_LONGUE_THEOREM_v12.pdf) (version 12).

## 1. The case analyses

**Proposition 5.6 (P2)** and **Proposition 7.4** are the only arguments in §5–§7 that are not one-line identities; §8 has its own (section 6 below).

- *(P2)* says that when a tail partition $\mu$ is dominated by $\tilde\mu$, every new option of $\mu$ is dominated by the corresponding option of $\tilde\mu$; this is what keeps the layers of the induction down-sets. Try long, very uneven partitions at $q = 3$ ($h = 1$) and at $q = 9$ ($h = 4$), where the lengths hit the cap $\ell \le h$.
- *Proposition 7.4* is the same statement for pairs of partitions, with nine cases. Look hardest at the cases **AR** and **MR**, where the removal of a box from one pair of partitions is compared with an option of another kind in the other.

Machine check of both, on every comparable pair of every cell small enough: `engines/v7-verification/theorem-b-and-translation/regla269_p2.py` and the `gateP.log` of [`engines/composite-degrees-auditor/`](engines/composite-degrees-auditor/). Zero failures; but a machine check of finitely many cells is not a proof, and the proof is the text.

## 2. The translation (§2)

Everything rests on reading [DS] correctly. Check the conventions: $j_0 = 0$; the variable $t_0$ never appears; $N = 2k + 2$; and **Lemma 2.4**, the identity $\bar\psi_J = \text{unit}\cdot Y \cdot D_J$ that turns the group ring of [DS] into the sum form (S). One of our readers audited the proofs inside [DS] from the source of arXiv:1405.4683v3 and found them sound for every $m \ge 3$ and every even $n \ge 2$ ([record/cold-readings/03_fable-3_on-v3/](record/cold-readings/03_fable-3_on-v3/REPORT.md)).

A cheap test of the signs: with $1 + t$ in place of $1 - t$ in $\psi_J$, the rank at the cubic surface would be $20$ instead of $7$.

## 3. The colour reduction (§6)

- **Proposition 6.5**: on a compatible colouring the surviving generators are pure tensors along the colour classes. This is where the full family of matchings is used in the composite case, as Lemma 5.2 is in §5.
- **Lemma 6.8**: the index $0$ couples the blocks only through $w_0$.
- **Corollary 7.8**, whose proof passes through the sum over the colourings.

The Fermat fourfolds of degree $15$ and $21$ were computed colouring by colouring from the literal generators of [DS], at both primes, independently of §6–§7 ([HOW_TO_VERIFY.md](HOW_TO_VERIFY.md)).

## 4. The places with no slack

The coverage formulas **(5.1)** and **(7.1)** and the lifting **Propositions 5.8** and **7.5** have no room to spare: tightening the slice by one makes them fail, and the negative controls confirm it ($604$ failures at $(q, m) = (9, 7)$; $17$, $58$, $10$ failures in the bipartite cells). An off-by-one here would be fatal.

## 5. What is quoted

- **Theorem 0.** Only parts (a), (c) and (d) are topological; part (b), which carries every upper bound of the paper, is a Chinese-remainder count, re-proved in Appendix B. Appendix B reduces the rest to **Pham's theorem** and the **intersection numbers of [DS, Theorem 2.2]**, which we quote.
- **Corollary H** uses the classical description of the Hodge classes of $X$ (Shioda–Katsura, Shioda, Ran) and **Aoki's Theorem A**, quoted and not re-proved. For prime $m$ and for $m = 4$, (H4) and (H4′) replace Aoki and are proved in §12.1.

## 6. The odd box (§8)

- **Lemma 8.4, part (D2), in the case $\nu_j = 1$**: that the layers of an interlaced pair are interlaced pairs.
- **Lemma 8.7′** and its ingredients: the identity (8.6), the two operations of Lemma 8.8 and the powers of $\zeta$ in Corollary 8.9. All of them are also proved in Lean (pieces E8–E10 of [lean/](lean/README.md)).
- **Proposition 8.10**: the case (M) with $\delta = 1$, where two Pfaffians are combined so that the terms with $D^-(y_1, \cdot)$ cancel, and the case (Z) with $\delta = 1$, where Lemma 8.7 is used.

## 7. The even degrees (§9)

- **Step 2 of Proposition 9.2**: the leading forms at $m = 2^v$.
- **§7 read with an even $q$**: the only use of the field is $C(q-1, r-1) \ne 0$ in case (γ) of Proposition 7.5.
- **Lemma 9.9** (the substitution $u = -t$) and **Lemma 9.10** (the map $\theta$).
- **Lemma 9.6**, where the index $0$ is a coordinate of the count but not of the ideals.

The whole algebraic chain of §8–§9 is also proved in Lean, and a separate reader of the Lean certificate followed it in the sources step by step ([record/cold-readings/](record/README.md), reading 17). A mistake there would therefore have to be in the statement, not in the proof: compare the Lean definitions with the paper and with [DS] in §1.2–§1.3 of the [certificate](lean/LEAN_CERTIFICATE_CHAISE_LONGUE_v2.pdf).

## 8. Mistakes we made and caught — so that you do not make them again

- **Do not identify the conjecture with the count $A_k(q) = P_k(q)$** (Theorem A). We did, for weeks; the identification is false for families of matchings (§11, Fact 11.2). The day we found it is told in [THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md).
- **Do not lift from $q$ to $3q$.** Every «tower lift» strong enough to close the problem is equivalent to the conjecture itself; the proof in the paper works for every box at once.
- The complete list of dead routes, with the reason each one died, is the [Cemetery](archive/CHAISE_LONGUE_CEMENTERIO_LIVE_v502.md).

If you find something, please [open an issue](https://github.com/tretoef-estrella/chaise-longue-theorem/issues) or write to tretoef@gmail.com. A precise counterexample, with the cell and the number, is worth more to us than any amount of agreement.

---

[README](README.md) · [Theorems](THEOREMS.md) · [How to verify](HOW_TO_VERIFY.md)
