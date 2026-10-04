# Grepy Skies, mission 1 — the auditor's FIRST PASS (2 October 2026)

Auditor: Grepy Chats. This is a first pass, not the cold audit. The cold audit (every step rewritten in my own words, every case of §2 and §6 of the proof) is owed.

Files audited (copies here, with `MANIFEST_md5.txt`): `REPORT.md` (md5 `993bfbbd…`, 374 lines), `PROOF_ODD_BOX.md` (322 lines), `checks/`.

## What the pilot claims

1. **Theorem O:** the lower bound of the odd box, `dim (D_{r,J} : J)·F[y_1..y_{2k+1}]/(y_i^r) ≥ N_r(2k+2)`, for every odd `r`, every field, every `k` (problem 7 of §13 of paper v10).
2. **Proposition B5:** Conjecture 1.2 at an even degree `m` follows from the odd box at `r = p^v` in characteristic `p` (odd primes of `m`) and at `r = 2^v − 1` in characteristic 2.
3. **Theorem E:** hence Conjecture 1.2 for every even `m ≥ 4`, every `k`; with paper v10 (odd `m`): **for every `m ≥ 3`**.
4. Independent of the rest: no 2-torsion for `m ≡ 2 (mod 4)` (Corollary B3′); and an elementary proof for `r = 3` (Theorem T3), which gives `m = 4, 6, 12`.

The pilot's own grade: «PROVED by one pilot in one flight, read by nobody else».

## What I checked today, and how

| Piece | How | Result |
|---|---|---|
| **Theorem T3** (`r = 3`, every field, every `k`; `PROOF_ODD_BOX.md` §8) | By hand, every case: the count of completions (3, 2, 1, 0), Cases I, II, III with their sub-cases, the two identities `y_c² = y_1(y_c − y_1) + D(1,c)` and `Δ(a,b,c) = D(1,a)(y_c−y_b) − D(1,b)(y_c−y_a) + D(1,c)(y_b−y_a)`, the parities of the generators of each `I(m−1, ·)`, the boundary cases `J = 0`, `J = m−1`, `J = m`. | **Correct.** I found no gap. |
| T3, by my own code | `corpus4/regla298_sky/auditoria_T3.py`: for `p = 2, 3`, `m ≤ 5`, every `J`: `dim I(m, J)` against `|Z_J^{(m)}|`, and every slice containment of the proof as an ideal membership. | **40 ideals of 40**; equality of dimensions in all (`auditoria_T3_5.log`). |
| **Step B2** (the prime 2 at `m = 2^v`: Conjecture 1.2 follows from the odd box at `r = 2^v − 1` over `F_2`) | By hand: the four steps (the Fact; `dim I = dim in(I)`; `in(I) ⊇ (L_J)`; `b(a+b)^{q−1} = ab·D(a,b)` modulo `b^q`, so `L_J = Y·D_J` and multiplication by `Y` embeds the box `q − 1` in the box `q`). | **Correct.** It is the rooftop reading of this morning, now with proof. |
| **Lemma 5.1** (the Pfaffian lies in the ideal; the «turbine») | By hand: `Ω_{2σ+1} = J_σ` (signs), `ω_{r−2} = B`, `ω_{r−1+i} = b^i D` in the box, `J(ζ) = E(ζ) ∧ O(ζ)`, `γ_n(J(ζ)) = 0`, the induction of Lemma 5.2 (powers of `ζ`), Corollary 5.3 (a) and (b), and the conclusion for `ℓ ≥ 1` and `ℓ = 0`. | **Correct as far as I read it.** Not re-derived by me: the dictionary (5.1)–(5.2) and the Laplace expansion (F7) with their signs, which are standard. |
| The identity of Remark (3) at `r = 3` | By hand. | Correct. |

## What follows from the part I checked

- **(a) The bone at `q = 3` for every `k`.** T3 in characteristic 3 at `(m, J) = (2k+2, 0)`: `dim Σ_J σ_J·B ≥ T(2k+2) = P_k(3)`, `σ_J = Π (x_a + x_b)^2`. This is «`dim W ≥ P` at `q = 3`», the single open box of the campaign from informe 66 to informe 95 (`L6`), and problem 7 of paper v10 at `r = 3`. One page, elementary.
- **(b) Conjecture 1.2 for Fermat quartics (`m = 4`) in every even dimension:** T3 over `F_2` + B2 + the count B1 + the Fact (paper, Proposition 2.1; [DS] Theorem 1.1(a), valid for `m ≥ 3`). B1 I have read (short) and measured this morning in my own cells; I have not rewritten it.

Grade I give to (a) and (b): **first pass positive, by hand and by my own code.** Not yet «proved» in the register: the item-by-item write-up is owed.

## Not audited yet

- §2 of the proof: shapes, interlaced pairs, the chain (Lemma 2.3), the layers (Lemma 2.4, in particular (D2) with `ν_j = 1`), and its use of Lemma 5.5 and Proposition 5.6 of the paper.
- §3: the bordered Pfaffians (F1)–(F7).
- §6: Proposition 6.1, seven cases (the pilot points at (M) with `ε = 1` and (Z) with `ε = 1`).
- The reduction for even `m` that is not B2: Lemma B.0, B3 (Theorem C of the paper at an even box in characteristic 2, re-read by the pilot, measured at 15 roots), B3′, B4 (the block of colour −1), B5.
- None of the pilot's 40 runs re-run by me, except through my own cells of this morning (the odd box at 18 cells; the leading forms at 7 cells), which agree with his.
- Literature: nobody has searched whether the odd box or the even degrees are proved elsewhere. Degtyarev (arXiv:1512.06199, Conj. 4.4) had the conjecture open; not re-checked today.

## If the whole of it holds

Conjecture 1.2 of Degtyarev–Shimada for every degree `m ≥ 3` and every even dimension; problem 7 of paper v10 closed; and whatever Hodge-type corollaries the literature allows for even degrees (Fermat quartics first), **to be read in the original before a word is written**.

— Grepy Chats

---
**Note of 2 October 2026, afternoon (Grepy Chats).** The cold audit announced above is written: `VIVOS/MISIONES_TRAS_BARRIDO/regla301_auditoria_fria_skies.md`. Every item is marked CORRECT there, and the auditor's own gates pass. The result is still not registered as proved: the second reader («Grepy Skies 2», folder `~/Desktop/GREPY_SKIES_2_COLD_READER/`, mission copied in `VIVOS/ATAQUES_Y_REPORTES/GREPY_SKIES_2_COLD_READER/`) has not reported yet.
