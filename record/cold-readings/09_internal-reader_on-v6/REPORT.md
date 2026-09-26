# Internal cold reader on PAPER_OFICIAL_v6 (new parts §6, §7, §10, §11) — 2026-09-25, read-only subagent

**VERDICT: HOLDS.** I found no FATAL, GAP or mathematical ERROR in §6, §7, the headline chain, §10 or §11. There is one citation ERROR and a list of PRESENTATION items.

**What I re-derived by hand**
- **§6:**
  - Lemma 6.1: CRT splitting over F̄_p.
  - Lemma 6.2: the factorisation φ(u)=(u−1)^{q−1}Π_{ξ≠1}(u−ξ)^q, and (u−ξ₀)^q=0 in R_c via Frobenius.
  - Lemma 6.3 and Prop 6.5: compatible matchings form the product set P×Π_ζ σ_ζ. The factor t_{k0}−1 lies in the block of k0. Lemma 6.4 then gives a pure-tensor ideal.
  - Lemma 6.6, both cases: 0∈𝒞₁ matches Lemma 5.2 and Thm 5.3 with relabelling; 0∉𝒞₁ is V_{∅}.
  - Lemma 6.7: t_it_l−1=(x_i−z_l)(1+z_l)^{−1}, and both phantom orientations.
  - Lemma 6.8: the coupling through w₀ is correct. Non-0 blocks satisfying their condition have product 1, so w₀ depends only on the block containing 0. Phantom: the multiset of ξ equals the multiset of η plus {Πξ/Πη} iff the multiset of η is contained in that of ξ.
- **§7:**
  - Binomials C(q−1,t)≡(−1)^t mod p.
  - Residue shapes, chain Lemma 7.3 and (7.1).
  - All nine cases of Prop 7.4, including MR and AR. The product order splits the comparison into one bracket per component, so δ−δ̃≤1 per component and no parity is needed.
  - The borrowed (T), (5.2), (a), (b), (c), (e2) use only weak dominance: no parity and no cap. I checked each proof in §5.6.
  - Prop 7.5 (α)/(β)/(γ): the slice index is q−F, the degree bounds hold (≤q−1), and the top coefficient is ±C(q−1,r−1)·G.
  - Theorem 7.6, Lemma 7.2, Corollary 7.8.
- **§10:** Lemma 10.4 (the 8-residue table, the sign bijection, M·s(a)=δ(a) on a=1,2,4,3, det M=81), the (H4) proof, Lemma 10.1, and the (i)/(ii) logic. **§11:** proof of W(ii).
- **Headline chain:** §2 + Cor 5.4 + Prop 6.9 + Thm C, with Thm 0(d) for p∤m, is complete for odd m and k≥1. k=0 is trivial.

**Computations (all under 130 MB, each under 30 s)**
- §3 table: Q_k(q) reproduced exactly. Q₂(15)=32900, Q₂(21)=102800.
- N_bal: 3, 15, 93, 639, 4653 and 15, 45, 91, 153, 231. Also 7885 and 11713.
- Lemma 6.8: brute-force |Γ| equals the block-product sum at (m,n) = (15,2), (21,2), (45,2), (33,2), (35,2), (15,4), for both primes of each m. This is 12 sums, all equal.
- Prop 6.5, directly in Singular over F₇ at (k,m)=(2,21) on four colourings. The literal ψ_J images in R_c gave 546, 1645, 546, 630. Predicted: 6·91, N_bal(3,7), 6·91, 7·90. All exact.
- Compatible-colouring counts: 61/19 (k=1) and 1001/141/3301 (k=2) all match §12.3.
- Theorem C over F_p: I^bal = 3, 15, 93 (q=3), 45 (q=5), 91 (q=7); I^ph = 15, 93 (q=3), 45 (q=5), 153 (q=9). All equal N_bal/N_ph.
- Theorem C in characteristic 0 (mod 1000003): I^bal = 4, 24, 129 and I^ph = 18, 126, matching Remark 7.9(2) and §12.4.
- Prop 7.4, the chain and membership: exhaustive at q=3,5,7,9, α+β≤9 (9712 comparable pairs, 0 failures). P1 by brute force (4260 tails, 0 failures).
- Theorem 7.6 on every down-set at (q,α,β) = (3,2,1), (3,2,2), (3,3,2), (3,3,3), (3,4,2), (5,2,1), (5,2,2), (5,3,2): 0 failures, equality in all 52.
- |𝔅| for all 17 cells of Remark 10.3 and Lemma 10.4 (216, 8000, 834, 1572, 2142, 6204, 19584, 78260, 185280, 543220; zero defect at the six cells listed): every number in the paper confirmed.
- Singular: (2,9) gives 5120; Fact 9.2 gives 4730, and |Γ_K|=4736 by enumeration. The q=3, k=2 subfamily scan gives 800 failures, worst deficit 2, 0 violations of ≤.

**Findings**

1. **PRESENTATION / near-GAP** — Cor 7.8 (l.642), Prop 6.9 (l.531), (6.1) (l.460).
   - (6.1) comes from Prop 2.1 and Theorem 0, which are stated only for n=2k≥2 (l.138).
   - Cor 7.8 sets n:=2a "for every a≥0", so a=0 gives n=0.
   - Fix: state k≥1 in §6 and Prop 6.9. In Cor 7.8 take a≥1, and dispose of a=0 directly: I^bal₀=F has dimension 1, I^ph₀=F[x]/(x^q) has dimension q.

2. **PRESENTATION** — Prop 5.8 (l.385) and Prop 7.5 (l.615, 622) write "F := F_Λ(μ)" while F is the field. In l.622, "≠0 in F" refers to the field inside the same proof. Rename the count (e.g. f or Φ).

3. **PRESENTATION** — symbol overload.
   - Z_r (l.481) clashes with the point sets Z_Λ and with Z.
   - "Block" means a colour block (§6.3), a column block B_c (§5.2, §7.2), and B=𝒞_{ζ^{-1}} (§6.5); B is also the box ring of §2.
   - R means the ring R, R_c, R_{A,B} and R_a(G).

4. **PRESENTATION** — a and a′ swap roles. In §1.5 (l.86) a′ counts the x-variables; in Lemma 6.7(iii) (l.515) a=|A*| counts the x-variables and a′ the z-variables. Unify.

5. **PRESENTATION** — abstract (l.17) calls the colour-1 blocks "instances of Theorem B". When 0∉𝒞₁ the block is V_{∅}, an instance of Theorem 5.3, not the root; l.49 says it correctly.

6. **PRESENTATION** — Lemma 6.2(iii) and (6.2) (l.474–476) write π_c(ψ_J); it should be π_c(ψ̄_J).

7. **PRESENTATION** — the definition of N₁(c) (l.504) does not require w₀≠1, which Lemma 6.8 condition (1) needs. It is automatic: if w₀=1, the other 2k′−1 entries would form a closed multiset of odd size in μ_q∖{1}. Add that sentence.

8. **PRESENTATION** — l.561 says r̄_j and r̲_j are "of §5.2 and §5.5"; they are defined only in §5.5.

9. **PRESENTATION** — l.599: the facts borrowed from §5.6 are correct as used, but the reader has to re-audit §5.6 to see that parity and the cap are not used. Extract (T), (5.2), (a), (b), (c), (e2) as one lemma on arbitrary partitions, and cite it from both 5.6 and 7.4.

10. **PRESENTATION** — Cor 7.8 (l.642) calls the colour-1 coordinate "k₀", a symbol that depends on J. Rename it.

11. **PRESENTATION** — Remark 7.9(3) (l.646) peels z_{a+1}, but Lemma 7.1 is stated for an x-variable. Cite the x↔z symmetry of Thm 7.6.

12. **PRESENTATION** — Remark 7.9(2) (l.645) says the integral bipartite quotient "has p-torsion" as a general statement. It follows only where dim_Q > N_bal is known (the computed cells, via Cor 7.8). Restrict the claim to those cells.

13. **ERROR (citation)** — [Jum] (l.1157) is given as "arXiv:2608.18134 (28 July 2026)". An identifier starting 2608 is an August 2026 submission. Check the identifier and the date.

14. **PRESENTATION / verify** — [AMV]: l.33 says AMV computed the quartic and quintic fourfolds. Remark 10.2 (l.720) says the k=1 closed forms "agree with the rows of [AMV, Table 1]", and §13.3 (l.835) points to the same table. Confirm that Table 1 has surface rows, or drop the claim.

15. **PRESENTATION** — Remark 10.2 (l.720) calls the k=1 discriminants "known in closed form", but the source is the unrefereed [Rep]. Match §14's "cited, not proved here". The formulas are internally consistent: the exponents sum to 3(p−3)², and m=5 gives 10+2=12.

16. **PRESENTATION** — the abstract (l.11) promises a "free complement of explicit rank". The rank is |𝔅|−Q_k(m), and |𝔅| has a closed form only for m=9. Say "of rank |𝔅|−Q_k(m)".

17. **PRESENTATION** — §13.3 (l.835) asserts without proof that |disc Hdg(X)| is a power of p. The sketch needs two things: 𝔅 stable under α↦−α, so that e_𝔅 is self-adjoint for the G-invariant form, and the h^k line. Either prove it or drop "independently".

18. **PRESENTATION** — the process narrative (§1.8, §12.6 l.808–819, acknowledgements l.857: "constructor", "auditor", AI readers, session counts) is not journal material. Move it and §12 into a short supplementary note. Keep the one-line AI disclosure.

19. **PRESENTATION** — l.104 restricts "p odd prime, q=p^v" to §2 and §9. §5 and §6–§7 also use it with q=p^v; say so there.

Nothing found in §11 or §14 that claims more than the proofs give. W(i) is correctly flagged as depending on [DS, §4.6], which the paper does not re-derive.

All scripts and logs are in `/private/tmp/claude-501/-Users-rafa-Desktop-ARBOLYAML/22974bd5-bf02-48be-a403-1d3fb78e7224/scratchpad/coldreader/`. No other file was touched.
