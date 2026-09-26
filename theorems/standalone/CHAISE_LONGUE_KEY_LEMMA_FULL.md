> **Rafael Amichis Luengo** · tretoef@gmail.com · *The Chaise Longue campaign* · 2026 (date not stated in the document)
>
> Part of the working record of **The Chaise Longue Theorem** — [the paper](../../paper/THE_CHAISE_LONGUE_THEOREM_v7.pdf) · DOI [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150) · [index of all standalones](../INDEX.md)
>
> **How to cite this document:** Amichis Luengo, R. (2026). *CHAISE LONGUE — THE KEY LEMMA, CLOSED forall k* [working document]. In *The Chaise Longue Theorem — working record*. https://github.com/tretoef-estrella/chaise-longue-theorem/blob/main/theorems/standalone/CHAISE_LONGUE_KEY_LEMMA_FULL.md
>
> **Status, as written in the document:** where S*(sigma) is the lex-largest valid support. PROVED forall k.
>
> **Later audit:** No later refutation of this document was found in the campaign's records; that is not the same as a referee's approval.
>
> ⚠️ *A working document of the campaign, reproduced as written (source version `v1`). It has not been refereed. Documents written before 23 September 2026 may treat the count `A_k(q) = P_k(q)` as the algebraic form of Conjecture 1.2; that identification is false (paper, §1.8 and §9). The authoritative statements are those of the paper, §14.*

---

# CHAISE LONGUE — THE KEY LEMMA, CLOSED forall k
### CHAISE_LONGUE_KEY_LEMMA_FULL_v1  ·  standalone

**Statement (KEY LEMMA).** Let sigma be J'_{k-1}-standard and S an admissible prefix support that is
*valid* for sigma (alpha_sigma(s_i) <= i for all i). Then
    sigma*theta_S in J'_{k-1}  <=>  S != S*(sigma),
where S*(sigma) is the lex-largest valid support. **PROVED forall k.**

Consequence: phi and psi (des-clack) are mutually inverse, so (BIJ) holds forall k, hence
**(*) is PROVED forall k**, i.e. piece (2) of the s=0 block of (B) is closed forall k.

---

## Floor language
alpha_nu(v) := ceil((v - nu_v)/2) = min rank at which v can be a g-generator element of nu; an m-gen
placing v at rank i divides nu iff alpha_nu(v) <= i. Ballot cap b(v)=floor(v/2). S valid <=>
alpha_sigma(s_i) <= i <= b(s_i). Since mu := sigma*theta_S has mu_v = sigma_v + 2[v in S]:
    **alpha_mu(v) = alpha_sigma(v) - [v in S]**   (the square drops the floor by 1 exactly on S).
A level gen m(U) (U={u_1<...<u_{p+1}}, cap u_p=2p, u_{p+1}=2p+1, ballot u_j>=2j for j<=p, exps
u_j-2(j-1)) divides nu iff alpha_nu(u_j) <= j-1 for all j.

**Insertable element.** t not in S is *insertable* (for sigma,S) if alpha_sigma(t) <= #{s in S : s<t}.
Write INS(sigma,S) for "an insertable t exists".

The proof is three lemmas: **A: INS => mu in J'.  B: INS <=> S != S*.  C: mu in J' => INS.**
Then mu in J' <=> INS <=> S != S*.

---

## Lemma A (INS => mu in J')  — the balance-point mirror
Given insertable t, set U'=S∪{t} (k elements in {2,...,2k-1}), sorted u'_1<...<u'_k. Then
alpha_mu(u'_l) <= l-1 for every l:
- u'_l in S at S-rank r<=l: alpha_mu = alpha_sigma(s_r)-1 <= r-1 <= l-1;
- u'_l = t: alpha_mu(t)=alpha_sigma(t) <= #{s in S:s<t} = l-1.
Run the balance point: N(p)=#{u' <= 2p+1}, g(p)=N(p)-p; g(0)=0, g(k-1)=k-(k-1)=1; p* = first p with
g(p)=1 (<= k-1). Then c_{p*}=2 (full pair {2p*,2p*+1} in U') and W = the p*+1 smallest of U' is an
admissible level support (ballot from g(j)<=0, j<p*). Since alpha_mu(w_j)=alpha_mu(u'_j)<=j-1, m(W)|mu.
Hence mu in J'.  QED. (This is the (L) balance-point run on the mu-floors.)

## Lemma B (INS <=> S != S*)
**(=>) INS => S != S*.** Insertable t sits in slot l: s_{l-1} < t < s_l, alpha_sigma(t) <= l-1, and
t > s_{l-1} >= 2(l-1) gives t >= 2(l-1)+1 > 2(l-1) so b(t) >= l-1. Replace s_{l-1} by t:
S'' = (s_1,...,s_{l-2}, t, s_l,...,s_{k-1}) is admissible (t between s_{l-2} and s_l), valid (rank l-1
holds t: alpha_sigma(t)<=l-1, ballot ok; ranks l..k-1 unchanged from S), and S'' >_lex S at rank l-1.
So S is not lex-max.  QED.

**(<=) S != S* => INS.** Pick any valid S' >_lex S; let t* = min(S' \ S) at S'-rank j*, so
alpha_sigma(t*) <= j* (S' valid). Let c = #{s in S : s < t*}. The j*-1 elements s'_1,...,s'_{j*-1} lie
below t* and, as t*=min(S'\S), all lie in S; so c >= j*-1. If c = j*-1 then those are exactly the S
elements below t*, so s_i=s'_i for i<j* and s_{j*} > t* = s'_{j*}, i.e. S >_lex S' — contradicting
S' >_lex S. Hence c >= j*, so alpha_sigma(t*) <= j* <= c, and t* is insertable.  QED.
(One rule t*=min(S'\S) settles both former sub-cases at once.)

## Lemma C (mu in J' => INS)  — the inverse reading
Suppose m(U) | mu, cap {2p,2p+1}.
**Fact 1 (U not subset of S).** S valid has s_i>=2i, so s_i<=2p+1 forces i<=p: at most p elements of S
are <= 2p+1. But all p+1 elements of U are <= 2p+1. Hence some u in U has u not in S; U\S is nonempty.
**The insertable witness t = min(U\S).** Let its U-position be J (so u_J=t, and u_1,...,u_{J-1} in S,
being the smaller U-elements, all in S because t is the FIRST U-element not in S). Then
#{s in S : s < t} >= J-1 (the elements u_1,...,u_{J-1} in S are all < t). And m(U)|mu with t not in S
gives alpha_sigma(t) = alpha_mu(t) <= J-1. So alpha_sigma(t) <= J-1 <= #{s in S:s<t}: t insertable.  QED.

## Assembly
Lemma A + Lemma C give **mu in J' <=> INS**. Lemma B gives **INS <=> S != S***. Therefore
**mu = sigma*theta_S in J'_{k-1} <=> S != S*(sigma)** — the Key Lemma, forall k.

Then for standard sigma, psi(sigma)=sigma*theta_{S*} lies in LHS (S=S* => mu not in J', from the Key
Lemma) with prefix divisor S* (unique divisor lemma), so phi(psi(sigma))=sigma; and for mu in LHS_S,
sigma=phi(mu) is valid for S with mu not in J', so S=S* and psi(phi(mu))=mu. **phi is a bijection
LHS<->RHS forall k => (*) PROVED forall k.**

## Gate (keylemma_close.py) — 0 failures, k=3,4,5
Lemma C [t=min(U\S) insertable]: 1645 / 114968 / 1441503 checks, FAIL=0.
Lemma B<= [t*=min(S'\S) insertable]: 2356 / 224414 / 3723436 checks, FAIL=0.
Full KEY LEMMA [notin J' <=> S=S*]: 1712 / 68121 / 698307 checks, FAIL=0.
(Prior: keylemma_check.py 807420 checks 0 viol; P1_proof.py 783783 checks 0 fail.)

**Grade: KEY LEMMA PROVED forall k => (BIJ) forall k => (*) PROVED forall k => piece (2) of s=0 CLOSED
forall k.** NOT GAP 3, NOT the theorem: from s=0 only piece (1) (matryoshka witness) remains to close
(B); and (B) does not close GAP 3 (s>=1 bulk + vertex-reduction induction remain).
