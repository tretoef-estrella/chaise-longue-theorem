-- MISSION 10: (G1) as a FUNCTION identity on W_(1)(n) (engine 3.3.3, n variables only).
-- Want: L in Ntilde_{m-1}(n)_d (monomial span), b in B_{d-1}, with NF_{I(W)}(s + L - b) of degree <= d-2.
-- Unknowns taken as S_P-orbit sums (P = y minus {y_j,y_l}, j=1,l=2) -> readable classes.
esym = (L,j) -> if j > #L or j < 0 then 0_(ring L#0) else if j == 0 then 1_(ring L#0) else sum apply(subsets(L,j), s -> product s);
setupW = (q, n) -> (
  S := ZZ/3[y_1..y_n, MonomialOrder => GRevLex]; ys := gens S;
  IW := ideal(apply(select(toList(1..n+1), j -> odd j), j -> esym(ys,j) + esym(ys,j-1)) | apply(ys, v -> v^q - v));
  (S, ys, IW));
-- monomial exponent vectors of degree dd, entries <= q-1
expsOf = (n, dd, q) -> if n == 0 then (if dd == 0 then {{}} else {}) else flatten apply(toList(0..min(dd,q-1)), a -> apply(expsOf(n-1, dd-a, q), e -> prepend(a, e)));
-- orbit key under S_P: (e_j, e_l, sorted exps on P)
okey = e -> (e#0, e#1, sort drop(e, 2));
inNt = (e, n, m, q) -> ( -- is the monomial y^e in Ntilde_{m-1}(n) (monomial ideal), n+1 even adds e_n = x_[n]
  A := select(toList(0..n-1), i -> e#i == q-1); -- A may use exps >= q-1 (all < q here)
  Cset := select(toList(0..n-1), i -> e#i >= 1 and e#i < q-1);
  -- the monomial is divisible by x_C x_A^{q-1} with |B| - |A| <= m-1, |B|>=1: best choice: A' subset A, C' = all other nonzero; B = zeros
  zeros := #select(e, x -> x == 0);
  ok := false;
  -- choose A' subset of A of size k (others of A go to C): B = zeros; need zeros - k <= m-1 and zeros >= 1
  if zeros >= 1 and zeros - #A <= m-1 then ok = true;
  if (not ok) and even(n+1) and m >= 1 and zeros == 0 then ok = true;
  ok);
runFun = (q, n, m) -> (
  c := n - m - 1; d := q + c - 1;
  (S, ys, IW) := setupW(q, n);
  t0 := cpuTime(); G := gb IW; << "=== (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " c=" << c << " d=" << d << " ; gb(I(W)) " << cpuTime()-t0 << " s ; dim S/I(W) = " << degree IW << endl << flush;
  s := (ys#0)^(q-2) * esym(drop(ys, {1,1}), c);
  -- top candidates: orbit sums of monomials of degree d in Ntilde
  E := select(expsOf(n, d, q), e -> inNt(e, n, m, q));
  keys := unique apply(E, okey);
  topC := apply(keys, k -> sum apply(select(E, e -> okey e == k), e -> product apply(n, i -> (ys#i)^(e#i))));
  -- B_{d-1}: even e_{2i} with 2i >= n-m times orbit sums of monomials of degree d-1-2i; squarefree x_C (|C|>=n-m+1) times monomials: as orbit sums of monomials of degree d-1 divisible by such x_C
  Bm := select(expsOf(n, d-1, q), e -> #select(e, x -> x >= 1) >= n-m+1);
  bkeys := unique apply(Bm, okey);
  bC := apply(bkeys, k -> sum apply(select(Bm, e -> okey e == k), e -> product apply(n, i -> (ys#i)^(e#i))));
  eC := {};
  for i from 0 to n do if even(2*i) and 2*i >= n-m and 2*i >= 1 and 2*i <= n and d-1-2*i >= 0 then (
    Ee := expsOf(n, d-1-2*i, q); ek := unique apply(Ee, okey);
    eC = eC | apply(ek, k -> esym(ys, 2*i) * sum apply(select(Ee, e -> okey e == k), e -> product apply(n, i2 -> (ys#i2)^(e#i2)))));
  << "  #top classes " << #topC << " ; #B squarefree classes " << #bC << " ; #B e_even classes " << #eC << endl << flush;
  t0 = cpuTime();
  nf := f -> ( r := f % G; 0_S + sum select(terms r, t -> first degree t >= d-1) );
  allC := topC | bC | eC;
  nfs := apply(allC, nf); ns := nf s;
  mons := unique flatten apply(select(append(nfs, ns), f -> f != 0), f -> flatten entries monomials f);
  << "  NFs done " << cpuTime()-t0 << " s ; standard monomials of degree >= d-1 involved: " << #mons << endl << flush;
  if #mons == 0 then (<< "  s is already of degree <= d-2 mod I(W)" << endl; return null);
  Mt := matrix apply(mons, mo -> apply(nfs, f -> coefficient(mo, f)));
  vt := matrix apply(mons, mo -> {coefficient(mo, ns)});
  Mt = sub(Mt, ZZ/3); vt = sub(vt, ZZ/3);
  sol := vt // Mt;
  ok := (Mt * sol == vt);
  << "  SOLVABLE with orbit classes? " << ok << " ; rank " << rank Mt << " of " << #allC << endl << flush;
  (S, ys, G, topC, bC, eC, keys, bkeys, Mt, vt, sol, ok, nf, s, d)
);
