-- MISSION 10 B2: uniform casilla K_mu(n) = Q_mu(n) + box + N_w(n) + F_mu(n), gated AS AN IDEAL against G_mu(n)
load "m10cas.m2";
conjP = (lam, n) -> ( lc := apply(toList(1..n), i -> #select(lam, x -> x >= i)); lc ); -- conjugate, padded to length n
Qmu = (S, ys, mu) -> ( n := #ys; f := n - sum mu; lam := mu | toList(f:1);
  lc := conjP(lam, n); -- lambda'_1 >= ... >= lambda'_n
  dk := k -> sum take(reverse lc, k);
  L := apply(select(toList(1..n), j -> odd j or j >= n - sum mu + 1), j -> esymL(ys, j));
  for k from 1 to n-1 do for Sset in subsets(n, k) do ( xs := apply(Sset, i -> ys#i);
     for r from max(1, k - dk(k) + 1) to k do L = append(L, esymL(xs, r)));
  ideal L);
layerN = (ys, w, q) -> ( nv := #ys; out := {};
  for a from 0 to nv do for b from 1 to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for Bs in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,Bs));
      out = append(out, (product apply(C, i -> ys#i)) * (product apply(A, i -> (ys#i)^(q-1))))));
  if #out == 0 then ideal(0_(ring ys#0)) else ideal out);
famPhi = (ys, q, ell, t) -> ( n := #ys; L := {};
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then (
    P := select(toList(0..n-1), i -> i != j and i != l); Pv := apply(P, i -> ys#i);
    L = append(L, (ys#j)^(q-ell) * sum apply(toList(0..ell-1), i -> (ys#j)^i * esymL(Pv, t-i))));
  ideal L);
gateU = (q, n, mu, dl) -> (
  (S, ys, G, tm) := casilla(q, n, mu, toList(0..#mu-1), dl);
  ell := #mu; f := n - sum mu;
  base := Qmu(S, ys, mu) + ideal apply(ys, v -> v^q);
  fam := famPhi(ys, q, ell, f + ell - 2);
  out := {};
  for w in unique {mu#0 - 1, sum mu - ell - 1, sum mu - ell} do if w >= 0 then (
    K := base + layerN(ys, w, q) + fam;
    eq := (K == G);
    out = append(out, (w, eq, if eq then degree K else degree K));
  );
  Kn := base + fam; eqn := (Kn == G);
  << "mu=" << toString mu << " n=" << n << " f=" << f << " |W|=" << degree G << " : (w, K==G, colength K) " << toString out << " ; no layer: " << eqn << " ; Q+box+layer(mu1-1) alone == G? " << ((base + layerN(ys, mu#0-1, q)) == G) << endl << flush;
);
