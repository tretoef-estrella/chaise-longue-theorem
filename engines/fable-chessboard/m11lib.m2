-- MISSION 11 library: uniform casilla K_mu(n) over ZZ/3 on a list of variables vs (any ring)
clE = (L,j) -> if j < 0 or j > #L then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
clConj = (lam, n) -> apply(toList(1..n), i -> #select(lam, x -> x >= i));
clQ = (vs, mu) -> ( n := #vs; f := n - sum mu; lam := mu | toList(f:1);
  lc := clConj(lam, n); dk := k -> sum take(reverse lc, k);
  L := apply(select(toList(1..n), j -> odd j or j >= n - sum mu + 1), j -> clE(vs, j));
  for k from 1 to n-1 do for Ss in subsets(n, k) do ( xs := apply(Ss, i -> vs#i);
     for r from max(1, k - dk(k) + 1) to k do L = append(L, clE(xs, r)));
  L);
clLayer = (vs, w, q) -> ( nv := #vs; out := {};
  for a from 0 to nv do for b from 1 to nv - a do ( if b - a <= w then
    for A in subsets(nv, a) do for Bs in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,Bs));
      out = append(out, (product apply(C, i -> vs#i)) * (product apply(A, i -> (vs#i)^(q-1))))));
  out);
clPhi = (vs, q, ell, t, j, l) -> ( n := #vs;
  Pv := apply(select(toList(0..n-1), i -> i != j and i != l), i -> vs#i);
  (vs#j)^(q-ell) * sum apply(toList(0..ell-1), i -> (vs#j)^i * clE(Pv, t-i)));
clFam = (vs, q, mu) -> ( n := #vs; ell := #mu; f := n - sum mu; L := {};
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then L = append(L, clPhi(vs, q, ell, f+ell-2, j, l));
  L);
-- uniform casilla generators; layer included iff mu_1 >= 2 or ell = 1
clK = (vs, q, mu) -> ( n := #vs; R := ring vs#0;
  if sum mu > n or #mu > (q-1)//2 then return {1_R};
  L := clQ(vs, mu) | apply(vs, v -> v^q) | clFam(vs, q, mu);
  if mu#0 >= 2 or #mu == 1 then L = L | clLayer(vs, mu#0 - 1, q);
  L);
