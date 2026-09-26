load "m11lib.m2";
-- R11: raise rows with a LEAF child need only I_{lambda_c}(n) + box.  Proved pieces of row q-ell (parent mu, n+1 vars, f_p):
--  (i) e_r(y\y_l), r >= ell+f_p-2 (from phi_{z,l} and the chain);  (ii) e_k(y), k odd or k >= T-2, T := n+1-|mu|+1;  (iii) box;
--  (iv) N_{mu_1-1}(n) if mu_1 >= 2 (z in C: row 1).   Test: I_{lambda_c}(n) ⊆ (i)+(ii)+(iii)+(iv) ?
clTan = (vs, lam) -> ( N := #vs; lc := clConj(lam, N); dk := k -> sum take(reverse lc, k); L := {};
  for k from 1 to N do for Ss in subsets(N, k) do ( xs := apply(Ss, i -> vs#i); for r from max(1, k - dk(k) + 1) to k do L = append(L, clE(xs, r)));
  L);
runL = (q, np1, mu, nu, lab) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S;
  ell := #mu; fp := np1 - sum mu; T := np1 - sum mu + 1;
  pcs := flatten apply(n, l -> apply(select(toList(0..n-1), r -> r >= ell + fp - 2), r -> clE(drop(ys,{l,l}), r)));
  pcs = pcs | apply(select(toList(1..n), k -> odd k or k >= T-2), k -> clE(ys,k)) | apply(ys, v -> v^q);
  if mu#0 >= 2 then pcs = pcs | clLayer(ys, mu#0 - 1, q);
  G := gb ideal pcs;
  fc := n - sum nu;
  lamc := nu | toList(fc:1);
  bad := select(clTan(ys, lamc), g -> g % G != 0);
  << lab << " : parent " << toString mu << " n+1=" << np1 << " -> child " << toString nu << " n=" << n << " f_c=" << fc << " : I_lambda_c in proved pieces? " << (#bad == 0) << " (" << #bad << " missing)" << endl;
  if #bad > 0 then << "     missing e.g. " << toString take(bad,3) << endl;
  << flush;
);
runL(9,4,{1,1},{2,1},"kind 2 (n=4)"); runL(9,5,{1,1},{2,1},"kind 2 (n=5)");
runL(9,5,{2,1},{2,2},"kind 4 (n=5)"); runL(9,6,{2,1},{2,2},"kind 4 (n=6)");
runL(9,6,{3,1},{3,2},"kind 7 (n=6)");
runL(9,6,{2,2},{3,2},"kind 12 (n=6)");
runL(9,5,{1,1,1},{2,1,1},"kind 16 (n=5)"); runL(9,6,{1,1,1},{2,1,1},"kind 16 (n=6)");
runL(9,6,{2,1,1},{2,2,1},"kind 21 (n=6)");
runL(9,6,{1,1,1,1},{2,1,1,1},"kind 26 (n=6)");
<< "FIN-OK" << endl;
