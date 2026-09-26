load "m11lib.m2";
-- R9 (a): TANISAKI ROW LEMMA: for lambda |- N (N = n+1 variables, z last) and a < l(lambda):  I_{lambda^(a)}(n) ⊆ R_a(I_lambda(N)),
--   lambda^(a) := lambda with lambda_{a+1} lowered by one;  and z^{l(lambda)} in I_lambda(N), z^{l(lambda)-1} not.   Over F_3 and over QQ.
clTan = (vs, lam) -> ( N := #vs; lc := clConj(lam, N); dk := k -> sum take(reverse lc, k); L := {};
  for k from 1 to N do for Ss in subsets(N, k) do ( xs := apply(Ss, i -> vs#i); for r from max(1, k - dk(k) + 1) to k do L = append(L, clE(xs, r)));
  L);
clParts = N -> partitions N;
tot = 0; good = 0; topok = 0; topn = 0;
for kk in {ZZ/3, QQ} do for N from 2 to 7 do for lam0 in partitions N do (
  lam := toList lam0; n := N - 1;
  S := kk[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  I := ideal clTan(vs, lam); G := gb I;
  topn = topn + 1; if (z^(#lam)) % G == 0 and (z^(#lam - 1)) % G != 0 then topok = topok + 1;
  for a from 0 to #lam - 1 do (
    ch := rsort select(apply(#lam, i -> if i == a then lam#i - 1 else lam#i), x -> x > 0);
    if sum ch == n then (
      Ga := gb(I + ideal(z^(a+1)));
      Ic := if n == 0 then {} else clTan(ys, ch);
      tot = tot + 1; if all(Ic, g -> (z^a * g) % Ga == 0) then good = good + 1 else << "  FAIL " << toString lam << " a=" << a << " over " << toString kk << endl)));
<< "(a) Tanisaki row lemma: " << good << "/" << tot << " (lambda |- N, N = 2..7, all a < l(lambda), F_3 and QQ) ; top power exact: " << topok << "/" << topn << endl << flush;
-- R9 (b): (G1) for m >= 2 with the FULL-h certificate C = z sum_{k odd} h_{N+1-k}(-a,b) e_k(y,z): C in K_(m)(n+1) and z^2 s in K + (z^3)
clh = (D, u, b) -> if D < 0 then 0 else sum apply(toList(0..D), i -> u^i * b^(D-i));
for cell in {(9,4,1),(9,5,1),(9,5,2),(9,5,3),(9,6,2),(9,6,3),(27,4,1),(27,5,2),(27,5,3)} do (
  (q, n, m) := cell; S := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  a := ys#0; b := ys#1; c := n - m - 1; N := q + c - 2;
  K := ideal clK(vs, q, {m}); G := gb K; G3 := gb(K + ideal(z^3));
  C := z * sum apply(toList(0..n+1), k -> if odd k then clh(N+1-k, -a, b) * clE(vs, k) else 0);
  s := a^(q-2) * clE(drop(ys, {1,1}), c);
  << "(b) (G1) cell q=" << q << " (n+1,m)=(" << n+1 << "," << m << ") : C in K " << (C % G == 0) << " ; z^2 s in K+(z^3) " << ((z^2*s) % G3 == 0) << endl << flush);
<< "FIN-OK" << endl;
