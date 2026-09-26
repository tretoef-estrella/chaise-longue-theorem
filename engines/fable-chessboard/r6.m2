load "m11lib.m2";
-- R6: exact gates of STEP 2.  (a) the two-letter generating identities (I),(II) as POLYNOMIAL identities over F_3 (no box):
--   (I)  sum_{k odd}  e_k(y) h_{M-k}(-a,b) = S^b_M - (-1)^M S^a_M ,   (II) sum_{k even} e_k(y) h_{M-k}(-a,b) = S^b_M + (-1)^M S^a_M,
--   S^a_M := sum_{p} a^{M-p} e_p(P), P = y\{a,b}, valid for M >= n-1.
clh = (D, u, b) -> if D < 0 then 0 else sum apply(toList(0..D), i -> u^i * b^(D-i));
Sx = (x, Pv, M) -> sum apply(toList(0..#Pv), p -> if M-p >= 0 then x^(M-p) * clE(Pv, p) else 0);
okI = true; cntI = 0;
for n from 2 to 7 do (
  S := ZZ/3[y_1..y_n]; ys := gens S; a := ys#0; b := ys#1; Pv := drop(ys, 2);
  for M from n-1 to n+9 do (
    lhsO := sum apply(toList(0..n), k -> if odd k then clE(ys,k) * clh(M-k, -a, b) else 0);
    lhsE := sum apply(toList(0..n), k -> if even k then clE(ys,k) * clh(M-k, -a, b) else 0);
    sg := (-1)^M;
    if lhsO != Sx(b,Pv,M) - sg*Sx(a,Pv,M) or lhsE != Sx(b,Pv,M) + sg*Sx(a,Pv,M) then okI = false;
    cntI = cntI + 1));
<< "(a) identities (I),(II), n = 2..7, M = n-1..n+9 (" << cntI << " cases): " << okI << endl << flush;
-- and a control: at M = n-2 (below the range) they must FAIL somewhere
S := ZZ/3[y_1..y_5]; ys := gens S; a := ys#0; b := ys#1; Pv := drop(ys,2); M := 3;
lhsO := sum apply(toList(0..5), k -> if odd k then clE(ys,k) * clh(M-k, -a, b) else 0);
<< "    control M = n-2: (I) holds? " << (lhsO == Sx(b,Pv,M) - (-1)^M*Sx(a,Pv,M)) << " (must be false)" << endl << flush;
-- (b) NC certificate for (1^ell): C := z^ell sum_{k odd} h_{N+1-k}(-a,b) e_k(y,z), N = q+c-2, c = n-ell-1.  Checks:
--   C = z^ell (S^b_{N+1} + eps S^a_{N+1}) + z^(ell+1) (eps S^a_N + S^b_N) exactly (eps = (-1)^N);  S^a_{N+1} == X_jl, S^b_{N+1} == X_lj,
--   S^a_N == X'_jl, S^b_N == X'_lj mod box;  z^ell X_jl, z^ell X_lj in K_parent;  z^(ell+1) X'_jl in K_parent + (z^(ell+2)).
runNC = (q, np1, ell, withGB) -> (
  n := np1 - 1; T := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  a := ys#0; b := ys#1; Pv := drop(ys, 2);
  c := n - ell - 1; N := q + c - 2; eps := (-1)^N;
  C := z^ell * sum apply(toList(0..np1), k -> if odd k then clh(N+1-k, -a, b) * clE(vs, k) else 0);
  split := z^ell * (Sx(b,Pv,N+1) + eps*Sx(a,Pv,N+1)) + z^(ell+1) * (eps*Sx(a,Pv,N) + Sx(b,Pv,N));
  Gbox := gb ideal apply(vs, v -> v^q);
  X := clPhi(ys, q, ell, n-2, 0, 1); Xr := clPhi(ys, q, ell, n-2, 1, 0);
  Xp := clPhi(ys, q, ell+1, n-2, 0, 1); Xpr := clPhi(ys, q, ell+1, n-2, 1, 0);
  o1 := (C == split);
  o2 := ((Sx(a,Pv,N+1) - X) % Gbox == 0) and ((Sx(b,Pv,N+1) - Xr) % Gbox == 0) and ((Sx(a,Pv,N) - Xp) % Gbox == 0) and ((Sx(b,Pv,N) - Xpr) % Gbox == 0);
  o3 := "skipped"; o4 := "skipped";
  if withGB then (
    Kp := ideal clK(vs, q, toList(ell:1)); G := gb Kp;
    o3 = ((z^ell * X) % G == 0) and ((z^ell * Xr) % G == 0);
    G2 := gb(Kp + ideal(z^(ell+2)));
    o4 = ((z^(ell+1) * Xp) % G2 == 0) and (C % G == 0));
  << "q=" << q << " (1^" << ell << ") n+1=" << np1 << " c=" << c << " : split exact " << o1 << " ; S = families mod box " << o2
     << " ; z^l X in K " << o3 << " ; z^(l+1) X' in K+(z^(l+2)) & C in K " << o4 << endl << flush;
);
for q in {9} do for ell from 1 to 3 do for np1 from ell+3 to 7 do runNC(q, np1, ell, np1 <= 6);
for ell from 1 to 3 do for np1 from ell+3 to 6 do runNC(27, np1, ell, np1 <= 5);
for ell from 1 to 3 do for np1 from ell+3 to 5 do runNC(81, np1, ell, np1 <= 4);
for ell from 1 to 3 do runNC(243, ell+3, ell, false);
<< "FIN-OK" << endl;
