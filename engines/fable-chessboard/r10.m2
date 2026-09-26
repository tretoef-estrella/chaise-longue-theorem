load "m11lib.m2";
-- R10: HOOK lemmas mu = (m,1^(ell-1)), m >= 2.  Monomial checks (no GB) + GB memberships at <= 6 vars (q = 9).
clh = (D, u, b) -> if D < 0 then 0 else sum apply(toList(0..D), i -> u^i * b^(D-i));
Sx = (x, Pv, M) -> sum apply(toList(0..#Pv), p -> if M-p >= 0 then x^(M-p) * clE(Pv, p) else 0);
-- monomial in N_w (k vars) + box + (product of all vars)?
inLayMono = (ex, w, q) -> ( if max ex >= q then return true;
  Z := #select(ex, e -> e == 0); A := #select(ex, e -> e == q-1); Cs := #select(ex, e -> e >= 1 and e <= q-2);
  if Z == 0 then return true;   -- full support: multiple of the product of all variables
  Z - A <= w );
allInLay = (F, w, q) -> F == 0 or all(exponents F, ex -> inLayMono(ex, w, q));
-- pure-y polynomial, layer in the n y-variables (drop the z coordinate)
allInLayY = (F, w, q) -> F == 0 or all(exponents F, ex -> (if last ex != 0 then error "not pure y"; inLayMono(drop(ex, -1), w, q)));
runH = (q, np1, m, ell, withGB) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  mu := {m} | toList((ell-1):1); M := sum mu; fp := np1 - M; a := ys#0; b := ys#1; Pv := drop(ys, 2);
  Gbox := gb ideal apply(vs, v -> v^q);
  out := {};
  -- (a) VALUE-0: z^ell X - mult*phi_p in N_{m-1}(n+1)+box+full
  X := clPhi(ys, q, ell, fp + ell - 3, 0, 1); php := clPhi(vs, q, ell, fp + ell - 2, 0, 1);
  mult := sum apply(toList(0..ell-1), i -> z^(ell-1-i) * (-a)^i);
  out = append(out, "VZ " | toString allInLay(z^ell * X - mult * php, m-1, q));
  -- (b) NEW-CLASS (child mu u (1), needs ell+1 <= h): C split, z^ell (S_{N+1} - X) in layer, S_N - X' in layer(n)
  c := n - M - 1;
  if ell + 1 <= (q-1)//2 and c >= 0 then (
    N := q + c - 2; eps := (-1)^N;
    C := z^ell * sum apply(toList(0..np1), k -> if odd k then clh(N+1-k, -a, b) * clE(vs, k) else 0);
    spl := z^ell * (Sx(b,Pv,N+1) + eps*Sx(a,Pv,N+1)) + z^(ell+1) * (eps*Sx(a,Pv,N) + Sx(b,Pv,N));
    Xr := clPhi(ys, q, ell, fp + ell - 3, 1, 0);
    Xp := clPhi(ys, q, ell+1, c + ell - 1, 0, 1); Xpr := clPhi(ys, q, ell+1, c + ell - 1, 1, 0);
    o := (N >= n-1) and (C == spl) and allInLay(z^ell*(Sx(a,Pv,N+1) - X), m-1, q) and allInLay(z^ell*(Sx(b,Pv,N+1) - Xr), m-1, q)
         and allInLayY(Sx(a,Pv,N) - Xp, m-1, q) and allInLayY(Sx(b,Pv,N) - Xpr, m-1, q);
    if not o then << "   NC parts: N>=n-1 " << (N >= n-1) << " split " << (C == spl) << " Ta " << allInLay(z^ell*(Sx(a,Pv,N+1) - X), m-1, q) << " Sh " << allInLayY(Sx(a,Pv,N) - Xp, m-1, q) << endl;
    out = append(out, "NC " | toString o));
  -- (c) LOWER row 1 (ell >= 2): child (m,1^(ell-2)) family = parent family at z=0 - a^(q-ell) e_{f+ell-2}(P), the latter in N_{m-1}(n)
  if ell >= 2 then (
    corr := a^(q-ell) * clE(Pv, fp + ell - 2);
    chf := clPhi(ys, q, ell-1, fp + ell - 3, 0, 1); pz := sub(php, z => 0);
    out = append(out, "LOW1 " | toString(((chf - (pz - corr)) % Gbox == 0) and allInLayY(corr, m-1, q))));
  -- (d) RAISE row q-1 (child (m+1,1^(ell-1)), f = fp-2): family = X' + a^(q-ell-1) e_{c+ell-1}(P) mod box, the latter in N_m(n)
  if c >= 0 then (
    rf := clPhi(ys, q, ell, c + ell - 2, 0, 1); Xp2 := clPhi(ys, q, ell+1, c + ell - 1, 0, 1);
    corr2 := a^(q-ell-1) * clE(Pv, c + ell - 1);
    out = append(out, "RAISEq-1 " | toString(((rf - (Xp2 - corr2)) % Gbox == 0) and allInLayY(corr2, m, q))));
  -- (e) GB memberships of the whole children (<= 6 vars, q = 9)
  if withGB then (
    Kp := ideal clK(vs, q, mu);
    rowIn := (aa, nu) -> ( Ga := gb(Kp + ideal(z^(aa+1))); all(clK(ys, q, nu), g -> (z^aa * g) % Ga == 0));
    out = append(out, "GB[VZ " | toString rowIn(ell, mu) | ", NC " | toString (if ell+1 <= (q-1)//2 then rowIn(ell+1, mu | {1}) else "-")
       | ", LOW1 " | toString (if ell >= 2 then rowIn(1, {m} | toList((ell-2):1)) else "-") | ", RAISEq-1 " | toString rowIn(q-1, {m+1} | toList((ell-1):1)) | "]"));
  << "q=" << q << " mu=" << toString mu << " n+1=" << np1 << " (child NC f=" << c << ") : " << toString out << endl << flush;
);
for mu in {{2,1},{3,1},{4,1},{2,1,1},{3,1,1},{2,1,1,1},{2},{3}} do (m := mu#0; ell := #mu;
  for np1 from sum mu + 2 to 7 do runH(9, np1, m, ell, np1 <= 6));
runH(27, 5, 2, 2, false); runH(27, 5, 2, 1, false); runH(27,5,3,1,false);
<< "FIN-OK" << endl;
