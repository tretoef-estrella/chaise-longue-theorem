-- INFORME_8 STEP 1: generic row R_2(K_(m)(n+1)) at q, its minimal generators beyond the lower neighbour K_(m)(n),
-- and the tests of guesses A (e_{2i}, 2i >= n-m) and B (y_j^(q-2) e_{n-m-1}(y minus y_l)).
q = QQQ; cellList = CELLS;
esym = (L,j) -> sum apply(subsets(L,j), s -> product s);
casilla = (V, mm) -> ( nv := #V; Kk := ideal apply(select(toList(1..nv), i -> odd i), i -> esym(V,i)) + ideal apply(V, v -> v^q);
  if even nv and mm >= 1 then Kk = Kk + ideal(product V);
  for a from 0 to nv do ( b := a + mm - 1; c := nv - a - b; if b >= 1 and c >= 0 then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      Kk = Kk + ideal((product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  Kk);
for cell in cellList do (
  nn = cell#0; m = cell#1; n = nn - 1;
  << "=== cell (n+1,m) = (" << nn << "," << m << ") q = " << q << endl << flush;
  S = ZZ/3[x_1..x_(nn)]; vs = gens S; z = x_(nn);
  K = casilla(vs, m);
  T = ZZ/3[x_1..x_n]; pz = map(T, S, append(gens T, 0_T));
  t0 = currentTime();
  R2 = pz(K : z^2);
  Klow = casilla(gens T, m);
  << "colength R2 = " << degree R2 << "   colength K_(m)(n) = " << degree Klow << "   (colon " << currentTime() - t0 << " s)" << endl << flush;
  << "Klow subset R2: " << isSubset(Klow, R2) << endl << flush;
  G = mingens R2; extra = select(numcols G, i -> (G_(0,i) % Klow) != 0);
  << "mingens of R2 not in Klow: " << #extra << "  degrees: " << tally apply(extra, i -> (degree G_(0,i))#0) << endl << flush;
  U = ZZ/3[x_2..x_n]; ph = map(U, T, prepend(-(sum gens U), gens U));
  for i in extra do if (degree G_(0,i))#0 <= 6 then << "   deg " << (degree G_(0,i))#0 << " (x_1 eliminated): " << ph(G_(0,i)) << endl;
  yv = gens T;
  evens = ideal apply(select(toList(1..n-1), j -> even j and j >= n-m), j -> esym(yv, j));
  if numgens evens == 0 then evens = ideal(0_T);
  << "guess A: e_{2i}, n-m <= 2i <= n-1, in R2: " << apply(select(toList(1..n-1), j -> even j and j >= n-m), j -> (esym(yv,j) % R2 == 0)) << endl << flush;
  d = n - m - 1;
  fam = ideal(0_T);
  if d >= 1 then for j from 0 to n-1 do for l from 0 to n-1 do if j != l then fam = fam + ideal((yv#j)^(q-2) * esym(select(yv, v -> v != yv#l), d));
  << "guess B: family y_j^(q-2) e_" << d << "(y minus y_l) subset R2: " << isSubset(fam, R2) << endl << flush;
  Bsum = Klow + evens + fam;
  << "Klow + evens + fam: colength " << degree Bsum << "  == R2 ? " << (Bsum == R2) << endl << flush;
  if Bsum != R2 then ( G2 = mingens R2; rest = select(numcols G2, i -> (G2_(0,i) % Bsum) != 0);
    << "   still missing: " << #rest << " generators, degrees " << tally apply(rest, i -> (degree G2_(0,i))#0) << endl;
    for i in rest do if (degree G2_(0,i))#0 <= 6 then << "     deg " << (degree G2_(0,i))#0 << " : " << ph(G2_(0,i)) << endl;
    -- is the missing part inside the upper neighbour K_(m+1)(n)? and q-free membership
    Kup = casilla(gens T, m+1);
    << "   R2 subset K_(m+1)(n) (sandwich): " << isSubset(R2, Kup) << endl;
  );
  << flush;
);
<< "FIN-OK" << endl;
