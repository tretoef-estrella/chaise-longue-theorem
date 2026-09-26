-- (1,1,1) at n=6 (row 3 of K_(1,1)(7), q=9) WITHOUT the colon: membership in K+(z^4); kernel of x_1^(q-e) * (degree e) forms, e = 2,3,4
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
-- base of the guess for profile mu in variables V: E_mu + box + N_{|mu|-l}
baseMu = (V, mu) -> ( nv := #V; smu := sum mu; lmu := #mu; w := smu - lmu;
  Kk := ideal apply(select(toList(1..nv), j -> odd j or j >= nv - smu + 1), j -> esym(V,j)) + ideal apply(V, v -> v^q);
  if numgens Kk == 0 then Kk = ideal(0_(ring V#0));
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      Kk = Kk + ideal((product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  Kk);
famA = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famB = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do for l2 from l+1 to nv-1 do if j != l and j != l2 then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l and v != V#l2), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famC = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for j2 from j+1 to nv-1 do for l from 0 to nv-1 do for l2 from l+1 to nv-1 do if #(set{j,j2,l,l2}) == 4 then L = append(L, (V#j)^(q-2) * (V#j2)^(q-2) * esym(select(V, v -> v != V#l and v != V#l2), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famD = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for j2 from j+1 to nv-1 do for l from 0 to nv-1 do if l != j and l != j2 then L = append(L, (V#j)^(q-2) * (V#j2)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famE = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * (V#l)^(q-2) * esym(select(V, v -> v != V#l and v != V#j), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
casMone = (V, m) -> baseMu(V, {m,1}) + famA(V, #V - m - 1);
doCell = (nn, m, profs, fibs) -> (
  n := nn - 1;
  << "=== rows of K_(" << m << ",1)(" << nn << ") at q = " << q << endl << flush;
  S := ZZ/3[x_1..x_(nn)]; vs := gens S; z := x_(nn);
  K := casMone(vs, m);
  << "colength K_(m,1)(n+1) = " << degree K << "  (fibre " << sum fibs << ")" << endl << flush;
  T := ZZ/3[x_1..x_n]; pz := map(T, S, append(gens T, 0_T)); yv := gens T;
  U := ZZ/3[x_2..x_n]; ph := map(U, T, prepend(-(sum gens U), gens U));
  tot := 0;
  for a from 0 to q-1 do (
    nu := profs#a; Ra := pz(K : z^a); tot = tot + degree Ra;
    Bn := baseMu(yv, nu);
    << "row " << a << " type " << toString nu << ": colength " << degree Ra << " vs fibre " << fibs#a << " ; base subset row? " << isSubset(Bn, Ra) << " ; base colength " << degree Bn;
    if Bn == Ra then << "  == base" << endl else (
      << endl;
      -- candidate families
      cands := {};
      for d from 0 to n-1 do cands = cands | {{"A"|toString d, famA(yv,d)}, {"B"|toString d, famB(yv,d)}, {"C"|toString d, famC(yv,d)}, {"D"|toString d, famD(yv,d)}, {"E"|toString d, famE(yv,d)}};
      inside := select(cands, c -> isSubset(c#1, Ra));
      << "    families inside the row: " << apply(inside, c -> c#0) << endl;
      -- greedy: add families in order until equality
      cur := Bn; used := {};
      for c in inside do ( if cur != Ra then ( nw := cur + c#1; if degree nw < degree cur then ( cur = nw; used = append(used, c#0)))); 
      << "    greedy base + " << used << " : colength " << degree cur << (if cur == Ra then "  == row" else "  != row") << endl;
      if cur != Ra then ( G := mingens Ra; rest := select(numcols G, i -> (G_(0,i) % cur) != 0);
        << "    remaining mingens: " << #rest << " degrees " << tally apply(rest, i -> (degree G_(0,i))#0) << endl;
        for i in rest do if (degree G_(0,i))#0 <= 6 then << "      deg " << (degree G_(0,i))#0 << " : " << ph(G_(0,i)) << endl;);
    );
    << flush;
  );
  << "sum of row colengths " << tot << " = colength K? " << (tot == degree K) << endl << flush;
);
S = ZZ/3[x_1..x_7]; vs = gens S; z = x_7; K = casMone(vs, 1) + ideal(z^4);
t0 = currentTime(); Kg = gb K; << "gb K_(1,1)(7)+(z^4): " << currentTime() - t0 << " s" << endl << flush;
T = ZZ/3[x_1..x_6]; yv = gens T; inc = map(S, T, take(vs, 6));
B0 = baseMu(yv, {1,1,1}); Bg = gb B0;
<< "base colength " << degree B0 << "  fibre |W_(1,1,1)(6)| = 1920" << endl << flush;
testShape = (pw, dg) -> ( mons := flatten entries basis(dg, T);
  NF := apply(mons, mo -> (z^3 * inc(x_1^pw * mo)) % Kg); allm := unique flatten apply(NF, f -> flatten entries monomials f);
  M := if #allm == 0 then map(ZZ/3^(#mons), ZZ/3^0, 0) else matrix apply(NF, f -> apply(allm, mo -> coefficient(mo, f))); Kr := kernel transpose M;
  NFb := apply(mons, mo -> (x_1^pw * mo) % Bg); allb := unique flatten apply(NFb, f -> flatten entries monomials f);
  Mb := if #allb == 0 then map(ZZ/3^(#mons), ZZ/3^0, 0) else matrix apply(NFb, f -> apply(allb, mo -> coefficient(mo, f))); Krb := kernel transpose Mb;
  << "x_1^" << pw << " * (degree " << dg << "): in row: dim " << rank Kr << " ; in base: dim " << rank Krb << " ; new: " << rank Kr - rank Krb << endl << flush;
  -- print new elements: a complement basis, reduced mod base, x_1 eliminated
  U := ZZ/3[x_2..x_6]; ph := map(U, T, prepend(-(sum gens U), gens U));
  if rank Kr > rank Krb then ( gK := gens Kr; cnt := 0;
    for i from 0 to numcols gK - 1 do ( el := sum apply(#mons, j -> gK_(j,i) * mons#j); if (x_1^pw * el) % Bg != 0 and cnt < 4 then ( cnt = cnt + 1;
      << "    new: x_1^" << pw << " * ( " << ph(el) << " )" << endl));
  ););
testShape(q-2, 3); testShape(q-3, 4); testShape(q-4, 5);
-- direct candidates
cand = {{"y1^(q-3) y2^4", x_1^(q-3)*x_2^4}, {"y1^(q-3) y2^3 y3", x_1^(q-3)*x_2^3*x_3}, {"y1^(q-3) y2^3 e1(y-{1,2})", x_1^(q-3)*x_2^3*esym(drop(yv,2),1)},
        {"y1^(q-3) y2^3 e1(y-1)", x_1^(q-3)*x_2^3*esym(drop(yv,1),1)}, {"y1^(q-3) e4(y-1)", x_1^(q-3)*esym(drop(yv,1),4)}, {"y1^(q-3) y2^3 y3 (+sym over 3)", x_1^(q-3)*x_2^3*x_3}};
for c in cand do << c#0 << " : in row3 " << ((z^3 * inc(c#1)) % Kg == 0) << " ; in base " << ((c#1) % Bg == 0) << endl;
<< "FIN-OK" << endl;
