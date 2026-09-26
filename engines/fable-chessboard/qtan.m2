-- INFORME_8 STEP 2: q-Tanisaki signature of the small casillas (rows of K_(m,1)(n+1)), q = 9.
-- For S = first k variables, twists: a = # x^(q-1) factors outside S, b = # x^(q-2) factors inside S, c = # x^(q-2) factors outside S:
-- print the set of r (0..k) with e_r(S) * twist in J.
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
signature = (J, V) -> ( n := #V;
  pats := {{0,0,0},{1,0,0},{0,1,0},{0,0,1},{2,0,0},{0,2,0},{1,1,0},{1,0,1},{0,1,1},{0,0,2}};
  for k from 1 to n do for p in pats do ( a := p#0; b := p#1; c := p#2;
    if k + a + c <= n and b <= k then (
      S := take(V, k); A := take(drop(V, k), a); Cc := take(drop(V, k + a), c); Jj := take(S, b);
      tw := (product apply(A, v -> v^(q-1))) * (product apply(Jj, v -> v^(q-2))) * (product apply(Cc, v -> v^(q-2)));
      rs := select(toList(0..k), r -> ((esym(S, r) * tw) % J) == 0);
      if #rs > 0 then << "      k=" << k << " (a,b,c)=" << toString p << " : r in " << toString rs << endl));
);
rowOf = (nn, m, a) -> ( S := ZZ/3[x_1..x_(nn)]; vs := gens S; z := x_(nn); K := casMone(vs, m);
  T := ZZ/3[x_1..x_(nn-1)]; pz := map(T, S, append(gens T, 0_T)); pz(K : z^a));
jobs = {{4,1,2,"(1,1) n=3"},{5,1,2,"(1,1) n=4"},{6,1,2,"(1,1) n=5"},{5,1,3,"(1,1,1) n=4"},{6,1,3,"(1,1,1) n=5"},{5,1,7,"(2,1) n=4"},{6,1,7,"(2,1) n=5"},
        {6,2,3,"(2,1,1) n=5"},{5,2,7,"(2,2) n=4"},{6,2,7,"(2,2) n=5"},{6,3,7,"(3,2) n=5"},{6,2,8,"(3,1) n=5"},{6,3,8,"(4,1) n=5"},
        {6,1,0,"(1) n=5"},{6,2,1,"(2) n=5"},{6,3,1,"(3) n=5"},{5,1,0,"(1) n=4"},{5,2,1,"(2) n=4"}};
for jb in jobs do ( Ra := rowOf(jb#0, jb#1, jb#2); << "=== " << jb#3 << " : colength " << degree Ra << endl; signature(Ra, gens ring Ra); << flush; );
<< "FIN-OK" << endl;
