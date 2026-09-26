-- (1,1,1) at n=5: shape of the degree-9 minimal generators, reduced modulo the base E+box+N_0 (and mod e_1 by elimination of x_1)
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
S = ZZ/3[x_1..x_6]; vs = gens S; z = x_6; K = casMone(vs, 1);
T = ZZ/3[x_1..x_5]; pz = map(T, S, append(gens T, 0_T)); yv = gens T;
R3 = pz(K : z^3); B0 = baseMu(yv, {1,1,1}); Bg = gb B0;
G = mingens R3; nine = select(numcols G, i -> (degree G_(0,i))#0 == 9);
U = ZZ/3[x_2..x_5]; ph = map(U, T, prepend(-(sum gens U), gens U));
<< "number of degree-9 mingens: " << #nine << endl;
for i in nine do ( f := G_(0,i) % Bg; << "--- reduced mod base, then x_1 eliminated: #terms " << #(terms ph f) << endl;
  << "    exponent patterns (sorted): " << tally apply(flatten entries monomials ph f, mo -> rsort flatten exponents mo) << endl; );
-- test: elements y_j^(q-3) * cubic, and y_j^(q-2) y_l * linear, y_j^(q-2) y_l^2, y_j^(q-4) quartic: dimension of the space {cubic C : x_1^(q-3) C in R3} mod those in B0
Rg = gb R3;
testShape = (pw, dg) -> ( mons := flatten entries basis(dg, T);
  NF := apply(mons, mo -> (x_1^pw * mo) % Rg); allm := unique flatten apply(NF, f -> flatten entries monomials f);
  M := matrix apply(NF, f -> apply(allm, mo -> coefficient(mo, f))); Kr := kernel transpose M;
  NFb := apply(mons, mo -> (x_1^pw * mo) % Bg); allb := unique flatten apply(NFb, f -> flatten entries monomials f);
  Mb := matrix apply(NFb, f -> apply(allb, mo -> coefficient(mo, f))); Krb := kernel transpose Mb;
  << "x_1^" << pw << " * (degree " << dg << "): in row: dim " << rank Kr << " ; in base: dim " << rank Krb << " ; new: " << rank Kr - rank Krb << endl;
  (Kr, mons));
testShape(q-2, 2); testShape(q-3, 3); testShape(q-4, 4); testShape(q-5, 5);
<< "FIN-OK" << endl;
