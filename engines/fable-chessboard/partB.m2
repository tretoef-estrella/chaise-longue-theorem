-- INFORME_9 STEP 3 (PART B): are the Tanisaki generators of leaf children reached by q-free certificates?
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famA = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
conj = lam -> ( mx := max lam; apply(toList(1..mx), i -> #select(lam, p -> p >= i)) );
tanGens = (V, lam) -> ( n := #V; lp := conj lam; lpad := lp | toList(n:0); dk := k -> sum apply(toList(n-k+1..n), i -> lpad#(i-1));
  L := {}; for k from 1 to n do for S in subsets(V, k) do for r from k - dk(k) + 1 to k do if r >= 1 then L = append(L, {S, r, esym(S, r)}); L);
doCase = (nn, m, a, lam) -> (
  n := nn - 1;
  << "=== K_(" << m << ",1)(" << nn << "), row " << a << ", child Tanisaki lambda = " << toString lam << " in n = " << n << endl << flush;
  S := ZZ/3[x_1..x_nn]; vs := gens S; z := x_nn; yv := take(vs, n);
  Qf := ideal apply(select(toList(1..nn), j -> odd j or j >= nn - m), j -> esym(vs, j));
  Bx := ideal apply(vs, v -> v^q);
  K := Qf + Bx + layerN(vs, m-1) + famA(vs, nn - m - 1);
  za := z^(a+1);
  G1 := gb(Qf + ideal za); G2 := gb(Qf + Bx + ideal za); G3 := gb(K + ideal za);
  T := ZZ/3[x_1..x_n]; inc := map(S, T, yv);
  for g in tanGens(gens T, lam) do (
    f := z^a * inc(g#2);
    if (f % G3) != 0 then << "  !! e_" << g#1 << "(S), |S|=" << #(g#0) << " NOT in K + (z^" << a+1 << ")" << endl
    else << "  e_" << g#1 << "(S), |S|=" << #(g#0) << " : q-free certificate (Q only)? " << ((f % G1) == 0) << " ; Q + box? " << ((f % G2) == 0) << " ; full K? true" << endl;
    << flush;);
);
doCase(5, 1, 3, {1,1,1,1});       -- child (1,1,1) at n=4, f=1
doCase(6, 2, q-2, {2,2,1});       -- child (2,2) at n=5, f=1
doCase(6, 1, 3, {1,1,1,1,1});     -- control: (1,1,1) at n=5 has f=2 (NOT a leaf): which Tanisaki gens survive?
doCase(6, 2, 3, {2,1,1,1});       -- child (2,1,1) at n=5, f=1 (new-class row of (2,1))
doCase(6, 3, q-2, {3,2});         -- child (3,2) at n=5, f=0
<< "FIN-OK" << endl;
