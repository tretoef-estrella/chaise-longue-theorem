-- INFORME_9 STEP 3 refinement: which non-q-free part carries the proper-subset Tanisaki generators
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
  << "=== K_(" << m << ",1)(" << nn << "), row " << a << ", child lambda = " << toString lam << endl << flush;
  S := ZZ/3[x_1..x_nn]; vs := gens S; z := x_nn; yv := take(vs, n);
  Qf := ideal apply(select(toList(1..nn), j -> odd j or j >= nn - m), j -> esym(vs, j));
  Iodd := ideal apply(select(toList(1..nn), j -> odd j), j -> esym(vs, j));
  Bx := ideal apply(vs, v -> v^q); Nl := layerN(vs, m-1); Fm := famA(vs, nn - m - 1);
  M := (Qf + Nl + Fm);
  za := z^(a+1);
  GN := gb(Qf + Bx + Nl + ideal za); GF := gb(Qf + Bx + Fm + ideal za); GK := gb(Qf + Bx + Nl + Fm + ideal za);
  Geng := gb(((Iodd + Bx) : z) + (M : z) + ideal(z^a));
  T := ZZ/3[x_1..x_n]; inc := map(S, T, yv);
  tal := tally apply(tanGens(gens T, lam), g -> ( f := z^a * inc(g#2); fe := z^(a-1) * inc(g#2);
    {#(g#0), g#1, "N-layer:" | toString((f % GN) == 0), "family:" | toString((f % GF) == 0), "full:" | toString((f % GK) == 0), "engine-type:" | toString((fe % Geng) == 0)}));
  for k in keys tal do << "  " << tal#k << " x  |S|=" << k#0 << " e_" << k#1 << "  " << k#2 << " " << k#3 << " " << k#4 << " " << k#5 << endl;
  << flush;);
doCase(5, 1, 3, {1,1,1,1});
doCase(6, 2, q-2, {2,2,1});
doCase(6, 2, 3, {2,1,1,1});
doCase(6, 3, q-2, {3,2});
doCase(6, 3, 3, {3,1,1});
<< "FIN-OK" << endl;
