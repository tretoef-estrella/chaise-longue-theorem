-- INFORME_9 STEP 2 fire test: t = y_j^(q-3) y_l^(n-2) in row 3 of K_(1,1)(n+1): full certificate vs engine-type (I-part in (z))
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famA = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
for n in {4,5} do (
  nn = n + 1;
  << "=== K_(1,1)(" << nn << "), row 3 (type (1,1,1) in n=" << n << "), q=" << q << endl << flush;
  S = ZZ/3[x_1..x_nn]; vs = gens S; z = x_nn; yv = take(vs, n);
  I1 = ideal apply(select(toList(1..nn), j -> odd j), j -> esym(vs, j)) + ideal apply(vs, v -> v^q);
  M = ideal apply(select(toList(1..nn), j -> j >= nn - 1), j -> esym(vs, j)) + layerN(vs, 0) + famA(vs, nn - 2);
  K = I1 + M;
  T = ZZ/3[x_1..x_n]; pz = map(T, S, append(gens T, 0_T)); yy = gens T;
  t = (yv#0)^(q-3) * (yv#1)^(n-2);
  << "colength K = " << degree K << endl << flush;
  R3 = pz(K : z^3); << "row 3 colength " << degree R3 << " ; t in row 3? " << ((pz t) % R3 == 0) << endl << flush;
  full = ((z^3 * t) % (K + ideal(z^4))) == 0;
  Iz = I1 : z; Mz = M : z;
  eng = ((z^2 * t) % (Iz + Mz + ideal(z^3))) == 0;
  << "FULL: z^3 t in K + (z^4)? " << full << "   ENGINE-TYPE: z^2 t in (I:z) + (M:z) + (z^3)? " << eng << endl << flush;
  -- finer: which parts of M:z are needed (engine-type)
  Mz0 = layerN(vs, 0) : z;  -- pure monomial layer
  << "   engine with (M:z) = (N_0 : z) only: " << (((z^2 * t) % (Iz + Mz0 + ideal(z^3))) == 0) << endl << flush;
  Mz1 = (layerN(vs,0) + ideal apply(select(toList(1..nn), j -> j >= nn - 1), j -> esym(vs, j))) : z;
  << "   engine with (M:z) = (N_0 + e_n, e_(n+1)) : z : " << (((z^2 * t) % (Iz + Mz1 + ideal(z^3))) == 0) << endl << flush;
  Mz2 = (layerN(vs,0) + famA(vs, nn-2)) : z;
  << "   engine with (M:z) = (N_0 + F_1) : z : " << (((z^2 * t) % (Iz + Mz2 + ideal(z^3))) == 0) << endl << flush;
  -- full row of the engine-type: colength of pi_z(((I:z) + (M:z) + (z^3)) : z^2)
  Reng = pz(((Iz + Mz + ideal(z^3))) : z^2);
  << "   engine-type row: colength " << degree Reng << " (fibre (1,1,1) at n=" << n << ": " << (if n == 4 then 24 else 360) << ") ; equals row 3? " << (Reng == R3) << endl << flush;
);
<< "FIN-OK" << endl;
