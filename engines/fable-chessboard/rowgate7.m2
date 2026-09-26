-- INFORME_9 STEP 4: membership gates in 7 variables, q = 9.
-- (2,2) at n=6 = row q-2 of K_(2,1)(7): z^(q-2) g in K + (z^(q-1)) ;  (1,1,1,1) at n=6 = row 4 of K_(1,1,1)(7): z^4 g in K + (z^5)
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
psum = (L, e) -> sum apply(L, v -> v^e);
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famA = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
conj = lam -> ( mx := max lam; apply(toList(1..mx), i -> #select(lam, p -> p >= i)) );
Qmu = (V, mu) -> ( n := #V; smu := sum mu; f := n - smu; lam := sort(mu | toList(f:1)); lp := conj lam; lpad := lp | toList(n:0); dk := k -> sum apply(toList(n-k+1..n), i -> lpad#(i-1));
  Kk := ideal apply(select(toList(1..n), j -> odd j or j >= n - smu + 1), j -> esym(V, j));
  for k from 1 to n-1 do for S in subsets(V, k) do for r from k - dk(k) + 1 to k do if r >= 1 then Kk = Kk + ideal(esym(S, r)); Kk);
S = ZZ/3[x_1..x_7]; vs = gens S; z = x_7; nn = 7; yv = take(vs, 6);
T = ZZ/3[x_1..x_6]; yy = gens T; inc = map(S, T, yv);
prs = select(flatten apply(yy, a -> apply(yy, b -> if a != b then {a,b} else null)), p -> p =!= null);
gate = (name, Kg, a, G) -> ( gg := flatten entries mingens G; bad := 0;
  for g in gg do if ((z^a * inc g) % Kg) != 0 then bad = bad + 1;
  << "  " << name << " : generators with z^" << a << " g NOT in K + (z^" << a+1 << "): " << bad << " of " << #gg << endl << flush; bad);
-- parent 1: K_(2,1)(7), row q-2
t0 = currentTime();
K21 = ideal apply(select(toList(1..nn), j -> odd j or j >= nn - 2), j -> esym(vs, j)) + ideal apply(vs, v -> v^q) + layerN(vs, 1) + famA(vs, nn - 3) + ideal(z^(q-1));
G21 = gb K21; << "gb K_(2,1)(7) + (z^(q-1)): " << currentTime() - t0 << " s" << endl << flush;
B22 = Qmu(yy, {2,2}) + ideal apply(yy, v -> v^q) + layerN(yy, 1);
gate("(2,2) base Q+box+N_1", G21, q-2, B22);
gate("(2,2) base + y_j^(q-2) e_2(y-l)", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-2) * esym(select(yy, v -> v != p#1), 2)));
gate("(2,2) base + y_j^(q-2) y_l^2", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-2) * (p#1)^2));
gate("(2,2) base + y_j^(q-2) p_2(y-l)", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-2) * psum(select(yy, v -> v != p#1), 2)));
gate("(2,2) base + y_j^(q-2) e_2(y-j-l)", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-2) * esym(select(yy, v -> v != p#1 and v != p#0), 2)));
gate("(2,2) base + y_j^(q-2) y_l e_1(y-j-l)", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-2) * (p#1) * esym(select(yy, v -> v != p#1 and v != p#0), 1)));
gate("(2,2) base + y_j^(q-3) y_l^3", G21, q-2, B22 + ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^3));
gate("(2,2) base + N_2", G21, q-2, B22 + layerN(yy, 2));
-- parent 2: K_(1,1,1)(7), row 4
t0 = currentTime();
K111 = ideal apply(select(toList(1..nn), j -> odd j or j >= nn - 2), j -> esym(vs, j)) + ideal apply(vs, v -> v^q) + layerN(vs, 0) + ideal flatten apply(vs, a -> apply(vs, b -> if a != b then a^(q-3) * b^(nn-2) else 0_S)) + ideal(z^5);
G111 = gb K111; << "gb K_(1,1,1)(7) + (z^5): " << currentTime() - t0 << " s" << endl << flush;
B1111 = Qmu(yy, {1,1,1,1}) + ideal apply(yy, v -> v^q) + layerN(yy, 0);
gate("(1,1,1,1) base Q+box+N_0", G111, 4, B1111);
gate("(1,1,1,1) base + y_j^(q-4) y_l^4", G111, 4, B1111 + ideal apply(prs, p -> (p#0)^(q-4) * (p#1)^4));
gate("(1,1,1,1) base + y_j^(q-4) p_4(y-l)", G111, 4, B1111 + ideal apply(prs, p -> (p#0)^(q-4) * psum(select(yy, v -> v != p#1), 4)));
gate("(1,1,1,1) base + y_j^(q-4) e_4(y-l)", G111, 4, B1111 + ideal apply(prs, p -> (p#0)^(q-4) * esym(select(yy, v -> v != p#1), 4)));
gate("(1,1,1,1) base + y_j^(q-3) y_l^3", G111, 4, B1111 + ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^3));
gate("(1,1,1,1) base + y_j^(q-3) y_l^4", G111, 4, B1111 + ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^4));
<< "FIN-OK" << endl;
