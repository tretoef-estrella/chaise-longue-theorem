-- INFORME_9 STEP 4 (PART C): candidates for K_(2,2)(6) (target 570) and K_(1,1,1,1)(6) (target 1800), q = 9, colength gates
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
psum = (L, e) -> sum apply(L, v -> v^e);
hsum = (L, e) -> sum apply(compositions(#L, e), c -> product apply(#L, i -> (L#i)^(c#i)));
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
conj = lam -> ( mx := max lam; apply(toList(1..mx), i -> #select(lam, p -> p >= i)) );
Qmu = (V, mu) -> ( n := #V; smu := sum mu; f := n - smu; lam := sort(mu | toList(f:1)); lp := conj lam; lpad := lp | toList(n:0); dk := k -> sum apply(toList(n-k+1..n), i -> lpad#(i-1));
  Kk := ideal apply(select(toList(1..n), j -> odd j or j >= n - smu + 1), j -> esym(V, j));
  for k from 1 to n-1 do for S in subsets(V, k) do for r from k - dk(k) + 1 to k do if r >= 1 then Kk = Kk + ideal(esym(S, r)); Kk);
S = ZZ/3[x_1..x_6]; vs = gens S; n = 6; Bx = ideal apply(vs, v -> v^q);
prs = flatten apply(vs, a -> apply(vs, b -> if a != b then {a,b} else null)); prs = select(prs, p -> p =!= null);
<< "=== (2,2) at n=6, target 570" << endl;
B22 = Qmu(vs, {2,2}) + Bx + layerN(vs, 1);
<< "Q + box + N_1 : " << degree B22 << endl << flush;
<< "Q + box + N_2 : " << degree(Qmu(vs, {2,2}) + Bx + layerN(vs, 2)) << endl << flush;
cands22 = {
 {"y_j^(q-2) e_2(y-l)", ideal apply(prs, p -> (p#0)^(q-2) * esym(select(vs, v -> v != p#1), 2))},
 {"y_j^(q-2) y_l^2", ideal apply(prs, p -> (p#0)^(q-2) * (p#1)^2)},
 {"y_j^(q-2) p_2(y-l)", ideal apply(prs, p -> (p#0)^(q-2) * psum(select(vs, v -> v != p#1), 2))},
 {"y_j^(q-2) h_2(y-l)", ideal apply(prs, p -> (p#0)^(q-2) * hsum(select(vs, v -> v != p#1), 2))},
 {"y_j^(q-2) e_2(y-j-l)", ideal apply(prs, p -> (p#0)^(q-2) * esym(select(vs, v -> v != p#1 and v != p#0), 2))},
 {"y_j^(q-2) y_l e_1(y-j-l)", ideal apply(prs, p -> (p#0)^(q-2) * (p#1) * esym(select(vs, v -> v != p#1 and v != p#0), 1))},
 {"y_j^(q-2) y_l^2 + y_j^(q-2) e_2(y-l)", ideal apply(prs, p -> (p#0)^(q-2) * (p#1)^2) + ideal apply(prs, p -> (p#0)^(q-2) * esym(select(vs, v -> v != p#1), 2))},
 {"y_j^(q-3) y_l^3", ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^3)},
 {"y_j^(q-3) e_3(y-l)", ideal apply(prs, p -> (p#0)^(q-3) * esym(select(vs, v -> v != p#1), 3))}};
for c in cands22 do << "  + " << c#0 << " : " << degree(B22 + c#1) << endl << flush;
<< "=== (1,1,1,1) at n=6, target 1800" << endl;
B1111 = Qmu(vs, {1,1,1,1}) + Bx + layerN(vs, 0);
<< "Q + box + N_0 : " << degree B1111 << endl << flush;
cands1111 = {
 {"y_j^(q-4) y_l^4", ideal apply(prs, p -> (p#0)^(q-4) * (p#1)^4)},
 {"y_j^(q-4) p_4(y-l)", ideal apply(prs, p -> (p#0)^(q-4) * psum(select(vs, v -> v != p#1), 4))},
 {"y_j^(q-4) e_4(y-l)", ideal apply(prs, p -> (p#0)^(q-4) * esym(select(vs, v -> v != p#1), 4))},
 {"y_j^(q-4) h_4(y-l)", ideal apply(prs, p -> (p#0)^(q-4) * hsum(select(vs, v -> v != p#1), 4))},
 {"y_j^(q-3) y_l^3", ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^3)},
 {"y_j^(q-3) y_l^4", ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^4)},
 {"y_j^(q-4) y_l^3", ideal apply(prs, p -> (p#0)^(q-4) * (p#1)^3)},
 {"y_j^(q-4) y_l^5", ideal apply(prs, p -> (p#0)^(q-4) * (p#1)^5)}};
for c in cands1111 do << "  + " << c#0 << " : " << degree(B1111 + c#1) << endl << flush;
<< "FIN-OK" << endl;
