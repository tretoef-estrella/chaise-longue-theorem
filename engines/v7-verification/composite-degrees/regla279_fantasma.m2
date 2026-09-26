-- regla279b (Grepy el Auditor, 2026-09-25). ESTIMATE before running: rings <= 5^7 = 78 125 monomials; < 600 MB, < 3 min.
-- Phantom bipartite count: A has a+1 variables x, B has a variables z; generators prod_{i != i0} (x_i - z_{s(i)})^(q-1),
-- over i0 in A and bijections s: A\{i0} -> B, in F_p[x,z]/(x^q, z^q). Prediction: dim ideal = #{(x,z) in S^{a+1} x S^a : multiset z <= multiset x}, |S| = q.
comps = (a,q) -> if q==1 then {{a}} else flatten apply(toList(0..a), i -> apply(comps(a-i,q-1), c -> prepend(i,c)));
multi = c -> ((sum c)!)/product apply(c, x -> x!);
-- count: sum over multisets x (composition c of a+1), times over sub-multisets y <= c of size a: multi(c)*multi(y)
Nph = (a,q) -> sum apply(comps(a+1,q), c -> multi(c) * sum apply(select(toList(0..q-1), i -> c#i > 0), i -> multi(apply(q, j -> if j==i then c#j - 1 else c#j))));
ph = (a,q,p) -> (
  S := ZZ/p[vars(0..2*a)]; X := take(gens S, a+1); Z := drop(gens S, a+1);
  box := ideal apply(gens S, v -> v^q);
  G := flatten apply(a+1, i0 -> (Xr := drop(X,{i0,i0}); apply(permutations a, s -> product apply(a, i -> (Xr#i - Z#(s#i))^(q-1)))));
  (q^(2*a+1) - degree(S/(box + ideal G)), Nph(a,q)) );
for c in {(1,3,3),(2,3,3),(3,3,3),(1,5,5),(2,5,5),(3,5,5),(1,9,3),(2,9,3),(2,7,7)} do (
  r := ph c; << "PHANTOM (a,q,p)=" << toString c << "  dim ideal=" << r#0 << "  count=" << r#1 << "  " << (if r#0==r#1 then "EQUAL" else "DIFFERENT") << endl << flush);
<< "FIN-OK" << endl;
