-- regla279 (Grepy el Auditor, 2026-09-25): composite odd degree, feasibility gates. ESTIMATE written before running:
-- all rings <= 16 000 monomials in <= 8 variables; Groebner bases tiny; < 200 MB, < 60 s total.
-- G1 (bipartite count): dim_F of the ideal (prod_i (x_i - z_{s(i)})^(q-1) : s in S_a) in F_p[x,z]/(x^q,z^q)
--    against N(a,q) = sum over compositions c of a into q parts of (a!/prod c!)^2 (pairs of a-tuples, one a permutation of the other).
-- G2 (literal [DS] ring, composite m): dim of (psi_J : J) in F[t_1..t_3]/(t_i^m - 1), k=1, over F_3, F_5 (p | m) and F_31 (splits mu_15, = char 0).
comps = (a,q) -> if q==1 then {{a}} else flatten apply(toList(0..a), i -> apply(comps(a-i,q-1), c -> prepend(i,c)));
N = (a,q) -> sum apply(comps(a,q), c -> (a!/product apply(c, x -> x!))^2);
bip = (a,q,p) -> (
  S := ZZ/p[vars(0..2*a-1)]; X := take(gens S, a); Z := drop(gens S, a);
  box := ideal apply(gens S, v -> v^q);
  G := apply(permutations a, s -> product apply(a, i -> (X#i - Z#(s#i))^(q-1)));
  Q := degree(S/(box + ideal G));
  (q^(2*a) - Q, N(a,q)) );
for c in {(1,3,3),(2,3,3),(3,3,3),(4,3,3),(2,5,5),(3,5,5),(2,7,7),(2,9,3),(3,9,3)} do (
  r := bip c; << "G1 bipartite (a,q,p)=" << toString c << "  dim ideal=" << r#0 << "  N=" << r#1 << "  " << (if r#0==r#1 then "EQUAL" else "DIFFERENT") << endl << flush);
-- literal [DS], k=1 (n=2): coordinates 0..3, t_0 implicit; matchings of {0,1,2,3}: J = {0,k0},{j1,k1}
lit = (m,p) -> (
  S := ZZ/p[t_1..t_3]; T := {1_S} | toList(t_1..t_3);
  phi := w -> sum apply(m, e -> w^e);
  Js := {{{0,1},{2,3}}, {{0,2},{1,3}}, {{0,3},{1,2}}};
  psi := J -> (T#(J#0#1) - 1) * (T#(J#1#1) - 1) * phi(T#(J#1#0) * T#(J#1#1));
  I := ideal apply(toList(1..3), i -> (T#i)^m - 1) + ideal apply(Js, psi);
  m^3 - degree(S/I) );
for c in {(15,3),(15,5),(15,31),(21,3),(21,7),(21,43),(9,3),(9,19)} do (
  << "G2 literal k=1 (m,p)=" << toString c << "  dim (psi_J)=" << lit c << endl << flush);
<< "FIN-OK" << endl;
