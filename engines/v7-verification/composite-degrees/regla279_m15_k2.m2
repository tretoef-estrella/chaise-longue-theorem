-- regla279 (Grepy el Auditor): literal [DS] ring for the Fermat FOURFOLD of degree 15 (k=2, n=4), not computed in [DS] or [AMV].
-- ESTIMATE before running: quotient of dim ~7.6e5 in 5 variables; Groebner basis could be large. Under vigia (1.2 GB / 600 s); may be killed.
m = 15;
clMatchings = L -> if #L == 0 then {{}} else flatten apply(drop(L,1), b -> apply(clMatchings(select(drop(L,1), x -> x != b)), M -> prepend({L#0,b}, M)));
clRun = p -> (
  S := ZZ/p[t_1..t_5]; T := {1_S} | toList(t_1..t_5);
  phi := w -> sum apply(m, e -> w^e);
  psi := J -> product apply(J, P -> (T#(P#1) - 1) * (if P#0 == 0 then 1 else phi(T#(P#0) * T#(P#1))));
  I := ideal apply(toList(1..5), i -> (T#i)^m - 1) + ideal apply(clMatchings toList(0..5), psi);
  m^5 - degree(S/I) );
for p in {31, 3, 5} do (<< "m=15 k=2 p=" << p << "  dim (psi_J)=" << clRun p << endl << flush);
<< "FIN-OK" << endl;
