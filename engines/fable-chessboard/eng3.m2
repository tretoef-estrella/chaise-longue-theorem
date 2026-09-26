-- INFORME_9 STEP 1 run 4: finer tau probe at (6,2) + certificate multipliers
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
nn = 6; m = 2; n = 5; c = 2; d = q + n - m - 2;
S = ZZ/3[x_1..x_nn]; vs = gens S; z = x_nn; yv = take(vs, n);
I1 = ideal apply(select(toList(1..nn), j -> odd j), j -> esym(vs, j)) + ideal apply(vs, v -> v^q);
T = ZZ/3[x_1..x_n]; pz = map(T, S, append(gens T, 0_T)); yy = gens T;
ss = (yy#0)^(q-2) * esym(drop(yy, {1,1}), c);
yj = yv#0; yl = yv#1; P = drop(yv, {0,1});
rowOf = G -> pz((I1 + z*G + ideal(z^3)) : z^2);
tst = (name, G) -> ( R := rowOf G; ok := ((ss % R) == 0); << "  tau-set " << name << " : s in row? " << ok << "  (colength " << degree R << ")" << endl << flush; ok);
layerA = {
 {"yj^(q-1) x_C, C in P", ideal apply(subsets(P, c), C -> yj^(q-1) * product C)},
 {"yj^(q-1) yl x_p", ideal apply(P, p -> yj^(q-1) * yl * p)},
 {"yl^(q-1) x_C, C in P", ideal apply(subsets(P, c), C -> yl^(q-1) * product C)},
 {"yl^(q-1) yj x_p", ideal apply(P, p -> yl^(q-1) * yj * p)},
 {"yp^(q-1) yj yl", ideal apply(P, p -> p^(q-1) * yj * yl)},
 {"yp^(q-1) yj yp'", ideal flatten apply(P, p -> apply(select(P, r -> r != p), r -> p^(q-1) * yj * r))},
 {"yp^(q-1) yl yp'", ideal flatten apply(P, p -> apply(select(P, r -> r != p), r -> p^(q-1) * yl * r))},
 {"yp^(q-1) yp' yp''", ideal apply(P, p -> p^(q-1) * product select(P, r -> r != p))}};
sqB = {
 {"x_[n]-j", ideal product select(yv, v -> v != yj)},
 {"x_[n]-l", ideal product select(yv, v -> v != yl)},
 {"x_[n]-p (all p)", ideal apply(P, p -> product select(yv, v -> v != p))},
 {"e_n", ideal esym(yv, n)}};
<< "=== singles" << endl;
for A in layerA do tst(A#0, A#1);
for B in sqB do tst(B#0, B#1);
<< "=== pairs layer + squarefree" << endl;
for A in layerA do for B in sqB do tst(A#0 | " + " | B#0, A#1 + B#1);
<< "=== all layer + one squarefree ; one layer + all squarefree" << endl;
allA = sum apply(layerA, A -> A#1); allB = sum apply(sqB, B -> B#1);
for B in sqB do tst("ALL layer + " | B#0, allA + B#1);
for A in layerA do tst(A#0 | " + ALL squarefree", A#1 + allB);
<< "FIN-OK" << endl;
