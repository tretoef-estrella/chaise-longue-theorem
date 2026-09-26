-- pointwise form of G-a on Z_5(F_q), q=9: y4^2 y0^2 y1^(q-2) in span{y_C [y_a != 0]} + y4^3 (deg q-1) + F_{q+1}
q = 9; K = GF(q, Variable=>w);
pts = {}; els = toList apply(0..q-1, i -> if i==0 then 0_K else w^i);
-- enumerate Z_5(F_q): multiset closed under negation
isClosed = v -> ( t := tally v; all(keys t, x -> t#x == (if t#?(-x) then t#(-x) else 0)) );
for v0 in els do for v1 in els do for v2 in els do for v3 in els do for v4 in els do ( v := {v0,v1,v2,v3,v4}; if isClosed v then pts = append(pts, v));
<< "|Z_5(F_9)| = " << #pts << "  (P'_2(9) should be 25+8*88=729? no: P'_2 = A'_2 = 1 + ... )" << endl;
-- functions as vectors over F_q indexed by points
R = K[y_0..y_4];
ev = f -> matrix{apply(pts, p -> sub(f, matrix{p}))};
-- F_{q+1}: span of all monomials of degree <= q+1 (reduced exponents <= q-1)
mons = d -> flatten entries basis(d, R, Variables=>gens R);
lowmons = flatten apply(toList(0..q+1), d -> select(mons d, m -> all(first exponents m, e -> e <= q-1)));
<< "#monomials of degree <= q+1 with exponents <= q-1: " << #lowmons << endl;
Flow = matrix apply(lowmons, m -> flatten entries ev m);   -- rows = functions
rk := rank Flow;
<< "dim F_{q+1} on Z_5 = " << rk << endl;
-- N_d part: y_C [y_a != 0] for |C|=3, and y4^3 * (monomials of degree q-1, exponents <= q-1)
Cmons = flatten apply(subsets(5,3), C -> apply(select(toList(0..4), a -> not member(a,C)), a -> product(C, i -> y_i) * y_a^(q-1)));
y4part = apply(select(mons(q-1), m -> all(first exponents m, e -> e <= q-1)), m -> y_4^3 * m);
Nrows = matrix apply(Cmons | y4part, m -> flatten entries ev m);
tgt = ev(y_4^2 * y_0^2 * y_1^(q-2));
big = Flow || Nrows;
<< "rank(F_{q+1} + N) = " << rank big << "   rank with target = " << rank(big || tgt) << "   G-a pointwise holds? " << toString(rank big == rank(big || tgt)) << endl;
<< "rank(F_{q+1} + target) = " << rank(Flow || tgt) << " (is target already of degree <= q+1? " << toString(rank(Flow||tgt) == rk) << ")" << endl;
<< "rank(F_{q+1} + Cmons only) = " << rank(Flow || matrix apply(Cmons, m -> flatten entries ev m)) << endl;
<< "FIN-OK" << endl; exit 0
