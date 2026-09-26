-- Cell (3,9): the generic row R2 = pz'(K_3 : z^2) of K_3 along z = x_6, its colength vs |W_v| (k=3), and its generators beyond L = K'_3 + pz'(M_3 : z^2).
q = 9; S = ZZ/3[x_0..x_6]; X = gens S; e = j -> sum(subsets(X, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
M3 = ideal(Mgen(toList(0..6), 1) | Mgen(toList(0..6), 2) | Mgen(toList(0..6), 3));
K3 = I7 + M3; z = x_6;
S6 = ZZ/3[y_0..y_5]; pz = map(S6, S, {y_0,y_1,y_2,y_3,y_4,y_5,0});
<< "colon K3 : z^2 ..." << endl << flush;
R2 = pz(K3 : z^2);
<< "colength of row 2 = " << degree R2 << endl << flush;
R1 = pz(K3 : z); << "colength of row 1 = " << degree R1 << endl << flush;
Rq = pz(K3 : z^(q-1)); << "colength of row q-1 = " << degree Rq << endl << flush;
-- explicit L = K'_3 + pz'(M_3 : z^2)
Y = gens S6; e6 = j -> sum(subsets(Y, j), s -> product s);
Mgen6 = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> Y#i) * product(A, i -> (Y#i)^(q-1)))); L);
Kp3 = ideal(e6 1, e6 3, e6 5) + ideal apply(Y, u -> u^q) + ideal(e6 6) + ideal(Mgen6(toList(0..5),1) | Mgen6(toList(0..5),2));
L = Kp3 + pz(M3 : z^2);
<< "L subset R2? " << toString isSubset(L, R2) << ", colength L = " << degree L << endl << flush;
-- generators of R2 beyond L: reduce a minimal generating set of R2 modulo L
G = flatten entries mingens R2; extra = select(G, g -> g % L != 0);
<< "minimal generators of R2: " << #G << "; not in L: " << #extra << "; their degrees: " << toString sort apply(extra, degree) << endl << flush;
<< "first few extra generators: " << endl; for g in take(extra, 6) do << "   " << toString g << endl;
-- |W_v| for k=3, q=9 combinatorially: y in F_9^6 with y u {v,1} closed = positions of -v, -1 and Z_4 on the rest, deduplicated
F = GF(q, Variable=>w); els = toList apply(q, i -> if i == 0 then 0_F else w^i);
closedSets = n -> ( if n == 0 then {{}} else ( LL := {}; prev := closedSets(n-2);
    for c in els do for p in prev do for pos from 0 to n-1 do for pos2 from 0 to n-1 do if pos != pos2 then (
        yy := new MutableList from (n:null); yy#pos = c; yy#pos2 = -c; rest := 0;
        for t from 0 to n-1 do if yy#t === null then (yy#t = p#rest; rest = rest+1);
        LL = append(LL, toList yy));
    unique LL));
Z4 = closedSets 4; v = w;
Wv = unique flatten for i from 0 to 5 list for j from 0 to 5 list if i == j then continue else flatten for p in Z4 list (
   yy := new MutableList from (6:null); yy#i = -v; yy#j = -1_F; rest := 0; for t from 0 to 5 do if yy#t === null then (yy#t = p#rest; rest = rest+1); {toList yy});
<< "|W_v| (k=3,q=9,v generic) = " << #Wv << endl;
<< "FIN-OK" << endl; exit 0
