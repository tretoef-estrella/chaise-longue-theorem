-- Cell (2,9): rows of the explicit casillas K_2 (along x_4) and K'_2 (along x_3) versus gr I of the fibres of V_1 / V'_1.
-- Fibres: W_v = {y in F_q^{2k} : y u {v,1} closed under negation} (even side, 2k=4), W'_v = {y in F_q^{2k-1} : y u {v,1} closed} (odd side, 3 coords).
q = 9; F = GF(q, Variable=>w);
-- points of W_v in n coordinates, built combinatorially (no enumeration of F_q^n)
els = toList apply(q, i -> if i == 0 then 0_F else w^i);   -- all elements of F_q
closedSets = n -> ( -- all y in F^n with multiset closed under negation, n even: pairs. built recursively
  if n == 0 then {{}} else ( L := {}; prev := closedSets(n-2);
    for c in els do for p in prev do for pos from 0 to n-1 do for pos2 from 0 to n-1 do if pos != pos2 then (
        y := new MutableList from (n:null); y#pos = c; y#pos2 = -c; rest := 0; 
        for t from 0 to n-1 do if y#t === null then (y#t = p#rest; rest = rest+1);
        L = append(L, toList y));
    unique L));
Wfib = (n, v) -> ( -- y in F^n, y u {v,1} closed: contains -v and -1 (or the pair structure when v = -1, 0, 1)
  Z := closedSets(n+2); S := select(Z, y -> y#n == v and y#(n+1) == 1_F); unique apply(S, y -> take(y, n)));
grI = (pts, R) -> ( -- ideal of top forms of I(pts) in R (graded revlex)
  n := numgens R; Ipts := intersect apply(pts, p -> ideal apply(n, i -> R_i - p#i));
  Rh := (coefficientRing R)[gens R, symbol h]; Gh := homogenize(sub(ideal gens gb Ipts, Rh), Rh_n);
  sub(Gh, (vars R) | matrix{{0_R}}));
-- even side k=2: S5 = F[x0..x4], K2 = I5 + M2; rows R^K_a = pi'(K2 : x4^a) in S4
S5 = F[x_0..x_4]; S4 = F[y_0..y_3];
X = gens S5; e = j -> sum(subsets(X, j), s -> product s);
I5 = ideal(e 1, e 3, e 5) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
M2 = ideal(Mgen(toList(0..4), 1) | Mgen(toList(0..4), 2));
K2 = I5 + M2;
pi5 = map(S4, S5, {y_0,y_1,y_2,y_3,0});
row = a -> pi5(K2 : x_4^a);
<< "dim S5/K2 = " << degree K2 << endl << flush;
vals = {-1_F, 0_F, w, 1_F}; names = {"v=-1","v=0","v=generic(w)","v=+1"}; as = {0, 1, 2, q-1};
for i from 0 to 3 do ( Wv := Wfib(4, vals#i); G := grI(Wv, S4); Ra := row(as#i);
  << names#i << ": |W_v| = " << #Wv << ", colength grI = " << degree G << ", row a=" << as#i << " colength = " << degree Ra
  << ", grI(W_v) subset row? " << toString isSubset(G, Ra) << ", equal? " << toString(G == Ra) << endl << flush;);
-- also: all generic rows equal?
<< "rows a=2..q-2 all equal to row 2? " << toString all(toList(3..q-2), a -> row a == row 2) << endl << flush;
-- odd side k=2: S4' = F[x0..x3], K'2 = I4 + (e4) + M'2, rows along x3 in S3
X4 = {x_0,x_1,x_2,x_3}; e4f = j -> sum(subsets(X4, j), s -> product s);
S4b = F[x_0..x_3]; use S4b; X4 = gens S4b; e4f = j -> sum(subsets(X4, j), s -> product s);
I4 = ideal(e4f 1, e4f 3) + ideal apply(X4, u -> u^q);
Mgen4 = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X4#i) * product(A, i -> (X4#i)^(q-1)))); L);
Kp2 = I4 + ideal(e4f 4) + ideal Mgen4(toList(0..3), 1);
S3 = F[y_0..y_2]; pi4 = map(S3, S4b, {y_0,y_1,y_2,0});
rowp = a -> pi4(Kp2 : x_3^a);
<< "dim S4/K'2 = " << degree Kp2 << endl << flush;
for i from 0 to 3 do ( Wv := Wfib(3, vals#i); G := grI(Wv, S3); Ra := rowp(as#i);
  << "odd " << names#i << ": |W'_v| = " << #Wv << ", colength grI = " << degree G << ", row a=" << as#i << " colength = " << degree Ra
  << ", grI(W'_v) subset row? " << toString isSubset(G, Ra) << ", equal? " << toString(G == Ra) << endl << flush;);
<< "FIN-OK" << endl; exit 0
