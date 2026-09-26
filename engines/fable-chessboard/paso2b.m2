-- (a) Lema E impar: filas desde K'_0 + e1 N' vs tablero_impar
lemaEimpar = (k,q) -> (
  m := 2*k-1; R := ZZ/3[y_0..y_(m-1)];
  el := j -> if j==0 then 1_R else if j>m then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el 1;
  P := apply(toList(1..k), i -> el(2*i+1) - e1*el(2*i));   -- P'_3..P'_{2k+1} (el ultimo es 0)
  box := apply(gens R, v -> v^q);
  K0 := ideal(P | box);
  Z := syz matrix{P | box};
  w := matrix{apply(toList(1..k), i -> el(2*i-1))};
  N := ideal(w * Z^(toList(0..k-1)));
  J1 := K0 + e1*N;
  r := apply(toList(0..q-1), a -> numColumns basis(R/((J1 : e1^a) + ideal e1)));
  << "LemaE impar (k,q)=(" << k << "," << q << ") r'=" << toString r << endl << flush;
);
lemaEimpar(1,9); lemaEimpar(2,3); lemaEimpar(2,9); lemaEimpar(3,3);
-- (b) certificado de la identidad "+" de nivel 2 en (2,9): x0 (x1^8 x2^8 + x3^8 x4^8) en J0
q = 9; S = ZZ/3[x_0..x_4]; x = gens S;
el = j -> sum(subsets(gens S, j), s -> product s);
G = {el 1, el 3, el 5} | apply(x, u -> u^q);
tgt = x_0*(x_1^(q-1)*x_2^(q-1) + x_3^(q-1)*x_4^(q-1));
c = matrix{{tgt}} // matrix{G};
<< "certificado '+' nivel 2, (2,9):" << endl;
<< "  e1: #terms " << #terms c_(0,0) << "  degree " << degree c_(0,0) << endl;
<< "  e3: " << toString c_(1,0) << endl;
<< "  e5: " << toString c_(2,0) << endl;
-- (c) familia x_C x_{A'}^{q-1} genera Q en (3,3)?
n = 8; q = 3; T = ZZ/3[z_0..z_(n-1)];
elT = j -> sum(subsets(gens T, j), s -> product s);
I8 = ideal(apply(select(toList(1..n), j -> odd j), j -> elT j)) + ideal(apply(gens T, u -> u^q));
T1 = ZZ/3[z_0..z_(n-2)]; f1 = map(T1, T, gens T1 | {0_T1}); J1 = f1(I8 : z_(n-1));
T2 = ZZ/3[z_0..z_(n-3)]; f2 = map(T2, T1, gens T2 | {0_T2}); Rq = f2(J1 : (z_(n-2))^(q-1));
y = gens T2; m = 6;
elY = j -> sum(subsets(y, j), s -> product s);
fam = flatten apply(toList(0..2), j -> flatten apply(subsets(m, j), A -> ( C := subsets(select(toList(0..m-1), i -> not member(i,A)), m-1-2*j);
    apply(C, Cs -> product(Cs, i -> y#i) * product(A, i -> y#i^(q-1))))));
Cand := ideal(elY 1, elY 3, elY 5) + ideal fam + ideal apply(y, u -> u^q);
<< "(3,3) fila +1: r=" << numColumns basis(T2/Rq) << "  cand2 (e_odd, x_C x_A'^(q-1) j=0,1,2, caja): dim=" << numColumns basis(T2/Cand) << "  igual? " << toString(Cand == Rq) << "  cand2 ⊆ R? " << toString(isSubset(Cand,Rq)) << endl;
<< "FIN-OK" << endl; exit 0
