-- INFORME_7 STEP 1: (3,9) colon (K3+(z^3)) : x1^(q-2): print ALL low (<=8) generators with x0 eliminated (x0 = -(x1+..+z)), and the certificate of the (G-a_3) target
q = 9;
S = ZZ/3[x0,x1,x2,x3,x4,x5,z]; vs = {x0,x1,x2,x3,x4,x5,z}; n = 7;
box = ideal apply(vs, v -> v^q);
e = j -> sum apply(subsets(vs, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + box;
Mk = ideal(0_S);
for j from 1 to 3 do (
  for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
    C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
    Mk = Mk + ideal((product apply(C, i -> vs#i)) * (product apply(A, i -> (vs#i)^(q-1))));
  );
);
K3 = I7 + Mk;
K3z = K3 + ideal(z^3);
C = K3z : x1^(q-2);
MC = mingens C;
low = select(numcols MC, i -> (degree MC_(0,i))#0 <= 8);
T = ZZ/3[x1,x2,x3,x4,x5,z];
ph = map(T, S, {-(x1+x2+x3+x4+x5+z), x1,x2,x3,x4,x5,z});
<< "=== low generators (x0 eliminated), degree : polynomial" << endl;
for i in low do << (degree MC_(0,i))#0 << " : " << ph(MC_(0,i)) << endl << endl;
-- reduce also modulo x1^2 (in the colon) to see the x1-linear structure
Tq = T/ideal(x1^2);
<< "=== same, modulo x1^2" << endl;
for i in low do << (degree MC_(0,i))#0 << " : " << sub(ph(MC_(0,i)), Tq) << endl << endl;
-- certificate of the target through the low generators
use S; t4 = z^2*x0^2*(sum apply(subsets({x1,x2,x3,x4,x5},2), s -> product s));
gl = matrix{apply(low, i -> MC_(0,i))};
Lc = t4 // gl;
<< "=== certificate: target = sum coeff_i * gen_i ; check " << (gl*Lc - matrix{{t4}} == 0) << endl;
for i from 0 to numrows Lc - 1 do if Lc_(i,0) != 0 then << "gen deg " << (degree MC_(0,(low#i)))#0 << " : coeff " << ph(Lc_(i,0)) << endl;
