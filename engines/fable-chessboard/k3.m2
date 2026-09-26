-- (3,3): n=8, S'' = F3[x0..x5], 5-variable-analog S' = F3[x0..x6]
q = 3; k = 3;
R = ZZ/3[x_0..x_5]; x = gens R;
el = j -> if j==0 then 1_R else if j>6 then 0_R else sum(subsets(gens R, j), s -> product s);
e1 = el 1;
P = apply(toList(1..k), i -> el(2*i+1) - e1*el(2*i));
box = apply(x, v -> v^q);
K0 = ideal(P | box);
M = matrix{P | box};
Z = syz M;
w = matrix{apply(toList(1..k), i -> el(2*i-1))};
Nmat = w * Z^(toList(0..k-1));
N = ideal Nmat;
J1 = K0 + e1*N;
-- candidates: x_A (x_l^{q-1} - x_m^{q-1}), |A|=4  (already: in N+K0 but not generating)
-- Which S_6-orbits of degree-6 monomial-type elements generate N mod K0? test some natural families:
fam1 = flatten apply(subsets(6,4), A -> ( lm := toList(set(0..5) - set A); {product(A,i->x#i)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))}));
<< "fam1 (x_A(x_l^2-x_m^2)) generates N mod K0? " << toString(N + K0 == K0 + ideal fam1) << endl;
-- fam2: x_i x_j x_l x_m^{q-1}... no. Try: e_{2}(A)-type: x_i x_j (x_l x_m)(...)? Let's get the degree-6 part of (N+K0)/K0 dimension and of K0+fam1:
d6 = d -> (hilbertFunction(d, R/K0) - hilbertFunction(d, R/(N+K0)));
<< "dim (N+K0)/K0 in degree 6: " << d6(6) << " ; with fam1 only: " << (hilbertFunction(6, R/K0) - hilbertFunction(6, R/(K0+ideal fam1))) << endl;
<< "dim (N+K0)/K0 by degree 4..9: " << toString apply(toList(4..9), d6) << endl;
-- Try fam3: x_i x_j (x_a x_b)^{?}... For q=3, q-1=2. Candidate: x_i x_j x_l x_m (x_a^2 - x_b^2) is fam1. Candidate fam2: x_i x_j (x_l^2 x_m^2 - x_a^2 x_b^2)? degree 6.
fam2 = flatten apply(subsets(6,2), ij -> ( rest := toList(set(0..5) - set ij); 
   flatten apply(subsets(rest,2), lm -> ( ab := toList(set rest - set lm); {x#(ij#0)*x#(ij#1)*(x#(lm#0)^2*x#(lm#1)^2 - x#(ab#0)^2*x#(ab#1)^2)}))));
<< "fam2 each in N+K0? " << toString(all(fam2, f -> f % (N+K0) == 0)) << endl;
<< "fam1+fam2 generate? " << toString(N + K0 == K0 + ideal fam1 + ideal fam2) << endl;
-- fam4: x_i x_j x_l (x_m^2 x_a - ...)? print the reduced generators mod K0 in a readable form: reduce each against GB of K0+fam1
G1 = flatten entries gens gb (K0 + ideal fam1);
extra = select(flatten entries gens trim(N+K0), g -> g % (K0 + ideal fam1) != 0);
<< "extra generators beyond fam1: " << #extra << endl;
scan(extra, g -> << "   " << toString(g % (K0 + ideal fam1)) << endl);
-- rows check and (U-a+) analog: in 7 vars S' = F3[x0..x6]: is x0x1x2x3x4 (x5^{q-1} + x6^{q-1}) in J0 = (e1,e3,e5,e7,box)?
S7 = ZZ/3[y_0..y_6]; y = gens S7;
el7 = j -> sum(subsets(gens S7, j), s -> product s);
J0 = ideal(el7 1, el7 3, el7 5, el7 7) + ideal apply(y, v -> v^q);
tgtp = y#0*y#1*y#2*y#3*y#4*(y#5^(q-1) + y#6^(q-1));
<< "(3,3) (U-a+) analog: x_A (x5^{q-1}+x6^{q-1}) in J0 (|A|=5)? " << toString(tgtp % J0 == 0) << endl;
tgtm = y#0*y#1*y#2*y#3*y#4*(y#5^(q-1) - y#6^(q-1));
J1full = ideal(el7 1, el7 3, el7 5, el7 7) + ideal apply(y, v -> v^q);
I8 = (ZZ/3[z_0..z_7]);
<< "FIN-OK" << endl; exit 0
