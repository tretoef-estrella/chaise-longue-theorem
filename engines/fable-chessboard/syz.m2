prep = (k,q) -> (
  m := 2*k; R := ZZ/3[x_0..x_(m-1)];
  el := j -> if j==0 then 1_R else if j>m then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el(1);
  P := apply(toList(1..k), i -> el(2*i+1) - e1*el(2*i));
  box := apply(gens R, v -> v^q);
  K0 := ideal(P | box);
  M := matrix{P | box};
  Z := syz M;
  w := matrix{apply(toList(1..k), i -> el(2*i-1))};
  Nmat := w * Z^(toList(0..k-1));
  (R, el, e1, P, K0, M, Z, w, Nmat)
);
test2 = (q) -> (
  (R, el, e1, P, K0, M, Z, w, Nmat) := prep(2,q);
  N := ideal Nmat;
  x := gens R;
  cand := {};
  scan(subsets(4,2), ij -> ( lm := toList(set(0..3) - set ij);
     cand = append(cand, x#(ij#0)*x#(ij#1)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1)))));
  << "(2," << q << ") each candidate in N+K0? " << toString apply(cand, c -> c % (N+K0) == 0) << endl;
  << "(2," << q << ") N+K0 == K0 + (candidates)? " << toString (N+K0 == K0 + ideal cand) << endl;
  -- explicit syzygy for t = x0 x1 (x2^{q-1} - x3^{q-1})
  t := x#0*x#1*(x#2^(q-1) - x#3^(q-1));
  A := Nmat | gens K0;
  c := (matrix{{t}}) // A;
  ncol := numColumns Nmat;
  cc := c^(toList(0..ncol-1));
  g := Z^{0,1} * cc;   -- (g3, g5)
  g3 := g_(0,0); g5 := g_(1,0);
  << "  check syzygy: g3*P3+g5*P5 in box? " << toString ((g3*P#0 + g5*P#1) % ideal(apply(gens R, v->v^q)) == 0) << endl;
  << "  check image: g3*e1+g5*e3 - t in K0? " << toString ((g3*e1 + g5*el(3) - t) % K0 == 0) << endl;
  << "  g3 = " << toString g3 << endl;
  << "  g5 = " << toString g5 << endl;
  << flush;
);
test2(3); test2(9); test2(27);
-- k=3, q=3
(R, el, e1, P, K0, M, Z, w, Nmat) = prep(3,3);
N = ideal Nmat;
Nmin = trim(N + K0);
Nred = select(flatten entries gens Nmin, g -> g % K0 != 0);
<< "(3,3) N mod K0: #gens " << #Nred << " degrees " << toString apply(Nred, g -> first degree g) << endl;
x = gens R; q = 3;
cand3 = {};
scan(subsets(6,4), A -> ( lm := toList(set(0..5) - set A);
   cand3 = append(cand3, product(A, i -> x#i)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1)))));
<< "(3,3) each x_A(x_l^{q-1}-x_m^{q-1}) in N+K0? " << toString apply(cand3, c -> c % (N+K0) == 0) << endl;
<< "(3,3) N+K0 == K0 + (candidates)? " << toString (N+K0 == K0 + ideal cand3) << endl;
<< "(3,3) rows via lemma E: " << toString apply(toList(0..2), a -> numColumns basis(R/(((K0 + e1*N) : e1^a) + ideal e1))) << endl;
<< "FIN-OK" << endl; exit 0
