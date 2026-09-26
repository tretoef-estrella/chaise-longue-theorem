cert = (q) -> (
  R := ZZ/3[x_0..x_3]; x := gens R;
  el := j -> if j==0 then 1_R else if j>4 then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el 1;
  P3 := el 3 - e1*el 2; P5 := -e1*el 4;
  K0 := ideal(P3, P5) + ideal apply(x, v -> v^q);
  ts := {};
  scan(subsets(4,2), ij -> ( lm := toList(set(0..3) - set ij);
     ts = append(ts, x#(ij#0)*x#(ij#1)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1)))));
  J1 := K0 + ideal apply(ts, t -> e1*t);
  << "== q=" << q << endl;
  rows := apply(toList(0..q-1), a -> numColumns basis(R/((J1 : e1^a) + ideal e1)));
  << " rows from J1cand: " << toString rows << endl;
  -- (U-a)
  m1 := x#0*x#1*x#2*x#3^(q-1);
  << " (U-a) x0x1x2x3^(q-1) in J1cand? " << toString(m1 % J1 == 0) << endl;
  << "       in K0 + (e1*t_{01|23}, e1*t_{02|13}, e1*t_{12|03})? " << toString(m1 % (K0 + ideal(e1*ts#0, e1*ts#1, e1*ts#2)) == 0) << endl;  -- pairs not containing 3: {0,1},{0,2},{1,2} are subsets 0,1,3 in M2 order? print
  << "       subsets(4,2) order: " << toString subsets(4,2) << endl;
  Rq1 := (J1 : e1^(q-1)) + ideal e1;
  << " (U) cubics x_ix_jx_l in R_{q-1}? " << toString apply(subsets(4,3), A -> (product(A, i->x#i)) % Rq1 == 0) << endl;
  << " (U) x_i x_j^(q-1) in R_{q-1}? " << toString apply({(0,1),(1,0),(2,3)}, p -> (x#(p#0)*x#(p#1)^(q-1)) % Rq1 == 0) << endl;
  << " (U) x_i x_j^(q-2) in R_{q-1}? " << toString((x#0*x#1^(q-2)) % Rq1 == 0) << endl;
  R2 := (J1 : e1^2) + ideal e1;
  e2' := x#1*x#2 + x#1*x#3 + x#2*x#3;
  << " (G) x2^2 x3^(q-2) in R_2? " << toString((x#2^2*x#3^(q-2)) % R2 == 0) << endl;
  << " (G) x3^(q-2) e2(x1,x2,x3) in R_2? " << toString((x#3^(q-2)*e2') % R2 == 0) << endl;
  << " (G) x2^(q-2) e2(x1,x2,x3) in R_2? " << toString((x#2^(q-2)*e2') % R2 == 0) << endl;
  << " (G) x_i^2 x_j^(q-2) in R_2 for all i!=j? " << toString apply({(0,1),(1,0),(0,3),(3,0),(1,2)}, p -> (x#(p#0)^2*x#(p#1)^(q-2)) % R2 == 0) << endl;
  << " (G) x_i x_j x_l^(q-2) in R_2? " << toString apply({(0,1,2),(0,1,3),(1,2,3)}, p -> (x#(p#0)*x#(p#1)*x#(p#2)^(q-2)) % R2 == 0) << endl;
  << " (G) e4 in R_2? " << toString((el 4) % R2 == 0) << " ; e3 in R_2? " << toString((el 3) % R2 == 0) << endl;
  << " (G) x_i x_j^(q-1) in R_2? " << toString apply({(0,1),(2,3)}, p -> (x#(p#0)*x#(p#1)^(q-1)) % R2 == 0) << endl;
  << " (G) hilbert R_2: " << toString apply(toList(0..q+1), d -> hilbertFunction(d, R/R2)) << endl;
  << " (G) which a has x_i x_j^(q-2) in R_a: " << toString select(toList(0..q-1), a -> (x#0*x#1^(q-2)) % ((J1 : e1^a) + ideal e1) == 0) << endl;
  << " (G) which a has x_i^2 x_j^(q-2) in R_a: " << toString select(toList(0..q-1), a -> (x#0^2*x#1^(q-2)) % ((J1 : e1^a) + ideal e1) == 0) << endl;
  << " (G) which a has x_ix_jx_l^(q-2) in R_a: " << toString select(toList(0..q-1), a -> (x#0*x#1*x#2^(q-2)) % ((J1 : e1^a) + ideal e1) == 0) << endl;
  << " (U) which a has x_ix_jx_l in R_a: " << toString select(toList(0..q-1), a -> (x#0*x#1*x#2) % ((J1 : e1^a) + ideal e1) == 0) << endl;
  << " (U) which a has x_ix_j^(q-1) in R_a: " << toString select(toList(0..q-1), a -> (x#0*x#1^(q-1)) % ((J1 : e1^a) + ideal e1) == 0) << endl;
  << flush;
);
cert(9); cert(27);
<< "FIN-OK" << endl; exit 0
