chk = (k,q) -> (
  n := 2*k+1; S := ZZ/3[x_0..x_(n-1)]; x := gens S;
  el := j -> if j==0 then 1_S else if j>n then 0_S else sum(subsets(gens S, j), s -> product s);
  J0 := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal apply(x, v -> v^q);
  a := x#(n-2); b := x#(n-1); B := toList(0..n-3);
  sig := j -> if j<0 then 0_S else if j==0 then 1_S else if j>#B then 0_S else sum(subsets(B, j), s -> product(s, i -> x#i));
  r := a*b; beta := a+b;
  F := j -> sum(toList(0..(j-1)//2), s -> (-r)^s * el(j-2*s));
  Psi := sum(toList(0..k-1), s -> (-r)^s * sig(2*k-2-2*s));
  Wq := sum(toList(0..q-1), s -> (-1)^s * a^(q-1-s) * b^s);
  Wq2 := sum(toList(0..q-3), s -> (-1)^s * a^(q-3-s) * b^s);
  lhs := product(B, i -> x#i) * (a^(q-1) + b^(q-1));
  rhs := F(2*k-1)*(a^(q-1)+b^(q-1)) + F(2*k+1)*Wq2 - (a^q+b^q)*Psi;
  << "(k,q)=(" << k << "," << q << ") identity exact? " << toString(lhs == rhs) << "  Wq+r*Wq2 == a^(q-1)+b^(q-1)? " << toString(Wq + r*Wq2 == a^(q-1)+b^(q-1)) << "  lhs in J0? " << toString(lhs % J0 == 0) << endl;
);
chk(1,9); chk(2,9); chk(2,27); chk(3,3);
<< "FIN-OK" << endl; exit 0
