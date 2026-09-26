cert2 = (q) -> (
  R := ZZ/3[x_0..x_3]; x := gens R;
  el := j -> if j==0 then 1_R else if j>4 then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el 1;
  P3 := el 3 - e1*el 2; P5 := -e1*el 4;
  K0 := ideal(P3, P5) + ideal apply(x, v -> v^q);
  prs := subsets(4,2);
  ts := apply(prs, ij -> ( lm := toList(set(0..3) - set ij); x#(ij#0)*x#(ij#1)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))));
  << "== q=" << q << "  t order (pairs ij, lm=complement): " << toString prs << endl;
  -- scalar combination test in degree q+1: target - sum c_i t_i in K0 ?
  scalarTest := (name, target) -> (
     found := false;
     -- brute force over F3^6 = 729 combos
     for v in toList((set{0,1,2}) ** (set{0,1,2}) ** (set{0,1,2}) ** (set{0,1,2}) ** (set{0,1,2}) ** (set{0,1,2})) do (
        vv := deepSplice v; cs := toList vv;
        if (target - sum(6, i -> cs#i * ts#i)) % K0 == 0 then (found = true; << " " << name << ": target = sum c_i t_i mod K0 with c = " << toString cs << endl; break;));
     if not found then << " " << name << ": NOT a scalar combination of t's mod K0" << endl;);
  scalarTest("(G-a) e1*x2^2*x3^(q-2)", e1*x#2^2*x#3^(q-2));
  scalarTest("(G-a') e1*x0^2*x1^(q-2)", e1*x#0^2*x#1^(q-2));
  scalarTest("(U-a) e1^(q-2)*x0*x1*x2", e1^(q-2)*x#0*x#1*x#2);
  scalarTest("(U-a') x0*x1*x2*x3^(q-2)... deg q+1: x0x1x2x3^(q-2)", x#0*x#1*x#2*x#3^(q-2));
  << " (U-a'') x0x1x2x3^(q-2) in J1cand? " << toString((x#0*x#1*x#2*x#3^(q-2)) % (K0 + ideal apply(ts, t->e1*t)) == 0) << endl;
  << " (U-a''') e1^(q-2) x0x1x2 in K0+(t's)? " << toString((e1^(q-2)*x#0*x#1*x#2) % (K0 + ideal ts) == 0) << endl;
  << " (G-a'') e1 x2^2 x3^(q-2) in K0+(t's)? " << toString((e1*x#2^2*x#3^(q-2)) % (K0 + ideal ts) == 0) << endl;
  << " (U-b) x0 x1^(q-1) x2^(q-1) in J1cand? " << toString((x#0*x#1^(q-1)*x#2^(q-1)) % (K0 + ideal apply(ts, t->e1*t)) == 0) << endl;
  << " (U-b') x0 x1^(q-1) e1^(q-1) in J1cand? " << toString((x#0*x#1^(q-1)*e1^(q-1)) % (K0 + ideal apply(ts, t->e1*t)) == 0) << endl;
  -- (U-b) certificate: multipliers of the e1*t's
  J1c := K0 + ideal apply(ts, t->e1*t);
  A := matrix{apply(ts, t->e1*t)} | gens K0;
  c := (matrix{{x#0*x#1^(q-1)*x#2^(q-1)}}) // A;
  << " (U-b) multipliers of e1*t_i: " << endl;
  scan(6, i -> << "   t" << toString prs#i << ": " << toString c_(i,0) << endl);
  << flush;
);
cert2(9); cert2(27);
<< "FIN-OK" << endl; exit 0
