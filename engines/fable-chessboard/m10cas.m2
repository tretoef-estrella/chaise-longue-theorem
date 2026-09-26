-- MISSION 10 PART B: true casilla G_mu(n) = gr I(W_mu(n)) from the fibre ideal of section 3.4, over GF(9)
-- anchor: profile mu -> multiset S: class i uses s_i with multiplicity mu_i. classes of F_9^*/{+-1}: 1, al, al^2, al^3
esymL = (L,j) -> if j < 0 or j > #L then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
trueCas = (q, n, mu, anc) -> (
  -- anc: list of class representatives (exponents of al) of length #mu
  Fq := GF(q, Variable => al);
  S := Fq[x_1..x_n, MonomialOrder => GRevLex]; ys := gens S;
  Sm := flatten apply(#mu, i -> toList(mu#i : (sub(al, S))^(anc#i)));
  nS := #Sm;
  eS := apply(toList(0..nS), r -> esymL(Sm, r));
  eY := apply(toList(0..n), r -> esymL(ys, r));
  Rj := j -> sum apply(toList(0..nS), r -> if j-r >= 0 and j-r <= n then (eS#r) * (eY#(j-r)) else 0_S);
  I := ideal(apply(select(toList(1..n+nS), j -> odd j), Rj) | apply(ys, v -> v^q - v));
  (S, ys, I));
topForms = (S, G) -> ideal apply(flatten entries gens G, g -> part(first degree g, g));
casilla = (q, n, mu, anc, dl) -> (
  (S, ys, I) := trueCas(q, n, mu, anc);
  t0 := cpuTime();
  G := if dl === null then gb I else gb(I, DegreeLimit => dl);
  J := topForms(S, G);
  (S, ys, J, cpuTime()-t0));
