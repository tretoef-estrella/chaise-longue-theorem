load "m11lib.m2";
-- R8: raise layer at child f = 3: is N_1(n) inside Known := K_(1^L)(n) + (x_{[n]\b}) + box ?  (L = ell+1)
runG = (q, n, L) -> (
  S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S; t0 := cpuTime();
  known := clK(ys, q, toList(L:1)) | apply(ys, b -> product delete(b, ys));
  Gk := gb ideal known; lay := clLayer(ys, 1, q);
  bad := select(lay, g -> g % Gk != 0);
  << "q=" << q << " n=" << n << " L=" << L << " (child f=" << n-L << ") : N_1(n) gens not in Known: " << #bad << " of " << #lay << " [" << cpuTime()-t0 << "s]" << endl << flush;
);
runG(9,5,2); runG(9,6,2); runG(9,6,3); runG(9,7,3); runG(9,7,4); runG(27,5,2);
<< "FIN-OK" << endl;
