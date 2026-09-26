load "m10unif.m2";
t0 = cpuTime();
(S, ys, G, tm) = casilla(9, 7, {1,1,1}, {0,1,2}, 17);
<< "G computed, colength " << degree G << " [" << cpuTime()-t0 << " s]" << endl << flush;
K = Qmu(S, ys, {1,1,1}) + ideal apply(ys, v -> v^9) + famPhi(ys, 9, 3, 4 + 3 - 2);
K = ideal mingens K;
<< "K' = Q + box + F_(1,1,1) (layer N_0 omitted: redundant for (1^l)) built [" << cpuTime()-t0 << " s]" << endl << flush;
<< "K' == G (as ideals)? " << (K == G) << " [" << cpuTime()-t0 << " s]" << endl << flush;
<< "FIN-OK" << endl;
