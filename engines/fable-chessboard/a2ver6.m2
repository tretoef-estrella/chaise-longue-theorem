load "m10cert.m2";
clres = {};
for q in {9} do for n from 3 to 6 do for m from 1 to n-2 do clres = append(clres, checkCell(q, n, m));
for q in {27} do for n from 3 to 5 do for m from 1 to n-2 do clres = append(clres, checkCell(q, n, m));
for q in {81} do for n from 3 to 4 do for m from 1 to n-2 do clres = append(clres, checkCell(q, n, m));
<< "ALL TRUE? " << all(clres, x -> x#0 and x#1) << endl;
<< "FIN-OK" << endl;
