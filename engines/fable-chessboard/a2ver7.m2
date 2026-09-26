load "m10cert.m2";
clres = {};
for m from 1 to 5 do clres = append(clres, checkCell(9, 7, m));
<< "ALL TRUE? " << all(clres, x -> x#0 and x#1) << endl;
<< "FIN-OK" << endl;
