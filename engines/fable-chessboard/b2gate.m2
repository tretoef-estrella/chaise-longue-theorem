load "m10unif.m2";
profs = {{1,1},{2,1},{3,1},{4,1},{2,2},{3,2},{1,1,1},{2,1,1},{3,1,1},{2,2,1},{1,1,1,1},{2,1,1,1}};
for mu in profs do for n from sum mu + 2 to 6 do gateU(9, n, mu, null);
<< "FIN-OK" << endl;
