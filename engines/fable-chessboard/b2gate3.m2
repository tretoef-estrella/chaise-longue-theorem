load "b2gate2.m2";
<< "--- leaves f <= 1, q = 9 ---" << endl;
profs2 = {{1,1},{2,1},{3,1},{4,1},{2,2},{3,2},{1,1,1},{2,1,1},{3,1,1},{2,2,1},{1,1,1,1},{2,1,1,1}};
for mu in profs2 do for n from max(sum mu, 2) to min(sum mu + 1, 6) do gateU2(9, n, mu, null);
<< "--- q = 27, n <= 5, f >= 2 ---" << endl;
for mu in {{1,1},{2,1},{1,1,1}} do for n from sum mu + 2 to 5 do gateU2(27, n, mu, null);
<< "FIN-OK" << endl;
