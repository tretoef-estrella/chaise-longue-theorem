load "m10cas.m2";
fib = hashTable {
 {1,1} => {0,0,2,6,84,380,3930,22302}, {2,1} => {0,0,0,3,12,200,1080,12390}, {3,1} => {0,0,0,0,4,20,390,2450},
 {4,1} => {0,0,0,0,0,5,30,672}, {2,2} => {0,0,0,0,6,30,570,3570}, {3,2} => {0,0,0,0,0,10,60,1295},
 {1,1,1} => {0,0,0,6,24,360,1920,20370}, {2,1,1} => {0,0,0,0,12,60,1020,6300}, {3,1,1} => {0,0,0,0,0,20,120,2310},
 {2,2,1} => {0,0,0,0,0,30,180,3360}, {1,1,1,1} => {0,0,0,0,24,120,1800,10920}, {2,1,1,1} => {0,0,0,0,0,60,360,5880}};
profs = {{1,1},{2,1},{3,1},{4,1},{2,2},{3,2},{1,1,1},{2,1,1},{3,1,1},{2,2,1},{1,1,1,1},{2,1,1,1}};
for mu in profs do for n from sum mu to 6 do (
  fb := (fib#mu)#n; if fb == 0 then continue;
  anc1 := toList(0..#mu-1); anc2 := reverse apply(#mu, i -> 3 - i);
  (S, ys, J, tm) := casilla(9, n, mu, anc1, null);
  cl := degree J;
  (S2, ys2, J2, tm2) := casilla(9, n, mu, anc2, null);
  same := (sub(J2, S) == J);
  mg := flatten entries mingens J;
  << "mu=" << toString mu << " n=" << n << " f=" << n - sum mu << " : colength " << cl << " fibre " << fb << (if cl == fb then " OK" else " MISMATCH") << " ; anchor-indep " << same << " ; mingens by degree " << toString sort pairs tally apply(mg, g -> first degree g) << " [" << tm << " s]" << endl << flush;
);
<< "FIN-OK" << endl;
