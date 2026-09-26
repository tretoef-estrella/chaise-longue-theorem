-- Theorem A.12 (row inclusions R_a(K_mu(L u z)) >= K_{child_a(mu)}(L)), tested from the definitions of Appendix A.
-- Also the negative control of Remark A.14 (reversed lower-row order).
-- Usage: M2 --script thmA12.m2   (cells listed at the bottom)

betaW = (mu, w) -> sum(mu, m -> max(m - w, 0));

-- truncated power series in t with coefficients in R, as a list of length D+1
mulSer = (ser, fac, D) -> (
    res := new MutableList from toList((D+1) : 0_(ring ser#0));
    for i from 0 to D do if ser#i != 0 then
        for j from 0 to min(#fac - 1, D - i) do res#(i+j) = res#(i+j) + ser#i * fac#j;
    res);

thetaS = (R, L, A, B, s, q) -> (
    Pset := select(L, x -> not member(x, A) and not member(x, B));
    r := #A; D := r*(q-1) + #Pset + 1 - s;
    if D < 0 then return 0_R;
    ser := new MutableList from toList((D+1) : 0_R); ser#0 = 1_R;
    for x in Pset do ser = mulSer(ser, {1_R, -x}, D);
    for a in A do ser = mulSer(ser, for i from 0 to D list (if i == 0 then 1_R else 2*(-1)^i * a^i), D);
    ser#D);

esym = (R, L, j) -> (  -- e_j(L)
    n := #L; if j < 0 or j > n then return 0_R;
    ser := new MutableList from toList((n+1) : 0_R); ser#0 = 1_R;
    for x in L do ser = mulSer(ser, {1_R, x}, n);
    ser#j);

Iq = (R, L, q) -> ideal(join(for j from 1 to #L list (if odd j then esym(R, L, j) else 0_R), for x in L list x^q));

Kmu = (R, L, mu, q) -> (
    gens0 := {};
    for A in subsets L do for B in subsets(select(L, x -> not member(x, A))) do (
        w := #B - #A;
        if w < 0 then continue;
        for s from 1 to betaW(mu, w) do gens0 = append(gens0, thetaS(R, L, A, B, s, q)));
    Iq(R, L, q) + ideal(join({0_R}, gens0)));

childOf = (mu, a, q, rev) -> (
    l := #mu;
    if a < l then (
        idx := if rev then l-1-a else a;
        nu := replace(idx, mu#idx - 1, mu);
        rsort select(nu, m -> m > 0))
    else if a == l then mu
    else if a <= q - l - 1 then rsort append(mu, 1)
    else (j := q - a; rsort replace(j-1, mu#(j-1) + 1, mu)));

testCell = (p, q, n, mu, rev) -> (
    kk := if p == 0 then QQ else ZZ/p;
    R := kk[x_1..x_n, z];
    L := for i from 1 to n list x_i;
    Kplus := Kmu(R, append(L, z), mu, q);
    G := Kplus;
    out := {};
    for a from 0 to q-1 do (
        ch := childOf(mu, a, q, rev);
        Kch := Kmu(R, L, ch, q);
        Ga := G + ideal(z^(a+1));
        Qa := Ga : z^a;
        Ra := eliminate(Qa, {z});
        gbRa := gb Ra;
        bad := #select(Kch_*, g -> g % gbRa != 0);
        out = append(out, (a, ch, bad)));
    tot := sum(out, o -> o#2);
    stdio << "char " << p << " q=" << q << " |L|=" << n << " mu=" << toString mu << (if rev then " [REVERSED lower order]" else "") << " : generators outside their row = " << tot << "  " << (if tot == 0 then "ALL ROW INCLUSIONS HOLD" else "FAILS") << endl;
    stdio << "    per row (a, child, #outside): " << toString out << endl;
    );

-- cells (none of these is in the paper's list; the (3,9,5,(3,1)) pair reproduces the paper's control)
testCell(5, 5, 4, {2,1}, false);
testCell(5, 5, 4, {2,2}, false);
testCell(5, 5, 4, {3,1}, false);
testCell(7, 7, 4, {2,1,1}, false);
testCell(7, 7, 3, {3,2,1}, false);
testCell(11, 5, 4, {1,1}, false);
testCell(0, 5, 4, {2,1}, false);
testCell(3, 3, 5, {2}, false);
testCell(3, 9, 4, {2,2,1}, false);
testCell(3, 9, 4, {4,1}, false);
testCell(5, 5, 4, {2,1}, true);
testCell(3, 9, 4, {3,1}, true);
testCell(3, 9, 5, {3,1}, true);
testCell(3, 9, 5, {3,1}, false);
