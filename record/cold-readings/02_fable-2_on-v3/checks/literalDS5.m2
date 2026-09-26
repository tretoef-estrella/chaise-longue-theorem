-- literal [DS] rings over F_5 and F_7 (Theorem 1.1(a) form and Section-5 form) at (k,m)=(1,5),(1,7),(2,5):
-- predicted m^{n+1}-Q and (m-1)^{n+1}-Q: (1,5): 125-36=89, 64-36=28 ; (1,7): 343-90=253, 216-90=126 ; (2,5): 3125-400=2725, 1024-400=624
matchingsOf = (S) -> ( if #S == 0 then return {{}}; a := S#0; flatten for i from 1 to #S-1 list ( b := S#i; rest := select(S, x -> x != a and x != b); for M in matchingsOf(rest) list prepend({a,b}, M)));
phiPoly = (u, m) -> sum(for i from 0 to m-1 list u^i);
rhoPoly = (x, y, m) -> sum(for mu from 0 to m-2 list x^mu * sum(for nu from 0 to mu list y^nu));
testA = (p, k, m) -> ( n := 2*k; N := n+2; R := ZZ/p[t_1..t_(n+1)];
    box := ideal(for i from 1 to n+1 list t_i^m - 1); boxbar := ideal(for i from 1 to n+1 list phiPoly(t_i, m));
    Js := matchingsOf(toList(0..N-1));
    psis := for J in Js list ( tau := product(J, pr -> t_(pr#1) - 1); tau * product(select(J, pr -> pr#0 != 0), pr -> phiPoly(t_(pr#0)*t_(pr#1), m)));
    rhos := for J in Js list product(select(J, pr -> pr#0 != 0), pr -> rhoPoly(t_(pr#0), t_(pr#1), m));
    stdio << "char " << p << " (k,m)=(" << k << "," << m << "): dim R/(psi_J) = " << degree(box + ideal psis) << "   dim Rbar/(rho_J) = " << degree(boxbar + ideal rhos) << endl;);
testA(5,1,5); testA(7,1,7); testA(5,2,5);
