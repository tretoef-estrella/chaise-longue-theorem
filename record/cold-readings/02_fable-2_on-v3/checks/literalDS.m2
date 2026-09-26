-- Literal forms of [DS] as an independent numerical test of the translation of Section 2.
-- (a) Theorem 1.1(a) form: dim_{F_3} R/(psi_J) with R=F_3[t_1..t_{n+1}]/(t_i^m-1), psi_J = tau_J * prod phi(t_{j_i}t_{k_i}).
--     Prop 2.5 predicts m^{n+1} - Q_k(m):  (1,9): 729-168=561 ; (2,3): 243-20=223 ; (1,3): 27-6=21.
-- (b) Section 5 form: dim_{F_3} Rbar/(rho_J), Rbar = F_3[t]/(phi(t_i)); predicted (m-1)^{n+1} - Q: (1,9): 512-168=344 ; (2,3): 32-20=12 ; (1,3): 8-6=2.
-- (c) Corollary 6.1 at (k,q)=(2,3): dim F_3[x_0..x_5]/(e_1,e_3,e_5,x_i^3) = P_2(3) = 141 (paper, Section 1.3).
-- (d) Remark 6.3(1): char 2, n=4: dims 21,65,133,225 for q=3,5,7,9.
matchingsOf = (S) -> ( if #S == 0 then return {{}}; a := S#0; flatten for i from 1 to #S-1 list ( b := S#i; rest := select(S, x -> x != a and x != b); for M in matchingsOf(rest) list prepend({a,b}, M)));
phiPoly = (u, m) -> sum(for i from 0 to m-1 list u^i);
rhoPoly = (x, y, m) -> sum(for mu from 0 to m-2 list x^mu * sum(for nu from 0 to mu list y^nu));
testA = (k, m) -> (
    n := 2*k; N := n+2;
    R := ZZ/3[t_1..t_(n+1)];
    tt := i -> if i == 0 then 0 else t_i;   -- t_0 never appears
    box := ideal(for i from 1 to n+1 list t_i^m - 1);
    boxbar := ideal(for i from 1 to n+1 list phiPoly(t_i, m));
    Js := matchingsOf(toList(0..N-1));
    psis := for J in Js list ( tau := product(J, pr -> t_(pr#1) - 1); tau * product(select(J, pr -> pr#0 != 0), pr -> phiPoly(t_(pr#0)*t_(pr#1), m)));
    rhos := for J in Js list product(select(J, pr -> pr#0 != 0), pr -> rhoPoly(t_(pr#0), t_(pr#1), m));
    dA := degree (box + ideal psis);
    dB := degree (boxbar + ideal rhos);
    stdio << "(k,m)=(" << k << "," << m << "): #J=" << #Js << "  dim R/(psi_J) = " << dA << "   dim Rbar/(rho_J) = " << dB << endl;
    );
testA(1,3); testA(2,3); testA(1,9);
-- (c)
S6 = ZZ/3[x_0..x_5];
esym = (L, j) -> ( n := #L; ser := new MutableList from toList((n+1):0_(ring L#0)); ser#0 = 1_(ring L#0); for x in L do ( nw := new MutableList from toList((n+1):0_(ring L#0)); for i from 0 to n do ( nw#i = nw#i + ser#i; if i+1 <= n then nw#(i+1) = nw#(i+1) + ser#i * x); ser = nw); ser#j);
L6 = for i from 0 to 5 list x_i;
stdio << "Cor 6.1 at (2,3): dim = " << degree(ideal(esym(L6,1), esym(L6,3), esym(L6,5)) + ideal(for x in L6 list x^3)) << "  (paper: P_2(3)=141)" << endl;
-- (d)
for q in {3,5,7,9} do ( S4 := ZZ/2[y_1..y_4]; L4 := for i from 1 to 4 list y_i; stdio << "char 2, n=4, q=" << q << ": dim = " << degree(ideal(esym(L4,1), esym(L4,3)) + ideal(for y in L4 list y^q)) << endl;);
