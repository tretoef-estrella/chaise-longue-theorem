-- which low generators of the x1-free colon are needed for z^2 x0^2 ? (q-free test in 4 variables x0,x2,x3,z; symmetric closure over perms of {x0,x2,x3})
T = ZZ/3[x0,x2,x3,z]; vs = {x0,x2,x3,z};
e1p = x0+x2+x3+z; e2p = x0*x2+x0*x3+x0*z+x2*x3+x2*z+x3*z;
cubic = x0*x2^2 + x2^3 - x0*x2*x3 - x2^2*x3 + x0*x3^2 - x2*x3^2 + x3^3 - x2^2*z - x2*x3*z - x3^2*z - x0*z^2;
perms = {{x0,x2,x3},{x0,x3,x2},{x2,x0,x3},{x2,x3,x0},{x3,x0,x2},{x3,x2,x0}};
symm = f -> apply(perms, p -> sub(f, {x0 => p#0, x2 => p#1, x3 => p#2}));
Ieasy = ideal(e1p^2, z^3, z*e2p) + ideal(symm cubic) + ideal(x0^3*z, x2^3*z, x3^3*z);
I7 = ideal(x2*x3*z*(x2+x3+z), x0*x3*z*(x0+x3+z), x0*x2*z*(x0+x2+z));
Isq = ideal(x0^2*z^2, x2^2*z^2, x3^2*z^2);
<< "cubic symmetric images distinct: " << #unique(symm cubic) << endl;
<< "z^2 x0^2 in Ieasy: " << ((z^2*x0^2) % Ieasy == 0) << endl;
<< "z^2 x0^2 in Ieasy + I7: " << ((z^2*x0^2) % (Ieasy + I7) == 0) << endl;
<< "z^2 x0^2 in Ieasy + I7 + (x2^2 z^2, x3^2 z^2): " << ((z^2*x0^2) % (Ieasy + I7 + ideal(x2^2*z^2, x3^2*z^2)) == 0) << endl;
<< "x2 x3 z (x2+x3+z) in Ieasy + Isq: " << ((x2*x3*z*(x2+x3+z)) % (Ieasy + Isq) == 0) << endl;
<< "is the cubic in (e1p, e3p, e4p)? " << (cubic % ideal(e1p, sum apply(subsets(vs,3), s -> product s), x0*x2*x3*z) == 0) << endl;
<< "cubic mod e1p (z = -(x0+x2+x3)): " << sub(cubic, {z => -(x0+x2+x3)}) << endl;
-- Hilbert function of the low ideal vs (e1p,e3p,e4p,z^3)
Ilow = Ieasy + I7 + Isq;
Fib = ideal(e1p, sum apply(subsets(vs,3), s -> product s), x0*x2*x3*z, z^3);
<< "HF of T/Ilow in degrees 0..8: " << apply(0..8, d -> hilbertFunction(d, T/Ilow)) << endl;
<< "HF of T/Fib in degrees 0..8: " << apply(0..8, d -> hilbertFunction(d, T/Fib)) << endl;
