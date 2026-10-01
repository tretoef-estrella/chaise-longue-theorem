R = QQ[x_0..x_3];
gs = {x_0+x_1+x_2+x_3, sum(subsets(gens R,3), s->product s)};
I = ideal(gs) + ideal(apply(gens R, v -> v^8));
<< "q=8 n=4 char0 dim=" << degree I << endl;
