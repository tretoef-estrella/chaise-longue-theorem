Y = ZZ/3[y_0,y_1,y_2]; e1 = y_0+y_1+y_2; e2 = y_0*y_1+y_0*y_2+y_1*y_2; e3 = y_0*y_1*y_2;
P3 = e3 - e1*e2; E4 = e1*e3;    -- (P'_3, e1 e3) = (ebar_3, ebar_4)
IZ = ideal(P3, E4);
<< "IZ saturado? " << toString(saturate IZ == IZ) << "  dim=" << dim IZ << "  degree=" << degree IZ << endl;
<< "radical: " << toString(flatten entries gens gb radical IZ) << "  degree radical=" << degree radical IZ << endl;
D = decompose IZ; << "componentes: " << #D << " ; " << toString apply(D, c -> (toString flatten entries gens c, degree c)) << endl;
-- longitud en cada punto: multiplicidad de IZ localizada = degree of primary component
PD = primaryDecomposition IZ; << "primarias: " << toString apply(PD, c -> (toString flatten entries gens c, degree c)) << endl;
-- pertenencias
scan({3,9,27}, q -> (
  g := y_0*y_1*y_2^(q-1) - e1^2*(y_0+y_1)^(q-1);
  << "q=" << q << ": g in IZ + caja? " << toString(g % (IZ + ideal(y_0^q,y_1^q,y_2^q)) == 0) << endl;));
<< "FIN-OK" << endl; exit 0
