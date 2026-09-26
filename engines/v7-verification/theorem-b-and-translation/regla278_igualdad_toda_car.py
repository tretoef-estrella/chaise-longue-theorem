# regla278 — gate: equality dim V_Lambda = |Z_Lambda| also when char F | q-1 (incl. char 2), predicted by the rank argument
# rank_Fp(integer spanning set) <= rank_Q = |Z| (Thm 5.9 in char 0) <= dim_Fp (Thm 5.3). ESTIMATE: same cells as regla276, < 100 MB, < 2 min.
import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))  # repo copy
from regla276_igualdad import G3
for q, p, m in ((5, 2, 3), (5, 2, 4), (7, 2, 3), (7, 3, 3), (7, 2, 4), (9, 2, 3)):
    res, ok = G3(q, p, m)
    print('q=%d p=%d m=%d  (p | q-1: %s)  down-sets=%d  all equal=%s' % (q, p, m, (q-1) % p == 0, len(res), ok), flush=True)
print('FIN-OK')
