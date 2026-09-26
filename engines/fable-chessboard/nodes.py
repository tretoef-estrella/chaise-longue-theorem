# nodes.py — Fable, Mission 15: list the nodes of the peeling tree (type level) with their minimal types
# (types whose witness-set is not contained in the witness-set of another type of the node). Usage: K Q
import sys, runpy
sys.argv = ['peelT.py', sys.argv[1], sys.argv[2]]
g = runpy.run_path('peelT.py')
seen, types, inZ = g['seen'], g['types'], g['inZ']
for (m, P) in sorted(seen, key=lambda x: (-x[0], -seen[x])):
    if m == 0: continue
    Zt = {t: frozenset(x for x in types(m) if g['witness'](x, t[0], t[1])) for t in P}
    mins = [t for t in P if not any(Zt[t] < Zt[u] or (Zt[t] == Zt[u] and u < t) for u in P if u != t)]
    print('m=%d |Z|=%d  gens=%s' % (m, seen[(m, P)], sorted(mins)))
