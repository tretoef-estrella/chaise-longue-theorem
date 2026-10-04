# control_subfamilia.py — Grepy Chats, 2 Oct 2026. (O) at k=2, r=3, char 3 with one matching removed: negative control.
import itertools, numpy as np, azotea, caja_impar
full = list(azotea.matchings(list(range(6))))
for drop in range(len(full)):
    sub = full[:drop] + full[drop+1:]
    orig = azotea.matchings
    caja_impar.matchings = lambda pts, sub=sub: iter(sub)
    print("dropped matching", drop, full[drop], end="  ->  ", flush=True)
    caja_impar.run(2, 3, 3)
    caja_impar.matchings = orig
print("FIN-OK")
