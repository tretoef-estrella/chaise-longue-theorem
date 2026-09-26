# ledger14x.py — the lines of the k = 5 ledger present at q >= 27 but not at q = 9 (printed with the q = 27 row numbering)
from ledger14 import ledger, fmt_rows
_, L9, _ = ledger(5, 9); _, L27, b27 = ledger(5, 27)
k9 = set((l[0], l[1], l[3], l[5]) for l in L9)
print('| parent | n | f | type | rows (q = 27) | child | status | mechanism |'); print('|---|---|---|---|---|---|---|---|')
for mu, n, f, t, al, c, st, used, openc in L27:
    if (mu, n, t, c) in k9: continue
    u = '; '.join('%s %s' % (m, ' '.join('(%d,%d)' % x for x in v)) for m, v in used.items()) or 'BASE only'
    print('| %s | %d | %d | %s | %s | %s | **%s** | BASE; %s |' % (mu, n, f, t, fmt_rows(al, 27), c, st, u))
