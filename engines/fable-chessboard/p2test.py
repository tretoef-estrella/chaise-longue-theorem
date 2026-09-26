# p2test.py — Fable, Mission 15. For partitions mu <= mut (weak dominance) of the SAME parity, len <= h, size <= S:
# is the sorted option chain of mu position-wise <= that of mut?  (sufficient for Lemma P2.)
import sys
q, S = int(sys.argv[1]), int(sys.argv[2]); h = (q-1)//2
def parts_upto(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for p in range(min(n, mx), 0, -1):
        for r in parts_upto(n-p, p): yield (p,) + r
def srt(l): return tuple(sorted([x for x in l if x > 0], reverse=True))
def wdom(a, b):
    sa = sb = 0
    for j in range(max(len(a), len(b))):
        sa += a[j] if j < len(a) else 0; sb += b[j] if j < len(b) else 0
        if sa > sb: return False
    return True
def chain(mu):
    l = len(mu); out = []
    for j in range(l):
        a = list(mu); a[j] -= 1; out.append(srt(a))
    new = srt(mu + (1,)) if l < h else None
    out += [new]*(q-1-2*l)
    for j in range(l-1, -1, -1):
        b = list(mu); b[j] += 1; out.append(srt(b))
    # verify it is a chain
    for x, y in zip(out, out[1:]): assert wdom(x, y), (mu, out)
    return out
P = [l for s in range(S+1) for l in parts_upto(s) if len(l) <= h]
bad = 0; pairs = 0
for mu in P:
    cm = chain(mu)
    for mut in P:
        if (sum(mut) - sum(mu)) % 2 or mu == mut or not wdom(mu, mut): continue
        pairs += 1
        ct = chain(mut)
        if not all(wdom(x, y) for x, y in zip(cm, ct)):
            bad += 1
            if bad <= 3: print('fails: mu=%s mut=%s' % (mu, mut))
print('q=%d size<=%d: comparable same-parity pairs=%d  position-wise failures=%d' % (q, S, pairs, bad))
