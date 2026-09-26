# batch14.py — Fable, MISION 14: run a list of gamlaw14.py cells through Singular, one after another, and compare with |W| (EGF).
import sys, subprocess, re, time
from grepy_verif import W
def parts(nmax, lmax):
    out = []
    def rec(left, mx, cur):
        out.append(tuple(cur))
        for p in range(min(left, mx), 0, -1):
            if len(cur) < lmax: rec(left - p, p, cur + [p])
    rec(nmax, nmax, []); return out
def run(mode, mu, N, q):
    f = 'g14/%s_%s_%d_%d.sing' % (mode, '-'.join(map(str, mu)) or 'e', N, q)
    subprocess.run(['python3', 'gamlaw14.py', mode, ','.join(map(str, mu)), str(N), str(q), f], check=True, capture_output=True)
    import os; assert os.path.getsize(f) > 0
    t = time.time()
    r = subprocess.run('Singular -q %s < /dev/null' % f, shell=True, capture_output=True, text=True)
    return r.stdout.strip(), time.time() - t
if __name__ == '__main__':
    mode = sys.argv[1]; q = int(sys.argv[2]); cells = []
    if sys.argv[3] == 'all':
        n0, n1 = int(sys.argv[4]), int(sys.argv[5])
        for N in range(n0, n1 + 1):
            for mu in parts(N, (q - 1) // 2):
                if mu: cells.append((mu, N))
    else:
        for c in sys.argv[3:]:
            m, N = c.split(':'); cells.append((tuple(int(x) for x in m.split(',') if x), int(N)))
    bad = 0
    for mu, N in cells:
        out, dt = run(mode, mu, N, q)
        if mode == 'vdim':
            v = int(re.search(r'vdim\(K\^G\) =\s+(-?\d+)', out).group(1)); w = W(mu, N, q)
            ok = (v == w); bad += (not ok)
            print('LAW q=%d mu=%s n=%d  vdim=%d  |W|=%d  %s  (%.1fs)' % (q, mu, N, v, w, 'EQUAL' if ok else '*** DIFFERENT ***', dt), flush=True)
        else:
            nb = sum(int(x) for x in re.findall(r'NOT in row:\s+(\d+)', out)); bad += (nb > 0)
            print('ROWS q=%d parent=%s n+1=%d  rows checked %d, generators NOT in their row: %d  (%.1fs)' % (q, mu, N, len(re.findall('ROW parent', out)), nb, dt), flush=True)
            if nb: print(out, flush=True)
    print('CELLS %d  BAD %d' % (len(cells), bad))
