# c02: (a) md5 of every .lean source vs logs/certificado_pares/MANIFEST_md5_233.txt;
#      (b) md5 of that manifest (certificate §8 claims 8ac0df81107480be80e53c75b2e4dbbd) and bytewise sort;
#      (c) which modules have a compiled .olean in .lake/build, which do not; olean mtimes vs sources;
#      (d) md5 of lakefile.toml, lean-toolchain, lake-manifest.json (certificate §8).
import hashlib, os, glob, datetime
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P = os.path.join(ROOT, 'material', 'project')
MAN = os.path.join(ROOT, 'material', 'logs', 'certificado_pares', 'MANIFEST_md5_233.txt')
md5 = lambda f: hashlib.md5(open(f, 'rb').read()).hexdigest()
lines = open(MAN, encoding='utf-8').read().splitlines()
entries = [l.split(None, 1) for l in lines if l.strip()]
paths = [e[1] for e in entries]
print('manifest md5 =', md5(MAN), '(claimed 8ac0df81107480be80e53c75b2e4dbbd)')
print('manifest entries =', len(entries), ' sorted bytewise:', paths == sorted(paths, key=lambda s: s.encode()))
src = sorted(os.path.relpath(f, P) for f in glob.glob(os.path.join(P, 'RequestProject', '**', '*.lean'), recursive=True))
print('.lean files on disk =', len(src))
print('on disk not in manifest:', sorted(set(src) - set(paths)))
print('in manifest not on disk:', sorted(set(paths) - set(src)))
bad = [(p, h, md5(os.path.join(P, p))) for h, p in entries if os.path.exists(os.path.join(P, p)) and md5(os.path.join(P, p)) != h]
print('md5 mismatches:', len(bad))
for b in bad: print('  ', b)
# (c) oleans
B = os.path.join(P, '.lake', 'build', 'lib', 'lean')
nolean = []
newer_src = []
mt = []
for p in src:
    mod = p[:-5]
    ol = os.path.join(B, mod + '.olean')
    if not os.path.exists(ol):
        nolean.append(mod); continue
    mt.append((os.path.getmtime(ol), mod))
    if os.path.getmtime(os.path.join(P, p)) > os.path.getmtime(ol):
        newer_src.append(mod)
print('modules without .olean:', len(nolean), nolean)
print('sources newer than their .olean:', len(newer_src), newer_src[:10])
mt.sort()
f = lambda t: datetime.datetime.fromtimestamp(t).strftime('%Y-%m-%d %H:%M:%S')
print('olean mtime range:', f(mt[0][0]), mt[0][1], '..', f(mt[-1][0]), mt[-1][1])
srcmt = sorted(os.path.getmtime(os.path.join(P, p)) for p in src)
print('source mtime range:', f(srcmt[0]), '..', f(srcmt[-1]))
for n in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']:
    print(n, md5(os.path.join(P, n)))
