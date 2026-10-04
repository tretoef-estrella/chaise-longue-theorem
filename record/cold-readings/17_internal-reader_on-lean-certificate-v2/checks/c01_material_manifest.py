# c01: verify MANIFEST_material_md5.txt (given with the mission) against material/ as it is now.
import hashlib, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
man = os.path.join(ROOT, 'MANIFEST_material_md5.txt')
ok = bad = missing = 0
listed = set()
for line in open(man, encoding='utf-8'):
    line = line.rstrip('\n')
    if not line.strip():
        continue
    h, p = line.split(None, 1)
    listed.add(p)
    fp = os.path.join(ROOT, p)
    if not os.path.exists(fp):
        print('MISSING', p); missing += 1; continue
    d = hashlib.md5(open(fp, 'rb').read()).hexdigest()
    if d == h: ok += 1
    else:
        print('DIFF', p, h, d); bad += 1
# files present in material/ (outside .lake and .git) not listed
extra = []
for dp, dn, fn in os.walk(os.path.join(ROOT, 'material')):
    dn[:] = [d for d in dn if d not in ('.lake', '.git')]
    for f in fn:
        rel = os.path.relpath(os.path.join(dp, f), ROOT)
        if rel not in listed:
            extra.append(rel)
print('listed', len(listed), 'ok', ok, 'diff', bad, 'missing', missing)
print('unlisted files in material (outside .lake/.git):', len(extra))
for e in sorted(extra)[:50]:
    print('  UNLISTED', e)
print('md5 of the manifest itself:', hashlib.md5(open(man,'rb').read()).hexdigest())
