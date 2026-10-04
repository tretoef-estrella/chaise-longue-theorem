#!/usr/bin/env python3
"""STEP 4 — recount the certificate's numbers from the files actually present.
Expected (claims to test): 113 files; 21 126 lines; 937 theorem/lemma at line start; 351 defs;
per-folder files/lines/thms of certificate §6; two SHA-256 fingerprints of §8; build logs for runs
1-2 (build.log) and 3..29 with the wall-clock/peak-RSS of §6 and sum 4108.7 s over 28 builds;
check logs only for runs 26-29; clean rebuild 113/113 rc=0, 18:41:27 -> 20:08:22, 5214 s, slowest
TheoremB.Root 117 s; order.txt = the 113 modules; deps log 2367 decls, 90 files, 26 folders; the
unused folders Upper, Degeneration, Support. Time estimate: < 5 s, < 50 MB.
"""
import os, re, hashlib, glob, collections
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'material', 'lean'))
PROJ = os.path.join(BASE, 'project')
RP = os.path.join(PROJ, 'RequestProject')
files = sorted(os.path.relpath(os.path.join(dp, f), PROJ) for dp, _, fs in os.walk(RP) for f in fs if f.endswith('.lean'))
print('files:', len(files))
def rd(p): return open(os.path.join(PROJ, p), 'rb').read()
nl = sum(rd(f).count(b'\n') for f in files)
print('lines (newline count, = wc -l):', nl)
thm = sum(len(re.findall(rb'^(theorem|lemma)\b', rd(f), re.M)) for f in files)
print('theorem/lemma at start of line:', thm)
thm_any = sum(len(re.findall(rb'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(theorem|lemma)\b', rd(f), re.M)) for f in files)
print('theorem/lemma incl. indented/attributed/private:', thm_any)
for label, pat in [
    ('def-like at line start (def|abbrev|structure|inductive|instance|class)', rb'^(def|abbrev|structure|inductive|instance|class)\b'),
    ('... also with noncomputable/private/@[..] prefixes', rb'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|structure|inductive|instance|class)\b'),
    ('... any indentation, with prefixes', rb'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|structure|inductive|instance|class)\b')]:
    print(label + ':', sum(len(re.findall(pat, rd(f), re.M)) for f in files))
# fingerprints (certificate §8), computed from the project root with paths RequestProject/...
cat = b''.join(rd(f) for f in files)
print('sha256(concat sorted):', hashlib.sha256(cat).hexdigest())
lst = ''.join(f'{hashlib.sha256(rd(f)).hexdigest()}  {f}\n' for f in files).encode()
print('sha256(shasum list):  ', hashlib.sha256(lst).hexdigest())
# per-folder
folders = collections.OrderedDict()
for f in files:
    parts = f.split('/')
    key = parts[1] if len(parts) > 2 else '(top) ' + parts[1]
    d = folders.setdefault(key, [0, 0, 0])
    b = rd(f); d[0] += 1; d[1] += b.count(b'\n'); d[2] += len(re.findall(rb'^(theorem|lemma)\b', b, re.M))
print('\nper folder: files lines thms')
for k, v in folders.items(): print(f'  {k:14s} {v[0]:3d} {v[1]:5d} {v[2]:4d}')
# certificate §6 table
CERT = {  # folder: (files, lines, thms)
 'Ballot+Main': (5, 897, 26), 'Upper': (4, 569, 19), 'Peel': (3, 574, 21), 'Chain': (4, 668, 37), 'Monotone': (4, 431, 28),
 'Fibres': (3, 599, 32), 'Tight': (3, 862, 48), 'Lifts': (6, 1137, 59), 'Induction': (2, 220, 7), 'TheoremB': (7, 1167, 63),
 'Degeneration': (3, 658, 25), 'Support': (4, 708, 29), 'EveryField': (4, 713, 28), 'FreeZ': (3, 406, 12), 'Bip': (5, 973, 35),
 'BipOpt': (4, 960, 39), 'BipP2': (2, 317, 22), 'BipP3': (3, 898, 43), 'BipInd': (2, 444, 23), 'ColSplit': (2, 419, 17),
 'ColSurv': (2, 467, 30), 'ColComp': (4, 653, 29), 'ColTensor': (3, 548, 24), 'ColDecomp': (4, 569, 17), 'ColPairs': (5, 1104, 42),
 'ColOne': (6, 1478, 71), 'ColCount': (4, 865, 25), 'ColUpper': (7, 1199, 55), 'ColAssembly': (5, 623, 31)}
act = dict(folders)
b = act['Ballot']; t = act['(top) Main.lean']; act['Ballot+Main'] = [b[0]+t[0], b[1]+t[1], b[2]+t[2]]
print('\ncertificate §6 vs actual (folder: cert -> actual) [mismatches only]')
mism = 0
for k, v in CERT.items():
    a = tuple(act[k])
    if a != v: mism += 1; print(f'  MISMATCH {k}: cert {v} actual {a}')
print('  mismatches:', mism, '; cert totals files/lines/thms:', tuple(map(sum, zip(*CERT.values()))))
# logs
L = os.path.join(BASE, 'logs')
logs = sorted(os.listdir(L)); print('\nlogs present:', logs)
runs = sorted(int(m.group(1)) for x in logs for m in [re.match(r'build_run(\d+)\.log', x)] if m)
print('build_runN present for N =', runs, ' missing in 3..29:', sorted(set(range(3, 30)) - set(runs)))
print('check_runN present for N =', sorted(int(m.group(1)) for x in logs for m in [re.match(r'check_run(\d+)\.log', x)] if m))
tot = 0.0; rows = []
for name in ['build.log'] + [f'build_run{n}.log' for n in runs]:
    s = open(os.path.join(L, name), encoding='utf-8', errors='replace').read()
    real = re.search(r'([\d.]+) real', s); rss = re.search(r'(\d+)\s+maximum resident set size', s)
    ok = 'Build completed successfully' in s; ex = re.search(r'EXIT (\d+)', s)
    err = len(re.findall(r'^error', s, re.M))
    r = float(real.group(1)) if real else None
    if r: tot += r
    rows.append((name, r, round(int(rss.group(1))/1e9, 2) if rss else None, ok, ex.group(1) if ex else None, err))
for row in rows: print('  ', row)
print('builds counted:', len(rows), ' sum real (s):', round(tot, 1))
mx = max(rows, key=lambda r: r[1] or 0); print('largest build:', mx[0], mx[1]); mr = max(rows, key=lambda r: r[2] or 0); print('largest RSS:', mr[0], mr[2])
# clean rebuild
s = open(os.path.join(L, 'clean_rebuild_2026-09-29.log')).read()
mods = re.findall(r'^(RequestProject\.\S+) rc=(\d+) sec=(\d+)', s, re.M)
print('\nclean rebuild: modules', len(mods), ' rc=0:', sum(1 for _, rc, _ in mods if rc == '0'),
      ' sum sec:', sum(int(x) for *_, x in mods), ' slowest:', max(mods, key=lambda m: int(m[2])))
print('  START/END:', re.findall(r'^(START|END) (.*)$', s, re.M), ' FIN-OK' in s)
order = open(os.path.join(BASE, 'checks', 'order.txt')).read().split()
modset = {f[:-5].replace('/', '.') for f in files}
print('  order.txt entries', len(order), ' distinct', len(set(order)), ' == project modules:', set(order) == modset,
      ' == rebuilt modules in log order:', [m for m, *_ in mods] == order)
# dependency order check: each module's imports appear earlier in order.txt
pos = {m: i for i, m in enumerate(order)}; bad = []
for f in files:
    m = f[:-5].replace('/', '.')
    for imp in re.findall(rb'^\s*(?:public\s+)?import\s+(RequestProject\S*)', rd(f), re.M):
        if pos[imp.decode()] > pos[m]: bad.append((m, imp.decode()))
print('  order.txt respects imports:', not bad, bad[:5])
# deps
s = open(os.path.join(L, 'deps_mainTheorem.log')).read()
head = re.search(r'project decls in cone: (\d+); modules: (\d+)', s)
per = re.findall(r'^(RequestProject\.\S+) (\d+)$', s, re.M)
fold = collections.Counter(); 
for m, c in per: fold[m.split('.')[1] if m.count('.') > 1 else '(top)'] += int(c)
print('\ndeps: header', head.groups(), ' lines', len(per), ' sum', sum(int(c) for _, c in per), ' folders', len(fold))
allfold = {f.split('/')[1] for f in files if f.count('/') > 1}
print('  folders NOT in cone:', sorted(allfold - set(fold)), ' top-level Main.lean in cone:', '(top)' in fold)
used = {m for m, _ in per}
for fo in ['Ballot', 'EveryField', 'FreeZ']:
    print(f'  {fo}: used modules', sorted(m for m in used if m.split(".")[1] == fo), ' of', sorted(f[:-5].replace("/", ".") for f in files if f.split("/")[1] == fo))
# check logs: axiom lines
print('\naxiom lines in check logs:')
for n in (26, 27, 28, 29):
    s = open(os.path.join(L, f'check_run{n}.log')).read()
    ax = re.findall(r"depends on axioms: \[(.*?)\]", s)
    print(f'  run{n}: {len(ax)} axiom lines; distinct sets: {collections.Counter(ax)}')
    print('    other axiom-related lines:', re.findall(r".*does not depend on any axioms.*|.*sorryAx.*", s))
