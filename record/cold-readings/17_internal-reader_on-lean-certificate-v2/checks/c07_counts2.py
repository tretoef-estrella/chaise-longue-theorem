# c07: second part of the recount (M4): the rule behind the "Defs" column; decide as a whole word;
# §3.2 cone; §8 clean rebuild; reproduction closure; Table 6a; Table 6b build columns.
import os, re, glob, collections, difflib, datetime
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
M = os.path.join(ROOT, 'material'); P = os.path.join(M, 'project'); RP = os.path.join(P, 'RequestProject')
L = os.path.join(M, 'logs'); CP = os.path.join(L, 'certificado_pares')
NEW = {'E1':'BipAny','E2':'EvenCount','E3':'Odd3','E4':'Pow2','E5':'EvenAssembly','E6':'OddShapes','E7':'OddLayers',
       'E8':'Pfaffian','E9':'RankTwo','E10':'Membership','E11':'OddPatterns','E12':'OddLifts','E13':'OddLifts2',
       'E14':'OddTheorem','E15':'OddEquality','E16':'EvenBlocks','E17':'EvenColours','E18':'EvenMinus','E19':'EvenOne','E20':'EvenAll'}
CERTDEFS = {'E1':0,'E2':6,'E3':15,'E4':13,'E5':1,'E6':14,'E7':5,'E8':23,'E9':9,'E10':6,'E11':7,'E12':2,'E13':2,'E14':1,
            'E15':28,'E16':13,'E17':15,'E18':13,'E19':12,'E20':2}
files = sorted(glob.glob(os.path.join(RP, '**', '*.lean'), recursive=True))
rel = lambda f: os.path.relpath(f, RP)
folder = lambda f: rel(f).split(os.sep)[0] if os.sep in rel(f) else '(top)'
newf = set(NEW.values())
print('== Defs column: stated rule (def / noncomputable def / abbrev) vs broader rule (def|noncomputable|abbrev|structure|class|instance|inductive at line start, comments included)')
t1 = t2 = 0
for e, fo in NEW.items():
    fs = [f for f in files if folder(f) == fo]
    r1 = r2 = 0; extra = []
    for f in fs:
        for i, l in enumerate(open(f, encoding='utf-8').read().split('\n'), 1):
            a = bool(re.match(r'(def |noncomputable def |abbrev )', l))
            b = bool(re.match(r'(def|noncomputable|abbrev|structure|class|instance|inductive)\b', l))
            r1 += a; r2 += b
            if b and not a: extra.append(f'{rel(f)}:{i}: {l[:70]}')
    t1 += r1; t2 += r2
    print(f'{e:4s} {fo:13s} stated-rule {r1:3d}  broad-rule {r2:3d}  certificate {CERTDEFS[e]:3d}', '' if r2 == CERTDEFS[e] else 'BROAD!=CERT')
    for x in extra: print('        +', x)
print('totals: stated rule', t1, ' broad rule', t2, ' certificate 187')
print('\n== decide: files with the whole word "decide" (grep -lw, comments included)')
w = [rel(f) for f in files if re.search(r'(?<![\w])decide(?![\w])', open(f, encoding='utf-8').read())]
print(len(w), ' new', sum(1 for x in w if x.split(os.sep)[0] in newf), ' v1', sum(1 for x in w if x.split(os.sep)[0] not in newf))
# §3.2 cone
print('\n== §3.2 dependency cones (deps_pares_postclean.log)')
dl = open(os.path.join(CP, 'deps_pares_postclean.log'), encoding='utf-8').read().split('\n')
heads = [(i, l) for i, l in enumerate(dl) if l.startswith('project decls in cone')]
order = ["EvenAll.mainTheorem'", 'OddEquality.D1', 'OddEquality.D2_DJ', 'EvenAll.B2']   # order of #deps in DepsPares.lean
cones = {}
for j, (i, l) in enumerate(heads):
    end = heads[j+1][0] if j + 1 < len(heads) else len(dl)
    mods = {}
    for x in dl[i+1:end]:
        m = re.match(r'(RequestProject\.\S+) (\d+)$', x.strip())
        if m: mods[m.group(1)] = int(m.group(2))
    nd, nm = map(int, re.findall(r'\d+', l))
    cones[order[j]] = (nd, nm, mods)
    print(f'{order[j]:22s} header: {nd} decls, {nm} modules; parsed {sum(mods.values())} decls, {len(mods)} modules')
allmods = sorted('RequestProject.' + rel(f)[:-5].replace(os.sep, '.') for f in files)
cone = set(cones["EvenAll.mainTheorem'"][2])
out = [m for m in allmods if m not in cone]
print('modules outside the cone of the final theorem:', len(out))
byf = collections.defaultdict(list)
for m in out: byf[m.split('.')[1] if m.count('.') > 1 else '(top)'].append(m.split('.')[-1])
for k in sorted(byf): print('   ', k, byf[k])
inD1 = set(cones['OddEquality.D1'][2]); print('OddEquality modules in cone of D1:', sorted(m for m in inD1 if '.OddEquality.' in m))
# §8 clean rebuild
print('\n== §8 clean rebuild log')
cr = open(os.path.join(CP, 'clean_rebuild_2026-10-03.log'), encoding='utf-8').read().split('\n')
rows = []
for l in cr:
    m = re.match(r'(RequestProject\.\S+) VIGIA-FIN-OK exit=(\d+) pico_kb=(\d+) t=(\d+)s wall=(\d+)s', l)
    if m: rows.append((m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5))))
print('modules with a result line:', len(rows), ' exit 0:', sum(1 for r in rows if r[1] == 0))
print('sum t:', sum(r[3] for r in rows), ' sum wall:', sum(r[4] for r in rows))
mx = max(rows, key=lambda r: r[3]); mw = max(rows, key=lambda r: r[4]); mp = max(rows, key=lambda r: r[2])
print('longest t:', mx[0], mx[3], ' longest wall:', mw[0], mw[4], ' peak:', mp[0], mp[2], 'kB =', round(mp[2]/1048576, 3), 'GiB')
print([l for l in cr if l.startswith(('START', 'END', 'SKIPPED', 'FIN'))])
# per-module logs agree with the summary?
bad = 0
for r in rows:
    f = os.path.join(CP, 'cr_logs', r[0] + '.log')
    last = open(f, encoding='utf-8').read().strip().split('\n')[-1]
    if f'exit={r[1]} pico_kb={r[2]} t={r[3]}s' not in last: bad += 1; print('  mismatch', r[0], last)
    s = open(f, encoding='utf-8').read()
    if re.search(r'error|sorry', s, re.I): print('  error/sorry text in', r[0])
print('per-module logs consistent with summary:', bad == 0, ' cr_logs files:', len(os.listdir(os.path.join(CP, 'cr_logs'))))
order_f = open(os.path.join(CP, 'orden_modulos.txt'), encoding='utf-8').read().split()
print('orden_modulos entries:', len(order_f), ' marked #:', [o for o in order_f if o.startswith('#')])
print('orden = set of all modules:', sorted(o.lstrip('#') for o in order_f) == allmods)
# imports graph from sources
imp = {}
for f in files:
    mod = 'RequestProject.' + rel(f)[:-5].replace(os.sep, '.')
    imp[mod] = re.findall(r'^\s*(?:public\s+)?import\s+(RequestProject\.\S+)', open(f, encoding='utf-8').read(), re.M)
pos = {o.lstrip('#'): i for i, o in enumerate(order_f)}
topo_ok = all(pos[d] < pos[m] for m in imp for d in imp[m])
print('orden_modulos is a topological order of the imports:', topo_ok)
four = ['RequestProject.EvenAll.Checks', 'RequestProject.EvenAll.Main', 'RequestProject.OddEquality.Checks', 'RequestProject.OddEquality.Main']
for x in four: print('  importers of', x, ':', [m for m in imp if x in imp[m]])
print('  imports of RequestProject.Main (top):', imp.get('RequestProject.Main'))
# reproduction closure
def closure(roots):
    seen = set(); st = list(roots)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st += imp.get(x, [])
    return seen
five = ['RequestProject.EvenAll.PartBC', 'RequestProject.EvenAll.PartD', 'RequestProject.EvenAll.PartE',
        'RequestProject.OddEquality.PartD', 'RequestProject.ColAssembly.Main']
chk = re.findall(r'^import\s+(\S+)', open(os.path.join(M, 'checks', 'CheckPares.lean'), encoding='utf-8').read(), re.M)
print('\nCheckPares imports:', chk, ' == the five of §8:', sorted(chk) == sorted(five))
cl = closure(five); print('import closure of the five modules:', len(cl), 'of', len(allmods))
dchk = re.findall(r'^import\s+(\S+)', open(os.path.join(M, 'checks', 'DepsPares.lean'), encoding='utf-8').read(), re.M)
print('DepsPares imports:', dchk, ' inside the closure:', all(d in cl for d in dchk))
print('modules of the final cone outside the closure:', sorted(cone - cl))
# check logs: identical except two lines?
print('\n== check_pares.log vs check_pares_postclean.log; deps_pares.log vs deps_pares_postclean.log')
for a, b in [('check_pares.log', 'check_pares_postclean.log'), ('deps_pares.log', 'deps_pares_postclean.log')]:
    A = open(os.path.join(CP, a), encoding='utf-8').read().split('\n'); B = open(os.path.join(CP, b), encoding='utf-8').read().split('\n')
    d = [x for x in difflib.unified_diff(A, B, lineterm='', n=0) if not x.startswith(('---', '+++', '@@'))]
    print(a, len(A), 'lines;', b, len(B), 'lines; differing lines:', len(d))
    for x in d: print('    ', x[:160])
    for bad in ('error', 'warning', 'sorry'):
        print('    ', b, 'contains', bad, ':', sum(1 for x in B if bad in x))
# Table 6a
print('\n== Table 6a brute force: "checks N" in the final log of each piece')
CERT6A = {'E2':64,'E3':195,'E4':106,'E5':21,'E6':93,'E7':120,'E8':4491,'E9':1718,'E10':840,'E11':1170,'E12':8261,'E13':2269,
          'E14':8743,'E16':3399,'E17':1869,'E18':84,'E19':118,'E20':59,'E15':111}
tot = 0
for e, c in CERT6A.items():
    s = open(os.path.join(L, 'brute_force', f'chk{e}.log'), encoding='utf-8').read()
    m = re.findall(r'(?:TOTAL checks:?|^checks|CHECKS)\s*(\d+),?\s*(?:failures|FAILURES|fails)?:?\s*(\d+)', s, re.M | re.I)
    n, fl = (int(m[-1][0]), int(m[-1][1])) if m else (None, None)
    ctl = re.findall(r'(?:controls|CONTROLS)\s*(\d+),?\s*(?:fire|FIRED|fired)\s*(\d+)', s)
    tot += n or 0
    print(f'{e:4s} log {n} failures {fl}  certificate {c}  {"OK" if n == c else "DIFF"}  controls(total,fired)={ctl[-1] if ctl else "-"}')
print('sum', tot, ' certificate 33 731')
# Table 6b build columns
print('\n== Table 6b build columns from per_piece/build_runE<n>_<Module>.log')
CERTB = {'E1':(6,411,1.87),'E2':(5,346,1.76),'E3':(6,397,1.83),'E4':(4,255,2.16),'E5':(3,172,2.07),'E6':(6,397,1.80),
         'E7':(6,481,1.98),'E8':(9,589,1.77),'E9':(8,463,2.07),'E10':(5,342,1.93),'E11':(7,495,2.13),'E12':(4,391,1.83),
         'E13':(5,429,1.70),'E14':(5,335,1.87),'E16':(6,410,1.98),'E17':(7,483,1.89),'E18':(7,440,1.99),'E19':(6,448,2.25),
         'E20':(4,296,1.85),'E15':(7,629,1.74)}
ts = 0; pk = 0
for e, (cm, cs, cp) in CERTB.items():
    logs = sorted(glob.glob(os.path.join(L, 'per_piece', f'build_run{e}_*.log')))
    logs = [g for g in logs if 'killed' not in g]
    ok = []; other = []
    for g in logs:
        last = open(g, encoding='utf-8').read().strip().split('\n')[-1]
        m = re.search(r'VIGIA-FIN-OK exit=0 pico_kb=(\d+) t=(\d+)s', last)
        (ok if m else other).append((os.path.basename(g), (int(m.group(1)), int(m.group(2))) if m else last[:60]))
    n = len(ok); s = sum(x[1][1] for x in ok); p = max(x[1][0] for x in ok)/1048576 if ok else 0
    ts += s; pk = max(pk, p)
    print(f'{e:4s} built {n} sum_t {s} peak {p:.2f} GiB   certificate {cm} {cs} {cp}  {"OK" if (n, s, round(p, 2)) == (cm, cs, cp) else "DIFF"}  others: {other}')
print('total build s', ts, '(certificate 8 209)  max peak', round(pk, 2), '(certificate 2.25)')
