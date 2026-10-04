# c06: recount the numbers of the certificate (mandate M4): §7 totals, Table 6b, §4 axioms lines,
# decide files, instances, §3.2 cone, §8 clean rebuild, reproduction closure, Table 6a, build data.
import os, re, glob, collections, difflib
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
M = os.path.join(ROOT, 'material'); P = os.path.join(M, 'project'); RP = os.path.join(P, 'RequestProject')
L = os.path.join(M, 'logs')
NEW = {'E1':'BipAny','E2':'EvenCount','E3':'Odd3','E4':'Pow2','E5':'EvenAssembly','E6':'OddShapes','E7':'OddLayers',
       'E8':'Pfaffian','E9':'RankTwo','E10':'Membership','E11':'OddPatterns','E12':'OddLifts','E13':'OddLifts2',
       'E14':'OddTheorem','E15':'OddEquality','E16':'EvenBlocks','E17':'EvenColours','E18':'EvenMinus','E19':'EvenOne','E20':'EvenAll'}
CERT6B = {'E1':(6,633,28,0),'E2':(5,825,24,6),'E3':(6,1150,74,15),'E4':(4,978,50,13),'E5':(3,253,14,1),'E6':(6,1056,57,14),
          'E7':(6,850,48,5),'E8':(9,2132,105,23),'E9':(8,1152,54,9),'E10':(5,552,23,6),'E11':(7,770,38,7),'E12':(4,1099,40,2),
          'E13':(5,1107,36,2),'E14':(5,504,14,1),'E16':(6,929,43,13),'E17':(7,1454,51,15),'E18':(7,1501,66,13),
          'E19':(6,957,48,12),'E20':(6,869,42,2),'E15':(9,1346,67,28)}
files = sorted(glob.glob(os.path.join(RP, '**', '*.lean'), recursive=True))
rel = lambda f: os.path.relpath(f, RP)
folder = lambda f: rel(f).split(os.sep)[0] if os.sep in rel(f) else '(top)'
def stats(fs):
    nl = nl2 = th = th2 = df = 0
    for f in fs:
        s = open(f, encoding='utf-8').read()
        lines = s.split('\n')
        nl += s.count('\n')                                  # wc -l
        nl2 += len(lines) - (1 if lines and lines[-1] == '' else 0)
        th += sum(1 for l in lines if l.startswith('theorem ') or l.startswith('lemma '))
        th2 += sum(1 for l in lines if re.match(r'\s*(@\[[^\]]*\]\s*)?(private |protected )?(theorem|lemma) ', l))
        df += sum(1 for l in lines if re.match(r'(def |noncomputable def |abbrev )', l))
    return len(fs), nl, nl2, th, th2, df
newfolders = set(NEW.values())
fnew = [f for f in files if folder(f) in newfolders]; fold = [f for f in files if folder(f) not in newfolders]
print('== §7 totals (files, lines[wc -l], lines[incl. unterminated last], thm/lemma[line start], thm/lemma[lenient], defs)')
print('whole project', stats(files), ' certificate: 233 / 41 243 / 1 859')
print('E1-E20       ', stats(fnew), ' certificate: 120 / 20 117 / 922 / 187')
print('version 1    ', stats(fold), ' certificate: 113 / 21 126 / 937')
print('old folders:', sorted(set(folder(f) for f in fold)))
print('\n== Table 6b (files, lines, thms, defs) mine vs certificate')
for e, fo in NEW.items():
    st = stats([f for f in files if folder(f) == fo])
    mine = (st[0], st[1], st[3], st[5]); c = CERT6B[e]
    print(f'{e:4s} {fo:13s} mine {mine}  cert {c}  {"OK" if mine == c else "DIFF"}' + ('' if st[3]==st[4] else f'  (lenient thm count {st[4]})'))
s6 = [sum(x) for x in zip(*[CERT6B[e] for e in CERT6B])]
print('sum of Table 6b rows (files, lines, thms, defs):', s6)
# §4 axioms lines in the twenty final check logs
print('\n== §4 #print axioms lines in per_piece/check_runE<n>.log (n = 1..20, final runs only)')
cnt = collections.Counter(); tot = 0; perlog = {}
for n in range(1, 21):
    f = os.path.join(L, 'per_piece', f'check_runE{n}.log')
    s = open(f, encoding='utf-8').read()
    ax = re.findall(r"depends on axioms: \[([^\]]*)\]", s)
    noax = len(re.findall(r"does not depend on any axioms", s))
    perlog[n] = (len(ax), noax)
    for a in ax: cnt[a] += 1
    cnt['(no axioms)'] += noax
    tot += len(ax) + noax
    for bad in ('sorryAx', 'error', 'warning'):
        if bad in s: print('   ', f'check_runE{n}.log contains', bad, s.count(bad))
print('total', tot, dict(cnt))
print('per log (axiom lines, no-axiom lines):', perlog)
# which theorems give fewer than three axioms
for n in range(1, 21):
    s = open(os.path.join(L, 'per_piece', f'check_runE{n}.log'), encoding='utf-8').read()
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", s):
        if m.group(2) != 'propext, Classical.choice, Quot.sound': print('   E%d' % n, m.group(1), '[' + m.group(2) + ']')
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", s): print('   E%d' % n, m.group(1), '(none)')
# decide files
print('\n== decide: files of RequestProject with the tactic decide')
def code_only(s):
    s = re.sub(r'/-.*?-/', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)
tac = []; anyd = []
for f in files:
    s = open(f, encoding='utf-8').read(); c = code_only(s)
    if 'decide' in s: anyd.append(rel(f))
    # tactic decide: 'decide' not followed by '(' / '_' / letters, not preceded by '.' or '_' (i.e. not Bool.decide, decide_eq_true)
    if re.search(r'(?<![\w.])decide(?![\w(])(?!\s*\()', c): tac.append(rel(f))
print('files containing the string "decide" anywhere:', len(anyd))
print('files using decide as a tactic (code):', len(tac), ' new:', sum(1 for t in tac if t.split(os.sep)[0] in newfolders), ' v1:', sum(1 for t in tac if t.split(os.sep)[0] not in newfolders))
for t in tac: print('   ', t)
print('string-but-not-tactic:', sorted(set(anyd) - set(tac)))
# instances
print('\n== instances (declarations in code)')
inst = []
for f in files:
    for i, l in enumerate(code_only(open(f, encoding='utf-8').read()).split('\n'), 1):
        if re.match(r'\s*(@\[[^\]]*\]\s*)?(noncomputable\s+)?(private\s+)?instance\b', l): inst.append((rel(f), i, l.strip()[:110]))
for x in inst: print('   ', 'NEW' if x[0].split(os.sep)[0] in newfolders else 'v1 ', x)
print('total', len(inst), ' new', sum(1 for x in inst if x[0].split(os.sep)[0] in newfolders))
