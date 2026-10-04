# c03: trust-base search over the 233 project sources and material/checks/*.lean (mandate M3).
# Lean comments (-- ..., nested /- ... -/, docstrings) and string literals are separated from code,
# so each token is reported as CODE or COMMENT/STRING occurrences.
import os, re, glob, collections
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P = os.path.join(ROOT, 'material', 'project')
files = sorted(glob.glob(os.path.join(P, 'RequestProject', '**', '*.lean'), recursive=True))
chk = sorted(glob.glob(os.path.join(ROOT, 'material', 'checks', '*.lean')))

def split_code(s):
    """return (code, comments) where code has comments/strings blanked (newlines kept)."""
    code = []; com = []
    i = 0; n = len(s); depth = 0
    while i < n:
        if depth == 0 and s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j
            com.append(s[i:j]); code.append(' ' * (j - i)); i = j; continue
        if s.startswith('/-', i):
            depth += 1; start = i; i += 2
            while i < n and depth > 0:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('-/', i): depth -= 1; i += 2
                else: i += 1
            seg = s[start:i]; com.append(seg); code.append(re.sub(r'[^\n]', ' ', seg)); continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            seg = s[i:j+1]; com.append(seg); code.append(re.sub(r'[^\n]', ' ', seg)); i = j + 1; continue
        code.append(s[i]); i += 1
    return ''.join(code), '\n'.join(com)

TOK = {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'\baxiom\b', 'native_decide': r'\bnative_decide\b',
 'implemented_by': r'implemented_by', 'extern': r'\bextern\b', 'unsafe': r'\bunsafe\b', 'opaque': r'\bopaque\b',
 'csimp': r'csimp', 'skipKernelTC': r'skipKernelTC', 'partial def': r'\bpartial\s+def\b',
 'elab': r'\belab(_rules)?\b', 'macro': r'\bmacro(_rules)?\b', 'syntax': r'\bsyntax\b',
 'notation': r'\b(notation|infix|infixl|infixr|prefix|postfix)\b', 'run_cmd/run_tac': r'\brun_(cmd|tac|elab|meta)\b',
 'ofReduceBool': r'ofReduceBool|reduceBool', 'import Lean': r'^\s*(public\s+)?import\s+Lean\b',
 'addDecl/Environment': r'\baddDecl\b|\bEnvironment\b|\bKernel\b', 'local instance': r'\blocal\s+instance\b|attribute\s*\[\s*(local\s+)?instance',
 'scoped instance': r'\bscoped\s+instance\b', 'decide (tactic)': r'\bdecide\b', '#eval': r'#eval',
 'Classical.choice usage text': r'Classical\.choice', 'trustCompiler': r'trustCompiler',
}
res = collections.OrderedDict((k, {'code': [], 'comment': []}) for k in TOK)
setopts = collections.Counter(); insts = []; imports = collections.Counter()
for f in files + chk:
    rel = os.path.relpath(f, ROOT)
    s = open(f, encoding='utf-8').read()
    code, com = split_code(s)
    for k, rx in TOK.items():
        fl = re.M if k == 'import Lean' else 0
        nc = len(re.findall(rx, code, fl)); nm = len(re.findall(rx, com, fl))
        if nc: res[k]['code'].append((rel, nc))
        if nm: res[k]['comment'].append((rel, nm))
    for m in re.finditer(r'set_option\s+([\w.]+)\s+(\S+)', code):
        setopts[(m.group(1), m.group(2))] += 1
    for ln, line in enumerate(code.split('\n'), 1):
        if re.search(r'\binstance\b', line):
            insts.append((rel, ln, s.split('\n')[ln-1].strip()))
    for m in re.finditer(r'^\s*(?:public\s+)?import\s+(\S+)', code, re.M):
        imports[m.group(1).split('.')[0]] += 1
print('files scanned: project', len(files), '+ material/checks', len(chk))
for k, v in res.items():
    print(f'[{k}] CODE: {sum(n for _, n in v["code"])} in {len(v["code"])} files; COMMENT/STRING: {sum(n for _, n in v["comment"])} in {len(v["comment"])} files')
    for rel, n in v['code'][:40]: print('    code   ', rel, n)
    if k not in ('decide (tactic)', '#eval', 'Classical.choice usage text'):
        for rel, n in v['comment'][:12]: print('    comment', rel, n)
print('\nset_option (code), distinct:')
for (o, v), c in sorted(setopts.items()): print(f'    {o} {v}  x{c}')
print('\nimports by root namespace:', dict(imports))
print('\ninstance lines in code:', len(insts))
for i in insts: print('   ', i[0], i[1], i[2][:150])
