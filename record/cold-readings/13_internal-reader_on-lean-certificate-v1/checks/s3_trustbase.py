#!/usr/bin/env python3
"""STEP 3 — trust base scan of every .lean file in material/lean/project/RequestProject.
Expected output (hypothesis to falsify): 0 hits for sorry/admit/axiom/native_decide/implemented_by/
extern/unsafe/opaque/csimp/skipKernelTC/ofReduceBool/elab/macro/syntax/notation/run_cmd/#eval;
a list of set_option lines; a list of instance declarations; no project declaration whose name
ends with a Mathlib/core name used in the final statement. Time estimate: < 5 s, < 50 MB.
Comments (-- and /- -/) are stripped before searching code tokens; hits inside comments are reported separately.
"""
import os, re, collections, sys
ROOT = os.path.join(os.path.dirname(__file__), '..', 'material', 'lean', 'project', 'RequestProject')
ROOT = os.path.abspath(ROOT)
files = sorted(os.path.join(dp, f) for dp, _, fs in os.walk(ROOT) for f in fs if f.endswith('.lean'))
print('lean files:', len(files))

def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    in_str = False
    while i < n:
        if depth == 0 and not in_str and src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if not in_str and src.startswith('/-', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src[i] == '"' and (i == 0 or src[i-1] != '\\'):
            in_str = not in_str
        out.append(src[i]); i += 1
    return ''.join(out)

TOKENS = {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'^\s*(private\s+|protected\s+)?axiom\b|\baxiom\s+\w',
 'native_decide': r'native_decide', 'implemented_by': r'implemented_by', 'extern': r'\bextern\b',
 'unsafe': r'\bunsafe\b', 'opaque': r'\bopaque\b', 'csimp': r'csimp', 'skipKernelTC': r'skipKernelTC',
 'ofReduceBool': r'ofReduceBool|reduceBool', 'partial': r'\bpartial\s+def\b',
 'elab': r'^\s*(local\s+|scoped\s+)?elab\b|elab_rules', 'macro': r'^\s*(local\s+|scoped\s+)?macro\b|macro_rules',
 'syntax': r'^\s*(local\s+|scoped\s+)?syntax\b', 'notation': r'^\s*(local\s+|scoped\s+)?(notation|infix|infixl|infixr|prefix|postfix)\b',
 'run_cmd/#eval': r'run_cmd|run_tac|#eval|#exit', 'import Lean': r'^\s*(public\s+)?import\s+Lean\b',
 'debug options': r'set_option\s+debug', 'Kernel/Environment API': r'\bKernel\.|addDecl|Environment\.',
 'attribute[-instance]': r'attribute\s*\[\s*-', 'decide': r'\bdecide\b',
 'unsafeCast/panic': r'unsafeCast|panic!|dbg_trace',
}
hits = collections.defaultdict(list); comment_hits = collections.defaultdict(list)
setopts = collections.Counter(); instances = []; decls = []; imports = collections.Counter()
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|nonrec|partial)\s+)*(def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[]+)?', re.M)
total_lines = 0
for f in files:
    src = open(f, encoding='utf-8').read()
    total_lines += src.count('\n') + (0 if src.endswith('\n') else 1)
    code = strip_comments(src)
    rel = os.path.relpath(f, ROOT)
    for name, pat in TOKENS.items():
        for m in re.finditer(pat, code, re.M):
            ln = code.count('\n', 0, m.start()) + 1
            hits[name].append(f'{rel}:{ln}: {src.splitlines()[ln-1].strip()[:110]}')
        for m in re.finditer(pat, src, re.M):
            ln = src.count('\n', 0, m.start()) + 1
            comment_hits[name].append(ln)
    for m in re.finditer(r'set_option\s+([\w.]+)\s+(\S+)', code):
        setopts[(m.group(1), m.group(2))] += 1
    for m in re.finditer(r'^\s*(?:public\s+)?import\s+(\S+)', code, re.M):
        imports[m.group(1).split('.')[0]] += 1
    # namespace tracking (approximate)
    ns = []
    for line in code.splitlines():
        mm = re.match(r'\s*namespace\s+(\S+)', line)
        if mm: ns.append(mm.group(1)); continue
        mm = re.match(r'\s*end\s+(\S+)\s*$', line)
        if mm and ns and ns[-1] == mm.group(1): ns.pop(); continue
        mm = DECL.match(line)
        if mm:
            kind, nm = mm.group(1), mm.group(2)
            full = '.'.join(ns + [nm]) if nm else '.'.join(ns) + '.<anon>'
            if nm and nm.startswith('_root_.'): full = nm[len('_root_.'):]
            decls.append((kind, full, rel))
            if kind == 'instance': instances.append(f'{rel}: {line.strip()[:120]}')
print('total lines:', total_lines)
print('\n== code hits (comments stripped) ==')
for name in TOKENS:
    print(f'{name}: {len(hits[name])}')
    if name not in ('decide',):
        for h in hits[name][:20]: print('   ', h)
print('decide: files =', len({h.split(":")[0] for h in hits["decide"]}))
for h in hits['decide']: print('   ', h)
print('\n== raw hits including comments (counts) ==')
for name in TOKENS:
    if len(comment_hits[name]) != len(hits[name]):
        print(f'{name}: raw {len(comment_hits[name])} vs code {len(hits[name])}')
print('\n== imports (top-level package) ==', dict(imports))
print('\n== set_option (name, value): count ==')
for k, v in sorted(setopts.items()): print('   ', k, v)
print('\n== instance declarations ==', len(instances))
for i in instances: print('   ', i)
kinds = collections.Counter(k for k, _, _ in decls)
print('\n== declarations by kind ==', dict(kinds))
# name-capture check
STD = ['Module.Free','Module.finrank','Odd','Field','MvPolynomial','Ideal','Ideal.span','Ideal.Quotient.mk','Set.range',
       'Finset.range','Fintype.piFinset','Nat.factorial','factorial','Fin','Fin.cases','X','MvPolynomial.X','Finset.univ',
       'Finset.filter','Submodule.restrictScalars','HasQuotient','Quotient','Int','Nat','CommRing','Semiring','Module',
       'finrank','Free','span','range','piFinset','mk','cases','Matrix.rank','Matrix.map','algebraMap']
print('\n== project declarations whose name ends with a standard name used in the statement ==')
bad = [(k, n, r) for k, n, r in decls for s in STD if n == s or n.endswith('.' + s)]
for b in bad: print('   ', b)
print('count:', len(bad))
top = collections.Counter(n.split('.')[0] for _, n, _ in decls)
print('\n== top-level namespaces of project declarations ==', dict(top))
