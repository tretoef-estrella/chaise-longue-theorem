# X1 — cross-references in the lines of v12 that are new or changed with respect to v11:
# every «Lemma/Proposition/Theorem/Corollary/Remark(s) x.y», «§x.y», «(8.n)», «[Key]» must have a target.
import re, difflib
A = open('material/THE_CHAISE_LONGUE_THEOREM_v11_for_comparison.md', encoding='utf-8').read().split('\n')
B = open('material/THE_CHAISE_LONGUE_THEOREM_v12.md', encoding='utf-8').read().split('\n')
changed = set()
for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, A, B, autojunk=False).get_opcodes():
    if tag != 'equal':
        changed |= set(range(j1, j2))
text = '\n'.join(B)
# targets
heads = set()
for l in B:
    m = re.match(r'^#+ (\d+(\.\d+)?|[A-Z](\.\d+)?)\b', l)
    if m: heads.add(m.group(1))
    m = re.match(r'^#+ (Appendix [A-Z])', l)
    if m: heads.add(m.group(1))
items = set()
for m in re.finditer(r'\*\*(?:THEOREM|Theorem|Lemma|Proposition|Corollary|Definition|Fact|Remarks?|COROLLARY)\s+([0-9A-Z]+(?:\.[0-9]+)?′?)', text):
    items.add(m.group(1))
for m in re.finditer(r'\*(?:Remarks?)\s+([0-9]+\.[0-9]+)', text):
    items.add(m.group(1))
eqs = set(re.findall(r'\((\d+\.\d+)\)`?\s*$', text, flags=re.M)) | set(re.findall(r'\*\*\((\d+\.\d+)\)\*\*', text)) | set(re.findall(r'`\s+\((\d+\.\d+)\)', text))
refkeys = set(re.findall(r'^- \*\*\[([^\]]+)\]\*\*', text, flags=re.M))
bad = []; n_checked = 0
for j in sorted(changed):
    l = B[j]
    for m in re.finditer(r'(Lemma|Lemmas|Proposition|Propositions|Theorem|Theorems|Corollary|Corollaries|Remark|Remarks|Definition|Fact)\s+((?:[0-9A-Z]+(?:\.[0-9]+)?′?)(?:\s*(?:,|and|–)\s*[0-9A-Z]+(?:\.[0-9]+)?′?)*)', l):
        for x in re.split(r'\s*(?:,|and|–)\s*', m.group(2)):
            x = x.strip()
            if not x or x in ('A', 'B', 'C', 'O', 'H', 'W') and m.group(1).startswith('Theorem'): continue
            if not re.match(r'^\d', x): continue
            n_checked += 1
            if x not in items: bad.append((j+1, m.group(1), x))
    for m in re.finditer(r'§(\d+(?:\.\d+)?)', l):
        n_checked += 1
        if m.group(1) not in heads: bad.append((j+1, '§', m.group(1)))
    for m in re.finditer(r'\[([A-Z][A-Za-z0-9]+)(?:,[^\]]*)?\]', l):
        k = m.group(1)
        n_checked += 1
        if k not in refkeys: bad.append((j+1, 'ref', k))
print('changed lines:', len(changed), ' references checked:', n_checked)
print('unresolved:', len(bad))
for b in bad: print('  ', b)
# control: a fake reference must be reported
print('control: fake «Lemma 8.99» resolves?', '8.99' in items, '; fake [Zzz] resolves?', 'Zzz' in refkeys)
