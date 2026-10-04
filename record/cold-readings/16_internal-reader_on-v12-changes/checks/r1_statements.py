# R1: extract every bold statement (Theorem/Lemma/Proposition/Corollary/Definition/Fact,
# MAIN THEOREM boxes, title, abstract) from v11 and v12 and compare them.
import re, difflib
A = open('material/THE_CHAISE_LONGUE_THEOREM_v11_for_comparison.md', encoding='utf-8').read().split('\n')
B = open('material/THE_CHAISE_LONGUE_THEOREM_v12.md', encoding='utf-8').read().split('\n')

head = re.compile(r'^(> )?\*\*(MAIN THEOREM′?|THEOREM [A-Z0-9]+|COROLLARY [A-Z]|Theorem [0-9A-Z.′]+|Lemma [0-9A-Z.′]+|Proposition [0-9A-Z.′]+|Corollary [0-9A-Z.′]+|Definition [0-9.]+|Fact [0-9.]+)')

def statements(L):
    out = {}
    i = 0
    while i < len(L):
        m = head.match(L[i])
        if m:
            key = m.group(2)
            # statement block: this line plus following '>' lines (boxed) or until a line starting with '*Proof'
            blk = [L[i]]
            j = i + 1
            if L[i].startswith('>'):
                while j < len(L) and L[j].startswith('>'):
                    blk.append(L[j]); j += 1
            else:
                while j < len(L) and L[j].strip() != '' and not L[j].startswith('*Proof') and not head.match(L[j]):
                    blk.append(L[j]); j += 1
            k = key
            n = 2
            while k in out:
                k = key + ' #' + str(n); n += 1
            out[k] = (i + 1, '\n'.join(blk))
            i = j
        else:
            i += 1
    return out

sa, sb = statements(A), statements(B)
print('v11 statements:', len(sa), ' v12 statements:', len(sb))
only_a = [k for k in sa if k not in sb]
only_b = [k for k in sb if k not in sa]
print('only in v11:', only_a)
print('only in v12:', only_b)
changed = 0
for k in sa:
    if k in sb and sa[k][1] != sb[k][1]:
        changed += 1
        print('\n=== CHANGED:', k, ' v11 line', sa[k][0], ' v12 line', sb[k][0])
        wa = sa[k][1].split(' '); wb = sb[k][1].split(' ')
        for op in difflib.SequenceMatcher(None, wa, wb, autojunk=False).get_opcodes():
            if op[0] != 'equal':
                print('  ', op[0], ' v11: «' + ' '.join(wa[op[1]:op[2]]) + '»  v12: «' + ' '.join(wb[op[3]:op[4]]) + '»')
print('\nnumber of statements with changed text:', changed)
# negative control: an artificially altered copy must be detected
sb2 = dict(sb); k0 = 'Theorem 8.11'
sb2[k0] = (sb[k0][0], sb[k0][1].replace('every odd', 'every'))
print('control (altered Theorem 8.11 detected):', sb2[k0][1] != sa[k0][1])
# title lines
print('\nTITLE v11:', A[1]); print('TITLE v12:', B[1])
