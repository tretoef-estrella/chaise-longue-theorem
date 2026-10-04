# X4: cross-references of the printed text. Own script (Grepy Tinta). Text processing only.
import re,sys,collections
P='/Users/rafa/Desktop/LECTORES_EN_FRIO/V11_PRINTED_1/material/THE_CHAISE_LONGUE_THEOREM_v11.md'
L=open(P,encoding='utf-8').read().split('\n')
kinds='Lemma|Lemmas|Theorem|Theorems|Proposition|Propositions|Corollary|Corollaries|Remark|Remarks|Definition|Example|Examples|Fact'
norm={'Lemmas':'Lemma','Theorems':'Theorem','Propositions':'Proposition','Corollaries':'Corollary','Remarks':'Remark','Examples':'Example'}
defs=collections.defaultdict(list)
# definitions: bold or italic label at the start of a statement
for i,l in enumerate(L,1):
    for m in re.finditer(r'(?:\*\*|\*)(%s) ([0-9A]+\.[0-9]+[′\']?)'%kinds,l):
        k=norm.get(m.group(1),m.group(1)); 
        # treat as definition if it appears within the first 6 chars of line or after "> "
        if m.start()<=4: defs[(k,m.group(2))].append(i)
    m=re.match(r'^(#+) ([0-9A-Z]+(?:\.[0-9]+)?)\.? ',l)
    if m: defs[('§',m.group(2))].append(i)
    m=re.match(r'^### (A\.[0-9]+)',l)
    if m: defs[('§',m.group(1))].append(i)
    for m in re.finditer(r'`,?\s+\((\d+\.\d+)\)\s*$',l): defs[('eq',m.group(1))].append(i)
    for m in re.finditer(r'\*\*\((\d+\.\d+)\)\*\*',l): defs[('eq',m.group(1))].append(i)
    for m in re.finditer(r'\s\((\d+\.\d+)\)$',l): defs[('eq',m.group(1))].append(i)
print('DEFINED LABELS: %d'%len(defs))
for k in sorted(defs,key=lambda x:(x[0],[int(t) if t.isdigit() else 0 for t in re.split(r'[.′\']',x[1]) if t!=''] )):
    if len(defs[k])>1: print('  DUPLICATE DEF',k,defs[k])
rng=[(588,1295),(1422,1440),(1,161),(1006,1137)]
def inr(i): return any(a<=i<=b for a,b in rng)
refs=collections.defaultdict(list)
for i,l in enumerate(L,1):
    if not inr(i): continue
    s=re.sub(r'\[[A-Za-z0-9′]+,[^\]]*\]','[EXT]',l)   # strip external citations
    for m in re.finditer(r'(%s) ([0-9A]+\.[0-9]+[′\']?)((?:(?:, | and |–| to )[0-9A]+\.[0-9]+[′\']?)*)'%kinds,s):
        k=norm.get(m.group(1),m.group(1))
        labs=[m.group(2)]+re.findall(r'[0-9A]+\.[0-9]+[′\']?',m.group(3))
        for lab in labs: refs[(k,lab)].append(i)
    for m in re.finditer(r'§([0-9A]+(?:\.[0-9]+)?)((?:(?:, §?| and §?|–§?)[0-9A]+(?:\.[0-9]+)?)*)',s):
        labs=[m.group(1)]+re.findall(r'[0-9A]+(?:\.[0-9]+)?',m.group(2))
        for lab in labs: refs[('§',lab)].append(i)
    for m in re.finditer(r'\((\d+\.\d+)\)',s):
        refs[('eq',m.group(1))].append(i)
print('\nREFERENCES WITH NO DEFINITION FOUND (kind,label): lines')
for k in sorted(refs,key=lambda x:(x[0],x[1])):
    if k not in defs:
        print('  MISSING',k,sorted(set(refs[k]))[:12])
print('\nALL REFERENCED LABELS and definition line (for the semantic check):')
for k in sorted(refs,key=lambda x:(x[0],[int(t) if t.isdigit() else 0 for t in re.split(r'[.′\']',x[1]) if t!=''])):
    print('  %-12s %-7s def@%s  refs@%s'%(k[0],k[1],defs.get(k,['-'])[0],sorted(set(refs[k]))[:14]))
