# c05: compare my L1 output (#check of the final theorem and Theorem O, #print of the definitions)
# with the certificate §1.1/§1.2/§1.4 code blocks and with logs/certificado_pares/check_pares_postclean.log.
import os, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
mine = open(os.path.join(ROOT, 'checks', 'L1_main.log'), encoding='utf-8').read()
post = open(os.path.join(ROOT, 'material', 'logs', 'certificado_pares', 'check_pares_postclean.log'), encoding='utf-8').read()
cert = open(os.path.join(ROOT, 'material', 'certificate', 'LEAN_CERTIFICATE_CHAISE_LONGUE_v2.md'), encoding='utf-8').read()

def blocks(text):
    """split a Lean log into top-level items: an item starts at a line with no leading space."""
    items = []; cur = []
    for line in text.split('\n'):
        if line and not line[0].isspace() and cur:
            items.append('\n'.join(cur)); cur = []
        cur.append(line)
    if cur: items.append('\n'.join(cur))
    return items

def head(item):
    m = re.match(r"(@\[reducible\] def [\w.']+|def [\w.']+|@?[\w.']+)", item)
    if not m: return None
    h = m.group(1).replace('@[reducible] ', '').lstrip('@')
    return h[:-1] if h.endswith('.') else h

M = {head(b): b.strip() for b in blocks(mine) if head(b)}
P = {head(b): b.strip() for b in blocks(post) if head(b)}
names = ['EvenAll.mainTheorem\'', 'EvenAll.B1', 'EvenAll.B2', 'EvenAll.A3', 'OddEquality.D1', 'OddEquality.D2_DJ',
         'OddEquality.D2_M', 'OddTheorem.theoremO'] + ['def ' + n for n in
         ['EvenAll.Qall','EvenCount.QkEven','TheoremB.Qk','ColAssembly.idealZ','ColAssembly.RZ','ColAssembly.IZ',
          'ColUpper.psiP','ColUpper.tP','ColSurv.phi','BallotBound.Matching','ColSplit.gaIdeal','ColSplit.GA',
          'ColUpper.IK','ColUpper.psiG','ColUpper.tU']]
# certificate code blocks
cblocks = re.findall(r'```\n(.*?)```', cert, re.S)
ctext = '\n'.join(cblocks)
C = {head(b): b.strip() for b in blocks(ctext) if head(b)}
norm = lambda s: re.sub(r'\s+', ' ', s).strip()
for n in names:
    m, p, c = M.get(n), P.get(n), C.get(n)
    print(f'{n:32s} mine-vs-postclean: {"SAME" if m and p and norm(m)==norm(p) else ("absent in postclean" if not p else "DIFF")}'
          f'   mine-vs-certificate: {"SAME" if m and c and norm(m)==norm(c) else ("not in certificate" if not c else "DIFF")}')
    if m and p and norm(m) != norm(p): print('   MINE:', m[:300], '\n   POST:', p[:300])
    if m and c and norm(m) != norm(c): print('   MINE:', m[:400], '\n   CERT:', c[:400])
