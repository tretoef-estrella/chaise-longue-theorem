# c09: does the certificate's PDF say what its Markdown says? Extract the PDF text with pdftotext
# (to stdout, nothing written in material/) and look for the key numbers and statements of the .md.
import subprocess, os, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
C = os.path.join(ROOT, 'material', 'certificate')
pdf = subprocess.run(['pdftotext', '-layout', os.path.join(C, 'LEAN_CERTIFICATE_CHAISE_LONGUE_v2.pdf'), '-'],
                     capture_output=True, text=True).stdout
md = open(os.path.join(C, 'LEAN_CERTIFICATE_CHAISE_LONGUE_v2.md'), encoding='utf-8').read()
norm = lambda s: re.sub(r'\s+', ' ', s.replace(' ', ' ').replace(' ', ' '))
P = norm(pdf)
print('pdf pages:', pdf.count('\f') + 1, ' pdf chars:', len(pdf))
keys = ['4 412', '4 169', '2 470', '2 425', '41 243', '1 859', '20 117', '922', '187', '33 731', '8 209',
        '13 190', '2.35 GiB', '229 of the 233', '216 of the 233', '413 lines', '401 give the three axioms',
        '15 instances', '22 files', '8ac0df81107480be80e53c75b2e4dbbd', '8f9d9cff6bd728b17a24e163c9402775d9e6a365',
        'v4.28.0', 'mainTheorem', 'Qall', 'QkEven', 'propext', 'Classical.choice', 'Quot.sound',
        'aligned with version 12', '4 October 2026', 'Two passages', 'coincide with those of version 11',
        'm ^ (2 * k + 1) - EvenAll.Qall m k', 'Module.Free', '359 properties PROVED', 'Lemma 8.12, Corollary 8.13',
        'Fin.cases 0', 'J x ≠ x ∧ J (J x) = x']
for k in keys:
    inmd = norm(k) in norm(md); inpdf = norm(k) in P
    flag = '' if inmd == inpdf else '   <-- DIFFERS'
    print(f'{k[:50]:52s} md:{inmd!s:5s} pdf:{inpdf!s:5s}{flag}')
# section headers of the md present in the pdf?
heads = re.findall(r'^#+ (.+)$', md, re.M)
miss = [h for h in heads if norm(h.replace('`', '').replace('*', ''))[:40] not in P]
print('md headers:', len(heads), ' not found verbatim in the pdf text (first 40 chars):', len(miss))
for h in miss[:20]: print('   ', h[:90])
# second part: hyphens inserted by the typesetter at line ends (U+2010 or '-' + newline) inside
# tokens that in the .md contain no hyphen (hashes, Lean names, paths).
lines = pdf.split('\n')
print('\nline-end hyphenations in the PDF text:')
cnt = 0
for i, l in enumerate(lines[:-1]):
    t = l.rstrip()
    if t.endswith('‐') or (t.endswith('-') and not t.endswith(' -')):
        a = t.split()[-1] if t.split() else ''
        nxt = lines[i + 1].strip().split()
        b = nxt[0] if nxt else ''
        joined = a.rstrip('‐-') + b
        hyph_in_md = (a + b) in md or (a.rstrip('‐') + '-' + b) in md
        if not hyph_in_md:
            cnt += 1
            print(f'   pdf line {i+1}: {a!r} + {b!r}  -> joined {joined!r}; joined in md: {joined in md}')
print('total suspicious hyphenations:', cnt)
