#!/usr/bin/env python3
"""STEP 4/7 supplement — (a) the full list of project modules outside the dependency cone of
mainTheorem' (order.txt minus deps_mainTheorem.log); expected: 23 modules (Upper x4, Degeneration x3,
Support x4, Ballot Alg/Comb/Construct, EveryField Integral/Invariance/Main, FreeZ Defs/Main, top Main,
and possibly Checks files). (b) per run section of AUDIT_LOG.md, the axiom sets recorded; expected: only
[propext, Classical.choice, Quot.sound], plus [propext, Quot.sound] for ColTensor.lemma64_v. Time < 1 s."""
import os, re
B = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'material', 'lean'))
used = {l.split()[0] for l in open(os.path.join(B, 'logs/deps_mainTheorem.log')) if l.startswith('RequestProject.')}
allm = [m.strip() for m in open(os.path.join(B, 'checks/order.txt')) if m.strip()]
out = sorted(set(allm) - used)
print('(a) modules outside the cone:', len(out)); [print('   ', m) for m in out]
s = open(os.path.join(B, 'AUDIT_LOG.md')).read()
print('(b) axiom sets per section of AUDIT_LOG.md')
for p in re.split(r'\n(?=## )', s):
    sets = sorted(set(re.findall(r'\[propext[^\]]*\]', p)))
    print('   %-60s %s' % (p.splitlines()[0][:60], sets))
