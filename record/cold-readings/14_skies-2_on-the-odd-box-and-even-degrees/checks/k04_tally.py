import re,glob
cells=pairs=non=tr=lt=eq=gt=ct=cf=sm=sf=st=g4=g4t=g4lt=0
for fn in sorted(glob.glob('checks/k04[a-f]_*.log')):
    for line in open(fn):
        if line.startswith('CELL'): cells+=1
        m=re.search(r'interlaced pairs: (\d+) .*not interlaced: (\d+)',line)
        if m: pairs+=int(m.group(1)); non+=int(m.group(2))
        m=re.search(r'\(G1\).* on (\d+) interlaced pairs: dim<\|Z\|: (\d+)\s+dim=\|Z\|: (\d+)\s+dim>\|Z\|: (\d+)',line)
        if m: tr+=int(m.group(1)); lt+=int(m.group(2)); eq+=int(m.group(3)); gt+=int(m.group(4))
        m=re.search(r'\(G3\).*tested (\d+), FAILURES (\d+);.*: (\d+)$',line.strip())
        if m: ct+=int(m.group(1)); cf+=int(m.group(2)); sm+=int(m.group(3))
        m=re.search(r'G3-control.*: (\d+) of (\d+) containments fail',line)
        if m: sf+=int(m.group(1)); st+=int(m.group(2))
        m=re.search(r'G4-control.*: (\d+) of (\d+) \(of which dim<\|Z\|: (\d+)\)',line)
        if m: g4+=int(m.group(1)); g4t+=int(m.group(2)); g4lt+=int(m.group(3))
print("cells",cells,"| interlaced pairs (incl. empty), summed over cells",pairs,"| non-interlaced pairs of down-sets",non)
print("(pair,cell,prime) triples",tr,"| dim<|Z|",lt,"| dim=|Z|",eq,"| dim>|Z|",gt)
print("Prop 6.1 containments tested",ct,"failures",cf,"| slices with dim W != |Z_layer|",sm)
print("shifted-slice control: fail",sf,"of",st)
print("non-interlaced control (pair,cell,prime): dim != |Z| in",g4,"of",g4t,"; of which dim<|Z|:",g4lt)
