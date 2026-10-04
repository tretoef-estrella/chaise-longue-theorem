import re
tot={}; cells=0
for line in open('checks/k07_constructions.log'):
    if line.startswith('CELL'): cells+=1
    m=re.match(r'\s+(.*?)\s+cases\s+(\d+) \|.*: (\d+) \|.*: (\d+) \|.*: (\d+) \|.*: (\d+)$',line.rstrip())
    if m:
        name=re.sub(r' \(.*\)','',m.group(1)).strip()
        full=m.group(1).strip()
        for key in (name, full) if full!=name else (name,):
            t=tot.setdefault(key,[0,0,0,0,0])
            for i in range(5): t[i]+=int(m.group(2+i))
print("cells",cells)
for k in sorted(tot): print("%-28s cases %6d | invalid %d | degree %d | top %d | membership %d"%(k,*tot[k]))
print("ALL cases (unsplit names only):",sum(v[0] for k,v in tot.items() if '(' not in k),"failures:",sum(sum(v[1:]) for v in tot.values()))
