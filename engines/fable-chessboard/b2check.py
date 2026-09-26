import sys
for k in map(int, sys.argv[1:]):
    n=2*k+1; got=set(tuple(map(int,l.split())) for l in open('lm_%d_3.txt'%k))
    U=set()
    for mask in range(1<<n):
        e=tuple((mask>>(n-1-i))&1 for i in range(n)); h=0; mn=0
        for x in e: h+=1 if x else -1; mn=min(mn,h)
        if mn>=-1: U.add(e)
    print('k=%d |LM|=%d |U|=%d equal=%s'%(k,len(got),len(U),got==U))
