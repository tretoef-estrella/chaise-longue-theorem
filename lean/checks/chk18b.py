exec(open('chk18.py').read().split('cells=[')[0])
import sys
for q,a,b,p in [(3,2,3,3),(3,3,2,3),(3,1,4,3),(5,2,2,5),(5,1,3,3),(5,2,2,3)]:
    d,ni,bd=run(q,a,b,p); print('q=%d a=%d b=%d p=%d: downsets %d, inclusions %d, failures %d'%(q,a,b,p,d,ni,bd)); sys.stdout.flush()
