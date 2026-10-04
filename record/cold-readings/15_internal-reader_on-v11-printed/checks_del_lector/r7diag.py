import resource,sys,re
src=open('checks/r7_prop92_blocks.py').read()
def peak(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6   # MB on macOS (bytes)
parts=re.split(r"\nprint\('== P7\.",src)
head=parts[0]
exec(head)
print('after imports: maxrss %.0f MB'%peak())
for part in parts[1:]:
    code="print('== P7."+part
    # cut the big cells apart for the first part
    exec(code)
    print('   >>> maxrss so far: %.0f MB'%peak()); sys.stdout.flush()
