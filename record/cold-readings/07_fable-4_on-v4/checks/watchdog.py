"""Run a command under a wall-clock cap and an RSS cap (kills the whole process group). Usage: python3 watchdog.py SECONDS MB -- cmd args..."""
import sys, subprocess, time, os, signal, resource
secs=int(sys.argv[1]); mb=int(sys.argv[2]); cmd=sys.argv[sys.argv.index('--')+1:]
t0=time.time()
p=subprocess.Popen(cmd, preexec_fn=os.setsid)
peak=0; reason="finished"
while p.poll() is None:
    time.sleep(0.5)
    try:
        out=subprocess.run(["ps","-o","rss=","-g",str(p.pid)],capture_output=True,text=True).stdout
        rss=sum(int(x) for x in out.split())//1024
    except Exception: rss=0
    peak=max(peak,rss)
    if rss>mb: reason="KILLED: RSS %d MB > cap %d MB"%(rss,mb); os.killpg(p.pid,signal.SIGKILL); break
    if time.time()-t0>secs: reason="KILLED: time > %d s"%secs; os.killpg(p.pid,signal.SIGKILL); break
p.wait()
print("[watchdog] %s ; wall %.1f s ; peak RSS of process group %d MB"%(reason,time.time()-t0,peak), flush=True)
