"""One-slot jobserver and aggregate cgroup thread measurement for NFZ_B005."""
from pathlib import Path
import os,subprocess,threading,time,json,sys
B=Path(__file__).resolve().parent
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:1])
os.environ.update(CARGO_BUILD_JOBS='1',RUSTFLAGS='-C codegen-units=1',RAYON_NUM_THREADS='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',LLVM_PARALLEL_COMPILE_JOBS='1')
r,w=os.pipe();os.write(w,b'+')
os.environ['MAKEFLAGS']=os.environ['CARGO_MAKEFLAGS']=f'--jobserver-auth={r},{w} -j1'
cg=Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
stop=threading.Event();counts=[]
def monitor():
 while not stop.is_set():
  counts.append(int((cg/'pids.current').read_text()));stop.wait(.01)
t=threading.Thread(target=monitor);t.start()
try:rc=subprocess.run([sys.executable,'-B','NFZ_check.py'],cwd=B,pass_fds=(r,w)).returncode
finally:
 stop.set();t.join();os.close(r);os.close(w)
 (B/'NFZ_THREADS.json').write_text(json.dumps(dict(measured_cgroup_threads_peak=max(counts),samples=len(counts),sampling_seconds=.01,limit=64,affinity=sorted(os.sched_getaffinity(0)),cargo_jobs=1,jobserver_tokens=1,RUSTFLAGS=os.environ['RUSTFLAGS'],exit=locals().get('rc')),indent=1)+'\n')
assert max(counts)<64
sys.exit(rc)
