import os,sys,subprocess,time,json,signal,hashlib,shutil
from pathlib import Path
base=Path(__file__).resolve().parent/'row-shape-proof-check';base.mkdir(exist_ok=True)
label=sys.argv[1];out=base/label;out.mkdir()
root=Path(__file__).resolve().parents[1]
source=root/'docs/research/100bit-spend-path-20261013/lean/ExtractedRowShape.lean'
objects=base/'objects';objects.mkdir(exist_ok=True)
coordinator=Path('/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015/.j1-record-source-check')
backend=Path('/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean')
cache=str(objects)+':'+str(coordinator/'objects')+':'+str(backend/'.lake/build/lib/lean')
cmd=['/usr/bin/time','-l','/Users/dominic/.elan/bin/lake','env','python3',str(coordinator/'lean-with-cache.py'),cache,'-M3500','-R',str(source.parent),'-o',str(objects/'ExtractedRowShape.olean'),str(source)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={str(source):sha(source)}
for stem in ['Types','Funs']:
 for suffix in ['.lean','.olean']:
  p=coordinator/('objects' if suffix=='.olean' else '')/'AspisR1RowShape'/(stem+suffix)
  pins[str(p)]=sha(p)
shutil.copy2(source,out/source.name)
start=time.monotonic();peak=0;killed=False
before=subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip()
with (out/'lean.log').open('w') as log:
 p=subprocess.Popen(cmd,cwd=backend,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['/bin/ps','-axo','pid=,pgid=,rss='],text=True)
  rss=sum(int(z[2])for line in ps.splitlines()if len(z:=line.split())==3 and int(z[1])==p.pid)
  peak=max(peak,rss)
  if rss>=4*1024*1024:
   killed=True;os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 rc=p.wait()
record={'command':cmd,'cwd':str(backend),'source_pins':pins,'checkout_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_group_rss_kib':peak,'guard_kib':4*1024*1024,'killed':killed,'system_swap_before':before,'system_swap_after':subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip(),'scope':'Focused Lean4.31 only; retained readonly row_shape and Aeneas dependency objects; no cold dependency build; maxRSS/swaps and axioms in lean.log.'}
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2));print((out/'lean.log').read_text());sys.exit(rc)
