import os,sys,subprocess,time,json,signal,hashlib,shutil
from pathlib import Path
base=Path(__file__).resolve().parent;base.mkdir(exist_ok=True)
label=sys.argv[1];out=base/label;out.mkdir()
root=base.parent
source=root/'docs/research/100bit-spend-path-20261013/lean'/sys.argv[2]
assert source.name in ['PublicRawAmountGuard.lean','PublicRawAmountGuardAgreement.lean']
objects=base/'objects';objects.mkdir(exist_ok=True)
coordinator=root/'.j1-raw-core-check'
backend=Path('/Users/dominic/ZK/AspisFormal')
cache=str(objects)+':'+str(coordinator/'objects')+':/Users/dominic/.cache/aspis/r1-j1-r7-r8-local-check-20261015-7c5ca8699/objects:'+str(root/'.j1-merge-check/objects')
cmd=['/usr/bin/time','-l','/Users/dominic/.elan/bin/lake','env','python3',str(coordinator/'lean-with-cache.py'),cache,'-M3500','-R',str(source.parent),'-o',str(objects/(source.stem+'.olean')),str(source)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={str(source):sha(source)}
for stem in ['PublicRawCore','PublicRawCoreAgreement']:
 for p in [source.parent/(stem+'.lean'),coordinator/'objects'/(stem+'.olean')]:
  pins[str(p)]=sha(p)
if source.stem=='PublicRawAmountGuardAgreement':
 for p in [source.parent/'PublicRawAmountGuard.lean',objects/'PublicRawAmountGuard.olean']:
  pins[str(p)]=sha(p)
runtime=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0')
runtime_pins={str(p):sha(p) for p in [runtime/'bin/lean',*sorted((runtime/'lib/lean').glob('libleanshared*.dylib'))]}
(out/'compiler-runtime.json').write_text(json.dumps({'version':subprocess.check_output([str(runtime/'bin/lean'),'--version'],text=True).strip(),'sha256':runtime_pins},indent=2)+'\n')
shutil.copy2(source,out/source.name)
shutil.copy2(Path(__file__),out/Path(__file__).name)
start=time.monotonic();peak=0;killed=False
before=subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip()
with (out/'lean.log').open('w') as log:
 p=subprocess.Popen(cmd,cwd=backend,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['/bin/ps','-axo','pid=,pgid=,rss='],text=True)
  rss=sum(int(z[2])for line in ps.splitlines()if len(z:=line.split())==3 and int(z[1])==p.pid)
  peak=max(peak,rss)
  if rss>=4*1024*1024 or time.monotonic()-start>180:
   killed=True;os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 rc=p.wait()
record={'command':cmd,'cwd':str(backend),'source_pins':pins,'checkout_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),'peak_group_rss_kib':peak,'guard_kib':4*1024*1024,'killed':killed,'system_swap_before':before,'system_swap_after':subprocess.check_output(['/usr/sbin/sysctl','vm.swapusage'],text=True).strip(),'scope':'Focused Lean4.32 only; retained readonly Core/Agreement and prior R1 dependency objects; no cold dependency build; maxRSS/swaps and axioms in lean.log. Core/guard checked separately under4.31 do not compose kernels.'}
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2));print((out/'lean.log').read_text());sys.exit(rc)
