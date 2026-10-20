#!/usr/bin/env python3
"""Single changed bridge check using the already-green coherent suffix owner."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
W=Path(__file__).resolve().parent
C=json.loads((W/'config.json').read_text())
src=W/'proofs/PrefixSuffixAlphaBridge.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src)==C['bridge_source_sha256']
cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':str(512*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0'},limits
selected={}
for rel,want in C['expected_imports'].items():
 hits=[Path(r)/rel for r in C['lean_path'] if (Path(r)/rel).is_file()]
 assert hits,rel
 got=sha(hits[0]);assert got==want,(rel,str(hits[0]),got,want)
 selected[rel]={'path':str(hits[0]),'sha256':got}
out=W/'runs/bridge-v3';out.mkdir(parents=True,exist_ok=False)
obj=W/'attempt/objects';obj.mkdir(parents=True,exist_ok=True)
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(obj),*C['lean_path']])
cmd=[C['lean'],'-M4400','-j1','-R',str(W/'proofs'),'-o',str(obj/'PrefixSuffixAlphaBridge.olean'),str(src)]
before=(cg/'memory.events').read_text();start=time.monotonic();timing=out/'time.log'
with (out/'lean.log').open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=W/'proofs',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 peak=0
 while p.poll() is None:
  peak=max(peak,int((cg/'memory.current').read_text()))
  if time.monotonic()-start>120:p.terminate();p.wait();break
  time.sleep(.2)
 p.wait()
t=timing.read_text() if timing.exists() else ''
def num(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',t);return int(m[1]) if m else None
receipt={'phase':'bridge-v3','exit_status':p.returncode,'wall_seconds':time.monotonic()-start,'peak_process_rss_kib':num('Maximum resident set size (kbytes)'),'process_swaps':num('Swaps'),'sampled_cgroup_peak_bytes':peak,'cgroup_peak_bytes':int((cg/'memory.peak').read_text()),'cgroup_swap_current':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'limits':limits,'command':cmd,'lean_path':env['LEAN_PATH'],'source_sha256':sha(src),'selected_imports':selected,'output_sha256':sha(obj/'PrefixSuffixAlphaBridge.olean') if p.returncode==0 else None,'scope':'Conditional generated-prefix and constructor-suffix successes; no full resume reachability claim.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(p.returncode)
