#!/usr/bin/env python3
"""One owned Linux Kani partition, fresh admission and12GiB/no-swap scope."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,time,signal,resource,re
W=Path(__file__).resolve().parent
BUILD=Path(json.loads((W/'plan.json').read_text()).get('build_directory',str(W)))
CASE='extract'
G=2**30;CAP=2*G;HIGH=1536*2**20
UNIT='aspis-s126-query-pairs-reference-extract-20261025-v1'
A=W/('run-'+CASE);A.mkdir(exist_ok='--inside'in sys.argv)
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(n,v):(A/n).write_text(json.dumps(v,indent=2)+'\n')
def inventory():
 root=Path('/sys/fs/cgroup');rows=[];size=0
 def read(p):
  nonlocal size
  with p.open('rb')as f:data=f.read(131073)
  assert len(data)<=131072
  size+=len(data);assert size<=8*2**20
  return data.decode().strip()
 def walk(p):
  assert len(rows)<8192
  row={'path':str(p.relative_to(root))}
  for n in ['cgroup.events','memory.max','memory.current','memory.swap.max']:
   if (p/n).exists():row[n]=read(p/n)
  rows.append(row)
  for q in sorted(p.iterdir()):
   if q.is_dir():assert not q.is_symlink();walk(q)
 walk(root)
 mem={}
 for line in read(Path('/proc/meminfo')).splitlines():
  k,v=line.split(':',1);words=v.split()
  if len(words)==2 and words[1]=='kB':mem[k]=int(words[0])*1024
 finite=[r for r in rows if 'populated 1' in r.get('cgroup.events','')and r.get('memory.max','max')!='max']
 reserved=sum(int(r['memory.max'])for r in finite)
 # Whole-host counters charge uncapped populations too. No subtraction,
 # process-name filtering or slab discount; overlaps deliberately overcharge.
 fields=['AnonPages','Shmem','Unevictable','Slab','KernelStack','PageTables','Dirty','Writeback']
 charge=sum(mem[k]for k in fields)
 own=any(r['path'].endswith(UNIT+'.scope')for r in finite)
 extra=0 if own else CAP
 limit=min(55*G,mem['MemTotal']-9*G)
 committed_current=sum(min(int(r['memory.current']),int(r['memory.max'])) for r in finite)
 headroom=reserved+extra-committed_current
 admitted=reserved+extra<limit and mem['MemAvailable']>=headroom+4*G
 return dict(time=time.time(),groups=rows,memory=mem,finite_reserved_bytes=reserved,
  host_counter_fields=fields,host_counter_charge_bytes=charge,additional_bytes=extra,
  own_scope_included=own,limit_bytes=limit,admitted=admitted,
  capped_current_bytes=committed_current,remaining_capped_headroom_bytes=headroom,
  qualification='All populated finite MemoryMax values plus new scope must fit the safe cap budget; MemAvailable must exceed unused headroom of every populated finite cap plus new scope and4GiB of additional free reserve (existing OS memory is already excluded); already resident capped memory is already excluded from MemAvailable. Host counters retained as context. Operational snapshot, not a lifetime bound on future uncapped growth.')

def sources():
 return {p:sha(BUILD/p)for p in json.loads((W/'plan.json').read_text())['files']}
def tools():
 K=Path('/home/dombarker/.kani/kani-0.67.0');assert (K/'rustc-version').read_text().strip()=='rustc 1.93.0-nightly (53732d5e0 2025-11-20)'
 paths=[p for p in (K/'bin').iterdir()if p.is_file()]+[K/'rustc-version',K/'toolchain/bin/rustc',K/'toolchain/bin/cargo']
 paths += [p for p in (K/'lib').glob('*')if p.is_file()]
 paths += [p for p in (K/'toolchain/lib').glob('*.so*')if p.is_file()]
 paths += [p for p in (K/'toolchain/lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('*')if p.is_file()]
 Z=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/z3-tool-v1');jp=json.loads((Z/'tool-pins.json').read_text());assert sha(Z/'bin/z3')==jp['tool_sha256'];paths+=[Z/'bin/z3',Z/'tool-pins.json']+[p for p in(Z/'lib').rglob('*.so*')if p.is_file()]
 return {str(p):sha(p)for p in paths}

C=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
D=C.parent/'charon-driver'
L=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
if '--inside'not in sys.argv:
 inv=inventory();save('admission.json',inv);assert inv['admitted']
 cmd=['systemd-run','--user','--scope','--unit='+UNIT,'-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','RuntimeMaxSec=540','-p','TasksMax=64','python3','-I','-S','-B',str(W/'extract.py'),'--inside']
 save('launch.json',dict(command=cmd,runner_sha256=sha(W/'extract.py')))
 status=subprocess.call(cmd);save('outer-terminal.json',dict(exit_status=status));raise SystemExit(status)
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
assert(cg/'memory.max').read_text().strip()==str(CAP)and(cg/'memory.swap.max').read_text().strip()=='0'
env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
commands=[('charon',[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--start-from','crate::pairs_reference','--start-from','core::option::Option','--include','core::option::Option','--include','crate::pairs_reference','--include','crate::OwnedScan','--include','aspis_core::transcript::QuerySampleError','--dest-file',str(W/'OwnedPairs.llbc'),'--','--manifest-path',str(W/'reference/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']),('aeneas',[str(L),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1OwnedQueryPairs','-dest',str(W/'generated'),'-subdir','AspisS1OwnedQueryPairs','-split-files','-emit-json',str(W/'OwnedPairs.llbc')])]
for phase,cmd in commands:
 inv=inventory();save(phase+'-admission.json',inv);assert inv['admitted']
 if phase=='aeneas':assert not json.loads((W/'OwnedPairs.llbc').read_text())['has_errors']
 inputs={str(p.relative_to(W)):sha(p)for p in [p for p in W.rglob('*')if p.is_file()and not p.is_relative_to(W/'target')and p.suffix in ['.rs','.toml','.lock']]};tp={str(p):sha(p)for p in [C,D,L]}
 save(phase+'-input.json',dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_pins=inputs,tool_pins=tp,environment={k:env[k]for k in ['RUSTUP_TOOLCHAIN','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']},print_axioms='N/A: extraction only'))
 start=time.monotonic()
 with(A/(phase+'-stdout.log')).open('wb')as out,(A/(phase+'-stderr.log')).open('wb')as err:status=subprocess.call(['/usr/bin/time','-v','-o',str(A/(phase+'-time.log')),*cmd],cwd=W,env=env,stdout=out,stderr=err)
 timing=(A/(phase+'-time.log')).read_text()
 def metric(label):
  m=re.search(label+r':\s*(\d+)',timing);return int(m[1])if m else None
 save(phase+'-receipt.json',dict(schema='focused-extractor-proof-packet-v1',exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_kib=metric(r'Maximum resident set size \(kbytes\)'),swaps=metric('Swaps'),source_unchanged=all(sha(W/p)==h for p,h in inputs.items()),tools_unchanged=all(sha(Path(p))==h for p,h in tp.items()),cgroup={k:(cg/k).read_text().strip()for k in ['memory.max','memory.high','memory.swap.max','memory.peak','memory.events']},print_axioms='N/A: extraction only'))
 if status:raise SystemExit(status)
save('terminal.json',dict(exit_status=0))
