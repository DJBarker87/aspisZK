#!/usr/bin/env python3
"""Focused owned reference extraction; fresh1GiB cap, no swap."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,time,resource,signal
W=Path(__file__).resolve().parent
PHASE=sys.argv[1];assert PHASE in ['charon','aeneas']
A=W/('run-'+PHASE);A.mkdir(exist_ok='--inside' in sys.argv)
G=2**30;CAP=G if PHASE=='charon' else 512*2**20
HIGH=896*2**20 if PHASE=='charon' else 448*2**20
UNIT='aspis-s126-bump-reference-'+PHASE+'-'+W.name.rsplit('-',1)[1]
def sha(p):
 with p.open('rb')as stream:return hashlib.file_digest(stream,'sha256').hexdigest()
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
 limit=min(57*G,mem['MemTotal']-5*G)
 committed_current=sum(min(int(r['memory.current']),int(r['memory.max'])) for r in finite)
 headroom=reserved+extra-committed_current
 # Aeneas itself measured60MiB. Stream tool hashes instead of materializing
 # rustc_driver, and use a512MiB scope. Keep the SAME >=5GiB physical OS
 # budget; require another1GiB free after ALL unused finite caps. Existing
 # uncapped/OS residents are already excluded from MemAvailable.
 free_reserve=4*G if PHASE=='charon' else G
 admitted=reserved+extra<limit and mem['MemAvailable']>=headroom+free_reserve
 return dict(time=time.time(),groups=rows,memory=mem,finite_reserved_bytes=reserved,
  host_counter_fields=fields,host_counter_charge_bytes=charge,additional_bytes=extra,
  own_scope_included=own,limit_bytes=limit,admitted=admitted,
  capped_current_bytes=committed_current,remaining_capped_headroom_bytes=headroom,
  additional_free_reserve_bytes=free_reserve,
  qualification='All populated finite MemoryMax values plus new scope below min57GiB/MemTotal-5GiB. MemAvailable covers ALL unused finite cap headroom plus recorded additional free reserve. Aeneas512MiB scope uses streaming hashes; predecessor translator60MiB. Other caps untouched. Snapshot, not a lifetime bound on future uncapped growth.')

if '--inside' not in sys.argv:
 original=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(512*2**20,original[1]));signal.alarm(40)
 inv=inventory();save('admission-before-scope.json',inv)
 if not inv['admitted']:raise SystemExit('Fresh admission denied; no compiler/extractor launched')
 signal.alarm(0);resource.setrlimit(resource.RLIMIT_AS,original)
 command=['systemd-run','--user','--scope','--unit='+UNIT,'-p','MemoryHigh='+str(HIGH),'-p','MemoryMax='+str(CAP),'-p','MemorySwapMax=0','-p','RuntimeMaxSec=180','-p','TasksMax=64','python3','-I','-S','-B',str(W/'nuc.py'),PHASE,'--inside']
 save('launch.json',{'command':command,'runner_sha256':sha(W/'nuc.py')})
 status=subprocess.call(command);save('outer-terminal.json',{'exit_status':status,'time':time.time()});raise SystemExit(status)
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
assert (cg/'memory.max').read_text().strip()==str(CAP)
assert (cg/'memory.high').read_text().strip()==str(HIGH)
assert (cg/'memory.swap.max').read_text().strip()=='0'
(cg/'memory.oom.group').write_text('1')
plan=json.loads((W/'plan.json').read_text())
def sources():return {p:sha(W/p)for p in plan['files']}
before=sources();assert before==plan['files']
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
AE=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-collapse-tool-recover-v2/source/src/_build/default/main.exe')
TC=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
toolpaths=[T/'charon',T/'charon-driver',AE,TC/'bin/rustc',TC/'bin/cargo']
toolpaths+=list((TC/'lib').glob('*.so*'))
toolpaths+=[p for p in (TC/'lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('*')if p.is_file()]
tp={str(p):sha(p)for p in toolpaths}
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(key,None)
if PHASE=='charon':
 command=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::branch','--include','core::option::_::from_residual','--start-from','crate::step','--dest-file',str(W/'BumpReference.llbc'),'--','--manifest-path',str(W/'input/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((W/'BumpReference.llbc').read_text())['has_errors']
 command=[str(AE),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6BumpOwnedReference','-dest',str(W/'generated'),'-subdir','AspisS6BumpOwnedReference','-split-files','-emit-json',str(W/'BumpReference.llbc')]
inv=inventory();save('admission-in-scope.json',inv);assert inv['admitted']and inv['own_scope_included']
save('input.json',{'schema':'focused-extractor-proof-packet-v1','command':command,'source_pins':before,'tool_pins':tp,'environment':{k:env[k]for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']},'expected_time':'Tiny optimized Rust reference compile/Charon extraction or focused Aeneas translation; no dependencies to build, arithmetic generation, Lean replay or aggregation.','llbc_sha256':sha(W/'BumpReference.llbc')if PHASE=='aeneas'else None})
start=time.monotonic()
with (A/'stdout.log').open('w')as out,(A/'time.log').open('w')as err:
 status=subprocess.call(['/usr/bin/time','-v','timeout','--signal=TERM','--kill-after=5s','140s',*command],cwd=W/'input',env=env,stdout=out,stderr=err)
timing=(A/'time.log').read_text()
import re
def metric(label):
 match=re.search(label+r':\s*(\d+)',timing);return int(match[1])if match else None
save('receipt.json',{'schema':'focused-extractor-proof-packet-v1','command':command,'exit_status':status,'wall_seconds':time.monotonic()-start,'peak_rss_kib':metric(r'Maximum resident set size \(kbytes\)'),'swaps':metric('Swaps'),'source_unchanged':sources()==before,'tools_unchanged':all(sha(Path(p))==h for p,h in tp.items()),'cgroup':{k:(cg/k).read_text().strip()for k in ['memory.max','memory.high','memory.swap.max','memory.peak','memory.events']},'print_axioms':'N/A: source extraction only','llbc_sha256':sha(W/'BumpReference.llbc')if (W/'BumpReference.llbc').exists()else None})
raise SystemExit(status)
