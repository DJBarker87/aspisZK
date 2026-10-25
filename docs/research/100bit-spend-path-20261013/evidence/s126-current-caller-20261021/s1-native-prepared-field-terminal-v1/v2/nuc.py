#!/usr/bin/env python3
"""One owned Linux Kani partition, fresh admission and24GiB/no-swap scope."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,time,signal,resource,re
W=Path(__file__).resolve().parent
BUILD=Path(json.loads((W/'plan.json').read_text()).get('build_directory',str(W)))
CASE=sys.argv[1];assert CASE=='point5'
G=2**30;CAP=24*G;HIGH=23*G
UNIT='aspis-s126-native-field-' +CASE+'-20261025-'+W.name.rsplit('-',1)[1]
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
 return {str(p):sha(p)for p in paths}
if '--inside'not in sys.argv:
 original=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(512*2**20,original[1]));signal.alarm(40)
 inv=inventory();save('admission-before-scope.json',inv)
 if not inv['admitted']:raise SystemExit('Fresh admission denied; no scope/compiler launched')
 signal.alarm(0);resource.setrlimit(resource.RLIMIT_AS,original)
 cmd=['systemd-run','--user','--scope','--unit='+UNIT,'--property=MemoryHigh=23G','--property=MemoryMax=24G','--property=MemorySwapMax=0','--property=RuntimeMaxSec=600','--property=TasksMax=64','/usr/bin/python3','-I','-S','-B',str(W/'nuc.py'),CASE,'--inside']
 save('launch.json',dict(command=cmd,runner_sha256=sha(W/'nuc.py')))
 status=subprocess.call(cmd);save('outer-terminal.json',dict(exit_status=status,time=time.time()));raise SystemExit(status)
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
assert (cg/'memory.max').read_text().strip()==str(CAP) and(cg/'memory.high').read_text().strip()==str(HIGH)
assert (cg/'memory.swap.max').read_text().strip()=='0';(cg/'memory.oom.group').write_text('1')
before=sources();assert before==json.loads((W/'plan.json').read_text())['files'];tp=tools()
env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(BUILD/'target'),RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
for key in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','RUSTC_BOOTSTRAP']:env.pop(key,None)
harness='verifier::proofs::prepared_new_claim_point_5'
base=['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',str(BUILD/'min/Cargo.toml'),'--lib','--exact','--harness',harness,'--solver','cadical','--no-assertion-reach-checks','-j','1','-Z','unstable-options','-Z','stubbing','--output-format','terse','--harness-timeout','500','--keep-temps']
for phase in ['compile','verify']:
 if phase=='compile' and CASE=='lo4' and BUILD!=W:
  prior=BUILD/'run-lo4/compile-receipt.json';r=json.loads(prior.read_text());i=json.loads((prior.parent/'compile-input.json').read_text())
  assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and i['source_pins']==before and i['tool_pins']==tp
  save('compile-reuse.json',dict(receipt=str(prior),sha256=sha(prior),input_sha256=sha(prior.parent/'compile-input.json'),source_pins_exact=True,tool_pins_exact=True,compiler_replayed=False));continue
 inv=inventory();save(phase+'-admission.json',inv);assert inv['admitted']and inv['own_scope_included']
 cmd=base+(['--only-codegen']if phase=='compile'else[])
 # Independent mathematical source loop bounds remain checked via unwinding
 # assertions. Use actual Linux loop identity discovered after focused compile.
 if phase=='verify':
  matches=list((BUILD/'target').rglob('*'+harness.split('::')[-1]+'.out'));assert len(matches)==1,matches
  q=subprocess.run(['/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','--show-loops',str(matches[0])],capture_output=True,text=True,timeout=15)
  (A/'loops.txt').write_text(q.stdout);assert q.returncode==0
  rows=re.findall(r'Loop ([^:]+):\n[^\n]*function verifier::prepared_claim[^\n]*',q.stdout)
  assert len(rows)==3,rows
  indexed={r.rsplit('.',1)[1]:r for r in rows};assert set(indexed)=={'0','1','2'}
  bound=7
  cmd+=['--cbmc-args','--unwinding-assertions','--unwindset',indexed['0']+':30,'+indexed['1']+':'+str(bound)+','+indexed['2']+':8']
 save(phase+'-input.json',dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_pins=before,tool_pins=tp,environment={k:env[k]for k in ['PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},expected_time='Focused optimized two-package compilation then ONE native full success constructor/claim SAT with actual field32 decoder; canonical928-byte payload and8 normal primitive cuts; no certificates/elimination/SBF.600s scope,500s solver,24GiB max/no swap.',print_axioms='N/A: Kani, no Lean axiom/theorem'))
 start=time.monotonic()
 with(A/(phase+'-stdout.log')).open('wb')as out,(A/(phase+'-stderr.log')).open('wb')as err:
  status=subprocess.call(['/usr/bin/time','-v','-o',str(A/(phase+'-time.log')),'/usr/bin/timeout','--signal=TERM','--kill-after=5s','540s',*cmd],cwd=BUILD/'min',env=env,stdout=out,stderr=err)
 timing=(A/(phase+'-time.log')).read_text()
 def metric(label):
  m=re.search(label+r':\s*(\d+)',timing);return int(m[1])if m else None
 receipt=dict(schema='focused-extractor-proof-packet-v1',command=cmd,exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_kib=metric(r'Maximum resident set size \(kbytes\)'),swaps=metric('Swaps'),source_unchanged=sources()==before,tools_unchanged=tools()==tp,cgroup={k:(cg/k).read_text().strip()for k in ['memory.max','memory.high','memory.swap.max','memory.peak','memory.events','memory.oom.group']},print_axioms='N/A: Kani only')
 save(phase+'-receipt.json',receipt);assert receipt['source_unchanged']and receipt['tools_unchanged']
 if status:raise SystemExit(status)
save('terminal.json',dict(exit_status=0,time=time.time(),harness=harness))
