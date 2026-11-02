"""One capped Kani invocation; fail-closed admission and 180-second own cooldown."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,os,re
ROOT=Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101')
INFRA=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
ident=sys.argv[1];config=json.loads((ROOT/sys.argv[2]).read_text());negative=config.get('negative',False)
assert re.fullmatch('K792[0-9][0-9]',ident),ident
out=ROOT/ident
assert not (out/'STARTED.json').exists(),'ID already launched'
out.mkdir(exist_ok=True)
state=ROOT/'last-launch.json'
if state.exists():
 remaining=json.loads(state.read_text())['epoch']+180-time.time()
 if remaining>0:raise SystemExit('cooldown pending %.3fs'%remaining)
# This check and launch belong to the same process/command; both JSON and exit are required.
r=subprocess.run(['python3',str(INFRA/'reservation.py'),str(out/'admission.json')],stdout=(out/'admission.log').open('w'),stderr=subprocess.STDOUT)
a=json.loads((out/'admission.json').read_text())
if r.returncode!=0 or not a['allowed']:raise SystemExit(78)
P=ROOT/config['package'];env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(ROOT/'resume-target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG_ASSERTIONS='false',CARGO_PROFILE_DEV_OVERFLOW_CHECKS='false')
cmd=['cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness',config['harness'],'--no-overflow-checks','--keep-temps','--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options']
if config.get('features'):cmd+=['--features',config['features']]
cmd+=['--cbmc-args','--unwinding-assertions']
md=['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--offline']
if config.get('features'):md+=['--features',config['features']]
# Metadata is read-only and invokes no compiler. Record every package's resolved features.
m=subprocess.run(md,env=env,capture_output=True);(out/'metadata.json').write_bytes(m.stdout);(out/'metadata.stderr').write_bytes(m.stderr)
if m.returncode:raise SystemExit(m.returncode)
(ROOT/'source-sha256.json').write_text(json.dumps({str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in P.rglob('*') if f.is_file() and 'target' not in f.parts},indent=2)+'\n')
start=time.time();state.write_text(json.dumps({'epoch':start,'id':ident}));(out/'STARTED.json').write_text(json.dumps({'epoch':start,'id':ident,'command':cmd,'negative':negative,'expected_phase':config['expected_phase'],'source_revision':os.environ.get('PV_SOURCE_REVISION')})+'\n')
scoped_cmd=cmd
scope=['systemd-run','--user','--scope','--unit','pv-k3scan-'+ident,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(INFRA/'barrier.py'),str(out/'barrier.json'),'/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','900','taskset','--cpu-list','0-3',*scoped_cmd]
with (out/'output.log').open('w') as log:r=subprocess.run(scope,cwd=P,env=env,stdout=log,stderr=subprocess.STDOUT)
receipt={'id':ident,'command':cmd,'scope_command':scope,'exit_status':r.returncode,'wall_seconds':time.time()-start,'source_revision':os.environ.get('PV_SOURCE_REVISION'),'negative_control':negative,'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},'print_axioms':'N/A: Kani; 0 Lean','profile':{'opt-level':3,'debug-assertions':False,'overflow-checks':False},'stubs':config.get('stubs',[]),'config':config,'oracle':'none; all records local','std_transfer':'withheld pending exact reached-item 1.93-nightly/1.94.1 parity'}
if (out/'time.log').exists():
 t=(out/'time.log').read_text()
 for pattern,key in [('Maximum resident set size \\(kbytes\\): (\\d+)','peak_rss_kib'),('Swaps: (\\d+)','swap')]:
  ma=re.search(pattern,t)
  if ma:receipt[key]=int(ma[1])
(ROOT/'source-sha256.json').replace(out/'source-sha256.json');(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
raise SystemExit(r.returncode)
