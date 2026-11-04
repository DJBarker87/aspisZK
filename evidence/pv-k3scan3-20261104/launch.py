from pathlib import Path
import subprocess,json,sys,time,hashlib,os,re
ROOT=Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101/d592')
INFRA=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
ident=sys.argv[1];cfg=json.loads((ROOT/sys.argv[2]).read_text());assert re.fullmatch(r'K919[0-5][0-9]',ident)
out=ROOT/ident
if out.exists():
 # Common (m'): a barrier refusal before compiler start consumes zero invocations.
 barrier=out/'barrier.json'
 assert barrier.exists() and not json.loads(barrier.read_text())['allowed'] and not (out/'time.log').exists(),'ID already compiled or unresolved'
 started=json.loads((out/'STARTED.json').read_text())
 assert time.time()-started['epoch']>=180,'refusal cooldown'
 archive=out/'refusals'/str(len(list((out/'refusals').glob('*'))) if (out/'refusals').exists() else 0)
 archive.mkdir(parents=True)
 for f in list(out.iterdir()):
  if f.name!='refusals':f.rename(archive/f.name)
else:out.mkdir()
state=ROOT/'last-launch.json'
# Admission refusals wait 180s under common (m′); successful serial scopes need no artificial cooldown.
quiet=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');(out/'quiet-marker.json').write_text(json.dumps({'now':time.time(),'marker':json.loads(quiet.read_text()) if quiet.exists() else None}))
r=subprocess.run(['python3',str(INFRA/'reservation.py'),str(out/'admission.json')],stdout=(out/'admission.log').open('w'),stderr=subprocess.STDOUT)
a=json.loads((out/'admission.json').read_text());assert r.returncode==0 and a['allowed'],f'admission refused exit={r.returncode}: {a}'
P=ROOT/'caller';env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(ROOT/'target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG_ASSERTIONS='false',CARGO_PROFILE_DEV_OVERFLOW_CHECKS='false')
cmd=['cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness',cfg['harness'],'--no-overflow-checks','--keep-temps','--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing']
features=cfg.get('features','');features=','.join(filter(None,[features,'negative-control' if cfg['negative'] else '']))
if features:cmd+=['--features',features]
cmd+=['--cbmc-args','--unwinding-assertions']
md=['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--offline']
if features:md+=['--features',features]
m=subprocess.run(md,env=env,capture_output=True);(out/'metadata.json').write_bytes(m.stdout);(out/'metadata.stderr').write_bytes(m.stderr)
if m.returncode:raise SystemExit(m.returncode)
(out/'source-sha256.json').write_text(json.dumps({str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for d in [P,ROOT/'source',ROOT/'native'] for f in d.rglob('*') if f.is_file()},indent=2)+'\n')
start=time.time();state.write_text(json.dumps({'epoch':start,'id':ident}));(out/'STARTED.json').write_text(json.dumps({'epoch':start,'id':ident,'command':cmd,'config':cfg,'source_revision':(ROOT/'source-revision.txt').read_text().strip() if (ROOT/'source-revision.txt').exists() else os.environ['PV_SOURCE_REVISION']})+'\n')
scope=['systemd-run','--user','--scope','--unit','pv-k3scan-'+ident,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(INFRA/'barrier.py'),str(out/'barrier.json'),'/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','900','taskset','--cpu-list','0-3',*cmd]
with (out/'output.log').open('w') as log:r=subprocess.run(scope,cwd=P,env=env,stdout=log,stderr=subprocess.STDOUT)
receipt={'id':ident,'command':cmd,'scope_command':scope,'exit_status':r.returncode,'wall_seconds':time.time()-start,'source_revision':(ROOT/'source-revision.txt').read_text().strip() if (ROOT/'source-revision.txt').exists() else os.environ['PV_SOURCE_REVISION'],'negative_control':cfg['negative'],'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},'print_axioms':'N/A: Kani; 0 Lean','expected_phase':'optimized compilation then '+cfg['harness']+' bounded caller/index/local-log proof; no field multiplication chain','profile':{'opt-level':3,'debug-assertions':False,'overflow-checks':False},'config':cfg,'std_transfer':'withheld pending reached-item parity/structural mapping; compiler V370 retained'}
if (out/'time.log').exists():
 t=(out/'time.log').read_text()
 for pattern,key in [(r'Maximum resident set size \(kbytes\): (\d+)','peak_rss_kib'),(r'Swaps: (\d+)','swap')]:
  m=re.search(pattern,t)
  if m:receipt[key]=int(m[1])
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(r.returncode)
