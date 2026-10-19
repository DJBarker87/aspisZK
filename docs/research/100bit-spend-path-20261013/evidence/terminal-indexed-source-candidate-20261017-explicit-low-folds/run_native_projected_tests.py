#!/usr/bin/env python3
"""Release differential tests against the isolated native workspace copy."""
import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
ROOT=Path('/tmp/aspis-poseidon-explicit-low-folds-native-20261017')
SOURCE=ROOT/'crates/aspis-statement/src/state_only_poseidon.rs'
TARGET=Path('/tmp/terminal-indexed-loops-candidate-20261016-v3/target-indexed-loops-v3')
CARGO=Path('/home/dombarker/.cargo/bin/cargo')
LIMITS={'MemoryHigh':'4G','MemoryMax':'4608M','MemorySwapMax':'0','TasksMax':'128'}
SOURCE_SHA='900c1ac840dcb86560ff26736fe63e4d35a8feafe0f365278a56f472d8f3273b'
TESTS=['factorized_projected_oracle_matches_reference_at_extreme_field_values','optimized_oracle_matches_independent_reference_at_random_off_domain_points']
ENV={**os.environ,'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_TARGET_DIR':str(TARGET),'CARGO_NET_OFFLINE':'true'}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def reservation(stage):
 units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True); active=0; scopes=[]
 for line in units.splitlines():
  fs=line.split()
  if not fs:continue
  unit=fs[0];out=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryMax','-p','MemoryHigh','-p','MemorySwapMax','-p','TasksMax','-p','ControlGroup'],text=True);d=dict(x.split('=',1) for x in out.splitlines() if '=' in x);scopes.append({'unit':unit,**d})
  if unit=='init.scope':continue
  m=d.get('MemoryMax','infinity')
  if m=='infinity':raise SystemExit('unbounded scope: '+unit)
  active+=int(m)
 target_procs=subprocess.check_output(['ps','-eo','args'],text=True).splitlines();writers=[x for x in target_procs if str(TARGET) in x and re.search(r'(^|/)(cargo|rustc)( |$)',x)]
 cap=active+45*1024**3+4608*1024**2;rec={'stage':stage,'scopes':scopes,'active_scoped_max_bytes':active,'external_reservation_bytes':45*1024**3,'this_rust_scope_bytes':4608*1024**2,'projected_bytes':cap,'policy_limit_bytes':50*1024**3,'target_writers':writers,'check':'pass' if cap<=50*1024**3 and not writers else 'fail'}
 d=ROOT/'run/explicit-low-folds-resume1-20261017';d.mkdir(parents=True,exist_ok=True);(d/(stage+'-reservation.json')).write_text(json.dumps(rec,indent=2)+'\n')
 if rec['check']!='pass':raise SystemExit('reservation check failed')
def inside():
 name=sys.argv[2];cmd=json.loads(sys.argv[3]);d=ROOT/'run/explicit-low-folds-resume1-20261017';log=d/(name+'.log');recp=d/(name+'.json');t=time.monotonic();started=time.time()
 with log.open('x') as f:p=subprocess.run(['/usr/bin/time','-v','timeout','--signal=KILL','300',*cmd],cwd=ROOT,env=ENV,stdout=f,stderr=subprocess.STDOUT)
 txt=log.read_text(errors='replace');m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt);cg=''
 for line in Path('/proc/self/cgroup').read_text().splitlines():
  if line.startswith('0::'):cg=line[3:];break
 c=Path('/sys/fs/cgroup')/cg.lstrip('/');rd=lambda x:(c/x).read_text().strip() if (c/x).exists() else None
 r={'stage':name,'command':cmd,'exit_status':p.returncode,'wall_seconds':round(time.monotonic()-t,3),'peak_process_rss_kib':int(m.group(1)) if m else None,'cgroup':cg,'memory_peak_bytes':rd('memory.peak'),'swap_peak_bytes':rd('memory.swap.peak'),'swap_current_bytes':rd('memory.swap.current'),'memory_events':rd('memory.events'),'memory_high':rd('memory.high'),'memory_max':rd('memory.max'),'memory_swap_max':rd('memory.swap.max'),'limits':LIMITS,'source_sha256':sha(SOURCE),'started_unix':started,'runner_sha256':sha(Path(__file__))};recp.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True);sys.exit(p.returncode)
if len(sys.argv)>1 and sys.argv[1]=='inside':inside()
if sha(SOURCE)!=SOURCE_SHA:raise SystemExit('isolated source hash mismatch')
for test in TESTS:
 reservation(test)
 cmd=[str(CARGO),'test','--manifest-path',str(ROOT/'Cargo.toml'),'--package','aspis-statement','--features','r0,pool-v1-kernel','--no-default-features','--release','--locked','--offline','--lib',test]
 unit='aspis-poseidon-explicit-low-folds-'+test+'-20261017';scope=['systemd-run','--user','--scope','--quiet','--unit='+unit]
 for k,v in LIMITS.items():scope+=['--property='+k+'='+v]
 scope += [sys.executable,str(Path(__file__).resolve()),'inside',test,json.dumps(cmd,separators=(',',':'))]
 result=subprocess.run(scope,cwd=ROOT,env=ENV,text=True,capture_output=True,timeout=360);d=ROOT/'run/explicit-low-folds-resume1-20261017';(d/(test+'-launch.json')).write_text(json.dumps({'test':test,'argv':scope,'exit_status':result.returncode,'stdout':result.stdout,'stderr':result.stderr,'limits':LIMITS},indent=2)+'\n');print(json.dumps({'test':test,'exit_status':result.returncode,'stdout':result.stdout,'stderr':result.stderr}),flush=True)
 if result.returncode:sys.exit(result.returncode)
