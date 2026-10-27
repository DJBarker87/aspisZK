"""Invoke unchanged admission and S2W runner; audit frozen graph per invocation."""
from pathlib import Path
import subprocess,json,time,hashlib,sys,tomllib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027'
a=sys.argv[1];n=sys.argv[2]
assert len(list(E.glob('LPi_K*/receipt.json'))) < 30, 'STOP proof budget exhausted'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
def admit(a):
 for retry in range(11):
  log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
  exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if exists:
   get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
   if r.returncode==0 and ad['allowed']:return retry
   if (r.returncode==78 or not ad['allowed']) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
  if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission '+r.stdout+r.stderr)
 raise SystemExit('STOP admission retries')
def launch(x):
 x['reservation_retries']=admit(x['attempt'])
 p=E/(x['attempt']+'.json');p.write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp','-q',str(p),H+':'+B+'/'+p.name],check=True)
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {p.name}')
 (E/(x['attempt']+'-launcher.log')).write_text(r.stdout+r.stderr)
 for f in ['receipt.json','stdout.log','time.log']:get(x['attempt']+'/'+f)
 rc=json.loads((E/x['attempt']/'receipt.json').read_text());print(x['attempt'],rc['exit_status'],round(rc['wall_seconds'],3),rc['peak_rss_kib'],flush=True);return rc
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();lockhash=hashlib.sha256(Path('Cargo.lock').read_bytes()).hexdigest()
base=dict(sources=['LPi_src/Cargo.lock','LPi_src/crates/aspis-r1-cost-probe/src/lib.rs','LPi_src/crates/aspis-r1-cost-probe/src/LPi_contracts.rs','LPi_src/crates/aspis-r1-cost-probe/src/LPi_verifier.rs','LPi_src/crates/aspis-core/src/field.rs','LPi_src/crates/aspis-core/src/field/wide_exact.rs','LPi_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs','LPi_src/crates/aspis-r1-cost-probe/src/verifier.rs'],source_revision=rev,source_tree_dirty=True,env={'TMPDIR':B+'/LPi_tmp','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1'})
g=a.replace('_K','_G');r=launch(dict(base,attempt=g,kind='metadata',command=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/LPi_src/Cargo.toml','--locked','--offline','--format-version','1'],timeout=120,expected_time='Frozen dependency graph validation, no solver'))
assert r['exit_status']==0
raw=(E/g/'stdout.log').read_text(); start=raw.find('{'); assert start>=0,'STOP metadata JSON missing'; m=json.loads(raw[start:]);lock=tomllib.loads(Path('Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'));frozen={key(p):p for p in lock['package']};actual={key(p) for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']};errors=[]
for p in m['packages']:
 if key(p) not in frozen:errors.append(['new package',key(p)]);continue
 for d in nodes[p['id']]['dependencies']:
  q=pkgs[d];variants=[k for k in frozen if k[0]==q['name']];ok=False
  for label in frozen[key(p)].get('dependencies',[]):
   z=label.split(' ')
   if z[0]==q['name'] and (len(z)>1 and z[1]==q['version'] or len(z)==1 and len(variants)==1) and (len(z)<3 or z[2].strip('()')==q.get('source')):ok=True
  if not ok:errors.append([key(p),key(q)])
def normalized_graph(m):
 k={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
 return {'packages':sorted(k.values()),'edges':sorted([k[n['id']],sorted(k[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
assert normalized_graph(m)==json.loads((E/'LPi_frozen_graph.json').read_text()),'STOP frozen resolved graph changed'
before=ssh(f'sha256sum {B}/LPi_src/Cargo.lock').stdout.split()[0]
check=dict(exact_frozen_resolved_graph_match=True,frozen_resolved_graph_receipt='LPi_frozen_graph.json',resolved_packages=len(actual),frozen_packages=len(frozen),new_package_tuples=sorted(actual-set(frozen),key=str),edge_errors=errors,graph_sha256=hashlib.sha256((E/g/'stdout.log').read_bytes()).hexdigest(),lock_before_sha256=before,frozen_lock_sha256=lockhash,package_and_edges_match=not errors and actual<=set(frozen))
(E/(a+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n');assert check['package_and_edges_match'] and before==lockhash
cfg=dict(base,attempt=a,kind='kani',command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+('/LPi_src/crates/aspis-core/Cargo.toml' if n.startswith('core:') else '/LPi_src/crates/aspis-r1-cost-probe/Cargo.toml'),'--target-dir',B+'/LPi_target','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',(n[5:] if n.startswith(('full:','core:')) else 'LPi_contracts::'+n),'--output-format','terse'],timeout=600,expected_time='Optimized compilation, then named solver stage '+n,deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_receipt':a+'-graph-check.json'})
r=launch(cfg);after=ssh(f'sha256sum {B}/LPi_src/Cargo.lock').stdout.split()[0];check['lock_after_sha256']=after;check['lock_unchanged']=after==before;(E/(a+'-graph-check.json')).write_text(json.dumps(check,indent=2)+'\n');assert after==before,'STOP lock changed'
print((E/a/'stdout.log').read_text()[-2400:],flush=True)
