"""Task orchestration only; all scopes/receipts use unchanged lead launchers."""
import hashlib,json,lzma,subprocess,sys,time
from pathlib import Path
E=Path(__file__).resolve().parent; R=E.parents[1]
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-axaudit-cache-20261028'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,module,selection,mode=sys.argv[1:]; assert mode in ('normal','agg16')
def record(**x):
 with (E/'NDP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
def transport(args,submitted=False):
 for retry in range(10):
  r=subprocess.run(args,text=True,capture_output=True)
  if r.returncode!=255:return r
  record(kind='transport',attempt=a,retry=retry,submitted=submitted,exit_status=255,error=r.stderr)
  if submitted:raise RuntimeError('Submitted attempt: recover read-only; do not resubmit')
  time.sleep(60)
 raise RuntimeError('Persistent transport failure')
def ssh(s,submitted=False):return transport(['ssh','-o','ControlMaster=no',H,s],submitted)
def get(n):
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 r=transport(['scp','-q','-o','ControlMaster=no',H+':'+B+'/'+n,str(p)])
 assert r.returncode==0,r.stderr
assert not (E/(a+'.json')).exists(),'attempt already exists'
if mode=='agg16':
 prior=json.loads((E/'NDP_R006/receipt.json').read_text())
 assert module=='NDP_Joint' and prior['exit_status']!=0
 assert 'NDP_POST_IMPORT' not in (E/'NDP_R006/stdout.log').read_text()
 expected=json.loads((R/'evidence/native-l188-20261028/NDJ_AGG16_RUNNER_HASHES.json').read_text())
 r=ssh('sha256sum '+' '.join(B+'/'+n for n in expected));assert r.returncode==0,r.stderr
 actual={l.split()[1].split('/')[-1]:l.split()[0] for l in r.stdout.splitlines()}
 assert actual==expected,(actual,expected)
 (E/'NDP_AGG16_RUNNER_HASHES.json').write_text(json.dumps(actual,indent=2)+'\n')
for retry in range(11):
 script=B+'/reservation_agg16.py' if mode=='agg16' else '/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py'
 r=ssh(f'python3 {script} {B}/{a}-reservation.json > {B}/{a}-barrier-{retry}.log 2>&1')
 get(a+f'-barrier-{retry}.log')
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 allowed=False
 if exists:
  get(a+'-reservation.json');allowed=json.loads((E/(a+'-reservation.json')).read_text()).get('allowed') is True
 record(kind='admission',attempt=a,retry=retry,exit_status=r.returncode,allowed=allowed)
 if r.returncode==0 and allowed:break
 if not exists and retry==0:time.sleep(30);continue
 if r.returncode==78 or (exists and not allowed):
  assert retry<10,'admission exhausted'
  print('Contention: waiting 180 seconds',flush=True);time.sleep(180);continue
 raise RuntimeError('Host admission infrastructure failure: '+r.stderr+(E/(a+f'-barrier-{retry}.log')).read_text())
pins=json.loads(lzma.decompress((R/'evidence/native-l188-20261028/NDJ_CACHE_PINS.json.xz').read_bytes()))
objects={x['module']:{'path':x['path'].replace('codex-cx-l188-cache-20261028','codex-cx-axaudit-cache-20261028'),'sha256':x['sha256'],'bytes':x['bytes']} for x in pins['objects'] if x['selection']==selection} if selection!='tool' else {}
if module!='NDP_Audit':
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  r=ssh(f'sha256sum {B}/NDP_Audit{suffix}')
  if r.returncode==0:objects['NDP_Audit'+suffix]={'path':B+'/NDP_Audit'+suffix,'sha256':r.stdout.split()[0]}
normal=mode=='normal'
cfg=dict(kind='lean',module=module,env={'LEAN_PATH':B+':'+B+('/joint_objects:' if selection=='joint' else '/objects:')+T+'/lib/lean'},timeout=540,command=[T+'/bin/lake','env','lean','-j1','-M7000' if normal else '-M15000','-DElab.async=false','-o',module+'.olean',module+'.lean'],sources=[module+'.lean'],attempt=a,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip(),source_tree_dirty=True,deps_fingerprint=dict(scope='Copied pinned predecessor '+selection+' objects; original seed read-only',selected_objects=objects,seed_manifest_sha256=hashlib.sha256(lzma.decompress((R/'evidence/native-l188-20261028/NDJ_CACHE_PINS.json.xz').read_bytes())).hexdigest()),expected_time='Import, full kernel dependency traversal, every imported axiom type/module inventory; no arithmetic proof reduction',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=transport(['scp','-q','-o','ControlMaster=no',str(E/(a+'.json')),str(E/(module+'.lean')),H+':'+B+'/']);assert r.returncode==0,r.stderr
hi,ma,runner=('6G','8G','S2W_run_host.py') if normal else ('14G','16G','S2W_lean_host_agg16.py')
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh={hi} -p MemoryMax={ma} -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log','sources/'+module+'.lean']:get(a+'/'+n)
d=json.loads((E/a/'receipt.json').read_text())
record(kind='compile',**{k:d[k] for k in ['attempt','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','source_revision','source_hashes','print_axioms']})
print(json.dumps({k:d[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
if d['exit_status']==0 and module!='NDP_Audit':
 r=ssh(f'cd {B} && sha256sum {module}_REACHABLE.txt > {module}_REACHABLE.txt.sha256 && xz -6 -k {module}_REACHABLE.txt');assert r.returncode==0,r.stderr
 get(module+'_REACHABLE.txt.xz');get(module+'_REACHABLE.txt.sha256')
sys.exit(d['exit_status'])
