"""Task orchestration around unchanged lead runner. Never resubmits an attempt."""
import json,subprocess,time,sys,hashlib,lzma
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parents[1]
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-l188-cache-20261028';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def ssh(s,inp=None):return subprocess.run(['ssh','-o','ControlMaster=no',H,s],input=inp,text=True,capture_output=True)
def get(name):
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['scp','-q','-o','ControlMaster=no',H+':'+B+'/'+name,str(p)],text=True,capture_output=True);assert r.returncode==0,r.stderr
mode=sys.argv[1];label=sys.argv[2];assert mode in ['normal','agg16'] and label in ['Headline','Joint']
a=({'Headline':'NDJ_R002','Joint':'NDJ_R003'}[label]) if mode=='normal' else 'NDJ_R004'
module='NDJ_'+label+'Audit'
assert not (E/a).exists(),'never repeat an attempt'
if mode=='agg16':
 prior=json.loads((E/'NDJ_R003/receipt.json').read_text());log=(E/'NDJ_R003/stdout.log').read_text()
 assert prior['exit_status']!=0 and 'NDJ_POST_IMPORT' not in log,'exception restricted to IMPORT failure'
 expect=json.loads((R/'evidence/joint-agg2-20261028/JHw_RUNNER_HASHES.json').read_text())['sha256']
 r=ssh("sha256sum "+' '.join(B+'/'+n for n in expect));assert r.returncode==0,r.stderr
 got={l.split()[1].split('/')[-1]:l.split()[0] for l in r.stdout.splitlines()};assert got==expect,(got,expect)
 (E/'NDJ_AGG16_RUNNER_HASHES.json').write_text(json.dumps(got,indent=2)+'\n')
for retry in range(11):
 script=B+'/reservation_agg16.py' if mode=='agg16' else '/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py'
 r=ssh(f'python3 {script} {B}/{a}-reservation.json > {B}/{a}-barrier-{retry}.log 2>&1')
 get(a+f'-barrier-{retry}.log')
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if exists:
  get(a+'-reservation.json');allowed=json.loads((E/(a+'-reservation.json')).read_text()).get('allowed') is True
 else:allowed=False
 with (E/'NDJ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='admission',attempt=a,retry=retry,exit_status=r.returncode,allowed=allowed))+'\n')
 if r.returncode==0 and allowed:break
 if not exists and retry==0:time.sleep(30);continue
 if r.returncode==78 or (exists and not allowed):
  assert retry<10,'admission exhausted'
  print('contention; wait 180 seconds',flush=True);time.sleep(180);continue
 raise RuntimeError('host admission infrastructure failure: '+r.stderr+(E/(a+f'-barrier-{retry}.log')).read_text())
get('NDJ_CACHE_PINS.json')
raw=(E/'NDJ_CACHE_PINS.json').read_bytes()
(E/'NDJ_CACHE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6))
(E/'NDJ_CACHE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NDJ_CACHE_PINS.json').unlink()
pins=json.loads(raw)
objects={r['module']:{k:r[k] for k in ['path','sha256','bytes']} for r in pins['objects'] if r['selection']==('joint' if label=='Joint' else 'union')}
cfg=dict(kind='lean',module=module,env={'LEAN_PATH':B+('/joint_objects:' if label=='Joint' else '/objects:')+T+'/lib/lean'},timeout=540,command=[T+'/bin/lake','env','lean','-j1','-M15000' if mode=='agg16' else '-M7000','-DElab.async=false','-o',a+'.olean',module+'.lean'],sources=[module+'.lean'],attempt=a,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip(),source_tree_dirty=True,deps_fingerprint=dict(scope='Separate pinned '+label+' root forest; shared-environment import failure retained in NDJ_IMPORT_FINDING.md',selected_objects=objects),expected_time='Import and kernel root/axiom/header audit only; unchanged dependency objects reused',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=subprocess.run(['scp','-q','-o','ControlMaster=no',str(E/(a+'.json')),str(E/(module+'.lean')),H+':'+B+'/'],capture_output=True,text=True);assert r.returncode==0,r.stderr
hi,ma,runner=('14G','16G','S2W_lean_host_agg16.py') if mode=='agg16' else ('6G','8G','S2W_run_host.py')
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh={hi} -p MemoryMax={ma} -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
assert r.returncode!=255,'submitted; recover read-only, NEVER resubmit'
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
d=json.loads((E/a/'receipt.json').read_text())
with (E/'NDJ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps({k:d[k] for k in ['attempt','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','source_revision','source_hashes','print_axioms']})+'\n')
print(json.dumps({k:d[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
