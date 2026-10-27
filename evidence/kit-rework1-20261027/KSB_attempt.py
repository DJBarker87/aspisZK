"""Serial invocation of the unchanged S2H admission and S2W runners."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-kit2-cache-20261027';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,local,module=sys.argv[1:];
if int(a.rsplit('L',1)[1])>150:raise SystemExit('budget exhausted')
local=Path(local);src='KSB_generated/'+module.replace('.','/')+'.lean';obj='KSB_objects/'+module.replace('.','/')+'.olean'
if (E/a/'receipt.json').exists():raise SystemExit('attempt already receipted')
def ssh(s):
 for transport_retry in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=20',H,s],capture_output=True,text=True)
  if r.returncode!=255:return r
  with (E/(a+'-transport.jsonl')).open('a') as f:f.write(json.dumps(dict(step=s,exit=255,retry=transport_retry,stderr=r.stderr))+'\n')
  if transport_retry==10:raise SystemExit('STOP transport after 10 retries')
  time.sleep(60)
 raise AssertionError

def transfer(args):
 for retry in range(11):
  r=subprocess.run(['scp','-o','ConnectTimeout=20','-q']+args,capture_output=True,text=True)
  if r.returncode==0:return
  if r.returncode!=255:raise RuntimeError(r.stderr)
  with (E/(a+'-transport.jsonl')).open('a') as f:f.write(json.dumps(dict(step=args,exit=255,retry=retry,stderr=r.stderr))+'\n')
  if retry==10:raise SystemExit('STOP scp transport after 10 retries')
  time.sleep(60)

def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 transfer([H+':'+B+'/'+n,str(E/n)])
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
# Pin every selected Aeneas object, before submission, using the selected search order.
pins=ssh("python3 - <<'PIN'\nfrom pathlib import Path\nimport hashlib,json\nroots="+repr([B+'/KSB_objects',C,C+'/objects'])+"\nkeys=set()\nfor root in roots:\n r=Path(root)\n keys.update(str(p.relative_to(r)) for base in ['Aeneas','AeneasMeta'] for p in (r/base).rglob('*.olean'))\n if (r/'Aeneas.olean').exists():keys.add('Aeneas.olean')\nselected={}\nfor key in sorted(keys):\n p=next(Path(r)/key for r in roots if (Path(r)/key).is_file())\n selected[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()\nprint(json.dumps(selected))\nPIN")
assert pins.returncode==0,pins.stderr
(E/(a+'-admission.json')).write_text(json.dumps({'exit_status':r.returncode,'allowed':ad['allowed'],'retry':retry})+'\n')
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','KSB_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':B+'/KSB_objects:'+C+':'+C+'/objects'},deps_fingerprint={'scope':'KSB raw kit private modules on persistent kit2 cache and coherent SInt2 objects','aeneas_library_objects':json.loads(pins.stdout)},expected_time='single module elaboration, no concrete arithmetic normalization',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh(f'mkdir -p {B}/{str(Path(src).parent)} {B}/{str(Path(obj).parent)}');assert r.returncode==0,r.stderr
transfer([str(local),H+':'+B+'/'+src])
transfer([str(E/(a+'.json')),H+':'+B+'/'+a+'.json'])
r=subprocess.run(['ssh','-o','ConnectTimeout=20',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json'],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
if r.returncode==255:
 (E/(a+'-transport.jsonl')).write_text(json.dumps(dict(phase='post-submission',exit=255,action='read-only recovery; no resubmission'))+'\n')
 time.sleep(60)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-2000:])
# Preserve the exact compiler input snapshot locally with the receipt.
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
