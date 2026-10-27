"""Job invocation only: unchanged S2H admission and S2W scoped runners."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-libmodel1-cache-20261027';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';A='/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027'
a,source,module=sys.argv[1:];assert int(a.rsplit('L',1)[1])<=80
assert not (E/a).exists()
events=[]
def transport(argv,submitted=False):
 for n in range(11):
  r=subprocess.run(argv,capture_output=True,text=True)
  if r.returncode!=255:return r
  events.append(dict(argv=argv,exit=255,retry=n,submitted=submitted,stderr=r.stderr))
  (E/(a+'-transport.json')).write_text(json.dumps(events,indent=2))
  if submitted:raise SystemExit('Submitted: recover read-only; NEVER resubmit')
  if n<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def ssh(s):return transport(['ssh','-o','ConnectTimeout=20',H,s])
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 r=transport(['scp','-q',H+':'+B+'/'+n,str(E/n)]);assert r.returncode==0,r.stderr
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:time.sleep(60);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
(E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,allowed=ad['allowed'],retry=retry))+'\n')
roots=[B+'/KSC1_objects',A+'/KSA_objects',A+'/XSd_objects',A+'/XRz_objects',A+'/XRx_objects',A+'/XRw_objects',C,C+'/objects']
r=ssh("python3 - <<'PIN'\nfrom pathlib import Path\nimport hashlib,json\nroots="+repr(roots)+"\nkeys=set()\nfor root in roots:\n r=Path(root)\n keys.update(str(p.relative_to(r)) for base in ['Aeneas','AeneasMeta'] for p in (r/base).rglob('*.olean'))\n if (r/'Aeneas.olean').exists():keys.add('Aeneas.olean')\nout={}\nfor key in sorted(keys):\n p=next(Path(r)/key for r in roots if (Path(r)/key).is_file())\n out[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()\nprint(json.dumps(out))\nPIN");assert r.returncode==0,r.stderr
src='KSC1_generated/'+module+'.lean';obj='KSC1_objects/'+module+'.olean'
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','KSC1_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':':'.join(roots)},deps_fingerprint={'scope':'private KSC1 objects; read-only prefixed KSA kit; coherent SInt2 dependency objects','aeneas_library_objects':json.loads(r.stdout)},expected_time='single focused module elaboration; tiny iterator probes only',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh(f'mkdir -p {B}/KSC1_generated {B}/KSC1_objects');assert r.returncode==0,r.stderr
for local,remote in [(source,src),(str(E/(a+'.json')),a+'.json')]:
 r=transport(['scp','-q',local,H+':'+B+'/'+remote]);assert r.returncode==0,r.stderr
r=transport(['ssh','-o','ConnectTimeout=20',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json'],submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
p=E/a/'sources'/src;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(source).read_bytes())
x=json.loads((E/a/'receipt.json').read_text());print({k:x[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']});print((E/a/'stdout.log').read_text()[-6500:])
