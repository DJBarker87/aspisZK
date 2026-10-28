from pathlib import Path
import json, subprocess, shlex, sys
E=Path('evidence/native-drvdom3-20261028'); B='/home/dombarker/project-offloads/codex-cx-native-drvdom3-20261028'; C='/home/dombarker/project-offloads/codex-cx-drvdom-cache-20261028'
a,module=sys.argv[1:]; source=Path('lean/'+module+'.lean').read_text()
(E/a).mkdir(exist_ok=True); (E/a/'source.lean.txt').write_text(source)
seed=[]
paths=[C,'/home/dombarker/project-offloads/codex-cx-prepare-cache-20261028','/home/dombarker/project-offloads/codex-cx-query-cache-20261028','/home/dombarker/project-offloads/codex-cx-kmx-cache-20261028','/home/dombarker/project-offloads/codex-cx-assoc-a6-cache-20261027/XSc_objects','/home/dombarker/project-offloads/codex-cx-assoc-a6-cache-20261027/XRx_objects','/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects']
cfg=dict(attempt=a,kind='lean',sources=[module+'.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false',module+'.lean','-o',C+'/'+module+'.olean'],timeout=180,env={'PATH':'/home/dombarker/.elan/bin:/usr/bin:/bin','LEAN_PATH':':'.join(paths)},deps_fingerprint={'scope':'Copied KMY and NCL caches; inherited coherent SInt2 and reference-library boundaries'},expected_time='single module symbolic elaboration',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
setup=f'''from pathlib import Path
import json,shutil,hashlib
b=Path({B!r}); c=Path({C!r}); b.mkdir(exist_ok=True)
if not c.exists():
 raise RuntimeError('Required retained cache missing')
if False:
 c.mkdir()
 rows=[]
 for root in {seed!r}:
  for p in Path(root).rglob('*'):
   if p.is_file():
    q=c/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
    rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
    shutil.copy2(p,q)
 (b/'NDA_CACHE_COPY.json').write_text(json.dumps(rows,indent=2))
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 p=Path('/home/dombarker/project-offloads/codex-cx-native-tx1top-20261028')/n
 if p.exists() and not (b/n).exists():shutil.copy2(p,b/n)
(b/{(module+'.lean')!r}).write_text({source!r})
(b/{(a+'.json')!r}).write_text({json.dumps(cfg)!r})
'''
# The existing S2W backend is copied byte-for-byte; this is input/transport only.
cmd='python3 -c '+shlex.quote(setup)+' && cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py '+a+'.json'
admit=f"mkdir -p {B}; python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1; status=$?; cat {B}/{a}-reservation.json; exit $status"
ad=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90',admit],capture_output=True,text=True)
(E/(a+'-admission.log')).write_text(ad.stdout+ad.stderr)
assert ad.returncode==0 and json.loads(ad.stdout).get('allowed') is True, 'No launch: admission refusal/failure'
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90',cmd],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
print(r.returncode,r.stdout,r.stderr)
if r.returncode==255:sys.exit('Submitted transport ambiguous; recover only')
recover=f'''from pathlib import Path
import json
b=Path({B!r}); names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r},{(a+'-reservation.json')!r},{(a+'-barrier.log')!r},'NDA_CACHE_COPY.json']
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -c '+shlex.quote(recover)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'NDA_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc.get(k) for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}))
print((E/a/'stdout.log').read_text()[-24000:])
