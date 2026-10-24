#!/usr/bin/env python3
"""Authorized focused single-file local check; never a dependency build."""
import pathlib,subprocess,hashlib,json,os,sys,time,signal,re
R=pathlib.Path(__file__).resolve().parents[2];T=R/'tools/port18final-20261024';E=R/'evidence/port18final-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
module=sys.argv[1];assert module == 'Port18COHERENCE_CheckedAudit';source=L/(module+'.lean');O=pathlib.Path('/tmp/port18coherence-local-objects');O.mkdir(exist_ok=True)
number=1+len(list(T.glob('lean-*.json')));assert number<=2
attempt=f'lean-{number:03d}';out=E/attempt;out.mkdir();(out/'sources').mkdir();(out/'sources'/source.name).write_bytes(source.read_bytes())
lean='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';lake=str(pathlib.Path(lean).with_name('lake'))
path=str(O)+':/tmp/port17release-local-objects:/tmp/port17release-local-dependencies';cmd=[lake,'env','lean','-j1','-M4400','-DElab.async=false','-R',str(L),'-o',str(O/(module+'.olean')),str(source)]
if module.startswith(('Port18COHERENCE_Checked', 'Port18VALIDATE_', 'Port18COHERENCE_Kernel')):
 path=str(O)+':'+str(pathlib.Path(lean).parent.parent/'lib/lean')
 manifest=pathlib.Path('/tmp/port18coherence-snapshot-manifest.json')
else:
 manifest=pathlib.Path('/tmp/port17release-local-dependencies.json')
assert manifest.is_file()
x={'recheck_reason':'Lead-authorized final normal-import audit after maintained attribution/source refresh, new rejection validation, and dependency revalidation; historical audit028 remains historical','attempt':attempt,'schema':'focused-extractor-proof-packet-v1','kind':'lean','target':module,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_tree_dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=R,text=True).strip()),'command':cmd,'env':{'LEAN_PATH':path},'source_hashes':{source.name:hashlib.sha256(source.read_bytes()).hexdigest()},'deps_fingerprint':{'full_manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'full_manifest_bytes':manifest.stat().st_size,'objects':{}},'tool_sha256':hashlib.sha256(pathlib.Path(lean).read_bytes()).hexdigest(),'launcher_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'resource_policy':'focused warm-import local fallback; -j1 -M4400; aggregate child RSS hard stop 8 GiB; no dependency build','lock':'/tmp/aspis-local-lean.lock.d'}
for line in source.read_text().splitlines():
 if line.startswith('import '):
  for n in line[7:].split():
   key=n.replace('.','/')+'.olean';p=next((pathlib.Path(d)/key for d in path.split(':') if (pathlib.Path(d)/key).is_file()),None);assert p,n
   x['deps_fingerprint']['objects'][n]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
for previous in E.glob('lean-*/receipt.json'):
 old=json.loads(previous.read_text())
 if old.get('source_hashes')==x['source_hashes'] and old.get('deps_fingerprint')==x['deps_fingerprint'] and old.get('env')==x['env'] and old.get('launcher_sha256')==x['launcher_sha256']:
  raise RuntimeError('Unchanged source and dependencies: '+str(previous))
if module.startswith('Port18COHERENCE_Checked'):
 assert hashlib.sha256(pathlib.Path('/tmp/port18coherence-snapshots.tsv').read_bytes()).hexdigest()==json.loads(manifest.read_text())['tsv_sha256']
 for entry in json.loads(manifest.read_text())['snapshots']:
  q=pathlib.Path(entry['path']);assert hashlib.sha256(q.read_bytes()).hexdigest()==entry['sha256'],str(q)
preflight=E/'preflight.json';assert preflight.is_file()
x['final_preflight_sha256']=hashlib.sha256(preflight.read_bytes()).hexdigest()
x['final_dependency_closure']=json.loads(preflight.read_text())['checked_objects']
x['checker_sha256']=hashlib.sha256((T/'Port18FINAL_check.py').read_bytes()).hexdigest()
with (T/(attempt+'.json')).open('x') as h:h.write(json.dumps(x,indent=2)+'\n')
lock=pathlib.Path(x['lock']);startwait=time.monotonic()
while True:
 try:lock.mkdir();break
 except FileExistsError:
  if time.monotonic()-startwait>600:raise RuntimeError('Local lock wait exceeded ten minutes; reservation remains charged')
  time.sleep(15)
try:
 existing=subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True)
 assert not existing.stdout.strip(),existing.stdout
 subprocess.run([sys.executable,str(T/'Port18FINAL_check.py'),'--guard'],cwd=R,check=True)
 x['launch_utc']=__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat()
 env=os.environ.copy();env['LEAN_PATH']=path;begin=time.monotonic();peak=0;stopped=None
 # Task-owned minimal Lake metadata; no package resolution/build commands.
 work=pathlib.Path('/tmp/port18coherence-local-lake');work.mkdir(exist_ok=True);(work/'lakefile.toml').write_text('name = "port18coherence"\nversion = "0.1.0"\n');(work/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
 with (out/'stdout.log').open('w') as log,(out/'time.log').open('w') as tim:
  p=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=work,env=env,stdout=log,stderr=tim,start_new_session=True)
  while p.poll() is None:
   rows=subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines();table=[list(map(int,l.split())) for l in rows if len(l.split())==3];ids={p.pid}
   while True:
    new=ids|{pid for pid,ppid,rss in table if ppid in ids}
    if new==ids:break
    ids=new
   aggregate=sum(rss*1024 for pid,ppid,rss in table if pid in ids);peak=max(peak,aggregate)
   if aggregate>=8*1024**3 or time.monotonic()-begin>180:
    stopped='aggregate RSS cap' if aggregate>=8*1024**3 else '180 second timeout';os.killpg(p.pid,signal.SIGTERM);p.wait();break
   time.sleep(.25)
  code=p.wait()
 duration=time.monotonic()-begin;logs=(out/'stdout.log').read_text()+(out/'time.log').read_text();tim=(out/'time.log').read_text()
 def metric(pattern):
  m=re.search(pattern,tim,re.M);return int(m[1]) if m else None
 x.update(accepted=code==0 and "PANIC" not in logs and "error:" not in logs,exit_status=code,wall_seconds=duration,aggregate_child_peak_rss_bytes=peak,peak_rss_bytes=metric(r'^\s*(\d+)\s+maximum resident set size'),swaps=metric(r'^\s*(\d+)\s+swaps'),stopped=stopped,print_axioms=re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",logs))
 if code==0:x['object_sha256']=hashlib.sha256((O/(module+'.olean')).read_bytes()).hexdigest()
 (out/'receipt.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_bytes','aggregate_child_peak_rss_bytes','swaps','print_axioms']}));print(logs[-5000:]);sys.exit(code if x["accepted"] else 1)
finally:lock.rmdir()
