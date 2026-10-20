from pathlib import Path
import os, sys, time, subprocess, hashlib, json, re
base=Path(__file__).resolve().parents[2]; ev=Path(__file__).resolve().parent
name=sys.argv[1]; source=base/'lean'/f'{name}.lean'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
key=sha(source); run=ev/name/key[:12]; run.mkdir(parents=True,exist_ok=False)
obj=Path('/tmp/cx-wire-tx1-objects'); obj.mkdir(exist_ok=True)
lp=(ev/'lean-path.txt').read_text().strip(); env=dict(os.environ,LEAN_PATH=lp)
cmd=['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-DElab.async=false','-o',str(obj/f'{name}.olean'),str(source)]
imports=[]
for mod in re.findall(r'^import (\S+)',source.read_text(),re.M):
 for root in lp.split(':'):
  f=Path(root)/(mod.replace('.','/')+'.olean')
  if f.exists(): imports.append(dict(module=mod,object_path=str(f),object_sha256=sha(f)));break
 else: raise RuntimeError('missing '+mod)
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while True:
  ps=subprocess.check_output(['ps','-axo','comm=,args='],text=True)
  if not any(line.split()[0].endswith('/lean') and '-M4400' in line for line in ps.splitlines() if line.split()):break
  time.sleep(60)
 start=time.monotonic()
 with (run/'lean.log').open('w') as out,(run/'time.log').open('w') as err:
  result=subprocess.run(['/usr/bin/time','-l',*cmd],env=env,stdout=out,stderr=err,cwd=base)
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(run/'lean.log').read_text(); tm=(run/'time.log').read_text()
receipt=dict(module=name,source=str(source.relative_to(base.parent.parent.parent)),source_sha256=key,exit_status=result.returncode,wall_seconds=wall,peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size',tm)[1]),process_swap_count=int(re.search(r'(\d+)\s+swaps',tm)[1]),source_revision_parent=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,lean_path=lp,direct_imports=imports,deps_fingerprint=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest(),axioms=[' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",log,re.M|re.S)],errors=[l for l in log.splitlines() if 'error:' in l])
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
m=ev/'manifest.json'; manifest=json.loads(m.read_text()) if m.exists() else dict(schema='focused-extractor-proof-packet-v1',attempts=[])
manifest['attempts'].append(receipt);m.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['module','exit_status','wall_seconds','peak_rss_bytes','process_swap_count','axioms','errors']},indent=2));print(log if result.returncode else '')
sys.exit(result.returncode)
