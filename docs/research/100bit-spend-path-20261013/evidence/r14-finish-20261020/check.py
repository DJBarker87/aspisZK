from pathlib import Path
import json,os,subprocess,time,hashlib,re,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[2]
OBJ=Path('/tmp/codex-cx-r14-finish-20261020-objects');OBJ.mkdir(exist_ok=True)
base=json.loads((ROOT/'evidence/log-tx2-20261020/resume-v3/command.json').read_text())
paths=base['environment']['LEAN_PATH'].split(':')
for packet in ['hchecks-20261020/reader-v9']:
 d=json.loads((ROOT/'evidence'/packet/'command.json').read_text()); paths+=(d.get('env',d.get('environment',{}))['LEAN_PATH']).split(':')
paths=[str(OBJ),'/tmp/codex-cx-geometry-20261020-objects','/tmp/cx-geometry-20261020-objects','/tmp/lean432-project-closure']+paths
paths=list(dict.fromkeys(paths))
# Lean chooses a namespace directory before checking the entire module path.
# Coalesce sparse inherited caches into this job's private overlay only.
for parent in paths[1:]:
 source_root=Path(parent)
 if not source_root.is_dir(): continue
 for objfile in source_root.rglob('*'):
  if not ('.olean' in objfile.name or objfile.suffix in ['.ir','.ilean']): continue
  if not objfile.is_file(): continue
  rel=objfile.relative_to(source_root); target=OBJ/rel
  if target.exists() or target.is_symlink(): continue
  target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(objfile)
env=dict(os.environ,LEAN_PATH=':'.join(paths))
module,attempt=sys.argv[1:];src=ROOT/'lean'/f'{module}.lean';dest=HERE/attempt;dest.mkdir()
argv=['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-DElab.async=false','-R',str(ROOT/'lean'),'-o',str(OBJ/f'{module}.olean'),str(src)]
imports={}
for m in re.findall(r'^import (\S+)',src.read_text(),re.M):
 for p in paths:
  f=Path(p)/(m.replace('.','/')+'.olean')
  if f.exists(): imports[m]={'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()};break
 else: imports[m]={'missing':True}
cmd={'argv':argv,'environment':{'LEAN_PATH':env['LEAN_PATH']},'imports':imports,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'deps_fingerprint':hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()}
(dest/'command.json').write_text(json.dumps(cmd,indent=2))
(dest/'source.lean').write_text(src.read_text())
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try: lock.mkdir()
 except FileExistsError: print('waiting for shared Lean lock',flush=True);time.sleep(15);continue
 # No other Lean compiler can be running; ignore noncompiler processes.
 ps=subprocess.check_output(['ps','-axo','comm=,args='],text=True)
 if any(line.split() and line.split()[0].rsplit('/',1)[-1] == 'lean' and '-M4400' in line for line in ps.splitlines()):
  lock.rmdir(); print('waiting for compiler memory gate',flush=True);time.sleep(15);continue
 break
try:
 t=time.monotonic()
 with (dest/'stdout.log').open('w') as out,(dest/'time.log').open('w') as err:
  proc=subprocess.run(['/usr/bin/time','-l']+argv,stdout=out,stderr=err,env=env,timeout=180)
 wall=time.monotonic()-t
finally: lock.rmdir()
out=(dest/'stdout.log').read_text();tim=(dest/'time.log').read_text()
def metric(pattern):
 m=re.search(pattern,tim);return int(m[1]) if m else None
receipt=dict(cmd,schema='focused-extractor-proof-packet-v1',module=module,attempt=attempt,exit=proc.returncode,wall_seconds=wall,peak_rss_bytes=metric(r'(\d+)\s+maximum resident set size'),swaps=metric(r'(\d+)\s+swaps'),axioms=re.findall(r"'[^']+' (?:depends on axioms:[\s\S]*?\]|does not depend on any axioms)",out))
(dest/'receipt.json').write_text(json.dumps(receipt,indent=2))
manifest=HERE/'manifest.json';data=json.loads(manifest.read_text()) if manifest.exists() else [];rows=data.get('attempts',[]) if isinstance(data,dict) else data;rows.append(receipt);manifest.write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':rows},indent=2))
print(out);print(json.dumps({k:receipt[k] for k in ['module','exit','wall_seconds','peak_rss_bytes','swaps']}));sys.exit(proc.returncode)
