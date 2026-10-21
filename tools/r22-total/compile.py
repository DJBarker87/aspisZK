#!/usr/bin/env python3
"""One focused local compile, private objects, serialized, complete receipts."""
import datetime, hashlib, json, os, pathlib, re, subprocess, sys, time
ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
OBJ=pathlib.Path('/tmp/codex-cx-r22-total-20261021-objects'); OBJ.mkdir(exist_ok=True)
LOCK=pathlib.Path('/tmp/aspis-local-lean.lock.d')
module=sys.argv[1]; attempt=sys.argv[2]
source=BASE/'lean'/f'{module}.lean'
seed=json.loads((BASE/'evidence/r19-budget-20261021/R1FinalSoundnessBinPerQueryR19-1/command.json').read_text())
extra=os.environ.get('R22_TOTAL_EXTRA_PATH','')
path=':'.join(x for x in [str(OBJ),extra,seed['lean_path']] if x)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Record actual resolved immediate import objects; transitive cache trust is
# inherited from their original packets, not a fresh dependency replay.
imports=[]
for name in re.findall(r'^import (\S+)',source.read_text(),re.M):
 for d in path.split(':'):
  p=pathlib.Path(d)/(name.replace('.','/')+'.olean')
  if p.exists(): imports.append({'module':name,'path':str(p),'sha256':sha(p),'size':p.stat().st_size}); break
 else: imports.append({'module':name,'missing':True})
deps=hashlib.sha256(json.dumps({'imports':imports,'lean_path':path},sort_keys=True).encode()).hexdigest()
out=BASE/'evidence/r22-total-20261021'/f'{module}-{attempt}'
if out.exists(): raise SystemExit('Attempt exists; use a changed source or new dependency fingerprint and a new attempt.')
out.mkdir()
(out/'source.lean.txt').write_text(source.read_text())
argv=[seed['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(BASE/'lean'),'-o',str(OBJ/f'{module}.olean'),str(source)]
record={'module':module,'attempt':attempt,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_sha256':sha(source),'deps_fingerprint':deps,'imports':imports,'argv':argv,'lean_path':path}
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n')
while True:
 try: LOCK.mkdir(); break
 except FileExistsError:
  if time.time()-LOCK.stat().st_mtime>1800:
   ps=subprocess.run(['pgrep','-fl','-x','lean'],capture_output=True,text=True).stdout
   if not any('-M4400' in l for l in ps.splitlines()): LOCK.rmdir(); continue
  print('Waiting for local Lean lock',flush=True); time.sleep(15)
try:
 while True:
  ps=subprocess.run(['pgrep','-fl','-x','lean'],capture_output=True,text=True).stdout
  if not any('-M4400' in l for l in ps.splitlines()): break
  print('Waiting for another capped Lean process',flush=True); time.sleep(15)
 (out/'preflight-processes.txt').write_text(ps)
 with (out/'lean.log').open('w') as log, (out/'time.log').open('w') as timing:
  start=time.monotonic()
  proc=subprocess.run(['/usr/bin/time','-l',*argv],env={**os.environ,'LEAN_PATH':path},cwd=ROOT,stdout=log,stderr=timing)
  wall=time.monotonic()-start
 log=(out/'lean.log').read_text(); timing=(out/'time.log').read_text()
 rss=re.search(r'(\d+)\s+maximum resident set size',timing)
 swaps=re.search(r'(\d+)\s+swaps',timing)
 record.update(schema='focused-extractor-proof-packet-v1',target=module,exit=proc.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(swaps[1]) if swaps else None,axiom_lines=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^]]*\]|does not depend on any axioms)", log),errors=[l for l in log.splitlines() if re.search(r'error(?:\([^)]*\))?:',l)])
 (out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
 manifests=BASE/'evidence/r22-total-20261021/manifest.json'
 old=json.loads(manifests.read_text()) if manifests.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
 old['attempts'].append(record)
 manifests.write_text(json.dumps(old,indent=2)+'\n')
 print(json.dumps({k:record[k] for k in ('module','exit','wall_seconds','peak_rss_bytes','swaps','axiom_lines','errors')},indent=2)); print(log[-10000:])
finally: LOCK.rmdir()
