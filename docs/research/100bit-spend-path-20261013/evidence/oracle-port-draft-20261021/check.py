#!/usr/bin/env python3
"""Focused local Lean attempts; private objects, shared lock, complete receipts."""
import os,sys,json,time,hashlib,subprocess,pathlib,re
root=pathlib.Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=pathlib.Path(__file__).resolve().parent
pin=json.loads((base/'evidence/oracle-multi-20261021/OracleDecisionMultiSummary-4/command.json').read_text())
extra=json.loads((base/'evidence/headline-20261021/R1FinalSoundnessHeadline-2/command.json').read_text())
obj=pathlib.Path('/tmp/codex-cx-oracle-port-draft-20261021-objects'); obj.mkdir(exist_ok=True)
module=sys.argv[1]; attempt=sys.argv[2]; src=base/'lean'/f'{module}.lean'
out=ev/f'{module}-{attempt}'; out.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=list(dict.fromkeys([str(obj)]+pin['lean_path'].split(':')+extra['lean_path'].split(':')))
imports=[]
for line in src.read_text().splitlines():
 if line.startswith('import '):
  for name in line.split()[1:]:
   found=next((pathlib.Path(p)/(name.replace('.','/')+'.olean') for p in paths if (pathlib.Path(p)/(name.replace('.','/')+'.olean')).exists()),None)
   imports.append({'module':name,'path':str(found),'sha256':sha(found) if found else None})
assert all(x['sha256'] for x in imports), imports
argv=[pin['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(base/'lean'),'-o',str(obj/f'{module}.olean'),str(src)]
cmd={'module':module,'attempt':attempt,'argv':argv,'lean_path':':'.join(paths),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_sha256':sha(src),'direct_imports':imports,'deps_fingerprint':hashlib.sha256(json.dumps({'imports':imports,'paths':paths},sort_keys=True).encode()).hexdigest()}
manifest_path=ev/'manifest.json'
if manifest_path.exists():
 for old in json.loads(manifest_path.read_text()).get('attempts',[]):
  if all(old.get(k)==cmd.get(k) for k in ['module','source_sha256','deps_fingerprint']):
   raise SystemExit('REFUSED unchanged source and dependencies; use existing receipt')
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
(out/'source.lean').write_bytes(src.read_bytes())
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir()
 except FileExistsError:time.sleep(15);continue
 running=subprocess.run(['pgrep','-fl','/bin/lean '],text=True,capture_output=True).stdout
 if any('-M4400' in line for line in running.splitlines()):lock.rmdir();time.sleep(60);continue
 break
try:
 assert sha(src)==cmd['source_sha256'], 'source changed while waiting for local lock'
 start=time.monotonic()
 with (out/'lean.log').open('w') as log,(out/'time.log').open('w') as timing:
  result=subprocess.run(['/usr/bin/time','-l']+argv,env={**os.environ,'LEAN_PATH':cmd['lean_path']},stdout=log,stderr=timing,cwd=root)
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(out/'lean.log').read_text(); timing=(out/'time.log').read_text()
rss=next((int(x.split()[0]) for x in timing.splitlines() if 'maximum resident set size' in x),None)
swap=next((int(x.split()[0]) for x in timing.splitlines() if 'swaps' in x),None)
receipt={**cmd,'exit':result.returncode,'wall_seconds':wall,'peak_rss_bytes':rss,'swaps':swap,'swap_measurement':'process swaps from time -l','axioms':re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log),'errors':log if result.returncode else []}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
manifest=ev/'manifest.json'
data=json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
data['attempts'].append(receipt);manifest.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['module','exit','wall_seconds','peak_rss_bytes','swaps']}));print(log)
sys.exit(result.returncode)
