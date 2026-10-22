#!/usr/bin/env python3
"""One focused Lean module; shared mkdir lock, own objects, full receipt."""
import hashlib,json,os,re,subprocess,time,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
module=sys.argv[1] if len(sys.argv)>1 else 'OraclePortS10ModelInventory';source=B/'lean'/f'{module}.lean'
obj=Path('/tmp/codex-cx-s10-inventory4-20261021-objects');obj.mkdir(exist_ok=True)
base=json.loads((B/'evidence/port-integrate-20261021/OraclePortFrozenOrderActualChecks-1/command.json').read_text())
argv=[base['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(B/'lean'),'-o',str(obj/f'{module}.olean'),str(source)]
sha=lambda b:hashlib.sha256(b).hexdigest()
imports=re.findall(r'^import (\S+)',source.read_text(),re.M);ckpt=json.loads((B/'evidence/ckpt-abi3-20261021/OraclePortCkptAbi3OwnedIter-1/command.json').read_text())
paths=list(dict.fromkeys([str(obj)]+base['lean_path'].split(':')+ckpt['lean_path'].split(':')));deps=[]
for name in imports:
 p=next(Path(p)/(name.replace('.','/')+'.olean') for p in paths if (Path(p)/(name.replace('.','/')+'.olean')).exists());deps.append(dict(module=name,path=str(p),sha256=sha(p.read_bytes())))
fingerprint=sha(json.dumps(deps,sort_keys=True).encode());source_sha=sha(source.read_bytes())
prior=sorted(E.glob(module+'-*'));attempt=len(prior)+1
for d in prior:
 c=json.loads((d/'command.json').read_text())
 if (c['source_sha256'],c['dependency_fingerprint'])==(source_sha,fingerprint):raise SystemExit('unchanged source/dependency attempt refused')
out=E/f'{module}-{attempt}';out.mkdir()
cmd=dict(module=module,attempt=attempt,argv=argv,lean_path=':'.join(paths),source_sha256=source_sha,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),dependencies=deps,dependency_fingerprint=fingerprint)
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');(out/'source.lean.txt').write_bytes(source.read_bytes())
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir()
 except FileExistsError:
  if time.time()-lock.stat().st_mtime>1800 and subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode!=0:lock.rmdir()
  else:print('Waiting for shared Lean lock',flush=True);time.sleep(15)
  continue
 if subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode==0:
  lock.rmdir();time.sleep(60);continue
 break
try:
 if sha(source.read_bytes())!=source_sha:raise RuntimeError("source changed while waiting for Lean lock")
 start=time.monotonic()
 with (out/'lean.log').open('w') as f:
  p=subprocess.run(['/usr/bin/time','-l',*argv],cwd=R,env=dict(os.environ,LEAN_PATH=':'.join(paths)),stdout=f,stderr=subprocess.STDOUT)
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(out/'lean.log').read_text();rss=re.search(r'(\d+)\s+maximum resident set size',log);swap=re.search(r'(\d+)\s+swaps',log)
axioms=re.findall(r"'[^\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
receipt=dict(**cmd,exit_status=p.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(swap[1]) if swap else None,print_axioms=axioms)
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
manifest=dict(schema='focused-extractor-proof-packet-v1',attempts=[json.loads((d/'receipt.json').read_text()) for d in sorted(E.glob('OraclePort*-*')) if (d/'receipt.json').exists()])
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['module','attempt','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']}));print(log[:6500] if p.returncode else '')
raise SystemExit(p.returncode)
