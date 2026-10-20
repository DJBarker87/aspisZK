#!/usr/bin/env python3
"""One module per attempt, private objects, mkdir lock, measured receipts."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,time,re
E=Path(__file__).resolve().parent; R=E.parents[4]; L=E.parents[1]/'lean'
O=Path('/tmp/codex-cx-ckpt-log-20261020-objects');O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((E.parents[1]/'evidence/source-global-oracle-full25-20261019/local-focused-attempts/root-source-global-oracle-coupling-v4-20261019/command.json').read_text())['lean_path'].split(':')
front=['/tmp/codex-cx-sampler-20261020-objects','/tmp/d18-full25-source-prefix-publication-20261019/d18-source-literal-initial-call-v22-attempt-20261019/objects','/tmp/root-source-global-oracle-full25-nuc-v1-fetched-20261019/attempt/objects','/tmp/root-source-global-oracle-nuc-v1-fetched-20261019/attempt/objects','/tmp/root-source-global-oracle-nuc-v1-fetched-20261019/prebuilt','/tmp/d18-full25-source-prefix-publication-20261019/d18-source-literal-full25-prefix-v8-attempt-20261019/objects','/tmp/d18-full25-source-prefix-publication-20261019/d18-source-literal-trace-lift-v14-attempt-20261019/objects','/tmp/d18-source-literal-step-green-20261019/evidence/objects','/tmp/d18-source-sampler-native-fetch-20261019/objects','/tmp/root-finish-prefix-deps-20261018']
paths=[O]+[Path(p) for p in front+prior+['/tmp/d18-typedfull-current-rebuild-20261019/objects','/tmp/d18-typedfull-current-20261019/objects','/tmp/gs-byte-extractor-deps-20261019/objects'] if Path(p).is_dir()]
module=sys.argv[1];attempt=sys.argv[2];src=L/(module+'.lean');a=E/attempt;a.mkdir()
imports=[]
for n in re.findall(r'^import (\S+)',src.read_text(),re.M):
 p=next((p/(n.replace('.','/')+'.olean') for p in paths if (p/(n.replace('.','/')+'.olean')).exists()),None)
 assert p,n
 imports.append(dict(module=n,path=str(p),sha256=sha(p),size=p.stat().st_size))
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 # Match the process executable, never a Codex prompt containing Lean flags.
 while any(re.search(r'^\s*\d+\s+(?:\S*/)?lean\s',s) and '-M4400' in s for s in subprocess.check_output(['ps','-axo','pid=,comm=,args='],text=True).splitlines()):time.sleep(60)
 argv=['/usr/bin/time','-l','/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-DElab.async=false','-o',str(O/(module+'.olean')),str(src)]
 env={**os.environ,'LEAN_PATH':':'.join(map(str,paths))}
 (a/'command.json').write_text(json.dumps(dict(argv=argv,environment={'LEAN_PATH':env['LEAN_PATH']},imports=imports),indent=2)+'\n')
 start=time.monotonic()
 with (a/'lean.log').open('w') as out,(a/'time.log').open('w') as err:p=subprocess.run(argv,env=env,stdout=out,stderr=err,cwd=L)
 wall=time.monotonic()-start
finally:lock.rmdir()
log=(a/'lean.log').read_text();tm=(a/'time.log').read_text()
ax=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
rss=re.search(r'(\d+)\s+maximum resident set size',tm);sw=re.search(r'(\d+)\s+swaps',tm)
receipt=dict(module=module,attempt=attempt,source=str(src.relative_to(R)),source_sha256=sha(src),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),exit_status=p.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(sw[1]) if sw else None,axiom_reports=ax,imports=imports)
(a/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));print(log)
sys.exit(p.returncode)
