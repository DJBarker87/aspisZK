#!/usr/bin/env python3
"""One focused local attempt, shared lock, immutable receipts, private objects."""
from pathlib import Path
import os, json, hashlib, subprocess, time, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
P=HERE.parent.parent
module='R1FinalSoundnessHeadlineV3'
src=P/'lean'/f'{module}.lean'
obj=Path('/tmp/codex-cx-loglen-20261021-objects'); obj.mkdir(exist_ok=True)
base=json.loads((P/'evidence/headline2-20261021/R1FinalSoundnessHeadlineV2-1/command.json').read_text())
leanpath=str(obj)+':'+base['lean_path']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports=[]
for m in re.findall(r'^import (\S+)',src.read_text(),re.M):
    f=next(Path(d)/(m.replace('.','/')+'.olean') for d in leanpath.split(':') if (Path(d)/(m.replace('.','/')+'.olean')).exists())
    imports.append(dict(module=m,path=str(f),sha256=sha(f)))
fp=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
attempt=1
while (HERE/f'{module}-{attempt}').exists(): attempt+=1
run=HERE/f'{module}-{attempt}'; run.mkdir()
argv=[base['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(P/'lean'),'-o',str(obj/f'{module}.olean'),str(src)]
command=dict(module=module,attempt=attempt,argv=argv,lean_path=leanpath,source_revision=revision,source_sha256=sha(src),direct_imports=imports,deps_fingerprint=fp)
(run/'command.json').write_text(json.dumps(command,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
    try: lock.mkdir(); break
    except FileExistsError: time.sleep(15)
try:
    # Check actual executable names, avoiding Codex prompts containing "lean".
    while True:
        ps=subprocess.check_output(['ps','-axo','pid=,comm=,args='],text=True)
        active=[s for s in ps.splitlines() if re.search(r'^\s*\d+\s+\S*/lean\s',s) and '-M4400' in s]
        if not active: break
        time.sleep(60)
    env=dict(os.environ,LEAN_PATH=leanpath)
    start=time.monotonic()
    with (run/'out.log').open('w') as out, (run/'time.log').open('w') as err:
        result=subprocess.run(['/usr/bin/time','-l']+argv,stdout=out,stderr=err,env=env)
    wall=time.monotonic()-start
finally: lock.rmdir()
output=(run/'out.log').read_text(); timing=(run/'time.log').read_text()
get=lambda pattern:int(re.search(pattern,timing).group(1)) if re.search(pattern,timing) else None
receipt=dict(command,schema='focused-extractor-proof-packet-v1',exit=result.returncode,wall_seconds=wall,peak_rss_bytes=get(r'(\d+)\s+maximum resident set size'),swaps=get(r'(\d+)\s+swaps'),axioms=re.findall(r"'AspisR1[\s\S]*?(?:does not depend on any axioms|depends on axioms: \[[^\]]*\])", output),errors=[s for s in output.splitlines() if 'error:' in s],time_log=timing)
if (obj/f'{module}.olean').exists():
    f=obj/f'{module}.olean'; receipt['object']={'sha256':sha(f),'size':f.stat().st_size}
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
previous=json.loads((HERE/'manifest.json').read_text()) if (HERE/'manifest.json').exists() else None
attempts=(previous['attempts'] if previous and 'attempts' in previous else [previous] if previous else [])
attempts.append(receipt)
(HERE/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':attempts},indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']},indent=2))
raise SystemExit(result.returncode)
