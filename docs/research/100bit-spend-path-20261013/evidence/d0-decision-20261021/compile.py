#!/usr/bin/env python3
import pathlib, json, hashlib, os, subprocess, sys, time, re
ROOT=pathlib.Path(__file__).resolve().parents[5]
LEAN=ROOT/'docs/research/100bit-spend-path-20261013/lean'
OUT=pathlib.Path(__file__).resolve().parent
OBJ=pathlib.Path('/tmp/codex-cx-d0-decision-20261021-objects'); OBJ.mkdir(exist_ok=True)
base=json.loads((OUT.parent/'r3-semantic-20261021/R3SemanticRemainingJoins-3/command.json').read_text())
paths=[str(OBJ), '/tmp/codex-cx-r15-writer-20261021-objects','/tmp/codex-cx-r16-canon-20261021-objects','/tmp/codex-cx-r16-decision-20261021-objects']+base['lean_path'].split(':')
module=sys.argv[1]; attempt=int(sys.argv[2]); source=LEAN/(module+'.lean')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
imports=[]
for m in re.findall(r'^import (\S+)',source.read_text(),re.M):
    p=next((pathlib.Path(d)/(m.replace('.','/')+'.olean') for d in paths if (pathlib.Path(d)/(m.replace('.','/')+'.olean')).exists()),None)
    if p is None: raise RuntimeError('missing import '+m)
    imports.append({'module':m,'path':str(p),'sha256':sha(p)})
fp=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
dest=OUT/f'{module}-{attempt}'; dest.mkdir()
argv=[base['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(LEAN),'-o',str(OBJ/(module+'.olean')),str(source)]
cmd={'module':module,'attempt':attempt,'argv':argv,'lean_path':':'.join(paths),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_sha256':sha(source),'direct_imports':imports,'deps_fingerprint':fp}
(dest/'command.json').write_text(json.dumps(cmd,indent=2)+'\n'); (dest/'source.lean.txt').write_text(source.read_text())
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
    try: lock.mkdir(); break
    except FileExistsError: time.sleep(15)
try:
    # Match executable basename rather than other agents' prompts containing 'lean'.
    while subprocess.run(['pgrep','-x','lean'],capture_output=True).returncode==0: time.sleep(15)
    start=time.monotonic()
    with (dest/'lean.log').open('w') as out, (dest/'time.log').open('w') as err:
        result=subprocess.run(['/usr/bin/time','-l']+argv,stdout=out,stderr=err,env={**os.environ,'LEAN_PATH':':'.join(paths)})
    wall=time.monotonic()-start
finally: lock.rmdir()
log=(dest/'lean.log').read_text(); timing=(dest/'time.log').read_text()
def stat(pattern):
    m=re.search(pattern,timing); return int(m.group(1)) if m else None
receipt={**cmd,'exit':result.returncode,'wall_seconds':wall,'peak_rss_bytes':stat(r'(\d+)\s+maximum resident set size'),'swaps':stat(r'(\d+)\s+swaps'),'axioms':[l for l in log.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],'errors':[l for l in log.splitlines() if 'error:' in l]}
(dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in sorted(OUT.glob('*/receipt.json'))]
(OUT/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']},indent=2))
sys.exit(result.returncode)
