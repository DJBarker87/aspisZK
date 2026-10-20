#!/usr/bin/env python3
"""Focused, locked, cached Lean checks; never rebuild dependencies."""
import hashlib,json,os,pathlib,re,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[5]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
HERE=pathlib.Path(__file__).resolve().parent
OBJ=pathlib.Path('/tmp/codex-cx-c3-skeleton-20261020-objects'); OBJ.mkdir(exist_ok=True)
LOCK=pathlib.Path('/tmp/aspis-local-lean.lock.d')
sha=lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
j=json.loads((BASE/'evidence/qv-stage2-20261020/manifest.json').read_text())
paths=[str(OBJ),'/tmp/cx-m10-extractor-cost-resume-20261020-objects','/tmp/codex-cx-decoder-inst-20261020-objects','/tmp/codex-cx-hchecks-20261020-objects','/tmp/cx-queryscan-20261020-objects']+j['attempts'][-1]['lean_path'].split(':')
decoder=json.loads((BASE/'evidence/decoder-instance-20261020/manifest.json').read_text())
paths=paths[:5]+decoder['attempts'][-1]['env']['LEAN_PATH'].split(':')+paths[5:]
cost=json.loads((BASE/'evidence/extractor-cost-composed-20261019/RawExtractorCostComposedV2/receipt.json').read_text())
paths+=cost['lean_path'].split(':')
paths=list(dict.fromkeys(paths)); env=dict(os.environ,LEAN_PATH=':'.join(paths))
module=sys.argv[1]; source=BASE/'lean'/f'{module}.lean'
manifest=HERE/'manifest.json'
m=json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
imports=[]
for dep in re.findall(r'^import (\S+)',source.read_text(),re.M):
 rel=dep.replace('.','/')+'.olean'
 found=next((pathlib.Path(p)/rel for p in paths if (pathlib.Path(p)/rel).exists()),None)
 if found is None: raise SystemExit('missing cached import '+dep)
 imports.append({'module':dep,'path':str(found),'sha256':sha(found)})
fp=hashlib.sha256(json.dumps({'imports':imports,'lean_path':paths},sort_keys=True).encode()).hexdigest(); ss=sha(source)
if any(a['module']==module and a['source_sha256']==ss and a['deps_fingerprint']==fp for a in m['attempts']): raise SystemExit('unchanged attempt refused')
while True:
 try: LOCK.mkdir(); break
 except FileExistsError:
  print('Waiting for shared Lean lock',flush=True); time.sleep(15)
try:
 while subprocess.run(['pgrep','-f','^/Users/dominic/.elan/toolchains/.*/bin/lean .*\\-M4400'],stdout=subprocess.DEVNULL).returncode==0:
  print('Waiting for active capped Lean process',flush=True);time.sleep(60)
 n=sum(a['module']==module for a in m['attempts'])+1
 out=HERE/f'{module}-{n}'; out.mkdir()
 argv=['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-DElab.async=false','-R',str(BASE/'lean'),'-o',str(OBJ/f'{module}.olean'),str(source)]
 start=time.monotonic()
 with open(out/'lean.log','w') as stdout,open(out/'time.log','w') as stderr:
  result=subprocess.run(['/usr/bin/time','-l']+argv,env=env,cwd=ROOT,stdout=stdout,stderr=stderr)
 wall=time.monotonic()-start; log=(out/'lean.log').read_text(); timing=(out/'time.log').read_text()
 def metric(p):
  x=re.search(p,timing);return int(x.group(1)) if x else None
 a={'module':module,'attempt':n,'argv':argv,'lean_path':env['LEAN_PATH'],'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'source_sha256':ss,'direct_imports':imports,'deps_fingerprint':fp,'exit':result.returncode,'wall_seconds':wall,'peak_rss_bytes':metric(r'(\d+)\s+maximum resident set size'),'swaps':metric(r'(\d+)\s+swaps'),'axioms':[l for l in log.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],'log':str((out/'lean.log').relative_to(ROOT)),'time':str((out/'time.log').relative_to(ROOT))}
 (out/'command.json').write_text(json.dumps(a,indent=2)+'\n');m['attempts'].append(a);manifest.write_text(json.dumps(m,indent=2)+'\n')
 print(json.dumps({k:a[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps']}));print(log)
 raise SystemExit(result.returncode)
finally: LOCK.rmdir()
