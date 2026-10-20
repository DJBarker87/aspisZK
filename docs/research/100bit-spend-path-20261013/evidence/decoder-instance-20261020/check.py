#!/usr/bin/env python3
"""Focused local checker; private objects, exclusive mkdir lock, retained receipts."""
import hashlib,json,os,pathlib,subprocess,time,sys,re
root=pathlib.Path(__file__).resolve().parents[5]
packet=pathlib.Path(__file__).resolve().parent
leanroot=root/'docs/research/100bit-spend-path-20261013/lean'
obj=pathlib.Path('/tmp/codex-cx-decoder-inst-20261020-objects');obj.mkdir(exist_ok=True)
base=json.loads((root/'docs/research/100bit-spend-path-20261013/evidence/sampler-rows-25-32-20261020/format-v14/command.json').read_text())
env=os.environ.copy();env['LEAN_PATH']=str(obj)+':/tmp/codex-cx-hchecks-20261020-objects:/tmp/cx-qv-stage1-objects:/tmp/codex-cx-bindings-20261020-objects:'+base['env']['LEAN_PATH']
binding=json.loads((root/'docs/research/100bit-spend-path-20261013/evidence/transfer-bindings-20261020/ExtractedAdapterStageBindingObligations-585a0f64c88e/command.json').read_text())
env['LEAN_PATH']+=':'+binding['environment']['LEAN_PATH']
module,attempt=sys.argv[1:];dest=packet/attempt;dest.mkdir()
source=leanroot/(module+'.lean');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
args=[base['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(leanroot),'-o',str(obj/(module+'.olean')),str(source)]
imports=[]
for line in source.read_text().splitlines():
 if line.startswith('import '):
  name=line.split()[1]; found=next((pathlib.Path(p)/(name.replace('.','/')+'.olean') for p in env['LEAN_PATH'].split(':') if (pathlib.Path(p)/(name.replace('.','/')+'.olean')).exists()),None)
  imports.append({'module':name,'path':str(found),'sha256':sha(found) if found else None})
(dest/'source.lean').write_text(source.read_text())
command={'argv':args,'env':{'LEAN_PATH':env['LEAN_PATH']},'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_sha256':sha(source),'imports':imports}
command['deps_fingerprint']=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
for previous in packet.glob('*/receipt.json'):
 old=json.loads(previous.read_text())
 if old.get('module')==module and old.get('source_sha256')==command['source_sha256'] and old.get('deps_fingerprint')==command['deps_fingerprint']:
  raise SystemExit('refusing unchanged source + direct dependencies')
(dest/'command.json').write_text(json.dumps(command,indent=2)+'\n')
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
 try:lock.mkdir();break
 except FileExistsError:time.sleep(15)
try:
 while any(line.split(None,1)[-1].split('/')[-1].split()[0]=='lean' for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines() if line.strip()):time.sleep(60)
 start=time.monotonic()
 with (dest/'output.log').open('w') as out,(dest/'time.log').open('w') as timing:
  result=subprocess.run(['/usr/bin/time','-l']+args,env=env,cwd=root,stdout=out,stderr=timing)
 wall=time.monotonic()-start
finally:
 try:lock.rmdir()
 except OSError as err:(dest/'lock-cleanup.txt').write_text(str(err)+'\n')
raw=(dest/'output.log').read_text();tm=(dest/'time.log').read_text()
receipt=dict(command,module=module,attempt=attempt,exit=result.returncode,wall_seconds=wall,peak_rss_bytes=next((int(x.split()[0]) for x in tm.splitlines() if 'maximum resident set size' in x),None),swaps=next((int(x.split()[0]) for x in tm.splitlines() if x.strip().endswith('swaps')),None),axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[.*?\]|does not depend on any axioms)",raw,re.S))
(dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
manifest={'schema':'focused-extractor-proof-packet-v1','attempts':[json.loads(p.read_text()) for p in sorted(packet.glob('*/receipt.json'))]}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['module','exit','wall_seconds','peak_rss_bytes','swaps','axioms']}));print(raw);print(tm if result.returncode else '')
sys.exit(result.returncode)
