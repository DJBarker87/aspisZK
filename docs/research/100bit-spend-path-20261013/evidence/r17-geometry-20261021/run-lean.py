#!/usr/bin/env python3
"""Focused local proof packets. Never rebuild dependencies or shared objects."""
import hashlib, json, os, pathlib, re, subprocess, sys, time
root=pathlib.Path(__file__).resolve().parents[2]
repo=pathlib.Path.cwd()
out=root/'evidence/r17-geometry-20261021'
objects=pathlib.Path('/tmp/cx-r17-geometry-20261021-objects'); objects.mkdir(exist_ok=True)
base=json.loads((root/'evidence/extractor-cost-composed-20261019/RawExtractorCostComposedV2/command.json').read_text())
lean=base['command'][2]
headline=json.loads((root/'evidence/headline-20261021/R1FinalSoundnessHeadline-2/command.json').read_text())
path=str(objects)+':/tmp/cx-geometry-20261020-objects:'+headline['lean_path']
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
module=sys.argv[1]; source=root/'lean'/f'{module}.lean'
sha=hashlib.sha256(source.read_bytes()).hexdigest()
packet=out/module/sha[:12]; packet.mkdir(parents=True,exist_ok=True)
if (packet/'receipt.json').exists(): raise SystemExit('unchanged attempt already receipted')
while True:
 try: lock.mkdir(); break
 except FileExistsError: time.sleep(15)
try:
 while True:
  ps=subprocess.check_output(['ps','-axo','comm=,args='],text=True)
  if not any(l.split()[0].endswith('/lean') and '-M4400' in l for l in ps.splitlines() if l.split()): break
  time.sleep(60)
 cmd=['/usr/bin/time','-l',lean,'-j1','-M4400','-DElab.async=false','-o',str(objects/f'{module}.olean'),str(source)]
 revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
 deps=[]
 for name in re.findall(r'^import ([A-Za-z0-9_.]+)',source.read_text(),re.M):
  relative=name.replace('.', '/')+'.olean'
  found=next((pathlib.Path(d)/relative for d in path.split(':') if (pathlib.Path(d)/relative).exists()),None)
  if found is None: raise RuntimeError('unresolved dependency '+name)
  deps.append({'module':name,'path':str(found),'sha256':hashlib.sha256(found.read_bytes()).hexdigest()})
 fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
 command={'deps_fingerprint':fingerprint,'direct_dependencies':deps,'module':module,'command':cmd,'lean_path':path,'source_revision':revision,'source_sha256':sha,'lock':str(lock),'cwd':str(repo),'executed':True}
 (packet/'source.lean').write_bytes(source.read_bytes())
 (packet/'command.json').write_text(json.dumps(command,indent=2)+'\n')
 start=time.monotonic()
 with (packet/'output.log').open('w') as stdout, (packet/'time.log').open('w') as stderr:
  result=subprocess.run(cmd,env={**os.environ,'LEAN_PATH':path},stdout=stdout,stderr=stderr)
 wall=time.monotonic()-start
 output=(packet/'output.log').read_text(); timing=(packet/'time.log').read_text()
 rss=re.search(r'(\d+)\s+maximum resident set size',timing)
 swaps=re.search(r'(\d+)\s+swaps',timing)
 receipt={**command,'schema':'focused-extractor-proof-packet-v1','exit':result.returncode,'wall_seconds':wall,'peak_rss_bytes':int(rss[1]) if rss else None,'swaps':int(swaps[1]) if swaps else None,'axioms':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",output,re.S), 'full_output':output.splitlines(),'errors': [l for l in output.splitlines() if 'error:' in l]}
 (packet/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 manifest=out/'manifest.json'
 old=json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
 old['attempts'].append(receipt); manifest.write_text(json.dumps(old,indent=2)+'\n')
 print(json.dumps({'module':module,'exit':result.returncode,'wall':wall,'rss':receipt['peak_rss_bytes'],'packet':str(packet)}));print(output)
finally:
 try: lock.rmdir()
 except FileNotFoundError: print('Shared lock disappeared during compile; no other lock removed.')
