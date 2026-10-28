from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path('evidence/pv-fscan-20261028')
dirs=['pv-cb-20261026','pv-cb3-20261026','pv-cb9-20261027','pv-cbmid-20261027','pv-cblib-20261027','pv-alib-20261027','pv-batch1-20261027','pv-batch2-20261027','pv-batch3-20261027','pv-op223-20261027','pv-dlib-20261028','pv-b3p6-20261028','pv-fxmem-20261028','pv-relink-20261028','pv-kstub-20261028','pv-op254-20261027','pv-d188-20261027','pv-kscan-20261028']
rows=json.loads(lzma.decompress((E/'rows7.json.xz').read_bytes()));selected=[r for r in rows if r['recount7_status']=='CLOSED-ON-CANDIDATE' or r['id'] in ['V229','V187','V201','V231','V234','V235','V236','V237','V238','V170','V183','V221','V222']]
items=[]
def walk(v,pointer=''):
 if isinstance(v,dict):
  for k,x in v.items():
   if k in ['target','command','argv','cmd'] and isinstance(x,(list,str)):
    s=' '.join(map(str,x)) if isinstance(x,list) else x
    if re.search(r'cargo|rustc|charon|aeneas|native|structural|binding|differential',s,re.I) and not re.search(r'run-joint|lake env lean',s):yield pointer+'/'+k,s
   elif isinstance(x,(dict,list)):yield from walk(x,pointer+'/'+k)
 elif isinstance(v,list):
  for i,x in enumerate(v):yield from walk(x,pointer+'/'+str(i))
for d in dirs:
 for p in sorted((Path('evidence')/d).rglob('*.json')):
  if p.stat().st_size>20000000:continue
  try:a=json.loads(p.read_text())
  except Exception:continue
  for pointer,cmd in walk(a):
   # Exclude formal target commands even if a wrapper directory mentions native.
   if re.search(r'\b(?:lean|lean-runner|lean4)\b',cmd) and not re.search(r'cargo|rustc|charon|aeneas',cmd):continue
   fs=re.findall(r'--features(?:=|\s+)([^\s]+)',cmd)
   env={k:v for k,v in (a.get('env',{}) if isinstance(a,dict) else {}).items() if k.startswith(('CARGO_PROFILE','RUST'))}
   profile='release' if '--release' in cmd else ('dev' if re.search(r'cargo\s+(?:kani|test|build|rustc|check)',cmd) else 'unrecorded / inspect wrapper')
   items.append(dict(path=str(p),pointer=pointer,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),command=cmd,explicit_features=fs,profile=profile,recorded_env=env,recorded_profile=a.get('profile') if isinstance(a,dict) else None,configuration_status='resolved features absent from historical receipt unless supplied by linked manifest; no parity inferred',exit=a.get('exit',a.get('exit_status')) if isinstance(a,dict) else None))
bindings=[]
for d in dirs:
 for p in sorted((Path('evidence')/d).rglob('*')):
  if p.is_file() and p.suffix in ['.json','.py','.sh','.toml'] and re.search('binding|Cargo.toml|structur|source-manifest|source-pins',p.name,re.I):bindings.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size))
(E/'native-evidence-index.json').write_text(json.dumps(dict(scope='Conservative superset: all retained native command receipts in closure-owning lanes, including failed/supporting runs; not every run earns row credit',lanes=dirs,items=items,bindings=bindings),indent=2)+'\n')
(E/'selected-rows.json').write_text(json.dumps([dict(id=r['id'],name=r['name'],prior_status=r['recount7_status'],theorem=r.get('closure_theorem'),prior_basis=r['recount7_basis'],evidence=r['recount7_evidence'],definition_witnesses=r.get('definition_witnesses7'),prior_route=r.get('recount6_closure_route')) for r in selected],indent=2)+'\n')
print(len(selected),'rows',len(items),'commands',len(bindings),'bindings/manifests')
