"""Pin the selected runtime closure and retain a small owned proof export."""
from pathlib import Path
import json,hashlib,lzma,os,shutil,sys
B=Path.cwd();cfg=json.loads((B/sys.argv[1]).read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(4<<20),b''):h.update(chunk)
 return h.hexdigest()
roots=os.environ['LEAN_PATH'].split(':')
rows=[json.loads(line) for line in (B/'NLL_LOADED_scan.jsonl').read_text().splitlines()]
assert rows and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows)
pins={}
for row in rows:
 rel=row['module'].replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins[str(q)]={'sha256':sha(q),'bytes':q.stat().st_size}
raw=(json.dumps({'runtime_LEAN_PATH':os.environ['LEAN_PATH'],'selected':pins},sort_keys=True)+'\n').encode()
(B/'NLL_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6))
(B/'NLL_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
before=json.loads((B/'NLL_L072/receipt.json').read_text())
audit=json.loads((B/'NLL_L073/receipt.json').read_text())
assert before['env']['LEAN_PATH']==audit['env']['LEAN_PATH']==os.environ['LEAN_PATH']
library={}
for path,pin in before['deps_fingerprint']['selected_objects'].items():
 if '/Aeneas/' in path or '/AeneasMeta/' in path or Path(path).name in ['Aeneas.olean','AeneasMeta.olean']:
  assert sha(Path(path))==pin['sha256'],path
  assert path in pins and pins[path]['sha256']==pin['sha256'],path
  library[path]=pin
assert library
(B/'NLL_LIBRARY_CONTINUITY.json').write_text(json.dumps({'before':'NLL_L072','audit':'NLL_L073','same_LEAN_PATH':True,'all_library_hashes_unchanged':True,'pins':library},indent=2)+'\n')
export=B/'NLL_exports_final_20261110';assert not export.exists();export.mkdir()
modules=list(json.loads((B/'NLL_PROOF_SET.json').read_text()))+['NLL_COMBINED_IMPORT']
files={}
for module in modules:
 p=B/'NLL_objects'/(module+'.olean');assert p.is_file(),str(p)
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():
   target=export/q.name;shutil.copy2(q,target)
   digest=sha(q);assert digest==sha(target)
   files[q.name]={'sha256':digest,'bytes':q.stat().st_size,'source':str(q)}
# Recheck seeded exports without changing any cache.
for name,group in json.loads((B/'NLL_SEED.json').read_text()).items():
 for rel,pin in group['files'].items():assert sha(B/'NLL_seed'/name/rel)==pin['sha256']
for rel,pin in json.loads((B/'NLL_NKE_SEED.json').read_text())['files'].items():assert sha(B/'NLL_seed/NKE'/rel)==pin['sha256']
workspace=int(__import__('subprocess').check_output(['du','-sb',str(B)],text=True).split()[0]);assert workspace<30000000000
manifest={'export':str(export),'module_count':len(modules),'files':files,'bytes':sum(x['bytes'] for x in files.values()),'source_revision':cfg['source_revision'],'runtime_closure_objects':len(pins),'runtime_closure_modules':len(rows),'Aeneas_objects':len(library),'free_bytes':shutil.disk_usage(B).free,'own_workspace_bytes':workspace,'retained_cargo_target':os.environ['CARGO_TARGET_DIR'],'deleted':0,'proof_set_sha256':sha(B/'NLL_PROOF_SET.json')}
(B/'NLL_EXPORT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k not in ['files','retained_cargo_target']}))
