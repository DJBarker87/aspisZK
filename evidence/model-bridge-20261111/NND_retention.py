"""Final selected-object, source and raw-audit retention check; no proof replay."""
from pathlib import Path
import json,hashlib,sys
B=Path.cwd();a=sys.argv[1]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
pins=json.loads((B/'NND_L019/NND_CLOSURE_PINS.json').read_text())
for n,pin in pins['objects'].items():
 p=Path(n);assert p.is_file() and p.stat().st_size==pin['bytes'] and digest(p)==pin['sha256'],n
current=json.loads((B/'NND_CURRENT_MODULES.json').read_text())
for m,row in current.items():
 p=B/'NND_generated'/(m.replace('.','/')+'.lean');assert digest(p)==row['source_sha256'],m
manifest=json.loads((B/'NND_AUDIT_ROOTS.json').read_text());expected=[n for g in manifest['groups'] for n in g]
found=[];archive_count=0;disagreements=[]
for group in range(len(manifest['groups'])):
 ids=list(range(272,301))+[17,18,19];scope=f'NND_L{ids[group]:03}'
 s=json.loads((B/scope/'NND_RAW_AUDIT.json').read_text());assert s['mode']=='proof'+str(group)
 found.extend(r['root'] for r in s['roots']);disagreements.extend(s['cache_disagreements'])
 for rec in s['archives']:
  p=B/rec['path'];assert digest(p)==rec['archive_sha256'],str(p);archive_count+=1
assert found==expected and len(found)==len(set(found))
result={'status':'PASS','target':'retention of exact selected combined closure, current own sources and all own raw roots','selected_objects':len(pins['objects']),'current_own_modules':len(current),'own_raw_roots':len(found),'compressed_graphs':archive_count,'cache_disagreements':disagreements,'cold_release_replay':False,'candidate_credit':False,'keys_deleted':False}
(B/a/'NND_RETENTION.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cache_disagreements'}))
