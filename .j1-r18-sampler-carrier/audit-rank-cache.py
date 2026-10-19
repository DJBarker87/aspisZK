from pathlib import Path
import hashlib,json
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-carrier-20261016')
p=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015');c=Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016')
closure=json.loads((w/'rank-closure.json').read_text());b=json.loads((p/'bridge/manifest.json').read_text())
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
roots={n:(root,json.loads((root/'sources/SOURCE-MANIFEST.json').read_text())) for n,root in [('r17',p/'extracted'),('c-models',c/'models')]}
rows=[]
for name in closure['topological_order']:
 target=closure['modules'][name];found=[]
 for label,(root,m) in roots.items():
  if name not in m['modules']:continue
  item=m['modules'][name];src=root/'sources'/item['stage_as'];obj=root/'objects'/Path(name.replace('.','/')+'.olean');rp=root/'successful-targets'/(name+'.json')
  if not(obj.exists() and rp.exists()):continue
  r=json.loads(rp.read_text());h=obj.read_bytes()[:79]
  found.append(dict(cache=label,source=str(src),source_sha256=sha(src),source_match=sha(src)==target['sha256'],object=str(obj),object_sha256=sha(obj),version=h[7:39].split(b'\0')[0].decode(),seal=h[7:79].hex(),receipt=str(rp),receipt_sha256=sha(rp),receipt_matches=r['key']['source_sha256']==sha(src) and r['objects']['.olean']['sha256']==sha(obj),exit_status=r['exit_status']))
 if name in b['dependency_pins']:
  item=b['dependency_pins'][name];src=p/'bridge'/item['source_snapshot'];obj=p/'bridge'/item['object_snapshot'];h=obj.read_bytes()[:79]
  found.append(dict(cache='bridge',source=str(src),source_sha256=sha(src),source_match=sha(src)==target['sha256'],object=str(obj),object_sha256=sha(obj),version=h[7:39].split(b'\0')[0].decode(),seal=h[7:79].hex(),manifest=str(p/'bridge/manifest.json'),manifest_sha256=sha(p/'bridge/manifest.json'),manifest_matches=item['source_sha256']==sha(src) and item['object_sha256']==sha(obj),provenance=item))
 rows.append(dict(module=name,canonical_source=target['path'],expected_source_sha256=target['sha256'],caches=found))
(w/'rank-cache-inventory.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:print(row['module'],','.join(x['cache']+':'+x['version']+(':MATCH' if x['source_match'] else ':DIFF') for x in row['caches']) or 'MISSING')
