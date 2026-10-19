from pathlib import Path
import hashlib,json,shutil
r=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015');w=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
backend=json.loads((r/'backend-final-manifest.json').read_text())
for p,h in backend['source_sha256'].items():assert sha(r/'backend'/p)==h,p
pins={}
for p in sorted((r/'successful-targets').glob('*.json')):
 d=json.loads(p.read_text());assert d['exit_status']==0
 src=r/'backend'/(d['target'].replace('.','/')+'.lean');obj=r/'backend/.lake/build/lib/lean'/(d['target'].replace('.','/')+'.olean')
 assert sha(src)==d['key']['source'],src
 assert sha(obj)==d['olean_sha256'],obj
 pins[d['target']]={'source_path':str(src),'source_sha256':sha(src),'object_path':str(obj),'object_sha256':sha(obj),'green_receipt_path':str(p),'green_receipt_sha256':sha(p)}
assert len(pins)==237,len(pins)
(w/'backend-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for f in ['backend-final-manifest.json','dependency-cache-pins.json']:shutil.copy2(r/f,w/f)
m={'production_revision':'b38b1ce770f91a86315a3de1f750fbe993389569','source_sha256':'4ce97b7bc11b495dc8af3ef79f29dbbd9ebba7c2427a6db1acb8851759b1d305','generated_origin':'extraction/prefix-e-exact','backend_source_manifest_sha256':sha(w/'backend-final-manifest.json'),'backend_object_pins_sha256':sha(w/'backend-object-pins.json'),'dependency_cache_pins_sha256':sha(w/'dependency-cache-pins.json'),'new_sources':{str(p.relative_to(w/'sources')):sha(p) for p in sorted((w/'sources').rglob('*.lean'))},'new_import_objects':{},'boundary':'Exact generated source; no dependency rebuild; Rust refinement and complete Prefix bridge remain OPEN'}
(w/'input-manifest.json').write_text(json.dumps(m,indent=2)+'\n');shutil.copy2(w/'input-manifest.json',w/'input-manifest-types-a.json')
print('Verified237 backend source/object/green receipt inputs; staged Types/Funs/15-target audit')
