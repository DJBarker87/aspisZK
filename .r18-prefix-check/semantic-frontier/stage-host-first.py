from pathlib import Path
import json,hashlib,shutil
base=Path('/home/dombarker/project-offloads');front=base/'aspis-r1-r18-prefix-20261016/semantic-frontier';work=base/'aspis-r1-r18-prefix-20261016/lean-bridge';rank=base/'aspis-r1-r18-sampler-rank-final-20261016'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((front/'full-inventory.json').read_text());mods=d['modules'];assert len(mods)==46 and not d['direct_import_object_mismatches']
snap=json.loads((rank/'external-inputs-rank-final.json').read_text());external={}
for n,x in mods.items():
 assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['object']))==x['object_sha256']
 if 'receipt' in x:assert sha(Path(x['receipt']))==x['receipt_sha256']
 for dep,h in x['direct_import_objects'].items():
  if dep in mods:assert mods[dep]['object_sha256']==h
  else:
   p=Path(snap['modules'][dep]['objects']['.olean']['path']);assert sha(p)==h,(n,dep)
   external[dep]={'object':str(p),'object_sha256':h}
 for p,expected in [(work/'sources'/(n.replace('.','/')+'.lean'),x['source_sha256']),(work/'objects'/(n.replace('.','/')+'.olean'),x['object_sha256'])]:assert not p.exists() or sha(p)==expected,(n,str(p))
for n,x in mods.items():
 for src,dest in [(Path(x['source']),work/'sources'/(n.replace('.','/')+'.lean')),(Path(x['object']),work/'objects'/(n.replace('.','/')+'.olean'))]:
  dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
 prov=front/'provenance';p=prov/'sources'/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(x['source'],p)
 if 'receipt' in x:
  p=prov/'receipts'/(n+'.json');p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(x['receipt'],p)
for x in json.loads((front/'target-source-pins.json').read_text()):
 p=front/'sources'/(x['module'].replace('.','/')+'.lean');assert sha(p)==x['source_sha256'];dst=work/'sources'/p.relative_to(front/'sources');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
n='R0C.ModuloField';src=rank/'sources/R0C/ModuloField.lean';r=json.loads((rank/'successful-targets'/(n+'.json')).read_text());assert sha(src)==r['key']['source_sha256']=='2c0f918c9eb6ac2ab93e07f955d3a5423a968dcefa01fcde58b31feb19d86594'
dst=work/'sources/R0C/ModuloField.lean';dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
report={'module_count':46,'inventory_sha256':sha(front/'full-inventory.json'),'current_source_pins_sha256':sha(front/'full-current-source-pins.json'),'direct_import_object_mismatches':[],'external_direct_imports':external,'target_source_pins_sha256':sha(front/'target-source-pins.json'),'additional_recheck':{'module':n,'source_sha256':sha(src),'reason':'Use current144 Circle object in coherent framing/semantic overlay; preserve old rank receipt and object.'},'objects_copied_to_private_overlay':True,'dependency_rebuild':False}
(front/'staging-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
p=work/'input-manifest.json';m=json.loads(p.read_text());m['current_semantic_cache']={'inventory_sha256':sha(front/'full-inventory.json'),'staging_receipt_sha256':sha(front/'staging-receipt.json'),'reused_modules':46,'direct_import_object_mismatches':0,'fresh_targets':d['proposed_missing_targets']};p.write_text(json.dumps(m,indent=2)+'\n')
print('PASS:46 exact sources/objects and all direct import hashes verified; private staging only; no compile')
