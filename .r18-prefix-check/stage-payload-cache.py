from pathlib import Path
import hashlib,json,shutil
old=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')
new=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['AspisR1RowShape.Types','AspisR1RowShape.Funs','ExtractedRowShape','ExtractedRecordFraming','ExtractedRecordHighZero','ExtractedRecordValidator','RecordPayloadPartition','ExtractedRecordPayloadSoundness']
rows=[];copies=[]
for module in modules:
 receipt=old/'successful-targets'/(module+'.json');r=json.loads(receipt.read_text())
 src=old/'sources'/(module.replace('.','/')+'.lean');obj=old/'objects'/(module.replace('.','/')+'.olean')
 assert r['exit_status']==0
 assert sha(src)==r['key']['source_sha256']
 assert sha(obj)==r['objects']['.olean']['sha256']
 for folder,p in [('sources',src),('objects',obj)]:
  dest=new/folder/p.relative_to(old/folder)
  assert not dest.exists() or sha(dest)==sha(p),str(dest)
  copies.append((p,dest))
 copies.append((receipt,new/'payload-cache-provenance'/receipt.name))
 rows.append({'module':module,'source_path':str(src),'source_sha256':sha(src),'object_path':str(obj),'object_sha256':sha(obj),'receipt_sha256':sha(receipt),'current_source':r['source_manifest_entry']['source']})
for src,dest in copies:
 dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
(new/'payload-cache-provenance'/'inventory.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
