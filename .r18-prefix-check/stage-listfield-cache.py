from pathlib import Path
import hashlib,json,shutil
old=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')
new=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m='R1ListFieldCodec';rp=old/'successful-targets'/(m+'.json');r=json.loads(rp.read_text());src=old/'sources'/(m+'.lean');obj=old/'objects'/(m+'.olean')
assert r['exit_status']==0 and sha(src)==r['key']['source_sha256']=='c30eeb96043b627a2fb240777bae9f31b7b4a01e86f1ccd129acf415877f7b7a'
assert sha(obj)==r['objects']['.olean']['sha256']
for p,d in [(src,new/'sources'/src.name),(obj,new/'objects'/obj.name),(rp,new/'list-field-cache-provenance'/rp.name),(src,new/'list-field-cache-provenance'/src.name)]:
 assert not d.exists() or sha(p)==sha(d)
 d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
(new/'list-field-cache-provenance/inventory.json').write_text(json.dumps({'module':m,'source_sha256':sha(src),'object_sha256':sha(obj),'receipt_sha256':sha(rp)},indent=2)+'\n')
print('PASS: existing ListFieldCodec successful source/object receipt; no rebuild')
