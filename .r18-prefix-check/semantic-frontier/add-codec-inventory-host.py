from pathlib import Path
import json,hashlib
base=Path('/home/dombarker/project-offloads');w=base/'aspis-r1-r18-prefix-20261016/semantic-frontier';r17=base/'aspis-r1-j17-port-20261015/extracted';pref=base/'aspis-r1-r18-prefix-20261016/lean-bridge'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((w/'inventory.json').read_text());selected=d['modules']
for n in ['R1FixedWidthDecoder','R1RetainedFieldByteCodec','R1RetainedExactLimbCodec','R1ListFieldCodec']:
 rp=r17/'successful-targets'/(n+'.json');r=json.loads(rp.read_text());src=r17/'sources'/(n+'.lean');obj=r17/'objects'/(n+'.olean')
 assert r['exit_status']==0 and r['axioms']['passed'] and sha(src)==r['key']['source_sha256'] and sha(obj)==r['objects']['.olean']['sha256']
 deps={k:v['objects']['.olean']['sha256'] for k,v in r['key']['imports'].items()}
 selected[n]={'kind':'R17','source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'receipt':str(rp),'receipt_sha256':sha(rp),'direct_import_objects':deps}
n='R1StrictWideByteCodec';rp=pref/'runs/strict-predecessor-a/receipt.json';r=json.loads(rp.read_text());src=rp.parent/'source.lean';obj=pref/'objects'/(n+'.olean');m=json.loads((pref/'input-manifest-strict-predecessor-a.json').read_text())
assert r['exit_status']==0 and sha(src)==r['source_sha256'] and sha(obj)==r['olean_sha256']
selected[n]={'kind':'A-focused-strict-predecessor','source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'receipt':str(rp),'receipt_sha256':sha(rp),'direct_import_objects':{'R1RetainedFieldByteCodec':m['new_import_objects']['R1RetainedFieldByteCodec.olean']}}
issues=[]
for n,x in selected.items():
 for dep,h in x['direct_import_objects'].items():
  if dep in selected and selected[dep]['object_sha256']!=h:issues.append([n,dep,h,selected[dep]['object_sha256']])
d['direct_import_object_mismatches']=issues
(w/'full-inventory.json').write_text(json.dumps(d,indent=2)+'\n');print('selected',len(selected),'mismatches',issues)
