#!/usr/bin/env python3
"""Read-only original-object inventory; no Lean or compiler execution."""
import pathlib,json,hashlib
B=pathlib.Path(__file__).resolve().parent
x=json.loads((B/'origin-input.json').read_text());rows=[]
for n in x['modules']:
 key=n.replace('.','/')+'.olean'
 p=next((pathlib.Path(d)/key for d in x['root_lean_path'].split(':') if (pathlib.Path(d)/key).is_file()),None)
 assert p is not None,n
 fs=[]
 for q in [p,pathlib.Path(str(p)+'.server'),pathlib.Path(str(p)+'.private'),p.with_suffix('.ir')]:
  if q.is_file():
   b=q.read_bytes();fs.append({'path':str(q),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
 rows.append({'module':n,'files':fs})
lean=pathlib.Path(x['lean_binary']);data=lean.read_bytes()
result={'root_proof_basis':x['root_proof_basis'],'snapshot_receipt':x['snapshot_receipt'],'assessment':'Original object hash inventory after snapshot capture; NOT promoted to a historical before/go pin. Snapshot bytes used for kernel checking are separately pinned before each replay.','objects':rows,'lean_binary_sha256_now':hashlib.sha256(data).hexdigest(),'lean_binary_pin_reused':x['lean_binary_pin_reused']}
assert result['lean_binary_sha256_now']==result['lean_binary_pin_reused']
(B/'original-root-objects.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(rows),'files':sum(len(r['files']) for r in rows),'all_tool_hashes_match':True}))
