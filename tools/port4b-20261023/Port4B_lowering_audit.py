#!/usr/bin/env python3
"""Pin reused local P6 source cuts without claiming a new native extraction."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2]
P=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021'
cuts=json.loads((P/'source-cuts.json').read_text())
names={'batch_keys','sort_batch_keys','batch_leaf','same_batch_leaf','same_batch_index','batch_key_at',
       'node_count','verify_in_place','binary_parent','occupied_binary_parent','sibling_binary_parent','well_formed'}
def extract(s,marker):
 a=s.index(marker);b=s.index('{',a)+1;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
rows=[]
for item in cuts['exact_items']:
 name=item['marker'].split('fn ',1)[-1].split('(')[0].split('<')[0]
 if name not in names:continue
 current=extract((R/item['path']).read_text(),item['marker'])
 assert current==item['body'],(name,'source changed; historical cut cannot be silently reused')
 assert hashlib.sha256(current.encode()).hexdigest()==item['sha256']
 rows.append({'name':name,'path':item['path'],'sha256':item['sha256'],'bytes':len(current.encode()),'identical_to_pinned_local_cut':True})
assert {'batch_keys','sort_batch_keys','batch_leaf'}<={r['name'] for r in rows}
live=json.loads((P/'audit-live-result.json').read_text())
def find(v):
 if isinstance(v,dict):
  if v.get('attempt')=='cone4-keys-1':return v
  for x in v.values():
   y=find(x)
   if y:return y
 elif isinstance(v,list):
  for x in v:
   y=find(x)
   if y:return y
key=find(live);assert key and key['exit_status']==0
out={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'local_source_cuts':rows,'inherited_key_receipt':key,
 'key_receipt_container_sha256':hashlib.sha256((P/'audit-live-result.json').read_bytes()).hexdigest(),
 'new_kani_runs':0,'source_adoption':'Existing named P6 local source/control/library lowering remains explicit; no new extraction or whole native/ELF agreement is asserted. Owned KeyInstall is only the canonical reached class. Source/Kani-to-Lean adoption is external P6, not a new kernel axiom.',
 'remaining':'Instantiation of S1 PreparedBinding on the actual prepare/resume returns, caller parser/model provenance and any non-P6 native source/runtime/artifact adoption remain separate.'}
(R/'evidence/port4b-20261023/lowering-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'identical_local_cuts':len(rows),'inherited_key_gate':key['attempt'],'new_kani_runs':0}))
