from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
old=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
a=old/'XRa_bin/aeneas-b59d5188-extended'
p=old/'XRa_release_candidate_tx1.llbc'
assert hashlib.file_digest(a.open('rb'),'sha256').hexdigest()=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()=='0814e4ec3481bef7fcca9a806ff24c868fdaeae3ed127b1e11a73973077510ba'
# Diagnostic derived LLBC only: preserve all declarations/signatures/types;
# replace unrelated function bodies with Opaque. NEVER release extraction.
j=json.loads(p.read_text())
# LLBC uses a global hash-cons table; masking bodies must not orphan keys.
table={}
def collect(x):
 if isinstance(x,dict):
  if list(x)==['HashConsedValue']: table[x['HashConsedValue'][0]]=x['HashConsedValue'][1]
  for v in x.values(): collect(v)
 elif isinstance(x,list):
  for v in x: collect(v)
collect(j)
def expand(x):
 if isinstance(x,dict):
  if list(x)==['Deduplicated']:
   k=x['Deduplicated'];return {'HashConsedValue':[k,expand(table[k])]}
  return {k:expand(v) for k,v in x.items()}
 if isinstance(x,list):return [expand(v) for v in x]
 return x
j=expand(j)
original_types=json.dumps(j['translated']['type_decls'],sort_keys=True)
masked=[]
for f in j['translated']['fun_decls']:
 if f and isinstance(f['body'],dict) and f['def_id'] in [26,27]:
  masked.append({'id':f['def_id'],'name':f['item_meta']['name'],'body_sha256':hashlib.sha256(json.dumps(f['body'],sort_keys=True).encode()).hexdigest()})
  f['body']='Opaque'
assert json.dumps(j['translated']['type_decls'],sort_keys=True)==original_types
p=B/'XRc_two_leaves.llbc';p.write_text(json.dumps(j))
(B/'XRc_001_mask.json').write_text(json.dumps({'status':'INCOMPLETE KIT: required bodies already absent from original LLBC; two leaf boundary feasibility only','masked_body_ids':[26,27],'masked':masked,'derived_llbc_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'type_decls_sha256':hashlib.sha256(original_types.encode()).hexdigest()},indent=2)+'\n')
cmd=[str(a),'-log','Translate','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1PublicPreparation','-dest',str(B/'XRc_two_leaves_generated'),'-subdir','AspisR1PublicPreparation','-split-files','-emit-json',str(p)]
(B/'XRc_two_leaves_command.json').write_text(json.dumps(cmd,indent=2)+'\n')
print('COMMAND',json.dumps(cmd),flush=True)
r=subprocess.run(cmd)
rows=[]
for p in sorted((B/'XRc_two_leaves_generated').rglob('*')):
 if p.is_file(): rows.append({'path':str(p),'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size})
(B/'XRc_two_leaves_outputs.json').write_text(json.dumps({'exit':r.returncode,'outputs':rows},indent=2)+'\n')
print(json.dumps(rows),flush=True)
raise SystemExit(r.returncode)
