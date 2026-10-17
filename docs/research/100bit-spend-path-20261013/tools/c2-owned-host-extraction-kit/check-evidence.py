#!/usr/bin/env python3
"""Read/hash-only checkpoint validator; never invokes Lean/Rust/Aeneas."""
from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parents[5];E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-owned-host-20261017'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 audit=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-historical-context-20261017/audit.json'
 assert sha(audit.read_bytes())=='d599abdfd7ca2ebd44a9b24e111596bf13d94b47f089912b6bd4b5de1ee973e8'
 assert json.loads(audit.read_text())['classification']=='HISTORICAL_CONTEXT_ONLY'
 members=json.loads((E/'checkpoint-members.json').read_text());archive=E/'checkpoint.tar.gz'
 with tarfile.open(archive) as tf:
  files={m.name:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
 assert set(files)==set(members)
 for name,b in files.items():assert sha(b)==members[name]['sha256'] and len(b)==members[name]['bytes'],name
 runs={}
 for name,b in files.items():
  if name.endswith('/receipt.json'):
   x=json.loads(b);runs[name]=x
   if 'limits' in x:assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
   assert x['source_revision']=='deb68369ba3ad7cc6706dc24b6503fac1cbe942b'
   assert x.get('process_swaps',0)==0
 f=runs['conditional-lean/runs/construction-f/receipt.json'];assert f['exit_status']==0 and f['external_lean_overlap']==[]
 source=files['conditional-lean/runs/construction-f/source.lean'];assert sha(source)==f['source_sha256']
 assert source==(ROOT/'docs/research/100bit-spend-path-20261013/lean/C2OwnedHostConstruction.lean').read_bytes()
 log=files['conditional-lean/runs/construction-f/lean.log'].decode();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
 assert len(reports)==9 and 'sorryAx' not in log and 'error:' not in log
 allowed={'propext','Classical.choice','Quot.sound'}
 for name,axioms in reports:assert set(x.strip() for x in axioms.split(',') if x.strip())<=allowed,name
 assert sha(files['conditional-lean/objects/C2OwnedHostConstruction.olean'])==f['olean_sha256']
 for prefix in ['actual-caller','actual-build','diagnostic-hash-carrier','diagnostic-unroll2','diagnostic-destructure2']:
  assert runs[prefix+'/runs/charon-a/receipt.json']['exit_status']==0
  assert runs[prefix+'/runs/aeneas-a/receipt.json']['exit_status']==2
  assert not json.loads(files[prefix+'/C2OwnedHost.llbc'])['has_errors']
  p=json.loads(files[prefix+'/input/source-pins.json'])
  for name,h in p['kit_files'].items():assert sha(files[prefix+'/input/'+name])==h,(prefix,name)
  if prefix.startswith('diagnostic'):assert p['classification'].startswith('REJECTED_DIAGNOSTIC')
 print(json.dumps({'status':'PASS','archive_sha256':sha(archive.read_bytes()),'members':len(files),'conditional_formal_results':len(reports),'result_context':'HISTORICAL_CONTEXT_ONLY','current_accepted_semantic_model_results':0,'accepted_actual_caller_or_build_cones':0,'unresolved_actual_source_bridge':True},sort_keys=True))
if __name__=='__main__':main()
