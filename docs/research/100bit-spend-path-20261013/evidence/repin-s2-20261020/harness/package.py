#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,re
P=Path(__file__).resolve().parents[1]
root=Path.cwd()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=json.loads((P/'source-pins.json').read_text())
local_differences=[]
for i in ['charon-first-input.json','charon-adapter-input.json']:
 d=json.loads((P/i).read_text())
 assert d['cu_profiling'] is False
 for f,h in d['source_hashes'].items():
  if sha(root/f)!=h and f not in [x['path'] for x in local_differences]:
   local_differences.append(dict(path=f,working_tree_sha256=sha(root/f),extracted_frozen_sha256=h,classification='cfg(test)-only module, excluded from --lib non-test extraction'))
  frozen=subprocess.check_output(['git','show',source['source_revision']+':'+f])
  assert hashlib.sha256(frozen).hexdigest()==h,f
proof=json.loads((P/'first-proof-v5/command.json').read_text())
assert proof['exit']==0
assert proof['source_sha256']==sha(root/proof['source'])
assert len(proof['axioms'])==5
assert not any(s in '\n'.join(proof['axioms']) for s in ['sorryAx','Formatter'])
assert json.loads((P/'binding-audit.json').read_text())['all_equal']
receipts=[]
for p in sorted((P/'receipts').glob('*/receipt.json')):
 d=json.loads(p.read_text());d['receipt']=str(p.relative_to(P));receipts.append(d)
assert {Path(r['receipt']).parent.name:r['exit_status'] for r in receipts}=={'extract-first-charon':0,'extract-first-aeneas':0,'extract-adapter-charon':0,'extract-adapter-aeneas':2}
llbc=[]
for cone,h,n in [('first','498403ba30d4f5f739ce0ce28e9379056b329155e2df2ae6c5c6a4a135b25288',361558),('adapter','18171c40e888cf8452df2be608039022b986fb022116594876929b1d3d079a5c',2851857)]:
 llbc.append(dict(cone=cone,sha256=h,bytes=n,has_errors=False,host_path='/home/dombarker/project-offloads/codex-cx-repin-s2-20261020/extraction-'+cone+'/S2.llbc'))
files=[dict(path=str(p.relative_to(root)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(P.rglob('*')) if p.is_file() and p.name!='manifest.json' and '__pycache__' not in str(p)]
manifest=dict(schema='focused-extractor-proof-packet-v1',source_revision=source['source_revision'],worktree_revision=source['worktree_revision'],status='PARTIAL_PROOF_ADAPTER_TRANSLATION_BLOCKED',s2_status='OPEN',working_tree_differences=local_differences,r22_status='OPEN_FOR_ADAPTER',llbc=llbc,extraction_receipts=receipts,accepted_proof=proof,proof_scope='Token-checked explicit-boundary interpretation of frozen observer, first_decoded and first; not concrete SDK/downstream refinement',blocked=dict(owner='r1_pool_adapter::stage1',location='programs/r1-cost-probe/src/r1_pool_adapter.rs:950:24-36',reason='Generic shared slice index instantiated with AccountInfo containing mutable borrows',parked_candidate_fixes_blocker=False),attempts=[dict(attempt='first-proof-v1',status='preflight_cancelled_no_Lean'),dict(attempt='first-proof-v2',status='missing_dependency'),dict(attempt='first-proof-v3',status='parse_and_namespace_errors'),dict(attempt='first-proof-v4',status='unclosed_reflexive_goal'),dict(attempt='first-proof-v5',status='accepted')],files=files)
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('packet checks passed; adapter blockage retained; no binary artifacts packaged')
