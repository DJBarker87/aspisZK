#!/usr/bin/env python3
"""Source-only driver extraction and TOTAL fixed-model proof audit."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
P=E/'s1-query-pairs-reference-extraction-v1';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((P/'collection.json').read_text())
for p,h in c['files'].items():assert sha(P/p)==h,p
proof=(R/'tools/s1-query-pairs-cut-20261025/proofs.rs').read_text().split('#[kani::proof]')[0]
reference='#![no_std]\nextern crate alloc;\nuse aspis_core::transcript::QuerySampleError;\n'+proof.replace('fn pairs_reference(','pub fn pairs_reference(')
assert reference==(T/'reference.rs').read_text()==(P/'v3/reference/src/lib.rs').read_text()
for tool in ['charon','aeneas']:
 r=json.loads((P/f'v3/run-extract/{tool}-receipt.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged'] and r['tools_unchanged'] and r['swaps']==0
 assert r['cgroup']['memory.max']==str(2*2**30) and r['cgroup']['memory.swap.max']=='0'
 for k in ['high','max','oom','oom_kill']:assert re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)
for old in ['v1','v2']:
 assert json.loads((P/f'{old}/run-extract/aeneas-receipt.json').read_text())['exit_status']!=0
 assert 'Not_found' in (P/f'{old}/run-extract/aeneas-stderr.log').read_text()
# Exact admitted normalization: remove resource options, use existing checked
# concrete callee, and qualify only the new datatype's generated instance name.
for item in json.loads((T/'lean-binding.json').read_text()):
 raw=P/f"v3/generated/AspisS1OwnedQueryPairs/{item['original']}.lean"
 dst=S/(item['checked']+'.lean');text=raw.read_text()
 assert sha(raw)==item['original_sha256'] and sha(dst)==item['checked_sha256']
 text=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',text,flags=re.M)
 if item['original']=='Types':
  text=text.replace('import Aeneas\n','import Aeneas\nimport ImportUnionNamedDiscriminant\n').replace('@[discriminant isize,','@[import_union_discriminant,')
 else:
  text=text.replace('import AspisS1OwnedQueryPairs.Types','import S1OwnedQueryPairsTypesV1').replace('import AspisS1OwnedQueryPairs.FunsExternal','import S1OwnedQueryBlockFunsV1').replace('    owned_block scan.accepted','    AspisS1OwnedQueryBlock.owned_block scan.accepted')
 assert dst.read_text().split('\n#print axioms')[0].rstrip()==text.rstrip(),dst
for name,attempt in [
 ('Types','types-v2'),('Funs','funs-v2'),('StepModel','step-model-v3'),('RunModel','run-model-v1'),
 ('Drive','drive-v5'),('FinishModel','finish-model-v6'),('IndexModel','index-model-v2'),('FixedModel','fixed-model-v1')]:
 f=S/f'S1OwnedQueryPairs{name}V1.lean';r=json.loads((E/f's1-owned-query-pairs-{attempt}/receipt.json').read_text())
 assert r['exit_status']==0 and r['source_sha256']==sha(f) and r['swaps']==0
 assert r['print_axioms'] and all('sorryAx' not in a for a in r['print_axioms'])
 for a in r['print_axioms']:
  if 'depends on axioms:' in a: assert set(re.search(r'\[(.*?)\]',a,re.S)[1].replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',f.read_text()),f
 for n,v in r['direct_imports'].items():
  q=Path(v['path']);assert q.exists() and sha(q)==v['sha256'],n
# Explicit pinned warm R4 theorem reuse; no unchanged replay.
r=json.loads((B/'evidence/r4-transport2-20261021/R4Transport2ScanComposition-2/receipt.json').read_text())
assert r['exit']==0 and sha(B/'lean/R4Transport2ScanComposition.lean')==r['source_sha256']=='5c5850ed20123cbe96a59c08d61d5b9681ffd15df963f1ae3a48b8229fc533dc'
assert sha(Path('/tmp/codex-cx-r4-transport2-20261021-objects/R4Transport2ScanComposition.olean'))==r['object_sha256']=='fe1af6d0ec3f9708e4c7aed48515fde6e5809964cd4662487311a74b514e91cc'
print(json.dumps(dict(status='PASS',extraction_pins=len(c['files']),scope='TOTAL exact owned driver to fixed Q22, accepted/rejected, no scanner/success/model hypotheses. Native relative-cut composition and caller installation remain explicit boundaries.')))
