#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=next(x for x in D.parents if (x/'.git').exists())
sha=lambda b:hashlib.sha256(b).hexdigest()
p=json.loads((D/'extraction-input/source-pins.json').read_text())
for f,h in p['kit_files'].items():assert sha((D/'extraction-input'/f).read_bytes())==h,f
tr=p['candidate_transform'];t=(D/'extraction-input/lib.rs').read_text();assert t.count(tr['after'])==1;original=t.replace(tr['after'],tr['before'])
for c in p['cuts']:
 b=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+c['path']]);frag=(D/'extraction-input/fragments'/(c['name']+'.rs')).read_bytes()
 assert sha(b)==c['source_file_sha256'] and b[c['start_byte']:c['end_byte_exclusive']]==frag and sha(frag)==c['sha256']
 assert original.count(frag.decode())==1,c['name']
raw=D/'diagnostics/raw-generated/AspisR1CurrentPreparedClaim'
types=(raw/'Types.lean').read_text().split('namespace AspisR1CurrentPreparedClaim\n')[1].rsplit('end AspisR1CurrentPreparedClaim',1)[0]
m=(D/'sources/CurrentClaimSumModel.lean').read_text();assert m.count(types)==1
f=(raw/'Funs.lean').read_text();chunk=f[f.index('@[global_simps, irreducible]'):f.index('/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::')];pivot=chunk.index('/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_sum]: loop body')
assert m.count(chunk[:pivot])==1 and m.count(chunk[pivot:])==1
for s in (D/'sources').glob('*.lean'):
 txt=s.read_text();assert 'sorry' not in txt and 'axiom ' not in txt and 'maxHeartbeats' not in txt and 'maxRecDepth' not in txt
q=json.loads((D/'measurements/gates/result.json').read_text());assert q['artifact_sha256']=='57d240de8cf88dc4428d1ca65bbd6fb9a5f8bad8df14660caa20994a4df20eef';assert q['strict_stack_receipt']['exit_status']==0
x=json.loads((D/'prereg-fixture-comparison.json').read_text());assert len(q['six_fixture_rows'])==len(x['rows'])==6
for a,b in zip(x['rows'],q['six_fixture_rows']):
 assert a['name']==b['name'] and a['candidate_stage1_cu']==b['candidate_stage1_cu'] and a['candidate_settlement_cu']==b['candidate_settlement_cu']
 assert a['candidate_stage1_cu']<=a['stage1_allowance'] and a['candidate_settlement_cu']<=a['settlement_allowance']
 assert b['receipt']['exit_status']==0 and b['return_data_same'] and b['stage1_checkpoint_tail_same']
for f in D.rglob('*'):
 if f.is_file():assert f.suffix not in ['.olean','.ilean','.ir','.llbc','.so','.elf','.bin'],str(f)
print(json.dumps({'status':'PASS','exact_frozen_source_cuts':len(p['cuts']),'model':'exact raw types/constants/trace/three weighted-sum definitions; concrete source arithmetic instance','runtime':'combined candidate six-fixture output agreement/strict-stack/prereg-item1 PASS','scope':'only final weighted sum PROVED; full cached claim and source/runtime/soundness OPEN'},indent=2))
