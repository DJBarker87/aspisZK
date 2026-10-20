#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
R=next(x for x in D.parents if (x/'.git').exists())
P=R/'docs/research/100bit-spend-path-20261013'
O=P/'lean-candidates/s1-explicit-loop-powers-proved-candidate-20261020'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'extraction-input/source-pins.json').read_text())
for f,h in pins['kit_files'].items():assert sha((D/'extraction-input'/f).read_bytes())==h,f
for c in pins['cuts']:
 b=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+c['path']])
 assert sha(b)==c['file_sha256'] and sha(b[c['start_byte']:c['end_byte_exclusive']])==c['sha256']
t=(D/'extraction-input/lib.rs').read_text();assert t.count(pins['candidate_transform']['after'])==1
z=D/'diagnostics/raw-generated/AspisR1LoopPowers';o=O/'diagnostics/raw-generated/AspisR1LoopPowers'
assert (z/'Types.lean').read_bytes()==(o/'Types.lean').read_bytes()
def block(t,name):
 s=t.index('def '+name);e=t.find('\n/--',s)
 return t[s:e if e!=-1 else t.index('\nend AspisR1LoopPowers',s)].strip()
a=(z/'Funs.lean').read_text();b=(o/'Funs.lean').read_text();m=(D/'sources/LoopPowersZeroCandidate.lean').read_text()
for n in ['weights.powers_loop.body','weights.powers_loop\n']:assert block(a,n)==block(b,n),n
assert '@[global_simps, irreducible]\n'+block(a,'field.WideExact.ZERO') in m
assert block(a,'weights.powers\n').replace('def weights.powers\n','def weights.powers_zero\n',1) in m
assert 'sorry' not in m and 'axiom ' not in m
for x in json.loads((D/'measurement-summary.json').read_text()):
 q=json.loads((D/'measurements'/x['variant']/'gates/result.json').read_text())
 assert q['artifact_sha256']==x['artifact_sha256']
 assert len(q['six_fixture_rows'])==6 and q['strict_stack_receipt']['exit_status']==0
 for row in q['six_fixture_rows']:assert row['stage1_checkpoint_tail_same'] and row['return_data_same'] and row['receipt']['exit_status']==0
 row=next(y for y in q['six_fixture_rows'] if y['name']=='cu-withdrawal-13')
 assert row['candidate_settlement_cu']==x['withdrawal13_settlement_cu']
 assert x['exceeds_allowance_by']==row['candidate_settlement_cu']-1148950>0
print(json.dumps({'status':'PASS','source_cuts':len(pins['cuts']),'reuse':'exact emitted types and both loop definitions','proof':'exact ZERO/public body, public declaration renamed only','runtime':'six fixtures and stack PASS for three variants; all fail settlement allowance','scope':'CANDIDATE NOT ADOPTED'},indent=2))
