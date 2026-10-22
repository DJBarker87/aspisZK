#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=next(x for x in D.parents if (x/'.git').exists());P=R/'docs/research/100bit-spend-path-20261013'
Z=P/'lean-candidates/s1-zero-loop-powers-proved-candidate-20261020'
sha=lambda b:hashlib.sha256(b).hexdigest()
p=json.loads((D/'extraction-input/source-pins.json').read_text())
for f,h in p['kit_files'].items():assert sha((D/'extraction-input'/f).read_bytes())==h,f
for c in p['cuts']:
 b=subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+c['path']]);assert sha(b)==c['file_sha256'];assert sha(b[c['start_byte']:c['end_byte_exclusive']])==c['sha256']
assert (D/'extraction-input/lib.rs').read_text().count(p['candidate_transform']['after'])==1
z=D/'diagnostics/raw-generated/AspisR1LoopPowers';old=Z/'diagnostics/raw-generated/AspisR1LoopPowers'
assert (z/'Types.lean').read_bytes()==(old/'Types.lean').read_bytes()
def block(t,n):
 s=t.index('def '+n);e=t.find('\n/--',s);return t[s:e if e!=-1 else t.index('\nend AspisR1LoopPowers',s)].strip()
f=(z/'Funs.lean').read_text();g=(old/'Funs.lean').read_text()
for n in ['field.CM31.ZERO','field.CM31.ONE','field.QM31.ZERO','field.QM31.ONE','field.WideExact.ZERO','field.WideExact.ONE']:
 if 'def '+n in f:assert block(f,n)==block(g,n),n
src=(D/'sources/LoopPowersEarlySteps.lean').read_text()
chunk=f[f.index('@[rust_loop_body]'):f.index('/-- [aspis_r1_current_powers::powers_entry]')].replace('weights.powers','weights.early_powers')
assert src.count(chunk)==1
for s in (D/'sources').glob('*.lean'):assert 'sorry' not in s.read_text() and 'axiom ' not in s.read_text()
x=json.loads((D/'prereg-fixture-comparison.json').read_text());assert len(x['rows'])==6
q=json.loads((D/'measurements/gates/result.json').read_text());assert q['strict_stack_receipt']['exit_status']==0
assert q['artifact_sha256']=='c9926274dcc16eab6d09d91f39af5e38ee6149cfb6dceb76ff6c666846e5a648'
for a,b in zip(x['rows'],q['six_fixture_rows']):
 assert a['name']==b['name'] and a['candidate_stage1_cu']==b['candidate_stage1_cu'] and a['candidate_settlement_cu']==b['candidate_settlement_cu']
 assert a['stage1_pass'] and a['settlement_pass'] and a['candidate_stage1_cu']<=a['stage1_allowance'] and a['candidate_settlement_cu']<=a['settlement_allowance']
 assert b['receipt']['exit_status']==0 and b['return_data_same'] and b['stage1_checkpoint_tail_same']
np=json.loads((D/'native/source-pins.json').read_text())
assert sha((D/'native/input/main.rs').read_bytes())==np['main_sha256']
for c in np['files']:assert sha(subprocess.check_output(['git','-C',str(R),'show','b2727acd3:'+c['path']]))==c['sha256']
samples=json.loads((D/'native/sample-inputs.json').read_text());assert len(samples)==268
assert all(len(x)==8 and all(0<=v<2147483647 for v in x) for x in samples)
for n in ['compile','test']:assert json.loads((D/'native/evidence'/(n+'-receipt.json')).read_text())['exit_status']==0
print(json.dumps({'status':'PASS','source_cuts':len(p['cuts']),'model':'raw types/constants reused; exact emitted functions renamed only','runtime':'six output-preserving fixtures, stack and prereg item1 PASS','scope':'PROVED CANDIDATE NOT ADOPTED; other release gates and full soundness OPEN'},indent=2))
