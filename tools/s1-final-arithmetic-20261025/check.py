#!/usr/bin/env python3
"""Source-only checker for accepted final arithmetic; no compiler replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-final-arithmetic-20261025';T=Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so'],rel
j=json.loads((T/'source-factor-binding.json').read_text());old=(R/j['operation_source']).read_text();oldp=(R/j['proof_source']).read_text();new=(R/j['maintained']).read_text();assert sha(R/j['operation_source'])==j['operation_source_sha256']and sha(R/j['proof_source'])==j['proof_source_sha256']and sha(R/j['maintained'])==j['maintained_sha256']
a=old.index('def add (');b=old.index('def mask (',a);a2=oldp.index('def decodeQ');b2=oldp.index('#print axioms add_total')
for chunk,h in [(old[a:b],j['operation_chunk_sha256']),(oldp[a2:b2],j['proof_chunk_sha256'])]:assert chunk in new and hashlib.sha256(chunk.encode()).hexdigest()==h
q=subprocess.run([sys.executable,str(T/'materialize-sdk.py'),'--check'],capture_output=True,text=True,cwd=R);assert q.returncode==0,q.stdout+q.stderr
# SDK statement: old binders/post are retained under the explicit add/mul
# source-instance substitution; only one stronger output predicate is added.
old=(S/'S1SdkCanonicalMaskV1.lean').read_text();new=(S/'S1SdkFinalArithmeticV1.lean').read_text();expected=old.replace('    (base : AspisR1PublicPreparation.FinishModel.Boundaries)','    (backend : AspisR1PublicPreparation.FinishModel.Boundaries)');expected=re.sub(r'\bbase\b','(AspisS1SourceFinalOps.install backend)',expected)
def signature(s):return s[s.index(' {W A M Cv : Type}'):s.index(' :\n    post =')]
def post(s):return s[s.index(' :\n    post ='):s.index(' := by')]
assert signature(new)==signature(expected)
extra=json.loads((T/'sdk-binding.json').read_text())['added_conjunct'];assert post(new).replace(extra,'')==post(expected)
# The actual successful source multiplication, not numeric input restrictions,
# is the only premise of the new generic result-canonicality theorems.
s=(S/'S1AcceptedProductCanonicalV1.lean').read_text()
for name in ['cm_mul_success_canonical','qm_mul_success_canonical','generated_mul_success_canonical']:
 sig=s[s.index('theorem '+name):];sig=sig[:sig.index(' := by')]
 assert '(hx :'not in sig and '(hy :'not in sig and '(h :'in sig
metrics=json.loads((P/'metrics.json').read_text());audits=0
for row in metrics['targets']:
 d=E/row['attempt'];j=json.loads((d/'receipt.json').read_text());src=R/row['source'];assert j['exit_status']==0 and j['swaps']==0 and j['source_sha256']==sha(src)==sha(d/'source.lean')
 assert '-j1'in j['command']and '-M4400'in j['command']and j['print_axioms']
 assert not re.search(r'(?m)^\s*axiom\b|\b(sorry|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',src.read_text())
 for a in j['print_axioms']:
  assert 'sorryAx'not in a
  v=re.findall(r'\[(.*?)\]',a,re.S)
  if v:assert set(v[0].replace(' ','').replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'},a
 audits+=len(j['print_axioms'])
assert len(metrics['targets'])==4 and audits==12
# Reused same-caller mask/selector/native evidence is checked as data only.
q=subprocess.run([sys.executable,str(R/'tools/s1-mask-caller-domains-20261025/check.py')],capture_output=True,text=True,cwd=R);assert q.returncode==0,q.stdout+q.stderr
print(f'PASS {len(m["files"])} pins, four focused targets/12 standard-only audits. Reached final arithmetic output ranges derived on SAME conditional SDK/source witness without Terminal input canonicality. Raw-input TOTAL, unconditional product-field formula and whole S1/S6/native/security joins remain OPEN.')
