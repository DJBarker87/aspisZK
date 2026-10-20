#!/usr/bin/env python3
"""Check the exact generated-source cut and selected focused evidence; no Lean replay."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
P=D.parent.parent
raw=(P/'lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/diagnostics/raw-generated/AspisR1CurrentPreparedClaim/Funs.lean').read_text()
sha=lambda b:hashlib.sha256(b).hexdigest()
a=raw.index('/-- [core::result::');b=raw.index('/-- [aspis_r1_verify_prepared_prefix::aspis_core::field::')
glue=raw[a:b]
a=raw.index('/-- [aspis_r1_verify_prepared_prefix::verifier::prepared_claim_dot::');b=raw.rindex('end AspisR1CurrentPreparedClaim');body=raw[a:b]
ops='''
structure ClaimDotOps (D : Type) where
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  field : Slice U8 → Usize → Result aspis_core.field.WideExact
  c0 : aspis_core.field.WideExact → Result aspis_core.field.QM31
  newDot : Result D
  pushDot : D → aspis_core.field.WideExact → aspis_core.field.QM31 → Result (core.result.Result Unit Unit × D)
  finishDot : D → Result aspis_core.field.WideExact
'''
extern={'aspis_core.field.WideExact.impl.c0':'ops.c0','weights.powers':'ops.powers','weights.field':'ops.field','fast_pairing.EbyKDot.new':'ops.newDot','fast_pairing.EbyKDot.push':'ops.pushDot','fast_pairing.EbyKDot.finish':'ops.finishDot'}
for old,new in sorted(extern.items(),key=lambda x:-len(x[0])):body=body.replace(old,new)
body=body.replace('fast_pairing.EbyKDot','D')
names=['verifier.prepared_claim_dot_loop.body','verifier.prepared_claim_dot_loop','verifier.prepared_claim_dot','verifier.prepared_claim_loop.body','verifier.prepared_claim_loop','verifier.prepared_claim']
# Token-exact changes avoid treating name prefixes as independent occurrences.
pat=re.compile(r'(?<![\w.])('+ '|'.join(re.escape(x) for x in sorted(names,key=len,reverse=True))+r')(?![\w.])')
body=pat.sub(lambda m:m[1]+' ops',body)
for n in names:
 needle='def '+n+' ops';assert body.count(needle)==1,(n,body.count(needle));body=body.replace(needle,'def '+n+'\n  {D : Type} (ops : ClaimDotOps D)',1)
t='import CurrentClaimSumTotal\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace AspisR1CurrentPreparedClaim\n'+ops+glue+body
for n in names:t+='\n#print axioms '+n
# The generic model intentionally assumes no laws about its child callbacks.
t+='\nend AspisR1CurrentPreparedClaim\n'

assert (D/'sources/CurrentClaimDotModel.lean').read_text()==t
adapter=json.loads((D/'adapter.json').read_text())
assert adapter['raw_funs_sha256']==sha(raw.encode())
assert adapter['extern_substitutions']==extern
assert adapter['ops_threaded_functions']==names
manifest=json.loads((D/'manifest.json').read_text())
for m in manifest['modules']:
 src=(D/m['source']).read_bytes()
 assert sha(src)==m['source_sha256'],m['module']
 assert not re.search(r'\b(sorry|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',src.decode()),m['module']
 rec=json.loads((D/m['receipt']).read_text())
 assert rec['exit_status']==0 and rec['scope_swap_peak_bytes']==0,m['module']
 assert rec['object_sha256']==m['object_sha256'] and rec['source_sha256']==m['source_sha256']
 log=(D/m['receipt']).with_name('lean.log').read_text()
 reports=re.findall(r"depends on axioms: \[([^\]]*)\]",log)
 assert reports,m['module']
 for report in reports:
  assert set(re.findall(r'[A-Za-z_.]+',report))<={'propext','Classical.choice','Quot.sound'},report
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1)
 assert sha((D/name).read_bytes())==h,name
print('PASS: exact six-declaration Ops cut; six green pinned sources/receipts; standard axioms; file hashes')
