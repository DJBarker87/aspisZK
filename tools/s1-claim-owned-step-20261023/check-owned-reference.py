#!/usr/bin/env python3
"""Audit the accepted reference closure; never replay unchanged proofs."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'tools/s1-claim-owned-step-20261023/check.py')],check=True)
subprocess.run(['python3',str(R/'tools/s1-claim-uf-20261023/check.py')],check=True)
pins=load(E/'s1-claim-owned-reference-import-pins.json')
accepted=load(E/'accepted-targets.json')['targets']
rows={
 'S1ClaimOwnedNestedModelV1':'s1-claim-owned-model-v3',
 'S1ClaimOwnedNestedTransferV1':'s1-claim-owned-transfer-v13',
 'S1ClaimOwnedNestedLoopsV1':'s1-claim-owned-loops-v4',
 'S1ClaimOwnedInnerCompleteV1':'s1-claim-owned-inner-complete-v1',
 'S1ClaimOwnedInnerCpsV1':'s1-claim-owned-inner-cps-v1',
 'S1ClaimOwnedOuterStepV1':'s1-claim-owned-outer-step-v2',
 'S1ClaimOwnedOuterCompleteV1':'s1-claim-owned-outer-complete-v5',
}
reports=0
for module,attempt in rows.items():
 p=S/(module+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==accepted[module]['source_sha256']==pins['targets'][module]['source_sha256']
 assert r['object_sha256']==pins['targets'][module]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for report in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
  assert m and set(re.findall(r'[A-Za-z_.]+',m[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
assert reports==23
mat=load(E/'s1-claim-owned-reference/materialization.json')
assert mat['candidate_sha256']==sha(S/'S1ClaimOwnedNestedModelV1.lean')
assert mat['raw_sha256']==sha(E/'s1-claim-owned-reference/raw-generated/AspisS1OwnedNestedClaim/Funs.lean')
original=load(E/'s1-claim-owned-reference/native-source-step-strict/input/source-binding.json')['original_claim']
freeze=load(E/'s1-claim-owned-reference/native-dependency-freeze-comparison.json')['revision']
rust=subprocess.check_output(['git','-C',str(R),'show',freeze+':crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
assert original in rust
assert original in (E/'s1-claim-owned-reference/native-source-step-strict/input/src/lib.rs').read_text()
print(json.dumps(dict(accepted_modules=len(rows),standard_axiom_reports=reports,
 whole_owned_reference_result_equivalence=True,inner_outer_finite_control=True,
 native_original_caller_binding=False,actual_child_totality_closed=False,whole_s1_closed=False,whole_s6_closed=False)))
