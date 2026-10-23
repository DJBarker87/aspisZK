#!/usr/bin/env python3
"""Read-only focused evidence and adopted source pin audit; no Lean replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-borrowed-caller-import-pins.json')
rows={'S1BorrowedClaimPreparedBoundaryV1':'s1-borrowed-claim-prepared-boundary-v2',
      'S1BorrowedClaimFirstCallerV1':'s1-borrowed-claim-first-caller-v2',
      'S1BorrowedClaimConcreteCallerV1':'s1-borrowed-claim-concrete-caller-v1'}
reports=0
for module,attempt in rows.items():
 r=load(E/attempt/'receipt.json');p=S/(module+'.lean')
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==a[module]['source_sha256']==pins['targets'][module]['source_sha256']
 assert r['object_sha256']==pins['targets'][module]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for line in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',line,re.S)
  assert m and set(re.findall(r'[A-Za-z_.]+',m[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
pin=load(E/'s1-borrowed-caller-powers-repin.json');rev=pin['freeze']
for path,h in pin['source_sha256'].items():
 b=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path])
 assert hashlib.sha256(b).hexdigest()==h
weights=subprocess.check_output(['git','-C',str(R),'show',rev+':crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
old=(B/'lean-candidates/s1-early-return-powers-proved-candidate-20261020/extraction-input/lib.rs').read_text()
assert pin['powers_body'] in weights and pin['powers_body'] in old
assert pin['original_prepared_new'].count('powers::<29>(gamma)')==1
assert 'prepared_claim(sem,v.y1,v.inactive,g,kappa)?' in pin['original_prepared_new']
assert 'let k=powers::<7>(kappa);' in pin['original_prepared_claim']
print(json.dumps(dict(accepted_targets=len(rows),standard_axiom_reports=reports,
 borrowed_reference_installed_in_enclosing_first=True,exact_early_return_powers_body_repinned=True,
 same_returned_gamma_scratch_proved=True,original_native_claim_whole_binding=False,
 actual_sdk_binding=False,whole_s1_closed=False,whole_s6_closed=False)))
