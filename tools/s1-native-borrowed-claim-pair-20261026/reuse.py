#!/usr/bin/env python3
"""Re-pin the already extracted borrowed-helper reference, without replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
D=Path(__file__).resolve().parent
old=E/'s1-claim-owned-reference/borrowed-abi-extraction'
new=E/'s1-native-borrowed-helper-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
reference=(D/'reference.rs').read_text();assert reference in(new/'input/lib.rs').read_text()
assert load(new/'historical-attempts/s1-claim-owned-nested-charon-v10/receipt.json')['exit_status']==0
assert load(new/'historical-attempts/s1-claim-owned-nested-aeneas-v10/receipt.json')['exit_status']==0
rows={}
for name in ['Types.lean','Funs.lean','FunsExternal_Template.lean','TypesExternal_Template.lean']:
 a=old/'generated/AspisS1OwnedNestedClaim'/name
 b=new/'historical-generated/AspisS1OwnedNestedClaim'/name
 left,right=a.read_text(),b.read_text()
 if name=='Funs.lean':
  # Retain EVERY non-documentation byte, including all whitespace, strings,
  # attributes, function bodies and source/external operation names.
  left=re.sub(r'/--[\s\S]*?-/', '',left)
  right=re.sub(r'/--[\s\S]*?-/', '',right)
 assert left==right,name
 rows[name]={'older_path':str(a.relative_to(R)),'older_sha256':sha(a),
             'borrowed_path':str(b.relative_to(R)),'borrowed_sha256':sha(b),
             'comparison':'exact non-doc bytes'if name=='Funs.lean'else'exact bytes'}
accepted=load(E/'accepted-targets.json')['targets']
targets={}
for module,attempt in [('S1ClaimBorrowedAbiNativeV1','s1-claim-borrowed-abi-native-v1'),
                       ('S1ClaimBorrowedAbiTransportV1','s1-claim-borrowed-abi-transport-v2')]:
 # The native source module's receipt name is discovered from the accepted
 # inventory; no guess or unverified cache is selected.
 record=accepted[module];p=E/record['receipt'];receipt=load(p)
 assert receipt['exit_status']==0 and receipt['swaps']==0
 assert sha(S/(module+'.lean'))==receipt['source_sha256']==record['source_sha256']
 assert (E/p.parent.name/'source.lean').read_bytes()==(S/(module+'.lean')).read_bytes()
 targets[module]={'source_sha256':receipt['source_sha256'],'object_sha256':receipt['object_sha256'],
                  'receipt':str(p.relative_to(E)),'print_axioms':receipt['print_axioms']}
report={'schema':'focused-extractor-proof-packet-v1','reference_sha256':sha(D/'reference.rs'),
 'reference_is_literal_historical_rust_fragment':True,'raw_program_comparisons':rows,
 'accepted_reference_targets':targets,'compiler_replayed':False,
 'normal_return_native_original_binding_proved':False,
 'qualification':'Same entire emitted program modulo ONLY documentation comments. Existing complete Result/reference proof is reused with its original primitive/carrier/extraction qualifications. This metadata check alone proves no native caller equivalence.'}
print(json.dumps(report,indent=2))
