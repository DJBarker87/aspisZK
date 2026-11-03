from pathlib import Path
import subprocess,hashlib
from NEQ_install import install
from NEQ_artifacts import ref,theorem,native_support
from NEQ_decode_checks import FUNCTIONS,PAIRS,THEOREMS,body
E=Path(__file__).resolve().parent;R=E.parent.parent
for case,f in FUNCTIONS.items():
 source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],cwd=R,text=True);b=body(source,case)
 ts=[theorem(*n.rsplit('.',1)) for n in THEOREMS[case]];attempts=sorted({a for pair in PAIRS[case] for a in pair});native=native_support(attempts)
 q=dict(function=f,case=case,pairs=PAIRS[case],method='actual frozen pure caller, complete Result/value and immutable frame; named emitted definition law',domain={'header':'every typed216-byte header, arbitrary magic and either kind','m31':'every four raw bytes','digest':'every typed32-byte input; every accepted output limb and all rejections'}[case],native_support=native,theorems=ts,manifests=[ref(E/(a+'-decode-scalar.json')) for a in attempts],inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',empty_external_modifies=True,ordered_effects=[],all_return_variants=True,all_typed_inputs=True,frozen_body=b,frozen_body_sha256=hashlib.sha256(b.encode()).hexdigest(),same_child_input='every i<8 passes original bytes[4*i..4*i+4] as a typed4 array')
 install(f,'decode_scalar',q,ts,native,ts,ts,'Direct frozen native scalar/header/unrolled8 decode runs on every typed byte input. The same original byte array supplies all checks and every output limb. Full Err/None rejection and exact successful value are paired with failing changed-value and changed-bound/argument controls under KMX, frozen graph/features/lock and local-record rules. Inputs are immutable; all selected children are pure, so external state and ordered effects are unchanged. The named emitted definition law gives the complete model Result, not an accepted-input restriction. Each M31 call receives exactly four original bytes and proves canonical output only after its own acceptance guard. No field multiplication or protocol loop is evaluated.')
