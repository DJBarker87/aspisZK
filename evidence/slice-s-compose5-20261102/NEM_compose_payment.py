from pathlib import Path
import subprocess,json,hashlib
from NEM_install import install
from NEM_artifacts import ref,theorem,native_support
from NEM_payment_checks import CASES,P
E=Path(__file__).resolve().parent;L=E.parent/'slice-s-compose4-20261101'
for case,spec in CASES.items():
 f=spec['function'];name=f.split('::')[1];source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],text=True);a=source.index('pub fn '+name+'(');z=source.index('\n}',a)+2;body=source[a:z]
 support=native_support(spec['prefix']+[a for pair in spec['suffix'] for a in pair])
 for pair in spec['frames']:
  for a in pair:support += [ref(L/n) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
 ts=[theorem('NEM_PaymentFrame',case+'_reply'),theorem('NEM_PaymentReached','payment_instance'),theorem('NEM_PaymentReached','payment_reached')]
 if case=='transfer':ts += [theorem('NEM_PaymentFrame','common_reserved')]
 q=dict(case=case,function=f,method='native rejection prefix and source-ordered KMX suffix frames',all_typed_inputs=True,full_Result_and_bytes=True,empty_external_modifies=True,trust_classification='P6/D188 option A reclassification',prefix=spec['prefix'],suffix=spec['suffix'],frames=spec['frames'],fields=spec['fields'],windows=spec['windows'],child_domains='all typed public/common records and all raw digests; validator acceptance only selects continuation',common_frame_subject=P+'encode_common',no_inner_native_hypotheses=True,native_support=support,frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),theorems=ts)
 install(f,'payment_encode_composition',q,ts,[ref(E/a/'receipt.json') for a in spec['prefix']+[a for pair in spec['suffix'] for a in pair]],ts[:1],ts[1:],'Actual '+case+' encoder: exact native validator prefix on the actual public borrow; full arbitrary error Result with continuation only on Ok. Caller zero initializes one local 216-byte allocation. The composed common child receives the selected magic/kind and same closed common projection. Each actual suffix field/child reply is bound to its disjoint KMX window on an arbitrary prestate; untouched bytes compose by the accepted frame/induction laws. Transfer debug fee is preserved as zero before the suffix. The complete emitted reply and external frame instantiate NEE payment_reached on the same argument. No accepted-run premise, stronger child domain, or inner physical hypothesis remains. P6/D188 option A reclassification.',alternatives=(["crates/aspis-core/src/field.rs::M31::to_le_bytes","crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes"] if case=='withdrawal' else []))
