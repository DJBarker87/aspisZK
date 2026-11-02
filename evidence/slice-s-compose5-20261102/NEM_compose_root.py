from pathlib import Path
import subprocess,json,hashlib
from NEM_install import install
from NEM_artifacts import ref,theorem
from NEM_root_checks import F,CHILDREN
E=Path(__file__).resolve().parent;R=E.parent.parent
P=R/'evidence/slice-s-compose2-20261029';L=R/'evidence/slice-s-compose4-20261101'
required=[]
for folder,prefix,pair in [(P,'NEE_',['NEE_K052','NEE_K053']),(L,'NEL_',['NEL_K006','NEL_K007'])]:
 required += [ref(folder/n) for a in pair for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-'+prefix+'native_contracts.patch',a+'-'+prefix+'oracle.patch']]
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+F.split('::')[0]],cwd=R,text=True);a=source.index('pub fn '+F.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
ts=[theorem(*p) for p in [('NEM_ValidatorComposed','result_state_effects'),('NEM_PaymentReached','payment_reached'),('NEM_LaneReached','lane_reached'),('NEM_LateOracle','late_reached')]]
q=dict(function=F,method='ruling y: frozen native caller, CLOSED child substitutions on same calls, concrete G theorem',child_functions=CHILDREN,inner_hypotheses_remaining=[],domain='every typed terminal Statement; valid root physical carrier; no acceptance or inner domain premise',trust_classification='P6/D188 option A reclassification',native_pairs=[['NEE_K052','NEE_K053'],['NEL_K006','NEL_K007']],native_support=required,frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),full_Result=True,ordered_effects=True,empty_external_modifies=True,late_buffer='same locally zero-initialized 1520-byte allocation; arbitrary complete child mutation never escapes',theorems=ts)
install(F,'validator_root',q,ts,required,ts[1:],ts,'Actual frozen root caller is identical after erasing the native oracle call-log instrumentation. NEE_K052/053 and NEL_K006/007 bind payment, lane and late calls to the same typed statement fields, complete Results, local zeroed late buffer and ordered effects. CLOSED children establish every reached domain; the concrete G theorem substitutes their laws without inner hypotheses. Native semantic transport is the approved P6/D188 option A reclassification. Root own typed PacketDomain and PhysicalInterpretation remain the ambient native bridge domain, never an acceptance or conclusion premise.')
