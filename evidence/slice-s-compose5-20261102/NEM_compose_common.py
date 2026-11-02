from pathlib import Path
import json,hashlib,subprocess
from NEM_artifacts import ref,theorem,native_support
from NEM_install import install
from NEM_common_checks import FUNCTION,PAIRS
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose3-20261101';L=E.parent/'slice-s-compose4-20261101'
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+FUNCTION.split('::')[0]],text=True);a=source.index('fn encode_common(');z=source.index('\n}',a)+2;body=source[a:z]
pairs=[['NEM_K006','NEM_K007'],['NEM_K008','NEM_K009'],['NEM_K010','NEM_K011']]
support=native_support([a for p in pairs for a in p])
for pair in PAIRS:
 for a in pair:support += [ref(P/n) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEJ_native_contracts.patch',a+'-NEJ_oracle.patch']]
ts=[theorem('NEJ_CommonSourceFrame','result_and_frame',P),theorem('NEJ_CommonFrame','common_bytes',P),theorem('NEJ_WindowStep','iteration',P),theorem('NEL_CopyArrayLaw','loop_binding',L)]
q=dict(function=FUNCTION,method='source-ordered window composition with same-call child instances',all_typed_inputs=True,same_complete_prestate=True,trust_classification='P6/D188 option A reclassification',windows=[[0,4],[4,1],[5,1],[6,1],[8,32],[40,32],[72,8],[80,32],[112,32],[144,4]],native_pairs=pairs,inherited_windows=[list(p) for p in PAIRS],frame='only bytes [0,7) union [8,148); original byte 7 and suffix >=148 preserved',empty_child_modifies=True,reply_widths=[32,32,4],ordered_children=['common.anchor_root','common.nullifier','common.asset_id'],frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),statements=[x.strip()+';' for x in body[body.index('    output[..4]'):body.rindex('}')].split(';') if x.strip()],theorems=ts,native_support=support)
install(FUNCTION,'common_composition',q,ts,[ref(E/a/'receipt.json') for p in pairs for a in p],ts[:1],ts[1:],'Actual encode_common same mutable 216-byte allocation and arbitrary prestate. The ten frozen ordered windows and their exact value/frame contracts compose by KMX induction and the emitted result_and_frame theorem. Anchor/nullifier/asset child instances use the actual immutable fields and fixed reply widths; all raw domains are total and child external modifies empty. No canonical input restriction is introduced. The asset_id is M31, so the WideExact candidate is excluded. P6/D188 option A reclassification.',alternatives=['crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'])
