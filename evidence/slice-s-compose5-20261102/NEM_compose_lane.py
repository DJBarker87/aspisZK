from pathlib import Path
import subprocess,json,hashlib
from NEM_install import install
from NEM_artifacts import ref,theorem
from NEM_lane_checks import P
E=Path(__file__).resolve().parent;L=E.parent/'slice-s-compose4-20261101';D=E.parent/'slice-s-compose-20261029'
for case in ['first','lane']:
 f=P+('first_canonical_byte' if case=='first' else 'pool_v1_pair_forest_output_lane_v1');source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],text=True);header='fn first_canonical_byte(' if case=='first' else 'pub fn pool_v1_pair_forest_output_lane_v1(';a=source.index(header);z=source.index('\n}',a)+2;body=source[a:z]
 pairs=[['NEL_K030','NEL_K031'],['NEL_K058','NEL_K059']] if case=='first' else [['NEL_K002','NEL_K003'],['NEL_K058','NEL_K059']]
 support=[ref(L/n) for pair in pairs for a in pair for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
 ts=[theorem('NED_SubtreeComposition','first_byte',D),theorem('NED_DigestCohorts','first_byte',D)] if case=='first' else [theorem('NEM_LaneReached','lane_instance'),theorem('NEM_LaneReached','lane_reached')]
 q=dict(case=case,function=f,method='reused NEL total native Result/order and exact immutable argument frames',all_raw_digests=True,empty_external_modifies=True,full_Result=True,trust_classification='P6/D188 option A reclassification',native_pairs=pairs,native_support=support,frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),child_log='encode(same raw digest), return reply[0]' if case=='first' else 'canonical(same nullifier); if true first(same nullifier); no later call on error',theorems=ts)
 install(f,'lane_composition',q,ts,[ref(L/a/'receipt.json') for pair in pairs for a in pair],ts[:1],ts[1:],'Frozen '+case+' caller on every raw digest: exact same immutable digest carrier, local log initialized by caller, arbitrary full child reply and Result, no external mutation. Native NEL caller/field certificates and corrected corrupt-reply controls are reused unchanged. Selected scanner/serializer/first-byte child domains are total on the exact argument; rejection prefixes and source call order are retained. The emitted/model instance supplies the reached law on that same nullifier. P6/D188 option A reclassification.')
